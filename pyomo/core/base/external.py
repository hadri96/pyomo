#  ___________________________________________________________________________
#
#  Pyomo: Python Optimization Modeling Objects
#  Copyright 2017 National Technology and Engineering Solutions of Sandia, LLC
#  Under the terms of Contract DE-NA0003525 with National Technology and 
#  Engineering Solutions of Sandia, LLC, the U.S. Government retains certain
#  rights in this software.
#  This software is distributed under the 3-clause BSD License.
#  ___________________________________________________________________________

import logging
import os
import types
import weakref

from ctypes import (
    Structure, POINTER, CFUNCTYPE, cdll, byref,
    c_int, c_long, c_ulong, c_double, c_byte, c_char_p, c_void_p )

from pyomo.core.expr.numvalue import native_types, NonNumericValue
from pyomo.core.expr import current as EXPR
from pyomo.core.base.component import Component
from pyomo.core.base.units_container import units

__all__  = ( 'ExternalFunction', )

logger = logging.getLogger('pyomo.core')


class ExternalFunction(Component):

    def __new__(cls, *args, **kwargs):
        if cls is not ExternalFunction:
            return super(ExternalFunction, cls).__new__(cls)
        elif args and len(args) <= 3 and all(
                isinstance(arg, types.FunctionType) for arg in args):
            return super(ExternalFunction, cls).__new__(PythonCallbackFunction)
        elif not args and 'library' not in kwargs and any(
                kw in kwargs and isinstance(kwargs[kw], types.FunctionType)
                for kw in ('function', 'fgh')):
            return super(ExternalFunction, cls).__new__(PythonCallbackFunction)
        else:
            return super(ExternalFunction, cls).__new__(AMPLExternalFunction)

    def __init__(self, *args, **kwargs):
        self._units = kwargs.pop('units', None)
        if self._units is not None:
            self._units = units.get_units(self._units)
        self._arg_units = kwargs.pop('arg_units', None)
        if self._arg_units is not None:
            self._arg_units = [units.get_units(u) for u in self._arg_units]
        kwargs.setdefault('ctype', ExternalFunction)
        Component.__init__(self, **kwargs)
        self._constructed = True
        ### HACK ###
        # FIXME: We must declare an _index attribute because
        # block._add_temporary_set assumes ALL components define an
        # index.  Sigh.
        self._index = None

    def get_units(self):
        """Return the units for this ExternalFunction"""
        return self._units

    def get_arg_units(self):
        """Return the units for this ExternalFunctions arguments"""
        return self._arg_units

    def __call__(self, *args):
        args_ = []
        for arg in args:
            if type(arg) is types.GeneratorType:
                args_.extend(val for val in arg)
            else:
                args_.append(arg)
        #
        # Loop and do two thing:
        #   1. Wrap non-numeric arguments
        #   2. See if we have a potentially variable argument
        #
        pv = False
        for i,arg in enumerate(args_):
            try:
                # Q: Is there a better way to test if a value is an object
                #    not in native_types and not a standard expression type?
                if arg.__class__ in native_types:
                    continue
                if arg.is_potentially_variable():
                    pv = True
            except AttributeError:
                args_[i] = NonNumericValue(arg)
        #
        if pv:
            return EXPR.ExternalFunctionExpression(args_, self)
        return EXPR.NPV_ExternalFunctionExpression(args_, self)

    def evaluate(self, args):
        args_ = [arg if arg.__class__ in native_types else value(arg)
                 for arg in args]
        return self._evaluate(args_, 0, None)[0]

    def evaluate_fgh(self, args, fixed=None, fgh=2):
        args_ = [arg if arg.__class__ in native_types else value(arg)
                 for arg in args]
        f, g, h = self._evaluate(args_, fgh, fixed)
        # Note: the ASL does not require clients to honor the fixed flag
        # (allowing them to return non-0 values for the derivative with
        # respect to a fixed numeric value).  We will allow clients to
        # be similarly lazy and enforce the fixed flag here.
        if fixed is not None:
            if fgh > 0:
                for i, v in enumerate(fixed):
                    if not v:
                        continue
                    g[i] = 0
            if fgh > 1:
                N = len(args_)
                for i, v in enumerate(fixed):
                    if not v:
                        continue
                    for j in range(N):
                        if i <= j:
                            h[i + (j*(j + 1))//2] = 0
                        else:
                            h[j + (i*(i + 1))//2] = 0
        return f, g, h

    def _evaluate(self, args):
        raise NotImplementedError(
            f"{type(self)} did not implement _evaluate()" )


class AMPLExternalFunction(ExternalFunction):

    def __init__(self, *args, **kwargs):
        if args:
            raise ValueError(
                "AMPLExternalFunction constructor does not support "
                "positional arguments" )
        self._library = kwargs.pop('library', None)
        self._function = kwargs.pop('function', None)
        self._known_functions = None
        self._so = None
        ExternalFunction.__init__(self, *args, **kwargs)

    def __getstate__(self):
        state = super(AMPLExternalFunction, self).__getstate__()
        # Remove reference to loaded library (they are not copyable or
        # picklable)
        state['_so'] = state['_known_functions'] = None
        return state

    def _evaluate(self, args, fgh, fixed):
        if self._so is None:
            self.load_library()
        if self._function not in self._known_functions:
            raise RuntimeError(
                "Error: external function %s was not registered within "
                "external library %s.\n\tAvailable functions: (%s)"
                % ( self._function, self._library,
                    ', '.join(self._known_functions.keys()) ) )
        #
        N = len(args)
        arglist = _ARGLIST(args, fgh, fixed)
        fcn = self._known_functions[self._function][0]
        f = fcn(byref(arglist))
        if fgh > 0:
            g = [arglist.derivs[i] for i in range(N)]
        else:
            g = None
        if fgh > 1:
            h = [arglist.hes[i] for i in range((N + N**2)//2)]
        else:
            h = None
        return f, g, h

    def load_library(self):
        try:
            self._so = cdll.LoadLibrary(self._library)
        except OSError:
            # On Linux, it is uncommon for "." to be in the
            # LD_LIBRARY_PATH, so if things fail to load, attempt to
            # locate the library via a relative path
            try:
                self._so = cdll.LoadLibrary(os.path.join('.',self._library))
            except OSError:
                # Re-try with the original library name and allow the
                # exception to propagate up.
                self._so = cdll.LoadLibrary(self._library)

        self._known_functions = {}
        AE = _AMPLEXPORTS()
        AE.ASLdate = 20160307
        def addfunc(name, f, _type, nargs, funcinfo, ae):
            # trap for Python 3, where the name comes in as bytes() and
            # not a string
            if not isinstance(name, str):
                name = name.decode()
            self._known_functions[str(name)] = (f, _type, nargs, funcinfo, ae)
        AE.Addfunc = _AMPLEXPORTS.ADDFUNC(addfunc)
        def addrandinit(ae, rss, v):
            # TODO: This should support the randinit ASL option
            rss(v, 1)
        AE.Addrandinit = _AMPLEXPORTS.ADDRANDINIT(addrandinit)
        def atreset(ae, a, b):
            logger.warning(
                "AMPL External function: ignoring AtReset call in external "
                "library.  This may result in a memory leak or other "
                "undesirable behavior.")
        AE.AtReset = _AMPLEXPORTS.ATRESET(atreset)

        FUNCADD = CFUNCTYPE( None, POINTER(_AMPLEXPORTS) )
        FUNCADD(('funcadd_ASL', self._so))(byref(AE))

    def _pprint(self):
        return (
            [ ('function', self._function),
              ('library', self._library),
              ('units', str(self._units)),
              ('arg_units', [ str(u) for u in self._arg_units ]
               if self._arg_units is not None else None),
            ],
            (), None, None
        )


class PythonCallbackFunction(ExternalFunction):
    global_registry = {}

    @classmethod
    def register_instance(cls, instance):
        _id = len(cls.global_registry)
        cls.global_registry[_id] = weakref.ref(instance)
        return _id

    def __init__(self, *args, **kwargs):
        for i, kw in enumerate(('function', 'gradient', 'hessian')):
            if len(args) <= i:
                break
            if kw in kwargs:
                raise ValueError(
                    "duplicate definition of external function through "
                    f"positional and keyword ('{kw}=') arguments")
            kwargs[kw] = args[i]
        if len(args) > 3:
            raise ValueError(
                "PythonCallbackFunction constructor only supports "
                "0 - 3 positional arguments" )
        self._fcn = kwargs.pop('function', None)
        self._grad = kwargs.pop('gradient', None)
        self._hess = kwargs.pop('hessian', None)
        self._fgh = kwargs.pop('fgh', None)
        if self._fgh is not None and any((self._fcn, self._grad, self._hess)):
            raise ValueError(
                "Cannot specify 'fgh' with any of "
                "{'function', 'gradient', hessian'}")

        # There is an implicit first argument (the function pointer), we
        # need to add that to the arg_units
        arg_units = kwargs.get('arg_units', None)
        if arg_units is not None:
            kwargs['arg_units'] = [None] + list(arg_units)

        # TODO: complete/distribute the pyomo_socket_server /
        # pyomo_ampl.so AMPL extension
        self._library = 'pyomo_ampl.so'
        self._function = 'pyomo_socket_server'
        ExternalFunction.__init__(self, *args, **kwargs)
        self._fcn_id = PythonCallbackFunction.register_instance(self)

    def __call__(self, *args):
        return super(PythonCallbackFunction, self).__call__(self._fcn_id, *args)

    def _evaluate(self, args, fgh, fixed):
        _id = args.pop(0)
        if _id != self._fcn_id:
            raise RuntimeError(
                "PythonCallbackFunction called with invalid Global ID" )
        if self._fgh is not None:
            f, g, h = self._fgh(args, fgh, fixed)
        else:
            f = self._fcn(*args)
            if fgh > 0:
                if self._grad is None:
                    raise RuntimeError(
                        "ExternalFunction {self.name} was not defined "
                        "with a gradient callback.  Cannot evaluate the "
                        "derivative of the function")
                g = self._grad(args, fixed)
            else:
                g = None
            if fgh > 1:
                if self._hess is None:
                    raise RuntimeError(
                        "ExternalFunction {self.name} was not defined "
                        "with a Hessian callback.  Cannot evaluate the "
                        "second derivative of the function")
                h = self._hess(args, fixed)
            else:
                h = None
        return f, g, h

    def _pprint(self):
        return (
            [ ('function', self._fcn.__qualname__),
              ('units', str(self._units)),
              ('arg_units', [ str(u) for u in self._arg_units[1:] ]
               if self._arg_units is not None else None),
            ],
            (), None, None
        )


class _ARGLIST(Structure):
    """Mock up the arglist structure from AMPL's funcadd.h

    This data structure is populated by AMPL when calling external
    functions (for both passing in the function arguments and retrieving
    the derivative/Hessian information.
    """

    _fields_ = [
        ('n', c_int),     # number of args
        ('nr', c_int),    # number of real input args
        ('at', POINTER(c_int)),  # argument types -- see DISCUSSION below
        ('ra', POINTER(c_double)),  # pure real args (IN, OUT, and INOUT)
        ('sa', POINTER(c_char_p)),  # symbolic IN args
        ('derivs', POINTER(c_double)),  # for partial derivatives (if nonzero)
        ('hes', POINTER(c_double)),  # for second partials (if nonzero)
        ('dig', POINTER(c_byte)),   # if (dig && dig[i]) { partials w.r.t.
                                    #	ra[i] will not be used }
        ('funcinfo', c_char_p),  # for use by the function (if desired)
        ('AE', c_void_p), # functions made visible (via #defines below)
        ('f', c_void_p),  # for internal use by AMPL
        ('tva', c_void_p),  # for internal use by AMPL
        ('Errmsg', c_char_p),  # To indicate an error, set this to a
			     # description of the error.  When derivs
                             # is nonzero and the error is that first
			     # derivatives cannot or are not computed,
			     # a single quote character (') should be
			     # the first character in the text assigned
			     # to Errmsg, followed by the actual error
			     # message.  Similarly, if hes is nonzero
                             # and the error is that second derivatives
			     # are not or cannot be computed, a double
			     # quote character (") should be the first
			     # character in Errmsg, followed by the
			     # actual error message text.
        ('TMI', c_void_p),     # used in Tempmem calls
        ('Private', c_char_p), # The following fields are relevant
			     # only when imported functions are called
			     # by AMPL commands (not declarations).
        ('nin', c_int),   # number of input (IN and INOUT) args
        ('nout', c_int),  # number of output (OUT and INOUT) args
        ('nsin', c_int),  # number of symbolic input arguments
        ('nsout', c_int), # number of symbolic OUT and INOUT args
        ]

    def __init__(self, args, fgh=0, fixed=None):
        super(_ARGLIST, self).__init__()
        N = len(args)
        self.n = self.nr = N
        self.at = (c_int*N)()
        self.ra = (c_double*N)()
        self.sa = None
        if fgh > 0:
            self.derivs = (c_double*N)(0.)
        if fgh > 1:
            self.hes = (c_double*((N+N*N)//2))(0.)

        for i,v in enumerate(args):
            self.at[i] = i
            self.ra[i] = v

        if fixed:
            # This has to be revisited if nr != ra
            self.dig = (c_byte*N)(0)
            for i,v in enumerate(fixed):
                if v:
                    self.dig[i] = 1

# The following "fake" class resolves a circular reference issue in the
# _AMPLEXPORTS datastructure
#
# Declare a dummy structure called _AMPLEXPORTS so that the symbol exists
# and the POINTER(_AMPLEXPORTS) call in the definition of ADDFUNC (needed
# to define AMPLExPORTS) will succeed.
class _AMPLEXPORTS(Structure):
    pass

class _AMPLEXPORTS(Structure):
    """Mock up the AmplExports structure from AMPL's funcadd.h

    The only thing we really need here is to be able to override the
    Addfunc function pointer to point back into Python so we can
    intercept the registration of external AMPL functions.  Ideally, we
    would populate the other function pointers as well, but that is
    trickier than it sounds, and at least so far is completely unneeded.
    """

    AMPLFUNC = CFUNCTYPE( c_double, POINTER(_ARGLIST) )

    ADDFUNC = CFUNCTYPE(
        None,
        c_char_p, AMPLFUNC, c_int, c_int, c_void_p,
        POINTER(_AMPLEXPORTS) )

    RANDSEEDSETTER = CFUNCTYPE(
        None,
        c_void_p, c_ulong )

    ADDRANDINIT = CFUNCTYPE(
        None,
        POINTER(_AMPLEXPORTS), RANDSEEDSETTER, c_void_p )

    ATRESET = CFUNCTYPE(
        None,
        POINTER(_AMPLEXPORTS), c_void_p, c_void_p )

    _fields_ = [
	('StdErr', c_void_p),
	('Addfunc', ADDFUNC),
	('ASLdate', c_long),
	('FprintF', c_void_p),
	('PrintF', c_void_p),
	('SprintF', c_void_p),
	('VfprintF', c_void_p),
	('VsprintF', c_void_p),
	('Strtod', c_void_p),
	('Crypto', c_void_p),
	('asl', c_char_p),
	('AtExit', c_void_p),
	('AtReset', ATRESET),
	('Tempmem', c_void_p),
	('Add_table_handler', c_void_p),
	('Private', c_char_p),
	('Qsortv', c_void_p),
	#/* More stuff for stdio in DLLs... */
	('StdIn', c_void_p),
	('StdOut', c_void_p),
	('Clearerr', c_void_p),
	('Fclose', c_void_p),
	('Fdopen', c_void_p),
	('Feof', c_void_p),
	('Ferror', c_void_p),
	('Fflush', c_void_p),
	('Fgetc', c_void_p),
	('Fgets', c_void_p),
	('Fileno', c_void_p),
	('Fopen', c_void_p),
	('Fputc', c_void_p),
	('Fputs', c_void_p),
	('Fread', c_void_p),
	('Freopen', c_void_p),
	('Fscanf', c_void_p),
	('Fseek', c_void_p),
	('Ftell', c_void_p),
	('Fwrite', c_void_p),
	('Pclose', c_void_p),
	('Perror', c_void_p),
	('Popen', c_void_p),
	('Puts', c_void_p),
	('Rewind', c_void_p),
	('Scanf', c_void_p),
	('Setbuf', c_void_p),
	('Setvbuf', c_void_p),
	('Sscanf', c_void_p),
	('Tempnam', c_void_p),
	('Tmpfile', c_void_p),
	('Tmpnam', c_void_p),
	('Ungetc', c_void_p),
	('AI', c_void_p),
	('Getenv', c_void_p),
	('Breakfunc', c_void_p),
	('Breakarg', c_char_p),
	#/* Items available with ASLdate >= 20020501 start here. */
	('SnprintF', c_void_p),
	('VsnprintF', c_void_p),
	('Addrand', c_void_p),
	('Addrandinit', ADDRANDINIT),
	]
