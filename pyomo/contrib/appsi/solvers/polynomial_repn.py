from pyomo.repn.standard_repn import _collect_sum, _repn_collectors, _collect_standard_repn, isclose_const, ResultsWithQuadratics, StandardRepn
from pyomo.repn.standard_repn import isclose_const, ResultsWithQuadratics, StandardRepn, generate_standard_repn
from pyomo.core.expr import numeric_expr, native_numeric_types
from pyomo.core.expr.visitor import ExpressionValueVisitor
from pyomo.core.expr import current as EXPR
from pyomo.core.expr.numvalue import value
import itertools
from io import StringIO

class ResultsWithPolynomials(ResultsWithQuadratics):
    __slot__ = ResultsWithQuadratics.__slot__ + ('polynomial',)

    def __init__(self, constant=0, nonl=0, linear=None, quadratic=None):
        super().__init__(constant, nonl, linear, quadratic)
        self.polynomial = {}  # Will store {(var, degree): coef}

    def __str__(self):
        return "Const:\t%s\nLinear:\t%s\nQuadratic:\t%s\nPolynomial:\t%s\nNonlinear:\t%s" % (
            str(self.constant),
            str(self.linear),
            str(self.quadratic),
            str(self.polynomial),
            str(self.nonl),
        )

class PolynomialRepn(StandardRepn):
    """Extension of StandardRepn to handle polynomial expressions."""
    __slots__ = StandardRepn.__slots__ + (
        'polynomial_vars',    # Variables in polynomial terms (degree > 2)
        'polynomial_coefs',   # Coefficients of polynomial terms
        'polynomial_degrees', # Degrees for each polynomial term
    )

    def __init__(self):
        super().__init__()
        self.polynomial_vars = tuple()
        self.polynomial_coefs = tuple()
        self.polynomial_degrees = tuple()

    def __getstate__(self):
        state = super().__getstate__()
        return state + (
            self.polynomial_vars,
            self.polynomial_coefs,
            self.polynomial_degrees,
        )

    def __setstate__(self, state):
        super().__setstate__(state[:-3])
        self.polynomial_vars = state[-3]
        self.polynomial_coefs = state[-2]
        self.polynomial_degrees = state[-1]

    def __str__(self):  # pragma: nocover
        output = StringIO()
        output.write("\n")
        output.write("constant:       " + str(self.constant) + "\n")
        output.write(
            "linear vars:    " + str([v_.name for v_ in self.linear_vars]) + "\n"
        )
        output.write(
            "linear var ids: " + str([id(v_) for v_ in self.linear_vars]) + "\n"
        )
        output.write("linear coef:    " + str(list(self.linear_coefs)) + "\n")
        output.write(
            "quadratic vars:    "
            + str([(v_[0].name, v_[1].name) for v_ in self.quadratic_vars])
            + "\n"
        )
        output.write(
            "quadratic var ids: "
            + str([(id(v_[0]), id(v_[1])) for v_ in self.quadratic_vars])
            + "\n"
        )
        output.write("quadratic coef:    " + str(list(self.quadratic_coefs)) + "\n")
        output.write(
            "polynomial vars:    " + str([tuple(var.name for var in v_) for v_ in self.polynomial_vars]) + "\n"
        )
        output.write(
            "polynomial var ids: " + str([tuple(id(var) for var in v_) for v_ in self.polynomial_vars]) + "\n"
        )
        output.write("polynomial coef:    " + str(list(self.polynomial_coefs)) + "\n")
        output.write("polynomial degrees: " + str(list(self.polynomial_degrees)) + "\n")
        if self.nonlinear_expr is None:
            output.write("nonlinear expr: None\n")
        else:
            output.write("nonlinear expr:\n")
            try:
                output.write(self.nonlinear_expr.to_string())
                output.write("\n")
            except AttributeError:
                output.write(str(self.nonlinear_expr))
                output.write("\n")
        output.write(
            "nonlinear vars: " + str([v_.name for v_ in self.nonlinear_vars]) + "\n"
        )
        output.write("\n")
        ret_str = output.getvalue()
        output.close()
        return ret_str


    def polynomial_degree(self):
        """
        Returns the highest polynomial degree in the expression.
        Returns None if the expression is not polynomial.
        """
        # Start with degree from standard terms
        degree = 0

        # Check if there's any non-polynomial expression
        if len(self.nonlinear_vars) > 0:
            return None

        # Check higher degree polynomial terms
        if len(self.polynomial_degrees) > 0:
            degree = max(degree, max(self.polynomial_degrees))

        # Check quadratic terms
        elif len(self.quadratic_vars) > 0:
            degree = max(degree, 2)

        # Check linear terms
        elif len(self.linear_vars) > 0:
            degree = max(degree, 1)

        elif self.constant.__class__ in native_numeric_types or self.constant != 0:
            degree = max(degree, 0)
        # Check if there's any non-polynomial expression
        else:
            return None  # Non-polynomial expression present

        return degree

def _collect_polynomial_repn(exp, multiplier, idMap, compute_values, verbose, quadratic):
    """Similar to _collect_prod but handles polynomial terms"""
    results = ResultsWithPolynomials()

    if isinstance(exp, EXPR.PowExpression):
        base, exponent = exp.args
        if (isinstance(exponent, numeric_expr.NumericConstant) and
            exponent.value > 2):
            # Handle polynomial term
            if base.is_variable_type():
                var_id = id(base)
                degree = int(value(exponent))
                results.polynomial[(var_id, degree)] = multiplier
                return results

    # If not a polynomial term, use standard collection
    return generate_standard_repn(exp, multiplier, idMap, compute_values, verbose, quadratic=True)

def generate_polynomial_repn(
    expr, idMap=None, compute_values=True, verbose=False, quadratic=True, repn=None
):
    #
    # Use a custom Results object
    #
    global Results
    Results = ResultsWithPolynomials

    if True:
        #
        # Setup
        #
        if idMap is None:
            idMap = {}
        idMap.setdefault(None, {})
        if repn is None:
            repn = PolynomialRepn()
        #
        # The expression is a number or a non-variable constant
        # expression.
        #
        if expr.__class__ in native_numeric_types or not expr.is_potentially_variable():
            if compute_values:
                repn.constant = EXPR.evaluate_expression(expr)
            else:
                repn.constant = expr
            return repn
        #
        # The expression is a variable
        #
        elif expr.is_variable_type():
            if expr.fixed:
                if compute_values:
                    repn.constant = value(expr)
                else:
                    repn.constant = expr
                return repn
            repn.linear_coefs = (1,)
            repn.linear_vars = (expr,)
            return repn
        #
        # The expression is linear
        #
        elif expr.__class__ is EXPR.LinearExpression:
            linear_coefs = {}
            linear_vars = {}
            C_ = 0
            if compute_values:
                for arg in expr.args:
                    if arg.__class__ is EXPR.MonomialTermExpression:
                        c, v = arg.args
                        if c.__class__ not in native_numeric_types:
                            c = EXPR.evaluate_expression(c)
                        if v.fixed:
                            C_ += c * v.value
                            continue
                        id_ = id(v)
                        if id_ in linear_coefs:
                            linear_coefs[id_] += c
                        else:
                            linear_coefs[id_] = c
                            linear_vars[id_] = v
                    elif arg.__class__ in native_numeric_types:
                        C_ += arg
                    elif arg.is_variable_type():
                        if arg.fixed:
                            C_ += arg.value
                            continue
                        id_ = id(arg)
                        if id_ in linear_coefs:
                            linear_coefs[id_] += 1
                        else:
                            linear_coefs[id_] = 1
                            linear_vars[id_] = arg
                    else:
                        C_ += EXPR.evaluate_expression(arg)
            else:  # compute_values == False
                for arg in expr.args:
                    if arg.__class__ is EXPR.MonomialTermExpression:
                        c, v = arg.args
                        if v.fixed:
                            C_ += c * v
                            continue
                        id_ = id(v)
                        if id_ in linear_coefs:
                            linear_coefs[id_] += c
                        else:
                            linear_coefs[id_] = c
                            linear_vars[id_] = v
                    elif arg.__class__ in native_numeric_types:
                        C_ += arg
                    elif arg.is_variable_type():
                        if arg.fixed:
                            C_ += arg
                            continue
                        id_ = id(arg)
                        if id_ in linear_coefs:
                            linear_coefs[id_] += 1
                        else:
                            linear_coefs[id_] = 1
                            linear_vars[id_] = arg
                    else:
                        C_ += arg

            vars_ = []
            coef_ = []
            for id_, coef in linear_coefs.items():
                if coef.__class__ in native_numeric_types and not coef:
                    continue
                if id_ not in idMap[None]:
                    key = len(idMap) - 1
                    idMap[None][id_] = key
                    idMap[key] = linear_vars[id_]
                else:
                    key = idMap[None][id_]
                vars_.append(idMap[key])
                coef_.append(coef)

            repn.linear_vars = tuple(vars_)
            repn.linear_coefs = tuple(coef_)
            repn.constant = C_
            return repn

        #
        # Unknown expression object
        #
        elif not expr.is_expression_type():  # pragma: nocover
            raise ValueError("Unexpected expression type: " + str(expr))

        return _generate_polynomial_repn(
            expr,
            idMap=idMap,
            compute_values=compute_values,
            verbose=verbose,
            quadratic=quadratic,
            repn=repn,
        )

def _collect_pow_poly(exp, multiplier, idMap, compute_values, verbose, quadratic):
    #
    # Exponent is a numeric value
    #
    if exp._args_[1].__class__ in native_numeric_types:
        exponent = exp._args_[1]
    #
    # Exponent is not potentially variable
    #
    # Compute its value if compute_values==True
    #
    elif not exp._args_[1].is_potentially_variable():
        if compute_values:
            exponent = value(exp._args_[1])
        else:
            exponent = exp._args_[1]
    #
    # Otherwise collect a standard repn
    #
    else:
        res = _collect_standard_repn(
            exp._args_[1], 1, idMap, compute_values, verbose, quadratic
        )
        #
        # If the expression is variable, then return a nonlinear expression
        #
        if (
            not (res.nonl.__class__ in native_numeric_types and res.nonl == 0)
            or len(res.linear) > 0
            or (quadratic and len(res.quadratic) > 0)
        ):
            return Results(nonl=multiplier * exp)
        exponent = res.constant

    if exponent.__class__ in native_numeric_types:
        #
        # #**0 = 1
        #
        if exponent == 0:
            return Results(constant=multiplier)
        #
        # #**1 = #
        #
        # Return the standard repn for arg(0)
        #
        elif exponent == 1:
            return _collect_standard_repn(
                exp._args_[0], multiplier, idMap, compute_values, verbose, quadratic
            )
        #
        # Ignore #**2 unless quadratic==True
        #
        elif exponent == 2 and quadratic:
            res = _collect_standard_repn(
                exp._args_[0], 1, idMap, compute_values, verbose, quadratic
            )
            #
            # If arg(0) is nonlinear, then this is a nonlinear repn
            #
            if (
                not (res.nonl.__class__ in native_numeric_types and res.nonl == 0)
                or len(res.quadratic) > 0
            ):
                return Results(nonl=multiplier * exp)
            #
            # If computing values and no linear terms, then the return a constant repn
            #
            elif compute_values and len(res.linear) == 0:
                return Results(constant=multiplier * res.constant**exponent)
            #
            # If the base is linear, then we compute the quadratic expression for it.
            #
            else:
                ans = Results()
                has_constant = (
                    res.constant.__class__ not in native_numeric_types
                    or res.constant != 0
                )
                if has_constant:
                    ans.constant = multiplier * res.constant * res.constant

                # this is reversed since we want to pop off the end for efficiency
                # and the quadratic terms have a convention that the indexing tuple
                # of key1, key2 is such that key1 <= key2
                keys = sorted(res.linear.keys(), reverse=True)
                while len(keys) > 0:
                    key1 = keys.pop()
                    coef1 = res.linear[key1]
                    if has_constant:
                        ans.linear[key1] = 2 * multiplier * coef1 * res.constant
                    ans.quadratic[key1, key1] = multiplier * coef1 * coef1
                    for key2 in keys:
                        coef2 = res.linear[key2]
                        ans.quadratic[key1, key2] = 2 * multiplier * coef1 * coef2
                return ans

        elif exponent > 2:  # Handle higher degree polynomial terms
            res = _collect_standard_repn(
                exp._args_[0], 1, idMap, compute_values, verbose, quadratic
            )
            #
            # If arg(0) is nonlinear or has quadratic terms, then this is nonlinear
            #
            if (not (res.nonl.__class__ in native_numeric_types and res.nonl == 0)
                or len(res.quadratic) > 0):
                return Results(nonl=multiplier * exp)
            #
            # If computing values and no linear terms, then return a constant repn
            #
            elif compute_values and len(res.linear) == 0:
                return Results(constant=multiplier * res.constant**exponent)
            #
            # If the base is linear and single variable, then we compute the polynomial term
            #
            elif len(res.linear) == 1:
                ans = ResultsWithPolynomials()
                key = next(iter(res.linear))
                coef = res.linear[key]

                # Handle constant term if present
                if res.constant.__class__ not in native_numeric_types or res.constant != 0:
                    ans.constant = multiplier * res.constant**exponent
                    # Add polynomial term for the variable
                    ans.polynomial[(key,) * exponent] = multiplier * coef**exponent

                    # Add mixed terms using binomial expansion if there's a constant
                    for k in range(1, exponent):
                        coef_k = (
                            multiplier
                            * _nCr(exponent, k)  # binomial coefficient
                            * coef**k
                            * res.constant**(exponent-k)
                        )
                        if k == 1:
                            ans.linear[key] = coef_k
                        elif k == 2:
                            ans.quadratic[key, key] = coef_k
                        else:
                            ans.polynomial[(key,) * k] = coef_k
                else:
                    # Just the pure power term
                    ans.polynomial[(key,) * exponent] = multiplier * coef**exponent
                return ans
            #
            # If the base is linear with multiple terms, treat as nonlinear
            #
            else:
                return Results(nonl=multiplier * exp)

_repn_collectors[EXPR.PowExpression] = _collect_pow_poly

def _collect_sum_polynomial_repn(exp, multiplier, idMap, compute_values, verbose, quadratic):
    ans = ResultsWithPolynomials()
    nonl = []
    varkeys = idMap[None]

    for e_ in itertools.islice(exp._args_, exp.nargs()):
        if e_.__class__ is EXPR.MonomialTermExpression:
            lhs, v = e_.args
            if lhs.__class__ in native_numeric_types:
                if not lhs:
                    continue
            elif compute_values:
                lhs = value(lhs)
                if not lhs:
                    continue
            if v.fixed:
                if compute_values:
                    ans.constant += multiplier * lhs * value(v)
                else:
                    ans.constant += multiplier * lhs * v
            else:
                id_ = id(v)
                if id_ in varkeys:
                    key = varkeys[id_]
                else:
                    key = len(idMap) - 1
                    varkeys[id_] = key
                    idMap[key] = v
                if key in ans.linear:
                    ans.linear[key] += multiplier * lhs
                else:
                    ans.linear[key] = multiplier * lhs
        elif e_.__class__ in native_numeric_types:
            ans.constant += multiplier * e_
        elif e_.is_variable_type():
            if e_.fixed:
                if compute_values:
                    ans.constant += multiplier * e_.value
                else:
                    ans.constant += multiplier * e_
            else:
                id_ = id(e_)
                if id_ in varkeys:
                    key = varkeys[id_]
                else:
                    key = len(idMap) - 1
                    varkeys[id_] = key
                    idMap[key] = e_
                if key in ans.linear:
                    ans.linear[key] += multiplier
                else:
                    ans.linear[key] = multiplier
        elif not e_.is_potentially_variable():
            if compute_values:
                ans.constant += multiplier * value(e_)
            else:
                ans.constant += multiplier * e_
        else:
            res_ = _collect_standard_repn(
                e_, multiplier, idMap, compute_values, verbose, quadratic
            )
            #
            # Add returned from recursion
            #
            ans.constant += res_.constant
            if not (res_.nonl.__class__ in native_numeric_types and res_.nonl == 0):
                nonl.append(res_.nonl)
            for i, v in res_.linear.items():
                ans.linear[i] = ans.linear.get(i, 0) + v
            if isinstance(res_, ResultsWithPolynomials):
                for i in res_.polynomial:
                    ans.polynomial[i] = ans.polynomial.get(i, 0) + res_.polynomial[i]
            if quadratic:
                for i in res_.quadratic:
                    ans.quadratic[i] = ans.quadratic.get(i, 0) + res_.quadratic[i]

    if len(nonl) > 0:
        if len(nonl) == 1:
            ans.nonl = nonl[0]
        else:
            ans.nonl = EXPR.SumExpression(nonl)
    zero_coef = [
        k
        for k, coef in ans.linear.items()
        if coef.__class__ in native_numeric_types and not coef
    ]
    for k in zero_coef:
        ans.linear.pop(k)
    return ans

def _generate_polynomial_repn(
    expr, idMap=None, compute_values=True, verbose=False, quadratic=True, repn=None
):
    if expr.__class__ is EXPR.SumExpression:
        #
        # This is the common case, so start collecting the sum
        #

        ans = _collect_sum_polynomial_repn(expr, 1, idMap, compute_values, verbose, quadratic)
    else:
        #
        # Call generic recursive logic
        #
        ans = _collect_standard_repn(expr, 1, idMap, compute_values, verbose, quadratic)
    #
    # Create the final object here from 'ans'
    #
    repn.constant = ans.constant
    #
    # Create a list (tuple) of the variables and coefficients
    #
    v = []
    c = []
    for key, val in ans.linear.items():
        if val.__class__ in native_numeric_types:
            if not val:
                continue
        elif val.is_constant():  # TODO: coverage?
            if value(val) == 0:
                continue
        v.append(idMap[key])
        c.append(val)
    repn.linear_vars = tuple(v)
    repn.linear_coefs = tuple(c)

    if quadratic:
        repn.quadratic_vars = []
        repn.quadratic_coefs = []
        for key in ans.quadratic:
            val = ans.quadratic[key]
            if val.__class__ in native_numeric_types:
                if val == 0:  # TODO: coverage?
                    continue
            elif val.is_constant():  # TODO: coverage?
                if value(val) == 0:
                    continue
            repn.quadratic_vars.append((idMap[key[0]], idMap[key[1]]))
            repn.quadratic_coefs.append(val)
        repn.quadratic_vars = tuple(repn.quadratic_vars)
        repn.quadratic_coefs = tuple(repn.quadratic_coefs)
        v = []
        c = []
        for key in ans.quadratic:
            v.append((idMap[key[0]], idMap[key[1]]))
            c.append(ans.quadratic[key])
        repn.quadratic_vars = tuple(v)
        repn.quadratic_coefs = tuple(c)

    # Handle polynomial terms
    if getattr(ans, 'polynomial', None):
        v = []
        c = []
        d = []
        for vars, coef in ans.polynomial.items():
            if coef.__class__ in native_numeric_types:
                if coef == 0:
                    continue
            elif coef.is_constant():
                if value(coef) == 0:
                    continue
            v.append(tuple(idMap[var_id] for var_id in vars))
            c.append(coef)
            d.append(len(vars))
        repn.polynomial_vars = tuple(v)
        repn.polynomial_coefs = tuple(c)
        repn.polynomial_degrees = tuple(d)

    if ans.nonl is not None and not isclose_const(ans.nonl, 0):
        repn.nonlinear_expr = ans.nonl
        repn.nonlinear_vars = []
        for v_ in EXPR.identify_variables(repn.nonlinear_expr, include_fixed=False):
            repn.nonlinear_vars.append(v_)
            #
            # Update idMap in case we skipped nonlinear sub-expressions
            #
            # Q: Should we skip nonlinear sub-expressions?
            #
            id_ = id(v_)
            if id_ in idMap[None]:
                key = idMap[None][id_]
            else:
                key = len(idMap) - 1
                idMap[None][id_] = key
                idMap[key] = v_
        repn.nonlinear_vars = tuple(repn.nonlinear_vars)

    return repn

def _collect_prod_poly(exp, multiplier, idMap, compute_values, verbose, quadratic):
    #
    # LHS is a numeric value
    #
    if exp._args_[0].__class__ in native_numeric_types:
        if exp._args_[0] == 0:  # TODO: coverage?
            return Results()
        return _collect_standard_repn(
            exp._args_[1],
            multiplier * exp._args_[0],
            idMap,
            compute_values,
            verbose,
            quadratic,
        )
    #
    # RHS is a numeric value
    #
    if exp._args_[1].__class__ in native_numeric_types:
        if exp._args_[1] == 0:  # TODO: coverage?
            return Results()
        return _collect_standard_repn(
            exp._args_[0],
            multiplier * exp._args_[1],
            idMap,
            compute_values,
            verbose,
            quadratic,
        )
    #
    # LHS is a non-variable expression
    #
    elif not exp._args_[0].is_potentially_variable():
        if compute_values:
            val = value(exp._args_[0])
            if val == 0:
                return Results()
            return _collect_standard_repn(
                exp._args_[1],
                multiplier * val,
                idMap,
                compute_values,
                verbose,
                quadratic,
            )
        else:
            return _collect_standard_repn(
                exp._args_[1],
                multiplier * exp._args_[0],
                idMap,
                compute_values,
                verbose,
                quadratic,
            )
    #
    # RHS is a non-variable expression
    #
    elif not exp._args_[1].is_potentially_variable():
        if compute_values:
            val = value(exp._args_[1])
            if val == 0:
                return Results()
            return _collect_standard_repn(
                exp._args_[0],
                multiplier * val,
                idMap,
                compute_values,
                verbose,
                quadratic,
            )
        else:
            return _collect_standard_repn(
                exp._args_[0],
                multiplier * exp._args_[1],
                idMap,
                compute_values,
                verbose,
                quadratic,
            )
    #
    # Both the LHS and RHS are potentially variable ...
    #
    # Collect LHS
    #

    lhs = _collect_standard_repn(
        exp._args_[0], 1, idMap, compute_values, verbose, quadratic
    )
    lhs_nonl_None = lhs.nonl.__class__ in native_numeric_types and not lhs.nonl
    #
    # LHS is potentially variable, but it turns out to be a constant
    # because the variables were fixed.
    #
    if (
        lhs_nonl_None
        and len(lhs.linear) == 0
        and (not quadratic or len(lhs.quadratic) == 0)
        and (len(lhs.polynomial) == 0)
    ):
        if lhs.constant.__class__ in native_numeric_types and lhs.constant == 0:
            return Results()
        if compute_values:
            val = value(lhs.constant)
            if val == 0:  # TODO: coverage?
                return Results()
            return _collect_standard_repn(
                exp._args_[1],
                multiplier * val,
                idMap,
                compute_values,
                verbose,
                quadratic,
            )
        else:
            return _collect_standard_repn(
                exp._args_[1],
                multiplier * lhs.constant,
                idMap,
                compute_values,
                verbose,
                quadratic,
            )
    #
    # Collect RHS
    #
    rhs = _collect_standard_repn(
        exp._args_[1], 1, idMap, compute_values, verbose, quadratic
    )
    rhs_nonl_None = rhs.nonl.__class__ in native_numeric_types and not rhs.nonl
    #
    # If RHS is zero, then return an empty results
    #
    if (
        rhs_nonl_None
        and len(rhs.linear) == 0
        and (not quadratic or len(rhs.quadratic) == 0)
        and rhs.constant.__class__ in native_numeric_types
        and rhs.constant == 0
        and (len(rhs.polynomial) == 0)
    ):
        return Results()
    #
    # If either the LHS or RHS are nonlinear, then simply return the nonlinear expression
    #
    if not lhs_nonl_None or not rhs_nonl_None:
        return Results(nonl=multiplier * exp)

    # If the resulting expression has a polynomial degree greater than 2
    # (1 if quadratic is False), then simply return this as a general
    # nonlinear expression
    #
    ans = ResultsWithPolynomials()
    ans.constant = multiplier * lhs.constant * rhs.constant
    if not (lhs.constant.__class__ in native_numeric_types and lhs.constant == 0):
        for key, coef in rhs.linear.items():
            ans.linear[key] = multiplier * coef * lhs.constant
    if not (rhs.constant.__class__ in native_numeric_types and rhs.constant == 0):
        for key, coef in lhs.linear.items():
            if key in ans.linear:
                ans.linear[key] += multiplier * coef * rhs.constant
            else:
                ans.linear[key] = multiplier * coef * rhs.constant

    if quadratic:
        if not (lhs.constant.__class__ in native_numeric_types and lhs.constant == 0):
            for key, coef in rhs.quadratic.items():
                ans.quadratic[key] = multiplier * coef * lhs.constant
        if not (rhs.constant.__class__ in native_numeric_types and rhs.constant == 0):
            for key, coef in lhs.quadratic.items():
                if key in ans.quadratic:
                    ans.quadratic[key] += multiplier * coef * rhs.constant
                else:
                    ans.quadratic[key] = multiplier * coef * rhs.constant
        for lkey, lcoef in lhs.linear.items():
            for rkey, rcoef in rhs.linear.items():
                ndx = (lkey, rkey) if lkey <= rkey else (rkey, lkey)
                if ndx in ans.quadratic:
                    ans.quadratic[ndx] += multiplier * lcoef * rcoef
                else:
                    ans.quadratic[ndx] = multiplier * lcoef * rcoef
        # TODO - Use quicksum here?
        el_linear = multiplier * sum(
            coef * idMap[key]
            for key, coef in lhs.linear.items()
            if coef.__class__ not in native_numeric_types or coef
        )
        er_linear = multiplier * sum(
            coef * idMap[key]
            for key, coef in rhs.linear.items()
            if coef.__class__ not in native_numeric_types or coef
        )
        el_quadratic = multiplier * sum(
            coef * idMap[key[0]] * idMap[key[1]]
            for key, coef in lhs.quadratic.items()
            if coef.__class__ not in native_numeric_types or coef
        )
        er_quadratic = multiplier * sum(
            coef * idMap[key[0]] * idMap[key[1]]
            for key, coef in rhs.quadratic.items()
            if coef.__class__ not in native_numeric_types or coef
        )
    # Handle polynomial combinations
    for rkey, rcoef in rhs.linear.items():
        # quadratic * linear
        for lkey, lcoef in lhs.quadratic.items():
            ans.polynomial[lkey + (rkey,)] = ans.polynomial.get(lkey + (rkey,), 0) + multiplier * lcoef * rcoef

        if isinstance(lhs, ResultsWithPolynomials):
            for lkey, lcoef in lhs.polynomial.items():
                ans.polynomial[lkey + (rkey,)] = ans.polynomial.get(lkey + (rkey,), 0) + multiplier * lcoef * rcoef
    # handle linear *
    for lkey, lcoef in lhs.linear.items():
        # Linear * quadratic
        for rkey, rcoef in rhs.quadratic.items():
            ans.polynomial[(lkey,) + rkey] = ans.polynomial.get((lkey,) + rkey, 0) + multiplier * lcoef * rcoef

        # Linear * polynomial
        if isinstance(rhs, ResultsWithPolynomials):
            for (rvar_id, rdegree), rcoef in rhs.polynomial.items():
                ans.polynomial[(lkey,) + rkey] = ans.polynomial.get((lkey,) + rkey, 0) + multiplier * lcoef * rcoef

    # Quadratic * polynomial
    for lkey, lcoef in lhs.quadratic.items():
        if isinstance(rhs, ResultsWithPolynomials):
            for rkey, rcoef in rhs.polynomial.items():
                ans.polynomial[lkey + rkey] = ans.polynomial.get(lkey + rkey, 0) + multiplier * lcoef * rcoef

    # Polynomial * quadratic
    if isinstance(lhs, ResultsWithPolynomials):
        for lkey, lcoef in lhs.polynomial.items():
            for rkey, rcoef in rhs.quadratic.items():
                ans.polynomial[lkey + rkey] = ans.polynomial.get(lkey + rkey, 0) + multiplier * lcoef * rcoef
    # Quadratic * quadratic
    for lkey, lcoef in lhs.quadratic.items():
        for rkey, rcoef in rhs.quadratic.items():
            ans.polynomial[lkey + rkey] = ans.polynomial.get(lkey + rkey, 0) + multiplier * lcoef * rcoef

    # Polynomial * polynomial
    if isinstance(lhs, ResultsWithPolynomials) and isinstance(rhs, ResultsWithPolynomials):
        for lkey, lcoef in lhs.polynomial.items():
            for rkey, rcoef in rhs.polynomial.items():
                ans.polynomial[lkey + rkey] = ans.polynomial.get(lkey + rkey, 0) + multiplier * lcoef * rcoef
    return ans

_repn_collectors[EXPR.ProductExpression] = _collect_prod_poly

import math

def _nCr(n, r):
    return math.comb(n, r)
