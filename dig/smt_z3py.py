from sage.all import (operator, var, sage_eval)
import z3

from vu_common import is_empty, is_list
from z3util import vprove
from sageutil import is_sage_expr, is_sage_int, is_sage_real, get_vars

"""
Adding z3py Api to SAGE_PATH
E.g.
in ~/.bash_profile
export Z3=$DEVEL/z3
export SAGE_PATH=$DROPBOX/code/git/invgen:$Z3/python
"""

class SMT_Z3(object):
    """
    SMT Helpers. Uses Z3py
    """

    @staticmethod
    def _reduce(op, ls):
        """
        Apply operator op to the list ls of arguments.

        The arguments must be of type that z3 exprs. In other words, cannot use Sage's datatype (e.g. 7==Real('x') gives False which is not expected)

        (+,*) work on 2+ arguments
        (pow,==,!=,>=,>,<=,<) work on 2 arguments


        Note, it seems the above arguments are *enough*, no need to implement for (-,div) etc because the function that calls this will break  x - y to _reduce(op,[x,-y]) or  x / y to _reduce(op,[x,1/y]) and 1/y =>  mul(1,y^{-1})


        sage: SMT_Z3._reduce(operator.add,[z3.Real('x'),z3.RealVal(3)])
        x + 3
        sage: SMT_Z3._reduce(operator.add,[z3.Real('x'),z3.RealVal(3),z3.Real('y')])
        x + 3 + y
        sage: SMT_Z3._reduce(operator.mul,[z3.Real('x'),z3.RealVal('3'),z3.Real('y')])
        x*3*y
        sage: SMT_Z3._reduce(operator.pow,[z3.Real('x'),z3.RealVal(3)])
        x**3
        sage: SMT_Z3._reduce(operator.pow,[z3.RealVal(3),z3.Real('x')])
        3**x
        sage: SMT_Z3._reduce(operator.pow,[z3.Real('x'),z3.RealVal(3.3)])
        x**(33/10)
        sage: SMT_Z3._reduce(operator.pow,[z3.Real('x'),z3.Real('x')])
        x**x

        #1/x
        sage: SMT_Z3._reduce(operator.pow,[z3.Real('x'),z3.IntVal('-1')])
        x**ToReal(-1)
        sage: SMT_Z3._reduce(operator.pow,[z3.Int('x'),z3.IntVal('-1')])
        x**-1

        sage: SMT_Z3._reduce(operator.pow,[z3.IntVal('-7'),z3.IntVal('-1')])
        -7**-1
        sage: SMT_Z3._reduce(operator.mul,[z3.IntVal('-7'),z3.IntVal('-1')])
        -7*-1
        sage: SMT_Z3._reduce(operator.mul,[z3.RealVal('-7'),z3.RealVal('-1')])
        -7*-1
        sage: SMT_Z3._reduce(operator.mul,[z3.RealVal('-7'),z3.RealVal('-9')])
        -7*-9
        sage: SMT_Z3._reduce(operator.mul,[z3.RealVal('-7'),z3.IntVal('-9')])
        -7*ToReal(-9)
        sage: SMT_Z3._reduce(operator.mul,[z3.RealVal(-7),z3.IntVal('-9')])
        -7*ToReal(-9)
        sage: SMT_Z3._reduce(operator.eq,[z3.RealVal(-7),z3.Real('x')])
        -7 == x
        sage: SMT_Z3._reduce(operator.eq,[z3.RealVal(-7),z3.Real('x')])
        -7 == x
        sage: SMT_Z3._reduce(operator.eq,[z3.RealVal('-7'),z3.Real('x')])
        -7 == x
        sage: SMT_Z3._reduce(operator.eq,[z3.IntVal('-7'),z3.Real('x')])
        ToReal(-7) == x
        sage: SMT_Z3._reduce(operator.eq,[z3.IntVal('-7'),z3.Int('x')])
        -7 == x
        sage: SMT_Z3._reduce(operator.div,[z3.IntVal('-7'),z3.Int('x')])
        Traceback (most recent call last):
        ...
        AssertionError: unknown op: <built-in function div>
        """

        if __debug__:
            assert all(z3.is_expr(f) for f in ls)

        if op == operator.add:
            if __debug__: assert len(ls) >= 2
            return reduce(lambda a, b: a+b, ls[1:], ls[0])

        elif op == operator.mul:
            if __debug__: assert len(ls) >= 2
            return reduce(lambda a, b: a*b, ls[1:], ls[0])

        elif op == operator.pow:
            if __debug__: assert len(ls) == 2
            return ls[0]**ls[1]

        elif op == operator.eq:
            if __debug__: assert len(ls) == 2
            return ls[0] == ls[1]

        elif op == operator.ne:
            if __debug__: assert len(ls) == 2
            return ls[0] != ls[1]

        elif op == operator.ge:
            if __debug__: assert len(ls) == 2
            return ls[0] >= ls[1]

        elif op == operator.gt:
            if __debug__: assert len(ls) == 2
            return ls[0] > ls[1]

        elif op == operator.le:
            if __debug__: assert len(ls) == 2
            return ls[0] <= ls[1]

        elif op == operator.lt:
            if __debug__: assert len(ls) == 2
            return ls[0] < ls[1]

        else:
            raise AssertionError('unknown op: {}'.format(op))

    @staticmethod
    def to_z3(p):
        typ = "{} = z3.Ints('{}')"
        vs = map(str, get_vars(p))
        z3_vars_decl = typ.format(','.join(vs),' '.join(vs))
        exec(z3_vars_decl)
        f = eval(str(p))
        print f
        print z3.is_expr(f)

    @staticmethod
    def to_z3exp(p, is_real):
        """
        Convert a Sage expression to a Z3 expression

        Initially implements with a dictionary containing variables
        e.g. {x:Real('x')} but the code is longer and more complicated.
        This implemention does not require a dictionary pass in.

        Todo: cache this function
        """

        assert is_sage_expr(p), p

        def retval(p):
            if p.is_symbol():
                z3exp = (z3.Real if is_real else z3.Int)(str(p))
            else:
                z3exp = (z3.RealVal if is_real else z3.IntVal)(str(p))

            if __debug__:
                assert z3.is_expr(z3exp), z3exp

            return z3exp

        try:
            oprs = p.operands()
        except Exception:
            return retval(p)
        
        if is_empty(oprs):
            return retval(p)
        else:
            oprs = [SMT_Z3.to_z3exp(o, is_real) for o in oprs]
            z3exp = SMT_Z3._reduce(p.operator(),oprs)

        assert z3.is_expr(z3exp), z3exp
        return z3exp


    @staticmethod
    def imply(fs, gs):
        """
        Checks if the set f of formulas implies the set f of formulas

        sage: var('x y')
        (x, y)

        sage: SMT_Z3.imply([x-6==0],x*x-36==0)
        True
        sage: SMT_Z3.imply([x-6==0,x+6==0],x*x-36==0)
        True
        sage: SMT_Z3.imply([x*x-36==0],x-6==0)
        False
        sage: SMT_Z3.imply([x-6==0],x-36==0)
        False
        sage: SMT_Z3.imply(x-7>=0,x>=6)
        True
        sage: SMT_Z3.imply(x-7>=0,x>=8)
        False
        sage: SMT_Z3.imply(x-6>=0,x-7>=0)
        False
        sage: SMT_Z3.imply([x-7>=0,y+5>=0],x+y-3>=0)
        False
        sage: SMT_Z3.imply([x-7>=0,y+5>=0],x+y-2>=0)
        True
        sage: SMT_Z3.imply([x-2*y>=0,y-1>=0],x-2>=0)
        True
        sage: SMT_Z3.imply([],x-2>=0)
        False
        sage: SMT_Z3.imply([x-7>=0,y+5>=0],x+y-2>=0)
        True
        sage: SMT_Z3.imply([x^2-9>=0,x>=0],x-3>=0)
        True
        sage: SMT_Z3.imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0)
        False
        sage: SMT_Z3.imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0)
        True
        sage: SMT_Z3.imply([x-6==0],x*x-36==0)
        True
        sage: SMT_Z3.imply([x+7>=0,y+5>=0],x*y+36>=0)
        False
        sage: SMT_Z3.imply([x+7>=0,y+5>=0],x*y+35>=0)
        False
        sage: SMT_Z3.imply([x+7>=0,y+5>=0],x*y-35>=0)
        False
        sage: SMT_Z3.imply([x+7>=0],x-8>=0)
        False
        sage: SMT_Z3.imply([x+7>=0],x+8>=0)
        True
        sage: SMT_Z3.imply([x+7>=0],x+8.9>=0)
        True
        sage: SMT_Z3.imply([x>=7,y>=5],x*y>=35)
        True
        sage: SMT_Z3.imply([x>=-7,y>=-5],x*y>=35)
        False
        sage: SMT_Z3.imply([x-7>=0,y+5>=0],[x+y-2>=0,x>=2-y])
        True

        """
        if __debug__:
            assert fs is not None, fs
            assert gs is not None, gs

        if is_empty(fs) or is_empty(gs):
            return False #conservative approach

        if not is_list(fs): fs = [fs]
        if not is_list(gs): gs = [gs]
            
        fs = [SMT_Z3.to_z3exp(f, is_real=True) for f in fs]
        gs = [SMT_Z3.to_z3exp(g, is_real=True) for g in gs]

        claim = z3.Implies(z3.And(fs), z3.And(gs))

        is_proved, _ = vprove(claim)
        return is_proved


    @staticmethod
    def get_constraints(m, result_as_dict=False):
        """
        Input a model m, returns its set of constraints in either
        1) sage dict {x:7,y:10}
        1) z3 expr [x==7,y==0]


        sage: S = z3.Solver()
        sage: S.add(z3.Int('x') + z3.Int('y') == z3.IntVal('7'))
        sage: S.check()
        sat
        sage: M = S.model()
        sage: d = SMT_Z3.get_constraints(M, result_as_dict=True)
        sage: sorted(d.items(), key=lambda(k,_): str(k))
        [(x, 7), (y, 0)]
        sage: SMT_Z3.get_constraints(M)
        [y == 0, x == 7]
        sage: S.reset()

        """

        assert m is not None, m

        if result_as_dict:  #sage format
            rs = [(var(str(v())),sage_eval(str(m[v]))) for v in m]
            rs = dict(rs)

            if __debug__:
                assert all(is_sage_expr(x) for x in rs.keys())
                assert all(is_sage_real(x) or is_sage_int(x) for x in rs.values())


        else:  #z3 format
            rs = [v()==m[v] for v in m]
            if __debug__:
                assert all(z3.is_expr(x) for x in rs)

        return rs



    #useful shortcuts
    @staticmethod
    def exp_int(x):
        """
        sage: SMT_Z3.exp_int(x>10)
        x > 10
        """
        return x if z3.is_expr(x) else SMT_Z3.to_z3exp(x,is_real=False)

    @staticmethod
    def exp_real(x):
        return x if z3.is_expr(x) else SMT_Z3.to_z3exp(x,is_real=True)

    @staticmethod
    def map_exp_int(*xs):
        """
        sage: SMT_Z3.map_exp_int(x>10,x>20)
        [x > 10, x > 20]
        """
        return map(lambda x: SMT_Z3.exp_int(x), xs)

    @staticmethod
    def map_exp_real(*xs):
        """
        """
        return map(lambda x: SMT_Z3.exp_real(x), xs)


    @staticmethod
    def and_int(*xs):
        return z3.And(SMT_Z3.map_exp_int(*xs))

    @staticmethod
    def and_real(*xs):
        return z3.And(SMT_Z3.map_exp_real(*xs))

    @staticmethod
    def or_int(*xs):
        return z3.Or(SMT_Z3.map_exp_int(*xs))

    @staticmethod
    def or_real(*xs):
        return z3.Or(SMT_Z3.map_exp_real(*xs))


    @staticmethod
    def implies_int(c1,c2):
        return z3.Implies(SMT_Z3.exp_int(c1),SMT_Z3.exp_int(c2))


    @staticmethod
    def implies_real(c1,c2):
        return z3.Implies(SMT_Z3.exp_real(c1),SMT_Z3.exp_real(c2))



"""
S = z3.Solver()
S.add(z3.Int('x') + z3.Int('y') == z3.IntVal('7'))
S.check()
sat
M = S.model()
M.eval(M.decls()[0])
crash

"""
