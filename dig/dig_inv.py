from abc import ABCMeta, abstractmethod
from sage.all import (PolynomialRing, QQ, sage_eval, operator, SR)

from vu_common import (VLog, vsetdiff, 
                       is_str, is_list, is_dict, is_tuple, 
                       merge_dict)
from sageutil import get_vars, is_sage_expr
from dig_miscs import Miscs, ExtFun

logger = VLog('dig_inv')
logger.set_level(VLog.INFO)

class Inv(object):
    __metaclass__ = ABCMeta
    def __init__(self, p, p_str=None): 
        if __debug__:
            assert p_str is None or is_str(p_str), p_str

        self.p = p
        if p_str is None:
            p_str = str(p)

        self.p_str = Inv.rm_lambda(p_str)


    def __eq__(self,other): return self.p.__eq__(other.p)
    def __ne__(self,other): return self.p.__ne__(other.p)
    def __hash__(self): return self.p.__hash__()
    def __str__(self): return self.p_str
    def __repr__(self): return self.p.__repr__()

    @staticmethod
    def rm_lambda(s):
        return s[s.find(':') + 1:].strip() #no lambda
        
    @abstractmethod
    def get_score(): return

    @abstractmethod
    def seval(self): return
    
    @staticmethod
    def print_invs(ps, nice_format=True):
        """
        sage: var('y')
        y
        
        #TODO
        # sage: from dig_polynomials import InvEqt
        # sage: Inv.print_invs(map(InvEqt, [3*x==2,x*x==1]))
        # 0: 3*x == 2
        # 1: x^2 == 1
        
        TODO
        # sage: Inv.print_invs(map(IExp,[3*x==2,x>=2, x*x+y == 2*y*y,('lambda expr: max(x,y) >= 0', 'If(x>=y,x>=0,y>=0)')]),nice_format=False)
        # [3*x == 2, x^2 + y == 2*y^2, x >= 2, If(x>=y,x>=0,y>=0)]
        
        """
        if __debug__:
            assert (is_list(ps) and 
                    all(isinstance(p,Inv) for p in ps)), map(type,ps)
    
        if ps:
            ps = sorted(ps, key=lambda p: p.get_score())
            
            ps_poly_eqt = []
            #ps_poly_ieq = []
            ps_other = []


            for p in ps:
                if '==' in str(p):
                    ps_poly_eqt.append(p)
                else:
                    ps_other.append(p)
                    
            ps = ps_poly_eqt + ps_other

            if nice_format:
                str_ = lambda p: ('{}, {}'.format(Inv.rm_lambda(p.p),
                                                  p.p_str)
                                  if isinstance(p,InvMPP) else p.p_str)
                
                rs = '\n'.join('{:>5}: {}'
                               .format(i,str_(p)) for i,p in enumerate(ps))
            else:
                rs = '[{}]'.format(', '.join(map(str,ps)))

            print rs



        
    # @abstractmethod
    # def __hash__(self): return
        # """
        # TODO: override this individually 

        # Potential error here since I only consider the hash value of the first part
        # sage: IExp(('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])).__hash__()
        # -242286530765552022

        # sage: IExp(('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 100}])).__hash__()
        # -242286530765552022
        # """
        # if is_tuple(self.inv):
        #     return self.inv[0].__hash__()
        # else:
        #     return self.inv.__hash__()



### Polynomial Invs ###
class InvExp(Inv):
    __metaclass__ = ABCMeta

    def __init__(self, p): 
        """
        Ex:
        x + y >= 0
        x^2 + y^2 + 3 == 0
        """

        if __debug__:
            assert is_sage_expr(p), p

        super(InvExp,self).__init__(p)

    def get_score(self):
        """
        Gives higher scores to invs with 'nicer' shapes

        Examples:
        sage: var('r a q y')
        (r, a, q, y)

        sage: assert InvIeq((1/2)*x**2 + 134.134234*y + 1 >= 0).get_score() == 12
        sage: assert InvEqt(x**3 + 2.432*x + 8 == 0).get_score() == 6
        sage: assert InvIeq(x**2+x+7 >= 0).get_score() == 3
        
        In case we cannot compute the score, returns the strlen of the inv
        sage: InvIeq(r + 2*a/q >= 0).get_score()
        14

        """
        try:
            Q = PolynomialRing(QQ, get_vars(self.p))
            p_lhs_poly = Q(self.p.lhs())
            rs = p_lhs_poly.coefficients()
            rs = [abs(r_.n()).str(skip_zeroes=True)
                  for r_ in rs if r_ != 0.0]
            rs = [sum(map(len,r_.split('.'))) for r_ in rs]
            rs = sum(rs)
            return rs
        except Exception:
            return len(self.p_str)
        
        
    def seval(self, tc): return bool(self.p.subs(tc))    
    

        
class InvEqt(InvExp):
    def __init__(self, p):
        if __debug__:
            assert is_sage_expr(p) and p.operator() == operator.eq
        super(InvEqt,self).__init__(p)
    
    @staticmethod
    def sreduce(ps):
        """
        Return the basis (e.g., a min subset of ps that implies ps) 
        of the set of eqts input ps using Groebner basis
       Examples:

        sage: var('a y b q k')
        (a, y, b, q, k)

        sage: rs =  InvEqt.sreduce([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        sage: assert set(rs) == set([a*y - b == 0, q*y + k - x == 0])

        sage: rs =  InvEqt.sreduce([x*y==6,y==2,x==3])
        sage: assert set(rs) == set([x - 3 == 0, y - 2 == 0])

        #Attribute error occurs when only 1 var, thus return as is
        sage: rs =  InvEqt.sreduce([x*x==4,x==2])
        sage: assert set(rs) == set([x == 2, x^2 == 4])


        """
        if __debug__:
            assert all(p.operator() == operator.eq for p in ps), ps

        try:
            Q = PolynomialRing(QQ,get_vars(ps))
            I = Q*ps
            #ps_ = I.radical().groebner_basis()
            ps = I.radical().interreduced_basis()
            ps = [(SR(p)==0) for p in ps]
        except AttributeError:
            pass

        return ps
        


class InvIeq(InvExp):
    def __init__(self, p):
        if __debug__:
            assert (is_sage_expr(p) and 
                    p.operator() in [operator.le, operator.ge])
        super(InvIeq,self).__init__(p)



    @staticmethod
    def sreduce(ps):
        """
        Return a minimum subset of ps that implies ps
        Use a greedy method to remove redundant properties.
        Thus it's quick, but not exact.

        Examples:

        sage: var('a y b q k s t z')
        (a, y, b, q, k, s, t, z)

        sage: InvIeq.sreduce([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        [q*y + k - x == 0, a*y - b == 0]

        sage: InvIeq.sreduce([a*y-b==0,a*z-a*x+b*q==0,q*y+z-x==0])
        [q*y - x + z == 0, a*y - b == 0]

        sage: InvIeq.sreduce([x-7>=0, x + y -2>=0, y+5 >= 0])
        [x - 7 >= 0, y + 5 >= 0]

        sage: InvIeq.sreduce([x+y==0,x-y==1])
        [x + y == 0, x - y == 1]

        sage: InvIeq.sreduce([x^2-1>=0,x-1>=0])
        [x - 1 >= 0]


        sage: InvIeq.sreduce([a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0,a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0])
        [t^2 - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]

        sage: InvIeq.sreduce([x*x-y*y==0,x-y==0,x*x-y*y==0,2*x*y-2*y*y==0])
        [x - y == 0]

        sage: InvIeq.sreduce([x-1>=0 , t*y - 6 >= 0, t - 1 >= 0, y - 6 >= 0, t*y - y >= 0, t*x - x >= 0, y*x - 6*x>=0 , y^2 - 36 >= 0, t^2 - 3*t + 2 >= 0, t^2 - 5*t + 6 >= 0 , t*y - 6*t - y + 6 >= 0])
        [x - 1 >= 0, t - 1 >= 0, y - 6 >= 0, t^2 - 3*t + 2 >= 0, t^2 - 5*t + 6 >= 0]


        sage: InvIeq.sreduce([x*y==6, y-2==0, x-3==0])
        [y - 2 == 0, x - 3 == 0]

        sage: InvIeq.sreduce([x*x==4,x==2])
        [x == 2]
        sage: InvIeq.sreduce([x==2,x*x==4])
        [x == 2]
        sage: InvIeq.sreduce([x==2,x*x==4,x==-2])
        [x == 2, x == -2]
        sage: InvIeq.sreduce([x==2,x==-2,x*x==4])
        [x == 2, x == -2]
        sage: InvIeq.sreduce([x*x==4,x==2,x==-2])
        [x == 2, x == -2]
        """

        from smt_z3py import SMT_Z3

        #Remove "longer" property first (i.e. those with more variables)
        ps = sorted(ps, reverse=True, key=lambda p: len(get_vars(p)))
        rs = list(ps) #make a copy
        for p in ps:
            if p in rs:
                #note, the use of set makes things in non order
                xclude_p = vsetdiff(rs,[p])

                if SMT_Z3.imply(xclude_p,p):
                    rs = xclude_p

        return rs

class InvMPP(Inv):
    def __init__(self, p): 
        """
        Ex:
        sage: m = InvMPP(('lambda p,r: 422 >= min(p,r + 29)', 'If(p <= r + 29, 422 >= p, 422 >= r + 29)'))
        
        sage: print m
        422 >= min(p,r + 29), If(p <= r + 29, 422 >= p, 422 >= r + 29)

        sage: m.get_score()
        62

        """
        if __debug__:
            assert (is_tuple(p) and len(p)==2 and 
                    is_str(p[0]) and 'lambda' in p[0] and
                    is_str(p[1])), p

        super(InvMPP,self).__init__(p[0].strip(), p_str=p[1])
                                    

    def get_score(self): 
        """
        sage: InvMPP(('lambda x: x**2+x+7 >0','If-then-else')).get_score()
        25
        """
        return len(self.p_str)
        
    def seval(self, tc): 
        return InvMPP.eval_lambda(self.p, tc, is_formula=True)
        

    @staticmethod
    def eval_lambda(f, d, is_formula=True):
        """
        Evaluates lambda function f

        Examples:

        sage: assert InvMPP.eval_lambda('lambda x,y: max(x - 13,-3) >= y', {'x':11,'y':100}) == False

        sage: assert InvMPP.eval_lambda('lambda x,y: x+y == 5', {'x':2,'y':3,'d':7})

        sage: assert InvMPP.eval_lambda('lambda x,y: x+y == 6', {'x':2,'y':3,'d':7}) == False


        sage: assert InvMPP.eval_lambda('lambda x,y: x+y', {'x':2,'y':3,'d':7}, is_formula=False) == 5
        


        sage: assert InvMPP.eval_lambda('lambda x,y: x+y == 10 or x + y == 5', {'x':2,'y':3,'d':7})

        sage: assert InvMPP.eval_lambda('lambda x,y: x+y == 1 or x + y == 2', {'x':2,'y':3,'d':7}) == False

        """
        if __debug__:
            assert is_str(f) and 'lambda' in f, f
            assert is_dict(d), d
            assert all(is_str(k) for k in d), d.keys()

        f = sage_eval(f)
        vs = f.func_code.co_varnames
        assert set(vs) <= set(d.keys()), (vs,d.keys())

        #if d has more keys than variables in f then remove those extra keys
        d=dict([(k,d[k]) for k in vs])
        rs = f(**d)
        return bool(rs) if is_formula else rs



### Array Invs ###
class InvArray(Inv):
    __metaclass__ = ABCMeta

    def __init__(self, p):
        """
        Ex:
        flat arr: 'lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0 
        nested arr: 'lambda A,B,i1: A[i1] == B[-2*i1 + 5]'
        """
        if __debug__:
            assert (is_str(p) and 
                    all(s in p for s in ['lambda','[' ,']'])), p

        super(InvArray,self).__init__(p)
        
    def get_score(self): return len(self.p_str)

    def seval(self, tc): 
        return InvArray.eval_lambda(self.p, idx_info=self.idx_info, tc=tc)

    @staticmethod
    def eval_lambda(f, idx_info, tc):
        """
        Evaluate array expression p, e.g. p:  A[i,j,k]=B[2i+3j+k]

        if idx_info is specified then only test p on the idxs from idx_info


        Assumes:
        the first array in lambda is the pivot
        lambda A,B,i,j,k: ...  =>  i,j,k  belong to A



        inv = 'lambda B,C,D,i,j: B[i][j]=C[D[2i+3]]'
        returns true if inv is true on tc

        Examples:

        sage: var('a,b,c,i,j')
        (a, b, c, i, j)

        sage: InvArray.eval_lambda('lambda a,b,c,i,j: a[i][j]==2*b[i]+c[j]', None, {'a':[[4,-5],[20,11]],'b':[1,9],'c':[2,-7]})
        True

        sage: InvArray.eval_lambda('lambda c,a,b,xor,i: c[i] == xor(a[i],b[i])', None, {'a': [147, 156, 184, 76], 'b': [51, 26, 247, 189], 'c': [160, 334, 79, 281]})
        False

        sage: InvArray.eval_lambda('lambda c,a,b,xor,i1: c[i1] == xor(a[i1],b[i1])', None, {'a': [147, 156, 184, 76], 'b': [51, 26, 247, 189], 'c': [160, 134, 79, 241]})
        True


        sage: InvArray.eval_lambda('lambda rvu, t, rvu1, rvu0: (rvu[rvu0][rvu1]) + (-t[4*rvu0 + rvu1]) == 0', None, {'t': [28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], 'rvu': [[28, 131, 11, 85], [133, 46, 179, 20], [227, 148, 225, 197], [38, 221, 221, 126]]})
        True

        #The following illustrate the use of idxVals,
        #i.e. p is only true under certain array rages

        sage: InvArray.eval_lambda('lambda st, rvu, st0, st1: (-st[st0][st1]) + (rvu[4*st0 + st1]) == 0', None, tc = {'rvu': [28, 131, 11, 85, 193, 124, 103, 215, 66, 26, 68, 54, 176, 102, 15, 237], 'st': [[28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], [193, 124, 103, 215, 106, 229, 162, 168, 166, 78, 144, 234, 199, 254, 152, 250], [66, 26, 68, 54, 206, 16, 155, 248, 231, 198, 240, 43, 208, 205, 213, 26], [176, 102, 15, 237, 49, 141, 213, 97, 137, 155, 50, 243, 112, 51, 124, 107]]})
        False

        sage: InvArray.eval_lambda('lambda st, rvu, st0, st1: (-st[st0][st1]) + (rvu[4*st0 + st1]) == 0', idx_info = [{'st0': 0, 'st1': 0}, {'st0': 0, 'st1': 1}, {'st0': 2, 'st1': 2}, {'st0': 2, 'st1': 3}, {'st0': 3, 'st1': 0}, {'st0': 3, 'st1': 1}, {'st0': 3, 'st1': 2}, {'st0': 3, 'st1': 3}, {'st0': 0, 'st1': 2}, {'st0': 0, 'st1': 3}, {'st0': 1, 'st1': 0}, {'st0': 1, 'st1': 1}, {'st0': 1, 'st1': 2}, {'st0': 1, 'st1': 3}, {'st0': 2, 'st1': 0}, {'st0': 2, 'st1': 1}], tc = {'rvu': [28, 131, 11, 85, 193, 124, 103, 215, 66, 26, 68, 54, 176, 102, 15, 237], 'st': [[28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], [193, 124, 103, 215, 106, 229, 162, 168, 166, 78, 144, 234, 199, 254, 152, 250], [66, 26, 68, 54, 206, 16, 155, 248, 231, 198, 240, 43, 208, 205, 213, 26], [176, 102, 15, 237, 49, 141, 213, 97, 137, 155, 50, 243, 112, 51, 124, 107]]})
        True

        """


        """
        Note: sage_eval vs eval
        sage_eval works on str of the format 'lambda x,y: 2*x+y'
        whereas eval works on str of the format 2*x+y directly (no lambda)
        Also, the result of sage_eval can apply on dicts whose keys are str
        e.g.  f(**{'x':2,'y':3})
        whereas the result of eval applies on dict whose keys are variables
        e.g.  f(**{x:2,y:3})
        """

        if __debug__:
            assert is_str(f) and 'lambda' in f, f
            assert (idx_info is None or 
                    is_list(idx_info) and all(is_dict(v) for v in idx_info)), indx_info
            assert is_dict(tc), tc
            assert all(is_str(k) for k in tc), tc.keys()

        f = sage_eval(f)
        vs = f.func_code.co_varnames

        arrs    = [v for v in vs if v in tc]        #A,B
        extfuns = [v for v in vs if v in ExtFun.efdict]
        idxStr  = [v for v in vs if v not in arrs+extfuns]  #i,j,k

        d_tc    = dict([(v,tc[v]) for v in arrs])
        d_extfun= dict([(v,ExtFun(v).get_fun()) for v in extfuns])
        d_      = merge_dict([d_tc,d_extfun])

        if idx_info is None: #obtain idxsVals from the pivot array
            pivotContents = tc[arrs[0]]
            idxVals  = [idx for idx,_ in Miscs.travel(pivotContents)]
            idx_info = [dict(zip(idxStr,idxV)) for idxV in idxVals]

        ds = [merge_dict([d_, idx_info_]) for idx_info_ in idx_info]

        try:
            return all(f(**d) for d in ds)
        except IndexError:
            return False
        except TypeError:
            return False
        except NameError as msg:
            logger.warn(msg)
            return False


class InvFlatArray(InvArray):
    def __init__(self, p): 
        """
        Ex:
        ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', 
        [{'A0': 2}, {'A0': 0}, {'A0': 1}])
        """

        if __debug__:
            assert (is_tuple(p) and len(p)==2 and 
                    is_str(p[0]) and 
                    all(s in p[0] for s in ['lambda','[' ,']']) and
                    is_list(p[1]) and all(is_dict(v) for v in p[1])), p
            
        super(InvFlatArray,self).__init__(p[0].strip())
        self.idx_info = p[1]

class InvNestedArray(InvArray):
    def __init__(self, p):
        """
        Ex:
        'lambda a,b,c,i,j: a[i][j]==2*b[i]+c[j]'
        """
        if __debug__:
            assert (is_str(p) and 
                    all(s in p for s in ['lambda','[' ,']'])), p

        super(InvNestedArray,self).__init__(p.strip())
        self.idx_info = None #no info about idx (only for FlatArr)

