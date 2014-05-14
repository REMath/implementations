import itertools
import multiprocessing as mp
from abc import ABCMeta, abstractmethod

from sage.all import (flatten, solve, srange, operator, sage_eval, prod,
                      Polyhedron, CartesianProduct, Combinations,
                      SR, RR, QQ, PolynomialRing, operator, oo, is_even)
from sageutil import (get_vars, is_sage_symbol, is_sage_int,
                      is_sage_expr, is_sage_rel)
from vu_common import (VLog, pause, vset, is_empty, is_list, is_bool, vcmd)
from dig_miscs import (Miscs, get_traces, get_sample, 
                       gen_terms_fixed_coefs)

from dig import Solver
from dig_inv import InvEqt, InvIeq, InvMPP

logger = VLog('dig_polynomials')
logger.level = VLog.INFO


class Eqt(Solver):
    """
    Find equality invariants using standard equation solving
    """

    def __init__(self,terms,tcs,xinfo):
        super(Eqt,self).__init__(terms, tcs, xinfo)

    def mk_traces(self):
        """
        No need to do too much filtering because 
        most eqts obtained are valid
        """
        tpercent = 150 # terms % for inv gen
        ntcs = int(round(len(self.terms) * tpercent / 100.00))
        ntcs_extra = 200
        return get_traces(self.tcs, ntcs, ntcs_extra)

        
    def solve(self): #eqt
        sols = Miscs.solve_eqts(ts=self.terms, rv=0, ds=self.tcs)
        self.sols = map(InvEqt, sols)

    def refine(self):
        from refine import Refine
        rf = Refine(ps=self.sols)
        #rf.rrank()
        rf.rfilter(tcs=self.tcs_extra)
        rf.rinfer()

        self.sols = rf.ps

class IeqDeduce(Solver):
    """
    Find Inequalities by Deduction (require external information, i.e assumes)

    sage: logger.set_level(VLog.DEBUG)

    sage: var('b rvu a y q')
    (b, rvu, a, y, q)

    sage: ieqdeduce = IeqDeduce(xinfo={'Assume':['-2*b + rvu >= 0']},eqts=[-a*y + b == 0,q*y + rvu - x == 0])
    Traceback (most recent call last):
    ...
    AssertionError: Assumes (['-2*b + rvu >= 0']) and Eqts ([-a*y + b == 0, q*y + rvu - x == 0]) must be relational

    sage: ieqdeduce = IeqDeduce(xinfo={'Assume':[-2*b + rvu >= 0]},eqts=[-a*y + b == 0,q*y + rvu - x == 0])
    dig:Info:*** IeqDeduce ***
    dig_polynomials:Debug:|assumes|=1, |eqts|=2

    sage: ieqdeduce.go()
    dig:Info:Select traces
    dig:Info:Compute invs over 0 tcs
    dig_polynomials:Debug:* deduce(|assumes|=1,|eqts|=2)
    dig_polynomials:Debug:assumed ps: -2*b + rvu >= 0
    dig:Info:Refine 2 invs
    dig:Info:Detected 2 invs for IeqDeduce:
    0: -2*a*y + rvu >= 0
    1: -q*y - 2*b + x >= 0

    """

    def __init__(self, eqts, xinfo):
        assumes = xinfo['Assume']
        if __debug__:
            assert is_list(eqts) and eqts, eqts
            assert is_list(assumes) and assumes, assumes
            assert all(is_sage_rel(x) 
                       for x in assumes + eqts), (assumes,eqts)
                    

        super(IeqDeduce,self).__init__(terms=[], tcs=[], xinfo=xinfo)
        logger.debug('|assumes|={}, |eqts|={}'
                     .format(len(assumes),len(eqts)))
                     

        self.eqts = eqts

    def mk_traces(self): return [], []

    def solve(self):
        assumes = [a - a.rhs() for a in self.xinfo['Assume']]
        sols = IeqDeduce.deduce(assumes=assumes, eqts=self.eqts)
        self.sols = map(InvIeq, sols)

    def refine(self):
        #no refinement for deduced invs
        pass
        
    ##### Helpers for IeqDeduce #####

    @staticmethod
    def substitute(e1,e2):
        """
        Examples:

        sage: var('x t q b y a')
        (x, t, q, b, y, a)

        sage: IeqDeduce.substitute(t-2*b>=0,x==q*y+t)
        [-q*y - 2*b + x >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b-y*a==0)
        [-2*a*y + t >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b-4==0)
        [t - 8 >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b+4==0)
        [t + 8 >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b^2+4==0)
        [t + 4*I >= 0, t - 4*I >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b^2-4==0)
        [t + 4 >= 0, t - 4 >= 0]

        #todo: cannot do when e2 is not equation
        sage: IeqDeduce.substitute(2*b>=0,b>=5)
        dig_polynomials:Warn:substitution fails on b >= 5
        2*b >= 0

        sage: IeqDeduce.substitute(2*b==0,b>=5)
        dig_polynomials:Warn:substitution fails on b >= 5
        2*b == 0
        """

        e1_vs = get_vars(e1)
        e2_vs = get_vars(e2)

        rs = [solve(e2,e2_v,solution_dict=True)
              for e2_v in e2_vs if e2_v in e1_vs]

        rs = flatten(rs)

        try:
            rs = [e1.subs(rs_) for rs_ in rs]
            return rs
        except Exception:
            logger.warn('substitution fails on {}'.format(e2))
            return e1


    @staticmethod
    def deduce(assumes ,eqts):
        """
        Examples

        sage: logger.set_level(VLog.DEBUG)

        sage: var('r a b q y x'); IeqDeduce.deduce([r>=2*b],[b==y*a,x==q*y+r])
        (r, a, b, q, y, x)
        dig_polynomials:Debug:* deduce(|assumes|=1,|eqts|=2)
        dig_polynomials:Debug:assumed ps: r >= 2*b
        [r >= 2*a*y, -q*y + x >= 2*b]

        sage: var('s n a t'); IeqDeduce.deduce([s<=n],[t==2*a+1,s==a**2+2*a+1])
        (s, n, a, t)
        dig_polynomials:Debug:* deduce(|assumes|=1,|eqts|=2)
        dig_polynomials:Debug:assumed ps: s <= n
        [a^2 + 2*a + 1 <= n]

        """
        logger.debug('* deduce(|assumes|={},|eqts|={})'
                     .format(len(assumes),len(eqts)))
        logger.debug('assumed ps: {}'.format(', '.join(map(str,assumes))))

        combs = [(aps,ei) for aps in assumes for ei in eqts
                 if any(x in get_vars(aps) for x in get_vars(ei))]

        sols= [IeqDeduce.substitute(e1,e2) for e1,e2 in combs] 
        sols = flatten(sols,list)

        return sols



class Ieq(Solver):
    """
    Base class for Inequality solvers
    """
    __metaclass__ = ABCMeta

    def mk_traces(self):
        """
        E.g., 
        |tcs| = 100 then 80 for invgen, 20 for filter
        |tcs| = 1000 then 300 for invgen, 700 for filter
        |tcs| = 10000 then 300 for invgen, 1000 for filter
        """
        max_ntcs = 300
        max_ntcs_extra = 1000

        if len(self.tcs)<=100:
            tpercent=100
        else:
            tpercent = 80 # traces % for inv gen
        ntcs = int(round(len(self.tcs) * tpercent / 100.00))
        ntcs = min(ntcs,max_ntcs)

        ntcs_extra = len(self.tcs) - ntcs
        ntcs_extra = min(ntcs_extra,max_ntcs_extra)
        
        return get_traces(self.tcs, ntcs, ntcs_extra)
    
    def refine(self):
        from refine import Refine
        rf = Refine(ps=self.sols)
        #rf.rrank()
        rf.rfilter(tcs=self.tcs_extra)
        #rf.rinfer()  #only run when deg >= 2

        self.sols = rf.ps

            
class IeqCLPFixed(Ieq):
    """
    Find Inequalities using Classic Polyhedra with fixed coefs (e.g. octagonal)
    

    sage: var('y z')
    (y, z)

    sage: ieq = IeqCLPFixed(terms=[x,y],tcs=[{x:2,y:-8},{x:0,y:-15},{x:15,y:5}],xinfo=None)
    dig:Info:*** IeqCLPFixed ***
    sage: ieq.solve()
    sage: ieq.sols
    [-x - y + 20 >= 0, -x + 15 >= 0, -x + y + 15 >= 0, -y + 5 >= 0, y + 15 >= 0,
     x - y - 10 >= 0, x >= 0, x + y + 15 >= 0]
     
     
   sage: ieq = IeqCLPFixed(terms=[x,y,z],tcs=[{x:2,y:-8,z:-7},{x:0,y:-15,z:88},{x:15,y:5,z:0}],xinfo=None)
    dig:Info:*** IeqCLPFixed ***
    sage: ieq.subset_siz = 2  #oct
    sage: ieq.solve()
    sage: ieq.sols
    [-x - y + 20 >= 0, -x + 15 >= 0, -x + y + 15 >= 0, -y + 5 >= 0,
     y + 15 >= 0, x - y - 10 >= 0, x >= 0, x + y + 15 >= 0,
     -x - z + 88 >= 0, -x + z + 15 >= 0,     
     -z + 88 >= 0, z + 7 >= 0,
     x - z + 88 >= 0, x + z + 5 >= 0,
     -y - z + 73 >= 0, -y + z + 5 >= 0,
     y - z + 103 >= 0, y + z + 15 >= 0]
     
    sage: ieq.subset_siz = None   #all 3 terms
    sage: ieq.solve()
    sage: ieq.sols
    [-x - y - z + 73 >= 0,
     -x - y + 20 >= 0,
     -x - y + z + 20 >= 0,
     -x - z + 88 >= 0,
     -x + 15 >= 0,
     -x + z + 15 >= 0,
     -x + y - z + 103 >= 0,
     -x + y + 15 >= 0,
     -x + y + z + 17 >= 0,
     -y - z + 73 >= 0,
     -y + 5 >= 0,
     -y + z + 5 >= 0,
     -z + 88 >= 0,
     z + 7 >= 0,
     y - z + 103 >= 0,
     y + 15 >= 0,
     y + z + 15 >= 0,
     x - y - z + 73 >= 0,
     x - y - 10 >= 0,
     x - y + z - 3 >= 0,
     x - z + 88 >= 0,
     x >= 0,
     x + z + 5 >= 0,
     x + y - z + 103 >= 0,
     x + y + 15 >= 0,
     x + y + z + 13 >= 0]
         
    """
    def __init__(self, terms, tcs, xinfo):
        super(IeqCLPFixed, self).__init__(terms, tcs, xinfo)
        self.subset_siz = None
        
    def solve(self):
        ts = [t for t in self.terms if t != 1]

        if self.subset_siz is None:
            subset_siz = len(ts)
        else:
            subset_siz = self.subset_siz
            
        ts_ = gen_terms_fixed_coefs(ts,subset_siz=subset_siz,
                                    blacklist=None,is_mpp=False)

        logger.debug('Build (fixed CL) poly from {} tcs in {} dims '
                     '(~ {} facets)'
                     .format(len(self.tcs),len(ts),len(ts_)))

        #can be done in parallel
        rs = []
        for t in ts_:
            rs.append(t - min(t.subs(tc) for tc in self.tcs) >= 0)
        
        self.sols = map(InvIeq,rs)
        
class IeqCLPGen(Ieq):
    """
    Find Inequalities using Classic Polyhedra

    Complexity:
    * building a Classic polyhedron takes *exponential* time wrt number
    of terms, so generally a (small) number of terms need to be specified.

    Traces: Unlike other type of invariants, it's much harder to obtain
    testcases exhibiting the Inequality. I.e. it's easy to get x+y>10,
    but much harder to get x+y = 10.  And we need both to get x+y >= 10.

    sage: var('y z')
    (y, z)

    sage: ieq = IeqCLPGen(terms=[x,y],tcs=[{x:2,y:-8},{x:0,y:-15},{x:15,y:5}],xinfo=None)
    dig:Info:*** IeqCLPGen ***
    sage: ieq.solve()
    sage: ieq.sols
    [7*x - 2*y - 30 >= 0, -4*x + 3*y + 45 >= 0, x - y - 10 >= 0]
    
    
    sage: ieq = IeqCLPGen(terms=[x,y,z],tcs=[{x:2,y:-8,z:-7},{x:0,y:-15,z:88},{x:15,y:5,z:0}],xinfo=None)
    dig:Info:*** IeqCLPGen ***
    sage: ieq.solve()
    sage: ieq.sols
    [95*y + 7*z + 809 >= 0, -22*y - 5*z + 110 >= 0, -7*y + 13*z + 35 >= 0]
         
     """
    
    def __init__(self, terms, tcs, xinfo):

        super(IeqCLPGen,self).__init__(terms,tcs,xinfo)
        self.subset_size = None
        
    def solve(self):
        """
        Builds a classic convex polyhedron over vts and
        returns a set of constraints (i.e. the facets of the polyhedron)
        """

        ts = [t for t in self.terms if t != 1]
        
        logger.debug('Create vertices from {} traces'
                     .format(len(self.tcs)))
                     
        vts = [[QQ(t.subs(tc)) for t in ts] for tc in self.tcs]
        vts = map(list,set(map(tuple,vts))) #make these vts unique

        logger.debug('Build (gen CL) poly from {} vts in {} dims: {}'
                     .format(len(vts),len(vts[0]),ts))

        poly = Polyhedron(vertices=vts,base_ring=QQ)
        try:
            rs = [list(p.vector()) for p in poly.inequality_generator()]

            logger.debug('Sage: found {} inequalities'.format(len(rs)))

            #remove rs of form [const_c, 0 , ..., 0]
            #because those translate to the trivial form 'const_c >= 0'
            rs = [s for s in rs if any(x != 0 for x in s[1:])]

        except AttributeError:
            logger.warn('Sage: cannot construct polyhedron')
            rs = []


        if rs:
            #parse the result
            _f = lambda s: s[0] + sum(map(prod,zip(s[1:],ts)))
            rs = [_f(s) >= 0 for s in rs]

            #remove trivial (tautology) str(x) <=> str(x)
            rs = [s for s in rs
                  if not (s.is_relational()
                          and str(s.lhs()) == str(s.rhs()))]

        self.sols = map(InvIeq,rs)



class IeqMPP(Ieq):
    __metaclass__ = ABCMeta
    
    opt_max_plus = 0
    opt_min_plus = 1
    opt_max_then_min = 2
        
    #utils for MPP
    
    @staticmethod
    def sparse(ls, is_max_plus):
        """
        Parse the result from
        'compute_ext_rays_polar' in TPLib into proper lambda format

        Examples:

        sage: var('x,y,z,d')
        (x, y, z, d)

        sage: IeqMPP.sparse([-oo,0,-oo,-oo,-6,-oo,-oo,-oo],[x,y,z,SR(0)], IeqMPP.opt_max_plus)
        ('lambda x,y: -x + y + 6 >= 0', 'y >= x - 6')

        sage: IeqMPP.sparse([-oo,-oo,-oo,9,-6,-oo,-oo,20],[x,y,z,d], IeqMPP.opt_max_plus)
        ('lambda d,x: d + 9 - max(x - 6,d + 20) >= 0', 'If(x - 6 >= d + 20, d + 9 >= x - 6, d + 9 >= d + 20)')

        sage: IeqMPP.sparse([-1,-oo,-oo,0],[x,SR(0)],IeqMPP.opt_max_plus)
        ('lambda x: x - 1 >= 0', 'x - 1 >= 0')

        sage: IeqMPP.sparse([0,-oo,-oo,1],[x,SR(0)],IeqMPP.opt_max_plus)
        ('lambda x: x - 1 >= 0', 'x >= 1')


        sage: IeqMPP.sparse([-oo,0,-oo,-oo,-6,-oo,-oo,-oo],[x,y,z,SR(0)], IeqMPP.opt_min_plus)
        ('lambda x,y: -x + y + 6 >= 0', 'y >= x - 6')

        sage: IeqMPP.sparse([-oo,-oo,-oo,9,-6,-oo,-oo,20],[x,y,z,d], IeqMPP.opt_min_plus)
        ('lambda d,x: d + 9 - min(x - 6,d + 20) >= 0', 'If(x - 6 <= d + 20, d + 9 >= x - 6, d + 9 >= d + 20)')

        sage: IeqMPP.sparse([-1,-oo,-oo,0],[x,SR(0)],IeqMPP.opt_min_plus)
        ('lambda x: x - 1 >= 0', 'x - 1 >= 0')

        sage: IeqMPP.sparse([0,-oo,-oo,1],[x,SR(0)],IeqMPP.opt_min_plus)
        ('lambda x: x - 1 >= 0', 'x >= 1')

        """

        if __debug__:
            assert is_list(ls) and is_even(len(ls)), ls
            assert is_bool(is_max_plus), is_max_plus

        mp = len(ls)/2
        lhs = [l for l in ls[:mp] if not l.is_infinity()] 
        rhs = [l for l in ls[mp:] if not l.is_infinity()]

        #if lhs contains the same exact elems as rhs then remove
        #b/c it's a tautology, e.g. max(x,y) >= max(y,x)
        if set(lhs) == set(rhs): 
            return None

        #if one of these is empty, i.e. contain only +/-Inf originally
        if not lhs or not rhs: 
            return None
        
        
        return IeqMPP.gen_lambda_disj(lhs, rhs, is_max_plus,is_eq=False)

    @staticmethod
    def gen_lambda_disj(lh, rh, is_max_plus,is_eq):
        """
        shortcut that creates lambda expr and disj formula
        """
        r_lambda = IeqMPP.gen_lambda_exp(lh, rh, 
                                         is_max_plus, is_formula=True,
                                         is_eq=is_eq)
        r_disj = IeqMPP.gen_disj_exp(lh,rh,is_max_plus,is_eq)
        return (r_lambda, r_disj)

    @staticmethod
    def gen_lambda_exp(ls, rs, is_max_plus, is_formula, is_eq):
        """
        Return lambda expression
        lambda x,y, ...  =  max(x,y...) >= max(x,y...)

        Examples:

        sage: var('y')
        y

        sage: IeqMPP.gen_lambda_exp([x-10,y-3],[y,5], is_max_plus=True)
        'lambda x,y: max(x - 10,y - 3) - max(y,5) >= 0'

        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y,5], is_max_plus=True,is_formula=True,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - max(y,5) >= 0'
        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y,5], is_max_plus=True,is_formula=False,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - max(y,5)'
        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y], is_max_plus=True,is_formula=False,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - (y)'
        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y], is_max_plus=True,is_formula=False,is_eq=True)
        'lambda x,y: max(x - 10,y - 3) - (y)'
        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y], is_max_plus=True,is_formula=True,is_eq=True)
        'lambda x,y: max(x - 10,y - 3) - (y) == 0'
        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y+12], is_max_plus=False,is_formula=True,is_eq=True)
        'lambda x,y: min(x - 10,y - 3) - (y + 12) == 0'
        sage:  IeqMPP.gen_lambda_exp([x-10,y-3],[y+12], is_max_plus=False,is_formula=True,is_eq=True)
        'lambda x,y: min(x - 10,y - 3) - (y + 12) == 0'
        sage: 
        """
        if __debug__:
            assert is_list(ls) and ls, ls
            assert is_list(rs) and rs, rs

        op = 'max' if is_max_plus else 'min'

        str_op = (lambda s: '{}({})'
                  .format(op, ','.join(map(str,s))) 
                  if len(s)>=2 else s[0])

        if len(rs) == 1:

            if len(ls) == 1:  #(x+3,y+8),  (3,8), (3,y)
                ss = ls[0] - rs[0] 

            else: #len(ls) >= 2
                rss = rs[0]
                lss = str_op(ls)
                if rss.is_zero():
                    ss = lss
                else:
                    if rss.operator is None:  #x,,y7
                        ss = '{} - {}'.format(lss,rss)
                    else:#x + 3,  y - 3
                        ss = '{} - ({})'.format(lss,rss)
        else: #len(rs) >= 2:
            ss = '{} - {}'.format(str_op(ls), str_op(rs))

        ss = ('lambda {}: {}{}'
              .format(','.join(map(str, get_vars(ls+rs))), ss,
                       ' {} 0'.format('==' if is_eq else '>=') 
                      if is_formula else ''))
        return ss

    @staticmethod
    def gen_disj_exp(ls,rs,is_max_plus,is_eq):
        """
        Return disjunctive format

        sage:  IeqMPP.gen_disj_exp([x-10,y-3],[y+12], is_max_plus=True,is_eq=True)
        'If(x - 10 >= y - 3,x - 10 == y + 12,y - 3 == y + 12)'
        sage:  IeqMPP.gen_disj_exp([x-10,y-3],[y+12], is_max_plus=True,is_eq=False)
        'If(x - 10 >= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'
        sage:  IeqMPP.gen_disj_exp([x-10,y-3],[y+12], is_max_plus=False,is_eq=False)
        'If(x - 10 <= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'
        sage:  IeqMPP.gen_disj_exp([x-10,y-3],[y+12], is_max_plus=False,is_eq=False)
        'If(x - 10 <= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'
        sage:  IeqMPP.gen_disj_exp([x-10,y-3],[y,12], is_max_plus=False,is_eq=False)
        'If(x - 10 <= y - 3,If(y <= 12, x - 10 >= y, x - 10 >= 12),If(y <= 12, y - 3 >= y, y - 3 >= 12))'
        sage:  IeqMPP.gen_disj_exp([x-10,y-3],[y,12], is_max_plus=False,is_eq=True)
        'If(x - 10 <= y - 3,If(y <= 12, x - 10 == y, x - 10 == 12),If(y <= 12, y - 3 == y, y - 3 == 12))'
        """
        if not is_list(ls):
            ls = [ls]
        if not is_list(rs):
            rs = [rs]
        
        return IeqMPP.l_mp2df(ls,rs,is_max_plus,0,is_eq)

    @staticmethod
    def l_mp2df(ls,rs,is_max_plus,idx,is_eq):
        if __debug__:
            assert not is_empty(ls), ls
            assert not is_empty(rs), rs
            assert idx >= 0, idx
            assert is_bool(is_max_plus), is_max_plus  

        ls_ = ls[idx:]

        if __debug__:
            assert ls_, ls_

        first_elem = ls_[0]
        first_elem_f = IeqMPP.r_mp2df(first_elem,rs,is_max_plus,0,is_eq)

        if len(ls_) == 1: #t <= max(x,y,z)
            return first_elem_f
        else:
            op = ">=" if is_max_plus else "<="
            rest_f = IeqMPP.l_mp2df(ls,rs,is_max_plus,idx+1,is_eq)
            
            others = ls[:idx]+ls[idx+1:]
            csts = ','.join('{} {} {}'.format(first_elem, op, t) 
                             for t in others)
            cond = ("And({})" if len(others) >= 2 else "{}").format(csts)
            return "If({},{},{})".format(cond, first_elem_f, rest_f)
        

    @staticmethod
    def r_mp2df(t,rs,is_max_plus,idx,is_eq):
        """
        Convert max/min-plus format to disjunctive formula
        Inputs:
        t = single term
        rs = list of terms
        idx = operate over rs[idx:]
        """
        if __debug__:
            assert not is_empty(rs)
            assert idx >= 0, idx
            assert is_bool(is_max_plus), is_max_plus

        rs_ = rs[idx:]

        if __debug__:
            assert not is_empty(rs_)

        first_elem = rs_[0]
        first_elem_f = ("{} {} {}"
                        .format(t, '==' if is_eq else '>=',first_elem))
                                          

        if len(rs_) == 1:  # t <= x ==> t <= x
            return first_elem_f

        else: # t <= max(x,y,z) ==> If(x>=y and x >= z, t <= x, ...)
            op = ">=" if is_max_plus else "<="
            rest_f = IeqMPP.r_mp2df(t,rs,is_max_plus,idx+1,is_eq)

            others = rs[:idx]+rs[idx+1:]
            csts = ','.join('{} {} {}'.
                            format(first_elem, op, t) for t in others)
            cond = ('And({})' if len(others) >= 2 else '{}').format(csts)
            return "If({}, {}, {})".format(cond, first_elem_f, rest_f)


class IeqMPPFixed(IeqMPP):
    """
    sage: var('y z')
    (y, z)
    sage: tcs = [{x:2,y:-8,z:-7},{x:-1,y:-15,z:88},{x:15,y:5,z:0}]
    sage: ieq = IeqMPPFixed(terms=[x,y],tcs=tcs,xinfo=None)
    sage: ieq.solve()
    sage: ieq.sols; len(ieq.sols)
    ['lambda x,y: max(x,0) - (y + 10) >= 0',
    'lambda x,y: y + 15 - max(x,0) >= 0',
    'lambda x,y: x - y - 10 >= 0',
    'lambda x,y: -x + y + 14 >= 0',
    'lambda x,y: max(y,0) - (x - 10) >= 0',
    'lambda x,y: x + 1 - max(y,0) >= 0',
    'lambda x: -x + 15 >= 0',
    'lambda x: x + 1 >= 0',
    'lambda y: -y + 5 >= 0',
    'lambda y: y + 15 >= 0']
    10

    
    sage: ieq = IeqMPPFixed(terms=[x,y,z],tcs=tcs,xinfo=None)
    dig:Info:*** IeqMPPFixed ***
    sage: ieq.solve()
    sage: ieq.sols; len(ieq.sols)
    ['lambda x,y,z: max(x,y,0) - (z - 88) >= 0',
    'lambda x,y,z: z + 15 - max(x,y,0) >= 0',
    'lambda x,y,z: max(x,y) - (z - 89) >= 0',
    'lambda x,y,z: z + 15 - max(x,y) >= 0',
    'lambda x,y,z: max(x,z,0) - (y + 10) >= 0',
    'lambda x,y,z: y + 103 - max(x,z,0) >= 0',
    'lambda x,y,z: max(x,z) - (y + 10) >= 0',
    'lambda x,y,z: y + 103 - max(x,z) >= 0',
    'lambda x,y: max(x,0) - (y + 10) >= 0',
    'lambda x,y: y + 15 - max(x,0) >= 0',
    'lambda x,z: max(x,0) - (z - 88) >= 0',
    'lambda x,z: z + 15 - max(x,0) >= 0',
    'lambda x,y: x - y - 10 >= 0',
    'lambda x,y: -x + y + 14 >= 0',
    'lambda x,z: x - z + 89 >= 0',
    'lambda x,z: -x + z + 15 >= 0',
    'lambda x,y,z: max(y,z,0) - (x - 10) >= 0',
    'lambda x,y,z: x + 89 - max(y,z,0) >= 0',
    'lambda x,y,z: max(y,z) - (x - 10) >= 0',
    'lambda x,y,z: x + 89 - max(y,z) >= 0',
    'lambda x,y: max(y,0) - (x - 10) >= 0',
    'lambda x,y: x + 1 - max(y,0) >= 0',
    'lambda y,z: max(y,0) - (z - 88) >= 0',
    'lambda y,z: z + 7 - max(y,0) >= 0',
    'lambda y,z: y - z + 103 >= 0',
    'lambda y,z: -y + z + 5 >= 0',
    'lambda x,z: max(z,0) - (x - 15) >= 0',
    'lambda x,z: x + 89 - max(z,0) >= 0',
    'lambda y,z: max(z,0) - (y - 5) >= 0',
    'lambda y,z: y + 103 - max(z,0) >= 0',
    'lambda x: -x + 15 >= 0',
    'lambda x: x + 1 >= 0',
    'lambda y: -y + 5 >= 0',
    'lambda y: y + 15 >= 0',
    'lambda z: -z + 88 >= 0',
    'lambda z: z + 7 >= 0']
    36


    sage: ieq.subset_siz = 2
    sage: ieq.solve()
    sage: ieq.sols; len(ieq.sols)
    ['lambda x,y: max(x,0) - (y + 10) >= 0',
    'lambda x,y: y + 15 - max(x,0) >= 0',
    'lambda x,y: x - y - 10 >= 0',
    'lambda x,y: -x + y + 14 >= 0',
    'lambda x,y: max(y,0) - (x - 10) >= 0',
    'lambda x,y: x + 1 - max(y,0) >= 0',
    'lambda x: -x + 15 >= 0',
    'lambda x: x + 1 >= 0',
    'lambda y: -y + 5 >= 0',
    'lambda y: y + 15 >= 0',
    'lambda x,z: max(x,0) - (z - 88) >= 0',
    'lambda x,z: z + 15 - max(x,0) >= 0',
    'lambda x,z: x - z + 89 >= 0',
    'lambda x,z: -x + z + 15 >= 0',
    'lambda x,z: max(z,0) - (x - 15) >= 0',
    'lambda x,z: x + 89 - max(z,0) >= 0',
    'lambda z: -z + 88 >= 0',
    'lambda z: z + 7 >= 0',
    'lambda y,z: max(y,0) - (z - 88) >= 0',
    'lambda y,z: z + 7 - max(y,0) >= 0',
    'lambda y,z: y - z + 103 >= 0',
    'lambda y,z: -y + z + 5 >= 0',
    'lambda y,z: max(z,0) - (y - 5) >= 0',
    'lambda y,z: y + 103 - max(z,0) >= 0']
    24
    
    sage: tcs=[{x:8,y:8},{x:0,y:-15},{x:0,y:0},{x:1,y:1}]
    sage: ieq = IeqMPPFixed(terms=[x,y],tcs=tcs,xinfo=None)
    dig:Info:*** IeqMPPFixed ***
    sage: ieq.solve()
    sage: ieq.refine()
    sage: ieq.sols
    ['lambda x,y: x - y >= 0',
    'lambda x,y: -x + y + 15 >= 0',
    'lambda x: -x + 8 >= 0',
    'lambda x: x >= 0',
    'lambda y: -y + 8 >= 0',
    'lambda y: y + 15 >= 0',
    'lambda x,y: max(x,0) - (y) >= 0',
    'lambda x,y: y + 15 - max(x,0) >= 0',
    'lambda x,y: max(y,0) - (x) == 0']

    """
    def __init__(self, terms, tcs, xinfo):
        super(IeqMPPFixed, self).__init__(terms, tcs, xinfo)
        self.mpp_opt = IeqMPP.opt_max_plus #default
        self.subset_siz = None

    def solve(self): #mpp fixed
        ts = [t for t in self.terms if t != 1]

        tcs = Miscs.keys_to_str(self.tcs)

        if self.subset_siz is None:
            subset_siz = len(ts)
        else:
            subset_siz = self.subset_siz

        blacklist = None

        if self.xinfo['Input']:
            blacklist = self.xinfo['Input']

        if (self.xinfo['Output'] and 
            len(self.xinfo['Output']) > len(self.xinfo['Input'])): 
            blacklist = self.xinfo['Output']

        ts_common = gen_terms_fixed_coefs(ts,subset_siz=subset_siz,
                                          blacklist=blacklist,
                                          is_mpp=True)
                                          
        if self.mpp_opt == IeqMPP.opt_max_then_min:
            def worker(Q,is_max_plus):
                Q.put(IeqMPPFixed.build_poly(ts_common,tcs,is_max_plus))
                
            Q = mp.Queue()
            workers = [mp.Process(target=worker,args=(Q,is_max_plus))
                       for is_max_plus in [True,False]]
            for w in workers: w.start()
            rs = []
            for _ in workers:
                rs.extend(Q.get())

        else: 
            is_max_plus = self.mpp_opt == IeqMPP.opt_max_plus
            rs = IeqMPPFixed.build_poly(ts_common, tcs, is_max_plus)

        self.sols = map(InvMPP, rs)
            
    #### Helpers for IeqMPPFixed ####
    @staticmethod
    def build_poly(ts, tcs, is_max_plus):
        mpp_str = 'max-plus' if is_max_plus else 'min-plus'

        logger.debug('Build (fixed {}) poly from {} tcs '
                     '(~ {} facets)'
                     .format(mpp_str,len(tcs),2*len(ts)))

        #Can be done in parallel
        rs = []
        for (lh,rh) in ts:
            #lh - rh
            r_lambda = IeqMPP.gen_lambda_exp(lh,[rh],is_max_plus,
                                             is_formula=False,is_eq=False)
            r_evals = [InvMPP.eval_lambda(r_lambda, tc, is_formula=False) 
                       for tc in tcs]

            #since Z3 doen't like numbers like 7/5 
            to_numeric = lambda c: c.n() if '/' in str(c) else c
            c_min = to_numeric(min(r_evals)) #lh >= rh + c_min
            c_max = to_numeric(max(r_evals)) #rh +c_max >= lh
            
            if c_min == c_max: #lh == rh + cmin
                r_e = IeqMPP.gen_lambda_disj(lh,[rh+c_min],
                                             is_max_plus,
                                             is_eq=True)
                rs.append(r_e)
            else:
                r_u = IeqMPP.gen_lambda_disj(lh,[rh+c_min],
                                             is_max_plus,
                                             is_eq=False)
                r_l = IeqMPP.gen_lambda_disj([rh+c_max],lh,
                                             is_max_plus,
                                             is_eq=False)
                rs.extend([r_u,r_l])

        
        return rs

class IeqMPPGen(IeqMPP):
    """
    Generating Max invariants (e.g.\ Max(x,y) >= z means x >= z or y >= z)
    using Max-Plus polyhedron (MPP)

    sage: ieq = IeqMPPGen(terms=[x,y,z],tcs=[{x:2,y:-8,z:-7},{x:0,y:-15,z:88},{x:15,y:5,z:0}],xinfo=None)
    dig:Info:*** IeqMPPGen ***
    sage: ieq.solve()
    sage: ieq.sols
    ['lambda x,z: x - z + 88 >= 0',
     'lambda x: x >= 0',
     'lambda y,z: y - z + 103 >= 0',
     'lambda y: y + 15 >= 0',
     'lambda x,y: -x + y + 15 >= 0',
     'lambda y,z: max(y,z - 96) - (-8) >= 0',
     'lambda x,z: max(x - 2,z - 88) >= 0',
     'lambda z: -z + 88 >= 0',
     'lambda x,y: max(y,-10) - (x - 10) >= 0',
     'lambda x,y,z: max(y,z - 98) - (x - 10) >= 0',
     'lambda x,y: x - y - 10 >= 0',
     'lambda x,z: -x + z + 15 >= 0',
     'lambda y,z: -y + z + 5 >= 0',
     'lambda x: -x + 15 >= 0',
     'lambda y: -y + 5 >= 0',
     'lambda z: z + 7 >= 0']

    sage: ieq = IeqMPPGen(terms=[x,y],tcs=[{x:0,y:5},{x:1,y:5},{x:2,y:5},{x:3,y:5},{x:4,y:5},{x:5,y:5},{x:6,y:6},{x:7,y:7},{x:8,y:8},{x:9,y:9},{x:10,y:10}],xinfo=None)
    dig:Info:*** IeqMPPGen ***
    sage: ieq.mpp_opt = ieq.opt_max_then_min
    sage: ieq.go()
    dig:Info:Select traces
    dig:Info:Compute invs over 11 tcs
    dig:Info:Refine 13 invs
    dig:Info:Detected 7 invs for IeqMPPGen:
    0: x >= 0, x >= 0
    1: -x + y >= 0, y >= x
    2: y - 5 >= 0, y >= 5
    3: -x + 10 >= 0, 10 >= x
    4: -y + 10 >= 0, 10 >= y
    5: x - y + 5 >= 0, x + 5 >= y
    6: max(x - 5,0) - (y - 5) >= 0, If(x - 5 >= 0,x - 5 >= y - 5,0 >= y - 5)
    
    """

    def __init__(self, terms, tcs, xinfo):
        """
        Example:
        #sage: var('rvu,a,y')
        (rvu, a, y)
        #sage: mpp = IeqMPP(terms=[rvu,a,y],tcs1=ig.tcs,tcs2=[])
        #sage: mpp.solve()
        #sage: mpp.go()


        #sage: dig = DIG('../invgen/Traces/MaxPlus/strncopy.tcs',verbose=1)
        *** DIG ***
        Wed Apr 10 14:35:30 2013
        Sage Version 5.8, Release Date: 2013-03-15
        godel Darwin 12.3.0 x86_64
        *** ReadFile ***
        number of traces (tcs) read: 671
        0. |_tcs|: 671
        1. |_tcs2|: 0
        2. _vs: (nn, s, d)
        3. _xinfo:
         0. All: ['nn', 's', 'd']
         1. Assume: []
         2. Const: []
         3. Expect: []
         4. ExtFun: []
         5. Global: []
         6. Input: []
         7. Output: []


        #sage: rs = dig.getInvs(inv_typ='ieq mpp', deg=1, seed=0,ss=dig.ss, mpp_optn=1)[0]
        seed 0 (test 0.111439 0.514348 0.0446897)
        * gen_terms(deg=1,vs=(nn, s, d))
        Generate 4 terms
        *** IeqMPP ***
        Create vertices from 671 data
        * INEQ: Constructing (MPP) Polyhedra with 671 vertices in 4 dim
        Refine 20 candidate invariants
        * rrank(|ps|=20)
        rrank (before 20, after 20, diff 0)
        * rfilter(|ps|=20,|tcs|=671)
        rfilter (before 20, after 20, diff 0)
        Detected invariants for IeqMPP:
          0: lambda nn,s: -nn >= -s - 20
          1: lambda d,nn: -nn >= -d - 20
          2: lambda d,nn,s: max(-nn - 17,-d) >= -s - 16
          3: lambda d,nn,s: max(-s,-d - 3) >= -nn - 19
          4: lambda d,nn,s: max(-s,-d - 1,-18) >= -nn - 17
          5: lambda d,nn: -d >= -nn - 20
          6: lambda nn: 0 >= -nn
          7: lambda d: -d >= -20
          8: lambda d,nn,s: max(-nn,-s) >= -d
          9: lambda nn: -nn >= -20
         10: lambda d,nn,s: max(-nn,-d) >= -s
         11: lambda d: 0 >= -d
         12: lambda s: 0 >= -s
         13: lambda s: -s >= -20
         14: lambda d,s: -s >= -d - 17
         15: lambda nn,s: -s >= -nn - 20
         16: lambda d,nn,s: max(-s - 1,-d) >= -nn - 18
         17: lambda d,nn,s: max(-s - 4,-d) >= -nn - 19
         18: lambda d,s: -d >= -s - 17
         19: lambda d,s: max(-d,-17) >= -s - 16
        """

        super(IeqMPPGen, self).__init__(terms, tcs, xinfo)
        self.mpp_opt = IeqMPP.opt_max_plus #default
        self.subset_siz = None

    def solve(self): #mpp gen

        ts = [t for t in self.terms if t != 1]        

        if self.subset_siz is None:
            subset_siz = len(ts)
        else:
            subset_siz = self.subset_siz
            
        def wprocess(tasks,Q):
            rs = []
            for ts_subset in tasks:
                rs.extend(IeqMPPGen.build_vts_poly(list(ts_subset),self.tcs,self.mpp_opt))

            if Q is None: #no multiprocessing
                return rs
            else:
                Q.put(rs)            

        from vu_common import get_workloads
        tasks = list(itertools.combinations(ts,subset_siz))
        Q = mp.Queue()
        workloads = get_workloads(tasks,max_nprocesses=mp.cpu_count(),
                                  chunksiz=2)

        logger.debug("workloads 'build_vts_poly' {}: {}"
                     .format(len(workloads),map(len,workloads)))
        workers = [mp.Process(target=wprocess,args=(wl,Q))
                   for wl in workloads]

        for w in workers: w.start()
        wrs = []
        for _ in workers: wrs.extend(Q.get())
            
        self.sols = map(InvMPP, wrs)


    ##### Helpers for IeqMPPGen #####
    @staticmethod
    def build_vts_poly(ts,tcs,mpp_opt):
        vts = [[t.subs(tc) for t in ts] for tc in tcs]
        vts = vset(vts,idfun=repr)

        #add 0 to the end of each vertex and identity elem to terms
        vts = [vt + [SR(0)] for vt in vts]
        ts = ts + [SR(0)]  #the identity element is 0 in MPP

        if mpp_opt == IeqMPP.opt_max_then_min:
            def worker_(Q,ts,is_max_plus):
                Q.put(IeqMPPGen.build_poly(vts,ts,is_max_plus))

            Q = mp.Queue()
            workers = [mp.Process(target=worker_,args=(Q,ts,is_max_plus))
                       for is_max_plus in [True,False]]
            for w in workers: w.start()
            rs = []
            for _ in workers: rs.extend(Q.get())
                

        else:
            is_max_plus = mpp_opt == IeqMPP.opt_max_plus
            rs = IeqMPPGen.build_poly(vts,ts,is_max_plus=is_max_plus)

        return rs


    @staticmethod
    def build_poly(vts, ts, is_max_plus):
        """
        Build a MPP convex polyhedron over vts and
        return a set of constraints

        Examples:

        sage: logger.set_level(VLog.DEBUG)
        sage: IeqMPP.build_poly([[0,0,0],[3,3,0]], is_max_plus=True)
        dig_polynomials:Debug:Ieq: Build (MPP max-plus) polyhedra from  2 vertices in 3 dim
        ['[-oo,0,-oo,-oo,-oo,0]', '[0,-oo,-oo,-oo,-oo,0]', '[0,-oo,-oo,-oo,-oo,-oo]',
        '[-oo,0,-oo,-oo,-oo,-oo]', '[-oo,-oo,0,-oo,-oo,-oo]', '[-oo,-oo,0,-oo,-oo,0]',
        '[-oo,-oo,0,-oo,-3,-oo]', '[-oo,-oo,0,-3,-oo,-oo]', '[-oo,0,-oo,-oo,0,-oo]',
        '[-oo,0,-oo,0,-oo,-oo]', '[0,-oo,-oo,-oo,0,-oo]', '[0,-oo,-oo,0,-oo,-oo]']

        """
        opt_arg = ''
        
        if is_max_plus:
            mpp_str = 'max-plus'
        else:
            mpp_str = 'min-plus'
            opt_arg = "{} {}".format(opt_arg, '-{}'.format(mpp_str))

        #if any vertex is float
        if any(any(not SR(v).is_integer() for v in vt) for vt in vts):
            vts = [[RR(v).n() for v in vt] for vt in vts]
            opt_arg = "{} -numerical-data ocaml_float".format(opt_arg) 

        #exec external program
        #important, has to end with newline \n !!!
        vts_s = '\n'.join(str(vt).replace(' ','') for vt in vts) + '\n'
        logger.debug('Build (gen {}) poly from {} vts in {} dims: {}'
                     .format(mpp_str,len(vts),len(vts[0]),ts))

        cmd = 'compute_ext_rays_polar {} {}'.format(opt_arg, len(vts[0]))
        rs,_ = vcmd(cmd, vts_s)
        rs = [sage_eval(s.replace('oo','Infinity')) for s in rs.split()]

        rs = IeqMPPGen.group_rs(rs)

        rs = map(lambda ls:[x+y for x,y in zip(ls,ts+ts)], rs)
        rs = map(lambda ls: IeqMPP.sparse(ls,is_max_plus), rs)
        rs = filter(None, rs)        
        return rs


    @staticmethod
    def group_rs(rs, max_group_siz=10):
        """
        Heuristic method to remove mpp invs having similar format, e.g.,
        2: ('lambda n,x: max(x - 46655,0) >= n - 35', 'If(x - 46655 >= 0, x - 46655 >= n - 35, 0 >= n - 35)')
        3: ('lambda n,x: max(x - 205378,0) >= n - 58', 'If(x - 205378 >= 0, x - 205378 >= n - 58, 0 >= n - 58)')
        4: ('lambda n,x: max(x - 405223,0) >= n - 73', 'If(x - 405223 >= 0, x - 405223 >= n - 73, 0 >= n - 73)')
        5: ('lambda n,x: max(x - 328508,0) >= n - 68', 'If(x - 328508 >= 0, x - 328508 >= n - 68, 0 >= n - 68)')
        6: ('lambda n,x: max(x - 342999,0) >= n - 69', 'If(x - 342999 >= 0, x - 342999 >= n - 69, 0 >= n - 69)')
        7: ('lambda n,x: max(x - 830583,0) >= n - 93', 'If(x - 830583 >= 0, x - 830583 >= n - 93, 0 >= n - 93)')
        8: ('lambda n,x: max(x - 511999,0) >= n - 79', 'If(x - 511999 >= 0, x - 511999 >= n - 79, 0 >= n - 79)')
        9: ('lambda n,x: max(x - 287495,0) >= n - 65', 'If(x - 287495 >= 0, x - 287495 >= n - 65, 0 >= n - 65)')
        10: ('lambda n,x: max(x - 5831999,0) >= n - 179', 'If(x - 5831999 >= 0, x - 5831999 >= n - 179, 0 >= n - 179)')
        11: ('lambda n,x: max(x - 7077887,0) >= n - 191', 'If(x - 7077887 >= 0, x - 7077887 >= n - 191, 0 >= n - 191)')
        12: ('lambda n,x: max(x - 5735338,0) >= n - 178', 'If(x - 5735338 >= 0, x - 5735338 >= n - 178, 0 >= n - 178)')
        """
        if __debug__:
            assert is_list(rs) and all(is_list(ls) for ls in rs), rs
        
        def get_gid(ls):
            k = [i for i,l in enumerate(ls) if not SR(l).is_infinity() and l != 0]
            return None if is_empty(k) else tuple(k)
                
        d = {}
        for ls in rs:
            k = get_gid(ls)
            if k not in d:
                d[k] = []
            d[k].append(ls)
        
        # db_msg = ['|gid {}|: {}'
        #           .format(k,len(vs)) for k,vs in d.iteritems()]
        # logger.debug(', '.join(db_msg))

        rs = []
        for k,vs in d.iteritems():
            #Don't remove group None, aka 'nice group'
            if k is None or len(vs) <= max_group_siz:
                rs.extend(vs)
            else:
                logger.warn('rm MPP group id {} (siz: {})'
                            .format(k, len(vs)))
        return rs    

 
#tcs = [{x:0,y:5},{x:1,y:5},{x:2,y:5},{x:3,y:5},{x:4,y:5},{x:5,y:5},{x:6,y:6},{x:7,y:7},{x:8,y:8},{x:9,y:9},{x:10,y:10}]
