from collections import OrderedDict
from pprint import pprint

from sage.all import (SR, srange, var, flatten)
from sageutil import (get_vars, get_coefs_terms, is_sage_eq)

from vu_common import (VLog, vall_uniq, is_empty, is_list, is_dict,
                       merge_dict, vpartition, list_str)
from dig_miscs import (Miscs, get_sample, Tree, AEXP, ExtFun, 
                        adjust_arr_sizs)        

from dig import Solver
from dig_inv import InvFlatArray, InvNestedArray

logger = VLog('dig_arrays')
logger.level = VLog.DEBUG



class FlatArray(Solver):
    """
    Find Flat Array Invariants of the form
    c1A[i][j].. + c2B[i1'][i2'].. = 0
    using standard equation solving

    Examples:
    ig = InvGen("Traces/AES/Flat/paper_multidim.tc",verbose=1)
    _ =  ig.getInvs(inv_typ='flat',seed=1)
    *** InvGen ***
    Sun Jun  3 21:44:39 2012
    Sage Version 5.0, Release Date: 2012-05-14
    Godel.local Darwin 10.8.0 x86_64
    *** ReadFile ***
    read 'Traces_ICSE2012/AES/Flat/paper_multidim.tc'
    number of traces (tcs) read: 9
    read 'Traces_ICSE2012/AES/Flat/paper_multidim.ext'
    0. |_tcs|: 9
    1. |_tcs2|: 0
    2. _vs: [A, B]
    3. _xinfo:
    0. All: ['A', 'B']
    1. Assume: []
    2. Const: []
    3. Expect: ['A[i] - 7B[2i] - 3i == 0']
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    Time elapsed: 0.0408 s (ReadFile)
    seed 1 (test 0.829402 0.595912 0.429361)
    *** FlatArray ***
    Create new trace format (treating array elems as seperate vars)
    Find linear equalities over 8 array elements
    sample_traces: chose |tcs1|=9, |tcs2|=0 (attempted 14/9 tcs)
    Time elapsed: 0.0000 s (function sample_traces)
    *** Eqt ***
    Create equations from 9 data
    * EQ: Solve 9 (uniq) eqts for 9 unknowns coeffs
    Time elapsed: 0.0287 s (solve)
    Refine 3 candidate invariants
    * rfilter skips
    * rinfer(|ps|=3)
    rinfer (before 3, after 3, diff 0)
    Time elapsed: 0.0492 s (refine)
    Detected Invariants for Eqt:
    0: A_0 - 7*B_0 == 0
    1: A_2 - 7*B_4 - 6 == 0
    2: -1/7*A_1 + B_2 + 3/7 == 0
    Some rels were modifed
    A_2 - 7*B_4 - 6 == 0
    A_0 - 7*B_0 == 0
    A_1 - 7*B_2 - 3 == 0
    Find rels over indices
    a_solve: Assume 'A' is pivot
    solve 'B' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    a_solve: Assume 'A' is pivot
    solve 'coef' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Result (pivot A): lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0
    a_solve: Assume 'B' is pivot
    solve 'A' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    a_solve: Assume 'B' is pivot
    solve 'coef' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Result (pivot B): lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0
    Detected Invariants for FlatArray:
    0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
    1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])
    Time elapsed: 0.1462 s (solve)
    Refine 2 candidate invariants
    * rfilter(|ps|=2,|tcs|=9)
    rfilter (before 2, after 2, diff 0)
    Time elapsed: 0.0051 s (refine)
    Detected Invariants for FlatArray:
    0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
    1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])

    """

    def __init__(self, terms, tcs, xinfo):
        """
        TODO: pass in terms , so that terms = terms
        set aeterms = self.terms instead of ainfo.keys()
        
        """
        super(FlatArray,self).__init__(terms  = [],  #not important
                                       tcs    = tcs,
                                       xinfo  = xinfo)

    def mk_traces(self):
        """
        Use all traces for inv generations
        and for refinement (filtering)
        """
        #VU: default is 200
        tcs = [adjust_arr_sizs(tc, 50) for tc in self.tcs]
        tcs_extra = self.tcs
        #tcs_extra = Miscs.keys_to_str(self.tcs)
        
        return tcs, tcs_extra
    
    def get_rels_elems1(self, tcs):
        if __debug__:
            assert len(tcs) >= 1, tcs

        aeterms = tcs[0].keys()

        #Find rels among array elements
        logger.debug('Find linear eqts over {} array elems'
                     .format(len(aeterms)))
        aeterms = [SR(1)] + aeterms

        from dig_polynomials import Eqt
        solverE = Eqt(aeterms, tcs, self.xinfo)
        
        logger.info('Select traces (note: |tcs|=|terms|={})'.format(len(aeterms)))
        solverE.tcs, solverE.tcs_extra = get_sample(tcs, len(aeterms),
                                                    sampleP=100, min_=None)
        solverE.do_refine=False
        solverE._go()
        
        from refine import Refine
        rf = Refine(solverE.sols)
        rf.rfilter(tcs=solverE.tcs_extra)
        ps = [p.p for p in rf.ps]
        
        return ps

    def get_rels_elems2(self, tcs, tsinfo):
        """
        Instead of solving a large N+M eqts once, we can solve 
        just a tuple of size N (N is the number of arrays) N*M times.
        This has a O(N^M) complexity, which is lower than solving N+M
        equations when M = 2.  


        Doesn't work really well in practice (even when M=2) because 
        the large number of invocations to the equation solver.
        """
        
        from dig_polynomials import Eqt
        from itertools import product

        ps = []
        for i,aeterms in enumerate(product(*tsinfo.values())):
            #Find rels among array elements
            logger.debug('{}. Find linear eqts over {} array elems {}'
                         .format(i, len(aeterms), aeterms))
            aeterms = [SR(1)] + list(aeterms)
            solverE = Eqt(aeterms, tcs, self.xinfo)
        
            logger.info('Select traces (note: |tcs|=|terms|={})'
                        .format(len(aeterms)))
            solverE.tcs, solverE.tcs_extra = get_sample(tcs, len(aeterms),
                                                        sampleP=100, min_=None)
            solverE.do_refine = False
            solverE._go()
            ps.extend(solverE.sols)
        
        from refine import Refine
        rf = Refine(ps)
        rf.rfilter(tcs=tcs)
        ps = rf.ps
        ps = [p.p for p in ps]
        return ps            

    def solve(self): #FlatArray
        
        #Create new variables and traces
        logger.info('Compute new traces (treating array elems as new vars)')
        ainfo  = {}  #{A_0_0=[0,0],B_1_2_3=[1,2,3]}
        tsinfo = {} #{A: [A_0,A_1, ..], B:[B_0_0,B_0_1,..]}
        
        tcs = [FlatArray.compute_new_trace(tc, ainfo, tsinfo) for tc in self.tcs]

        ps = self.get_rels_elems1(tcs)
        #ps = self.get_rels_elems2(tcs,tsinfo)
        
        #Group arrays and in each group, find rels among array idxs 
        gs = FlatArray.group_arr_eqts(ps, ainfo)
        logger.info('Partition {} eqts into {} groups'
                    .format(len(ps), len(gs)))
        
        sols = []
        for i,(gns,gps) in enumerate(gs.iteritems()):
            if __debug__:
                assert not is_empty(gps)
                
            # Modify/reformat if necessary        
            gps = FlatArray.modify_arr_eqts(gps, ainfo)
           
            #Find rels over array indices
            logger.debug("{}. Find rels over idx from {} eqts (group {})"
                         .format(i,len(gps),gns))
            gps = [FlatArray.parse_arr_eqt(p,ainfo) for p in gps]
            gsols = FlatArray.find_rels(gps)
            
            sols.extend(gsols)

        
        if is_empty(sols):
            logger.warn('No rels found over arr idxs, use orig results')
            sols = flatten(ps)
            self.do_refine = False

        self.sols = map(InvFlatArray, sols)
        self.print_sols()


    def refine(self):
        #No inferrence for array invs
        #Don't do ranking either since array equations is very long 
        from refine import Refine
        rf = Refine(ps=self.sols)
        rf.rfilter(tcs=self.tcs_extra)
        self.sols = rf.ps


    @staticmethod
    def compute_new_trace(d, ainfo, tsinfo):
        """
        Convert array elements into new variables and generate traces from these.

        Examples:
        sage: var('A B')
        (A, B)
        sage: ainfo = {}
        sage: tc = FlatArray.compute_new_trace({A: [0,1,2], B: [[0, 1], [2, 3]]}, ainfo, {})
        sage: sorted(tc.items(),key= lambda (x,_) : str(x))
        [(A_0, 0), (A_1, 1), (A_2, 2), (B_0_0, 0), (B_0_1, 1), (B_1_0, 2), (B_1_1, 3)]
        sage: sorted(ainfo.items(), key=lambda (x,_): str(x))
        [(A_0, {'idx_': [(A0, 0)], 'name': 'A'}),
         (A_1, {'idx_': [(A0, 1)], 'name': 'A'}),
         (A_2, {'idx_': [(A0, 2)], 'name': 'A'}),
         (B_0_0, {'idx_': [(B0, 0), (B1, 0)], 'name': 'B'}),
         (B_0_1, {'idx_': [(B0, 0), (B1, 1)], 'name': 'B'}),
         (B_1_0, {'idx_': [(B0, 1), (B1, 0)], 'name': 'B'}),
         (B_1_1, {'idx_': [(B0, 1), (B1, 1)], 'name': 'B'})]

        
        sage: ainfo = {}
        sage: tc = FlatArray.compute_new_trace({'A':[['a','b'],['c','d'],['e','f',['z','w']]], \
        'B':[1,2,[7,8]],'C':[100]}, ainfo, {})
        sage: sorted(tc.items(),key= lambda (x,_) : str(x))
        [(A_0_0, 'a'), (A_0_1, 'b'), (A_1_0, 'c'), (A_1_1, 'd'), 
        (A_2_0, 'e'), (A_2_1, 'f'), (A_2_2_0, 'z'), (A_2_2_1, 'w'), 
        (B_0, 1), (B_1, 2), (B_2_0, 7), (B_2_1, 8), (C_0, 100)]

        sage: sorted(ainfo.items(), key=lambda (x,_): str(x))
        [(A_0_0, {'idx_': [(A0, 0), (A1, 0)], 'name': 'A'}),
         (A_0_1, {'idx_': [(A0, 0), (A1, 1)], 'name': 'A'}),
         (A_1_0, {'idx_': [(A0, 1), (A1, 0)], 'name': 'A'}),
         (A_1_1, {'idx_': [(A0, 1), (A1, 1)], 'name': 'A'}),
         (A_2_0, {'idx_': [(A0, 2), (A1, 0)], 'name': 'A'}),
         (A_2_1, {'idx_': [(A0, 2), (A1, 1)], 'name': 'A'}),
         (A_2_2_0, {'idx_': [(A0, 2), (A1, 2), (A2, 0)], 'name': 'A'}),
         (A_2_2_1, {'idx_': [(A0, 2), (A1, 2), (A2, 1)], 'name': 'A'}),
         (B_0, {'idx_': [(B0, 0)], 'name': 'B'}),
         (B_1, {'idx_': [(B0, 1)], 'name': 'B'}),
         (B_2_0, {'idx_': [(B0, 2), (B1, 0)], 'name': 'B'}),
         (B_2_1, {'idx_': [(B0, 2), (B1, 1)], 'name': 'B'}),
         (C_0, {'idx_': [(C0, 0)], 'name': 'C'})]
 
        """
        def compute_traces(aname, acontents, ainfo, tsinfo):
            vi = Miscs.travel(acontents)
            vals = Miscs.getVals(vi)
            idxs = Miscs.getIdxs(vi)
            aname = str(aname)
            newvars = [var(aname + '_' + list_str(idx, '_')) for idx in idxs]

            if aname not in tsinfo:
                tsinfo[aname] = newvars
            else:
                assert tsinfo[aname] == newvars
            
            dVals = dict(zip(newvars,vals)) #{A_0_0_1:'w'}
            for nv,idx in zip(newvars,idxs):
                if nv not in ainfo:
                    idx_ = zip([var('{}{}'.format(aname,li))
                                 for li in srange(len(idx))],idx)
                    ainfo[nv]={'name':aname, 'idx_':idx_}

            return dVals

        if __debug__:
            assert is_dict(d), d 
            assert is_dict(ainfo), d

        tcs = [compute_traces(k,v,ainfo,tsinfo) for k,v in d.iteritems()]
        tcs = merge_dict(tcs)
        return tcs
    
    
    @staticmethod
    def group_arr_eqts(ps, ainfo):
        """
        Group the resulting list of eqts among array elements.
        Also remove eqts that involve elements from same arrays


        sage: var('x_0 x_1 y_0 y_1')
        (x_0, x_1, y_0, y_1)
        sage: ainfo = {x_0:{'name':'x','idxs':[0]}, x_1:{'name':'x','idxs':[1]}, \
                       y_0:{'name':'y','idxs':[0]},y_1:{'name':'y','idxs':[1]}}
        sage: FlatArray.group_arr_eqts([x_0 + x_1 == 0, x_1 + y_1 == 0, \
                                          x_0 + y_1 + y_0==0, x_0 + x_1-2==0 , \
                                          y_0 == 1, x_1 == 2, x_0 == 3], ainfo)
        dig_arrays:Warn:Removed arr eqt: x_0 + x_1 == 0
        dig_arrays:Warn:Removed arr eqt: x_0 + y_0 + y_1 == 0
        dig_arrays:Warn:Removed arr eqt: x_0 + x_1 - 2 == 0
        OrderedDict([(('x', 'y'), [x_1 + y_1 == 0]), 
        (('y',), [y_0 == 1]), 
        (('x',), [x_1 == 2, x_0 == 3])])

        sage: FlatArray.group_arr_eqts([x_0 == 0, x_1==1], ainfo)
        OrderedDict([(('x',), [x_0 == 0, x_1 == 1])])
        sage: FlatArray.group_arr_eqts([x_0 + x_1 == 0, x_0 + x_1-2==0], ainfo)
        dig_arrays:Warn:Removed arr eqt: x_0 + x_1 == 0
        dig_arrays:Warn:Removed arr eqt: x_0 + x_1 - 2 == 0
        OrderedDict()

        """
       
        gs = OrderedDict()
        
        get_anames = lambda p: tuple([ainfo[v]['name'] for v in get_vars(p)])
        
        for p in ps:
            anames = get_anames(p)
            
            if not vall_uniq(anames): #e.g. A_1 + A_2 = 0
                logger.warn('Removed arr eqt: {}'.format(p))
                continue
            
            anames
            if anames in gs:
                gs[anames].append(p)
            else:
                gs[anames]=[p]
        
        return gs
            
    
    @staticmethod
    def modify_arr_eqts(ps, ainfo):
        """
        Shortcut to modify/format eqts
        """
        ps_old = set(map(str,ps))
        ps = [Miscs.elim_denom(p) for p in ps] #Eliminating denominators if exist
        ps = FlatArray.modify_signs(ps)
                
        if set(map(str,ps)) != ps_old:
            logger.warn('Some rels were modifed\n{}'.format(list_str(ps,'\n')))

        
        return ps

    @staticmethod
    def rem_dup_arrs(ps, ainfo):
        """
        Remove relations that involve elements from same arrays

        Examples:

        sage: var('x_0 x_1 y_0 y_1')
        (x_0, x_1, y_0, y_1)
        sage: ainfo = {x_0:{'name':'x','idxs':[0]},x_1:{'name':'x','idxs':[1]}, y_0:{'name':'y','idxs':[0]},y_1:{'name':'y','idxs':[1]}}
        sage: FlatArray.rem_dup_arrs([x_0 + x_1 == 0, x_1 + y_1 == 0, x_0 + y_1 + y_0==0, x_0 + x_1-2==0], ainfo)
        dig_arrays:Warn:Removed 3 array eqts
        x_0 + x_1 == 0
        x_0 + y_0 + y_1 == 0
        x_0 + x_1 - 2 == 0
        [x_1 + y_1 == 0]

        
        """
        get_anames = lambda p: [ainfo[v]['name'] for v in get_vars(p)]
        ps_rem, ps = vpartition(ps, lambda p: vall_uniq(get_anames(p)))
        
        if not is_empty(ps_rem):
            logger.warn('Removed {} array eqts\n{}'
                        .format(len(ps_rem), list_str(ps_rem,'\n')))

            
        return ps

    @staticmethod
    def modify_signs(ps):
        """
        Modify equations so that they have same sign

        Examples:

        sage: var('y')
        y
        sage: FlatArray.modify_signs([x-y==0,-2*x + 2*y ==0])
        [x - y == 0, 2*x - 2*y == 0]

        sage: FlatArray.modify_signs([-x-y==0,2*x+2*y==0])
        [-x - y == 0, -2*x - 2*y == 0]

        sage: FlatArray.modify_signs([-x-y==0,2*x-2*y==0])
        [-x - y == 0, -2*x + 2*y == 0]
        """

        if len(ps) <= 1:
            return ps

        #sign of the coef of the 1st term in p
        _get_sign = lambda p: get_coefs_terms(p)[0][0] 

        p0_sign = _get_sign(ps[0]) #of the p
        ps_ = [p if _get_sign(p) == p0_sign else -1*p for p in ps[1:]]

        return [ps[0]] + ps_


    @staticmethod
    def parse_arr_eqt(p, ainfo):
        """
        
        sage: var('A B A_0 A_1 B_1_0 B_1_1')
        (A, B, A_0, A_1, B_1_0, B_1_1)
        sage: ainfo = {}
        sage: tcs = FlatArray.compute_new_trace({A: [0,1,2], B: [[0, 1], [2, 3]]}, ainfo, {})
        sage: sorted(tcs.items(),key= lambda (x,_) : str(x))
        [(A_0, 0), (A_1, 1), (A_2, 2), (B_0_0, 0), (B_0_1, 1), (B_1_0, 2), (B_1_1, 3)]
        sage: sorted(ainfo.items(), key=lambda (x,_): str(x))
        [(A_0, {'idx_': [(A0, 0)], 'name': 'A'}),
         (A_1, {'idx_': [(A0, 1)], 'name': 'A'}),
         (A_2, {'idx_': [(A0, 2)], 'name': 'A'}),
         (B_0_0, {'idx_': [(B0, 0), (B1, 0)], 'name': 'B'}),
         (B_0_1, {'idx_': [(B0, 0), (B1, 1)], 'name': 'B'}),
         (B_1_0, {'idx_': [(B0, 1), (B1, 0)], 'name': 'B'}),
         (B_1_1, {'idx_': [(B0, 1), (B1, 1)], 'name': 'B'})]

        sage: d = FlatArray.parse_arr_eqt(-A_0 + 7/2*B_1_0 - 100 == 0, ainfo)
        sage: pprint(d)
        {'A': {A0: 0, coef: -1}, 'B': {B0: 1, B1: 0, coef: 7/2}, 'coef': {coef: -100}}
        

        sage: d = FlatArray.parse_arr_eqt(-5*A_1 + 3*B_1_1 == 0, ainfo)
        sage: d
        {'A': {A0: 1, coef: -5}, 'B': {B0: 1, B1: 1, coef: 3}, 'coef': {coef: 0}}

        """
        if __debug__:
            assert is_sage_eq(p), p

        cs, ts = get_coefs_terms(p)

        if 1 not in ts: #e.g., A_1 + B_2 == 0
            ts = ts + [1]
            cs = cs + [0]

        d = {}
        for c,t in zip(cs,ts):
            contents=[(var('coef'),c)]
            if t == 1:
                name='coef'
            else:
                t=var(t)
                name = ainfo[t]['name']
                idx_ = ainfo[t]['idx_']
                contents = contents + idx_

            d[name] = dict(contents)

        return d


    @staticmethod
    def find_rels(ps):
        """
        Find relations among array indices
        
        #sage: var('rvu_2_1 t_9 rvu_2_3 t_11 rvu_2_0 t_8 rvu_3_2 t_14 rvu_0_0 t_0 rvu_0_2 t_2 rvu_3_1 t_13 rvu_3_3 t_15 rvu_0_1 t_1 rvu_0_3 t_3 rvu_1_3 t_7 rvu_1_0 t_4 rvu_1_2 t_6 rvu_3_0 t_12 rvu_1_1 t_5 rvu_2_2 t_10')
        (rvu_2_1, t_9, rvu_2_3, t_11, rvu_2_0, t_8, rvu_3_2, t_14, rvu_0_0, t_0, rvu_0_2, t_2, rvu_3_1, t_13, rvu_3_3, t_15, rvu_0_1, t_1, rvu_0_3, t_3, rvu_1_3, t_7, rvu_1_0, t_4, rvu_1_2, t_6, rvu_3_0, t_12, rvu_1_1, t_5, rvu_2_2, t_10)

        #sage: FlatArray.find_rels(ps=[-rvu_2_1 + t_9 == 0, rvu_2_3 - t_11 == 0, rvu_2_0 - t_8 == 0, -rvu_3_2 + t_14 == 0, -rvu_0_0 + t_0 == 0, rvu_0_2 - t_2 == 0, -rvu_3_1 + t_13 == 0, rvu_3_3 - t_15 == 0, rvu_0_1 - t_1 == 0, -rvu_0_3 + t_3 == 0, -rvu_1_3 + t_7 == 0, -rvu_1_0 + t_4 == 0, rvu_1_2 - t_6 == 0, -rvu_3_0 + t_12 == 0, rvu_1_1 - t_5 == 0, rvu_2_2 - t_10 == 0],verbose=0)
        """

        ks = ps[0]
        pivots = [k for k in ks if k != 'coef']

        rs = [FlatArray.find_relsPivot(pivot, ps) for pivot in pivots]
        rs = [rs_ for rs_ in rs if rs_ is not None]

        return rs


    @staticmethod
    def find_relsPivot(pivot, psInfo):
        """
        Note: we want to choose an array A as pivot only when all elements of A has relations to elements in other arrays,
        e.g.,
        assume A has 4 elements, then we only choose A as pivot if it has the below relations

        A[0] = B[0]
        A[1] = B[10]
        A[2] = B[20]
        A[3] = B[30]

        A[4] = B[11]
        B[11] = B[40]

        """
        ks = psInfo[0]

        rs = [FlatArray.a_solve(pivot,k,psInfo)
              for k in ks if k != pivot]
        if None in rs:
            return None

        #create template, e.g. lambda p,a,b,p1,p2 = p[p1][p2] - 7a[2p1] + 8p3
        arrs = [k for k in ks if k != 'coef' and k != pivot]
        arrs = [pivot] + arrs  #pivot array is the first one
        pivotIdxs = [str(k) for k in ks[pivot] if str(k) != 'coef']

        #e.g. pivotD = {'A0':A0, 'coef': 1}
        pivotD = dict([(str(k),(c if str(k) == 'coef' else k))
                        for k,c in ks[pivot].iteritems()])

        rs = [(pivot,pivotD)] + rs
        terms = [FlatArray.genTemplate(name,d) for name,d in rs]

        rel = ' + '.join([t for t in terms if t is not None])
        idxStr = ', '.join(arrs + pivotIdxs)

        rs = 'lambda %s: %s == 0'%(idxStr,rel)

        #extract the index info since this result only works for these indices
        idx_info = FlatArray.extractIdxInfo(pivot,psInfo)


        logger.debug('Result (pivot %s): %s'%(pivot,rs))

        return rs,idx_info

    @staticmethod
    def extractIdxInfo(pivot,psInfo):
        ps = [p[pivot] for p in psInfo]
        ps = Miscs.keys_to_str([p for p in ps])
        ps = [dict([(k,c) for k,c in p.iteritems() if k != 'coef'])
              for p in ps]
        return ps


    @staticmethod
    def a_solve(pivot, solve_for, tcs):
        """
        pivot = 'A'
        solve_for_arr = 'B'


        0: A_0 - 7*B_0 == 0
        1: A_1 - 7*B_2 - 3 == 0
        2: A_2 - 7*B_4 - 6 == 0

        Hypothesizes
        B_coef = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)

        B_i0 = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)

        B_i1 = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)
        """


        logger.debug("a_solve: Assume '%s' is pivot"%pivot)
        logger.debug("solve '%s' with respect to pivot with |tcs|=%d"%(solve_for,len(tcs)))


        _getIdxs = lambda a,d: [k for k in d[a] if not 'coef' in str(k)]
        mytcs = [dict(tc[pivot].items() + tc[solve_for].items()) for tc in tcs]
                 
        idxs_ = _getIdxs(pivot,tcs[0])
        pivot_idxs_n_const = [SR(1)] + idxs_
        solve_for_keys= tcs[0][solve_for].keys()

        rs = [Miscs.solve_eqts_(ts=pivot_idxs_n_const,rv=k,ds=mytcs)
              for k in solve_for_keys]

        rs = Miscs.keys_to_str(rs)  #so that the keys are string

        try:
            sol = merge_dict(rs)
            sol = (solve_for, sol)
            return sol
        except Exception:
            return None


    @staticmethod
    def genTemplate(name,d):
        if name == 'coef':
            assert(len(d.values())==1)
            coefVal = d.values()[0]
            template = None if coefVal == 0 else '(%s)'%str(coefVal)
        else:
            idxVals= ['[%s]'%d[name+str(idx)] for idx in srange(len(d)-1)]
            if d['coef'] == -1:
                coefStr = '-'
            elif d['coef'] == 1:
                coefStr = ''
            else:
                coefStr = "({}) *".format(d['coef'])

            template = '(%s%s%s)'%(coefStr,name,list_str(idxVals,''))

        return template


class NestedArray(Solver):
    """
    Find NestedArray Invariant of the form  A[i] = B[e] where e = e1 | C[e]

    Examples:

    sage: logger.set_level(VLog.DEBUG)
    sage: from dig import DIG

    # sage: ig = DIG("Traces/AES/Nested/paper_nested.tc",verbose=1)
    # *** InvGen ***
    # ...
    # *** ReadFile ***
    # read 'Traces/AES/Nested/paper_nested.tc'
    # number of traces (tcs) read: 1
    # 0. |_tcs|: 1
    # 1. |_tcs2|: 0
    # 2. _vs: [A, B, C]
    # 3. _xinfo:
    # 0. All: ['A', 'B', 'C']
    # ...

    # sage: ig.verbose = 2
    # sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
    # seed 1 (test 0.829402 0.595912 0.429361)
    # sample_traces: chose |tcs1|=1, |tcs2|=0 (attempted 1/1 tcs)
    # ...
    # *** NestedArray ***
    # 0. All: ['A', 'B', 'C']
    # 1. Assume: []
    # 2. Const: []
    # 3. Expect: []
    # 4. ExtFun: []
    # 5. Global: []
    # 6. Input: []
    # 7. Output: []
    # 8. ZDims:
    # 0. A: 1
    # 1. B: 1
    # 2. C: 1
    # Generate Nestings
    # * gen_aexps [A,C,B]: 2 expressions generated
    # * Find valid nestings using reachability analysis
    # 0. A[i1] == B[C[(i1)_]] has 1 relation(s)
    # lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]
    # 1. A[i1] == B[(i1)_] has 1 relation(s)
    # lambda A,B,i1: A[i1] == B[-2*i1 + 5]
    # * Relations: 2
    # ...
    # Refine 2 candidate invariants
    # * rfilter(|ps|=2,|tcs|=1)
    # rfilter (before 2, after 2, diff 0)
    # ...
    # Detected Invariants for NestedArray:
    # 0: lambda A,B,i1: A[i1] == B[-2*i1 + 5]
    # 1: lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]


    # sage: ig = InvGen("Traces/AES/Nested/aes_addroundkey_vn.tc",verbose=1)
    # *** InvGen ***
    # ...
    # *** ReadFile ***
    # read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.tc'
    # number of traces (tcs) read: 100
    # read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.ext'
    # 0. |_tcs|: 100
    # 1. |_tcs2|: 0
    # 2. _vs: [r_, rk, st]
    # 3. _xinfo:
    # 0. All: ['r_', 'rk', 'st']
    # 1. Assume: []
    # 2. Const: []
    # 3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
    # 4. ExtFun: ['xor']
    # 5. Global: []
    # 6. Input: ['st', 'rk']
    # 7. Output: ['r_']
    # ...

    # sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
    # seed 1 (test 0.829402 0.595912 0.429361)
    # sample_traces: chose |tcs1|=1, |tcs2|=99 (attempted 1/100 tcs)
    # ...
    # *** NestedArray ***
    # * gen_extfuns: ext funs ['xor']
    # * getExtFunReps(['xor'],|avals|=32,doCartesianProd=False)
    # * fun: xor, fvals 152, idxs 224
    # 0. All: ['r_', 'rk', 'st']
    # 1. Assume: []
    # 2. Const: []
    # 3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
    # 4. ExtFun: ['xor']
    # 5. Global: []
    # 6. Input: ['st', 'rk']
    # 7. Output: ['r_']
    # 8. ZDims:
    # 0. r_: 2
    # 1. rk: 2
    # 2. st: 2
    # 3. xor: 2
    # Generate array expressions (nestings)
    # * gen_aexps [r_,xor,st,rk]: 1 expressions generated
    # * Find valid nestings using reachability analysis
    # 0. r_[i1][i2] == xor(st[(i1,i2)_][(i1,i2)_],rk[(i1,i2)_][(i1,i2)_]) has 1 relation(s)
    # lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])
    # * Relations: 1
    # ...
    # Refine 1 candidate invariants
    # * rfilter(|ps|=1,|tcs|=100)
    # rfilter (before 1, after 1, diff 0)
    # ...
    # Detected Invariants for NestedArray:
    # 0: lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])


    # na = NestedArray(terms=ig.ss,tcs1=[ig.tcs[0]],tcs2=ig.tcs[1:],xinfo=ig.xinfo,verbose=1)
    # na.solve()


    #paper_nested.tc example
    #sage: var('A B C')
    (A, B, C)
    #sage: na = NestedArray(terms=None,tcs=[{C: [8, 5, 6, 6, 2, 1, 4], B: [1, -3, 5, 1, 0, 7, 1], A: [7, 1, -3]}],xinfo={'All': ['A', 'B', 'C'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []})
    *** NestedArray ***
    0. All: ['A', 'B', 'C']
    1. Assume: []
    2. Const: []
    3. Expect: []
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    8. ZDims:
    0. A: 1
    1. B: 1
    2. C: 1


    #sage: na = NestedArray(terms=None,tcs=[{'R': [128, 127, 126, 125], 'N':[128]}], xinfo={'All': ['R'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': ['R[i]=sub(N,i)'], 'ExtFun': ['sub'], 'Input': [], 'Output': ['R']})
    *** NestedArray ***
    * gen_extfuns: 1 ext funs ['sub']
    * getExtFunReps(['sub'],|avals|=5)
    * fun: sub, fvals 15, idxs 25
    #sage: na.go()
    Generate array expressions (nestings)* gen_aexps [R,sub,N]:
    2 expressions generated
    * Find valid nestings using reachability analysis
    0. R[i1] == sub(N[(i1)_],(i1)_) has 1 relation(s)
    lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
    1. R[i1] == sub((i1)_,(i1)_) has 1 relation(s)
    lambda R,sub,i1: R[i1] == sub(128,i1)
    * Relations: 2
    Time elapsed: 0.0424 s (solve)
    Refine 2 candidate invariants
    * rfilter skips
    Time elapsed: 0.0001 s (refine)
    Detected Invariants for NestedArray:
    0: lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
    1: lambda R,sub,i1: R[i1] == sub(128,i1)

    """

    def __init__(self,terms,tcs,xinfo):

        super(NestedArray,self).__init__(
            terms   = [],  # not important
            tcs     = tcs,
            xinfo   = xinfo)

    def preprocess(self, xinfo):
        """
        Preprocess input data
        1) transforms external functions to special arrays
        1) change arr repr to value->index repr to speed up arr idx lookup
        2) generate nodes
        """
        if __debug__:
            assert is_dict(xinfo), xinfo
        
        evs = ExtFun.gen_extvars(xinfo=xinfo)
        #arrays only
        evs = [OrderedDict([(k,v) for k,v in ev.iteritems() 
                            if is_list(v)]) 
               for ev in evs]
        evs = Miscs.keys_to_str(evs)
        
        if not is_empty(evs): #add to traces
            self.tcs = [merge_dict(evs + [tc]) for tc in self.tcs]
            self.tcs_extra = [merge_dict(evs + [tc]) for tc in self.tcs_extra]

        
        mytcs = []
        for tc in self.tcs:
            #arrs reprent ext funs (already in new format)
            efs = ExtFun.gen_extfuns(tc=tc,xinfo=xinfo)
            
            #convert normal arr format to new format
            arrs = [(k, Miscs.getListIdxs(v)) for k,v in tc.items()] 
            arrs = OrderedDict(arrs)
            
            d = merge_dict(efs + [arrs])
            mytcs.append(d)
         
 
        self.tcs = mytcs

        self.trees = [Tree({'root':k,
                            'children': [None] * len(c.values()[0][0]),
                            'commute': ExtFun(k).is_commute()})
                      for k,c in self.tcs[0].items()]
        
        self.xinfo = xinfo
        

    def mk_traces(self):
        # will be modified in preprocess
        tcs_all = Miscs.keys_to_str(self.tcs) 
        
        tcs,_ = get_sample(tcs     = tcs_all,
                           tcsN    = 1,  #using only 1 array
                           sampleP = 100,
                           min_    = None)

        tcs_extra = tcs_all #refine on all tcs
        return tcs, tcs_extra


    def solve(self): #nested arrays

        logger.info('Preprocessing arrays')
        self.preprocess(self.xinfo) #add ext funs, generate nodes, modify tcs

        logger.info("Generate arr exps (nestings)")
        aexps = AEXP.gen_aexps(nodes   = self.trees,
                               xinfo   = self.xinfo,
                               data    = self.tcs[0])

        logger.info('Apply reachability analysis to {} '
                    'nestings to find valid ones'
                    .format(len(aexps)))
        
        smtResults = []
        for i,ae in Miscs.senumerate(aexps):
            #logger.detail('%d. '%i, ae.lt, ' = ', ae.rt)
            sRes = ae.peelme(data=self.tcs[0])
            if sRes is not None:

                smtResults = smtResults + sRes

                logger.debug('{}. Nesting {} has {} rel(s)'
                             .format(i,ae,len(sRes)))
                logger.debug('\n'.join(sRes))


        logger.info('Potential rels: %d'%(len(smtResults)))

        self.sols = map(InvNestedArray,smtResults)

    def refine(self):
        #No inferrence for array invs
        #Don't do ranking either since array equations is very long 
        from refine import Refine
        rf = Refine(ps=self.sols)
        rf.rfilter(tcs=self.tcs_extra)
        self.sols = rf.ps






# from sage.all import (SR, srange, var)
# from sageutil import get_vars

# import vu_common as CM
# from dig_miscs import (VLog, Miscs, Tree, AEXP, ExtFun, get_sample)
# from refine import Refine
# from dig import Inv

# logger = VLog('dig_arrays')
# logger.level = VLog.INFO

# class FlatArray(Solver):
#     """
#     Find Flat Array Invariants of the form
#     c1A[i][j].. + c2B[i1'][i2'].. = 0
#     using standard equation solving

#     Examples:
#     ig = InvGen("Traces/AES/Flat/paper_multidim.tc",verbose=1)
#     _ =  ig.getInvs(inv_typ='flat',seed=1)
#     *** InvGen ***
#     Sun Jun  3 21:44:39 2012
#     Sage Version 5.0, Release Date: 2012-05-14
#     Godel.local Darwin 10.8.0 x86_64
#     *** ReadFile ***
#     read 'Traces_ICSE2012/AES/Flat/paper_multidim.tc'
#     number of traces (tcs) read: 9
#     read 'Traces_ICSE2012/AES/Flat/paper_multidim.ext'
#     0. |_tcs|: 9
#     1. |_tcs2|: 0
#     2. _vs: [A, B]
#     3. _xinfo:
#     0. All: ['A', 'B']
#     1. Assume: []
#     2. Const: []
#     3. Expect: ['A[i] - 7B[2i] - 3i == 0']
#     4. ExtFun: []
#     5. Global: []
#     6. Input: []
#     7. Output: []
#     Time elapsed: 0.0408 s (ReadFile)
#     seed 1 (test 0.829402 0.595912 0.429361)
#     *** FlatArray ***
#     Create new trace format (treating array elems as seperate vars)
#     Find linear equalities over 8 array elements
#     sample_traces: chose |tcs1|=9, |tcs2|=0 (attempted 14/9 tcs)
#     Time elapsed: 0.0000 s (function sample_traces)
#     *** Eqt ***
#     Create equations from 9 data
#     * EQ: Solve 9 (uniq) eqts for 9 unknowns coeffs
#     Time elapsed: 0.0287 s (solve)
#     Refine 3 candidate invariants
#     * rfilter skips
#     * rinfer(|ps|=3)
#     rinfer (before 3, after 3, diff 0)
#     Time elapsed: 0.0492 s (refine)
#     Detected Invariants for Eqt:
#     0: A_0 - 7*B_0 == 0
#     1: A_2 - 7*B_4 - 6 == 0
#     2: -1/7*A_1 + B_2 + 3/7 == 0
#     Some rels were modifed
#     A_2 - 7*B_4 - 6 == 0
#     A_0 - 7*B_0 == 0
#     A_1 - 7*B_2 - 3 == 0
#     Find rels over indices
#     a_solve: Assume 'A' is pivot
#     solve 'B' with respect to pivot with |tcs|=3
#     Create equations from 3 data
#     * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
#     Create equations from 3 data
#     * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
#     a_solve: Assume 'A' is pivot
#     solve 'coef' with respect to pivot with |tcs|=3
#     Create equations from 3 data
#     * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
#     Result (pivot A): lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0
#     a_solve: Assume 'B' is pivot
#     solve 'A' with respect to pivot with |tcs|=3
#     Create equations from 3 data
#     * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
#     Create equations from 3 data
#     * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
#     a_solve: Assume 'B' is pivot
#     solve 'coef' with respect to pivot with |tcs|=3
#     Create equations from 3 data
#     * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
#     Result (pivot B): lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0
#     Detected Invariants for FlatArray:
#     0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
#     1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])
#     Time elapsed: 0.1462 s (solve)
#     Refine 2 candidate invariants
#     * rfilter(|ps|=2,|tcs|=9)
#     rfilter (before 2, after 2, diff 0)
#     Time elapsed: 0.0051 s (refine)
#     Detected Invariants for FlatArray:
#     0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
#     1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])

#     """

#     def __init__(self,terms,tcs,xinfo):

#         super(FlatArray,self).__init__(
#             terms  = terms,  #not important
#             tcs   = tcs,
#             xinfo  = xinfo)

#     def mk_traces(self):
#         tcs_extra= Miscs.keys_to_str(self.tcs)
#         return self.tcs, tcs_extra


#     def solve(self): #flat
#         print 'Create new trace format (treating array elems as seperate vars)'
#         aInfo = {}  #{A_0_0=[0,0],B_1_2_3=[1,2,3]}

#         tcs = [FlatArray.genTracesE2V(t,aInfo=aInfo)
#                for t in self.tcs]

#         aeterms = aInfo.keys()
#         assert set(map(str,aeterms)) == set(map(str,tcs[0].keys()))

#         print 'Find linear equalities over %d array elements'%len(aeterms)
#         aeterms = [SR(1)] + aeterms

#         from inv_polynomials import Eqt
#         solverE = Eqt(aeterms, tcs, self.xinfo)

#         logger.info('Select traces (note: |tcs|= |terms|={})'.format(len(aeterms)))
#         from dig_miscs import get_sample
#         solverE.tcs, solverE.tcs_extra = get_sample(tcs, len(aeterms),
#                                                     sampleP=100, min_=None)
#         solverE._go()
#         ps = [s.inv for s in solverE.sols]

#         #modify/reformat results if necessary
#         psOld = set(map(str,ps))
#         ps = FlatArray.filterDupArrs(ps,aInfo=aInfo)
#         ps = [Miscs.elim_denom(p) for p in ps] #Eliminating denominators if exist
#         ps = FlatArray.modifySigns(ps)

#         if ps == []:
#             self.set_sols([])
#             return

#         if set(map(str,ps)) != psOld:
#             print 'Some rels were modifed'
#             print '\n'.join(map(str,ps))

#         ###
#         print "Find rels over indices"
#         psInfo = [FlatArray.parseP(p,aInfo) for p in ps]
#         sols = FlatArray.findRels(psInfo)

#         if CM.is_none_or_empty(sols):
#             sols = ps
#             self.do_refine = False

#         self.set_sols(sols)
#         self.print_sols()


#     def refine(self):

#         rf = Refine(ps=self.sols)
#         rf.rrank()
#         rf.rfilter(tcs=self.tcs_extra)

#         self.set_sols(rf.ps)

#     #######

#     @staticmethod
#     def genTracesE2V(d,aInfo):
#         """
#         Convert array elements into new variables


#         EXAMPLES:

#         sage: aInfo = {}

#         sage: dsVals = FlatArray.genTracesE2V({'A':[['a','b'],['c','d'],['e','f',['z','w']]],'B':[1,2,[7,8]],'C':[100]},aInfo,verbose=1)

#         sage: sorted(dsVals.items(),key=lambda (x,_) : str(x))
#         [(A_0_0, 'a'), (A_0_1, 'b'), (A_1_0, 'c'), (A_1_1, 'd'), (A_2_0, 'e'), (A_2_1, 'f'), (A_2_2_0, 'z'), (A_2_2_1, 'w'), (B_0, 1), (B_1, 2), (B_2_0, 7), (B_2_1, 8), (C_0, 100)]

#         sage: aInfo.items()
#         [(A_1_0, {'idx_': [(A0, 1), (A1, 0)], 'name': 'A'}), (B_0, {'idx_': [(B0, 0)], 'name': 'B'}), (A_2_1, {'idx_': [(A0, 2), (A1, 1)], 'name': 'A'}), (B_2_1, {'idx_': [(B0, 2), (B1, 1)], 'name': 'B'}), (A_0_1, {'idx_': [(A0, 0), (A1, 1)], 'name': 'A'}), (A_2_0, {'idx_': [(A0, 2), (A1, 0)], 'name': 'A'}), (B_2_0, {'idx_': [(B0, 2), (B1, 0)], 'name': 'B'}), (A_0_0, {'idx_': [(A0, 0), (A1, 0)], 'name': 'A'}), (A_2_2_1, {'idx_': [(A0, 2), (A1, 2), (A2, 1)], 'name': 'A'}), (C_0, {'idx_': [(C0, 0)], 'name': 'C'}), (A_1_1, {'idx_': [(A0, 1), (A1, 1)], 'name': 'A'}), (B_1, {'idx_': [(B0, 1)], 'name': 'B'}), (A_2_2_0, {'idx_': [(A0, 2), (A1, 2), (A2, 0)], 'name': 'A'})]

#         #[(B_2_0, {'idx_': [(B0, 2), (B1, 0)], 'name': 'B'}), (A_0_0, {'idx_': [(A0, 0), (A1, 0)], 'name': 'A'}), (A_2_2_1, {'idx_': [(A0, 2), (A1, 2), (A2, 1)], 'name': 'A'}), (C_0, {'idx_': [(C0, 0)], 'name': 'C'}), (A_1_1, {'idx_': [(A0, 1), (A1, 1)], 'name': 'A'}), (B_1, {'idx_': [(B0, 1)], 'name': 'B'}), (A_2_2_0, {'idx_': [(A0, 2), (A1, 2), (A2, 0)], 'name': 'A'}), (A_1_0, {'idx_': [(A0, 1), (A1, 0)], 'name': 'A'}), (B_0, {'idx_': [(B0, 0)], 'name': 'B'}), (A_2_1, {'idx_': [(A0, 2), (A1, 1)], 'name': 'A'}), (B_2_1, {'idx_': [(B0, 2), (B1, 1)], 'name': 'B'}), (A_0_1, {'idx_': [(A0, 0), (A1, 1)], 'name': 'A'}), (A_2_0, {'idx_': [(A0, 2), (A1, 0)], 'name': 'A'})]


#         """

#         def extractValsIdxs(arrName,arrContents,aInfo):
#             vi = Miscs.travel(arrContents)
#             vals = Miscs.getVals(vi)
#             idxs = Miscs.getIdxs(vi)
#             aName = str(arrName)
#             newVars = [var(aName + '_' + '_'.join(map(str,idx))) for idx in idxs]

#             dVals = dict(zip(newVars,vals)) #{A_0_0_1:'w'}

#             for nv,idx in zip(newVars,idxs):
#                 if nv not in aInfo:
#                     idx_ = zip([var('%s%s'%(aName,li))
#                                  for li in srange(len(idx))],idx)
#                     aInfo[nv]={'name':aName,'idx_':idx_}

#             return dVals


#         ds = [extractValsIdxs(k,v,aInfo) for k,v in d.items()]
#         dsVals = CM.merge_dict(ds)
#         return dsVals

#     @staticmethod
#     def filterDupArrs(ps,aInfo):
#         """
#         remove relations that involve elements from same arrays

#         EXAMPLES:

#         sage: var('x_0 x_1 y_0 y_1')
#         (x_0, x_1, y_0, y_1)

#         sage: FlatArray.filterDupArrs([x_0 + x_1 == 0, x_1 + y_1 == 0, x_0+y_1+y_0==0, x_0+x_1-2==0],{x_0:{'name':'x','idxs':[0]},x_1:{'name':'x','idxs':[1]},y_0:{'name':'y','idxs':[0]},y_1:{'name':'y','idxs':[1]}},verbose=0)
#         [x_1 + y_1 == 0]
#         """

#         getArrNames = lambda p: [aInfo[v]['name'] for v in get_vars(p)]
#         ps = [p for p in ps if CM.vall_uniq(getArrNames(p))]

#         return ps

#     @staticmethod
#     def modifySigns(ps):
#         """
#         convert equations so that they have same sign

#         EXAMPLES:

#         sage: var('y')
#         y
#         sage: FlatArray.modifySigns([x-y==0,-2*x + 2*y ==0])
#         [x - y == 0, 2*x - 2*y == 0]

#         sage: FlatArray.modifySigns([-x-y==0,2*x+2*y==0])
#         [-x - y == 0, -2*x - 2*y == 0]

#         sage: FlatArray.modifySigns([-x-y==0,2*x-2*y==0])
#         [-x - y == 0, -2*x + 2*y == 0]
#         """

#         if len(ps) <= 1 :
#             return ps

#         _getSign = lambda p: Miscs.get_coefs_terms(p)[0][0]

#         p0_sign = _getSign(ps[0]) #sign of the coef of the 1st term of the 1st p
#         ps_ = [p if _getSign(p) == p0_sign else -1*p for p in ps[1:]]

#         return [ps[0]]+ps_


#     @staticmethod
#     def parseP(p,d):
#         """
#         # sage: var('A_1_4 B_2_11_8 C_20_5_0')
#         # (A_1_4, B_2_11_8, C_20_5_0)

#         # sage: d = FlatArray.a_parse(-A_1_4 + 7/2*B_2_11_8 - 8*C_20_5_0 + 100 == 0)
#         # sage: sorted(d.items())
#         # [('A', {'_contents_': {A_i_1: 4, A_i_0: 1, A_coef: -1}}), ('B', {'_contents_': {B_coef: 7/2, B_i_2: 8, B_i_1: 11, B_i_0: 2}}), ('C', {'_contents_': {C_i_2: 0, C_i_1: 5, C_i_0: 20, C_coef: -8}}), ('COEF', {'_contents_': {COEF_coef: 100}})]
#         # sage: var('A_4 B_11')
#         # (A_4, B_11)
#         # sage: d = FlatArray.a_parse(1/7*A_4+B_11==0)
#         # sage: sorted(d.items())
#         # [('A', {'_contents_': {A_i_0: 4, A_coef: 1/7}}), ('B', {'_contents_': {B_coef: 1, B_i_0: 11}}), ('COEF', {'_contents_': {COEF_coef: 0}})]

#         """
#         coefs,ts = Miscs.get_coefs_terms(p)

#         if 1 not in ts: #e.g., A_1 + B_2 == 0
#             ts = ts + [1]
#             coefs = coefs + [0]

#         md = {}
#         for c,t in zip(coefs,ts):

#             contents=[(var('coef'),c)]
#             if t == 1:
#                 name='coef'
#             else:
#                 t=var(t)
#                 name = d[t]['name']
#                 idx_ = d[t]['idx_']
#                 contents = contents + idx_

#             md[name]=dict(contents)

#         return md


#     @staticmethod
#     def findRels(psInfo):
#         """
#         #sage: var('rvu_2_1 t_9 rvu_2_3 t_11 rvu_2_0 t_8 rvu_3_2 t_14 rvu_0_0 t_0 rvu_0_2 t_2 rvu_3_1 t_13 rvu_3_3 t_15 rvu_0_1 t_1 rvu_0_3 t_3 rvu_1_3 t_7 rvu_1_0 t_4 rvu_1_2 t_6 rvu_3_0 t_12 rvu_1_1 t_5 rvu_2_2 t_10')
#         (rvu_2_1, t_9, rvu_2_3, t_11, rvu_2_0, t_8, rvu_3_2, t_14, rvu_0_0, t_0, rvu_0_2, t_2, rvu_3_1, t_13, rvu_3_3, t_15, rvu_0_1, t_1, rvu_0_3, t_3, rvu_1_3, t_7, rvu_1_0, t_4, rvu_1_2, t_6, rvu_3_0, t_12, rvu_1_1, t_5, rvu_2_2, t_10)

#         #sage: FlatArray.findRels(ps=[-rvu_2_1 + t_9 == 0, rvu_2_3 - t_11 == 0, rvu_2_0 - t_8 == 0, -rvu_3_2 + t_14 == 0, -rvu_0_0 + t_0 == 0, rvu_0_2 - t_2 == 0, -rvu_3_1 + t_13 == 0, rvu_3_3 - t_15 == 0, rvu_0_1 - t_1 == 0, -rvu_0_3 + t_3 == 0, -rvu_1_3 + t_7 == 0, -rvu_1_0 + t_4 == 0, rvu_1_2 - t_6 == 0, -rvu_3_0 + t_12 == 0, rvu_1_1 - t_5 == 0, rvu_2_2 - t_10 == 0],verbose=0)
#         """

#         ks = psInfo[0]
#         pivots = [k for k in ks if k != 'coef']

#         rs = [FlatArray.findRelsPivot(pivot,psInfo) for pivot in pivots]
#         rs = [rs_ for rs_ in rs if rs_ is not None]

#         return rs




#     @staticmethod
#     def findRelsPivot(pivot, psInfo):
#         """
#         Note: we want to choose an array A as pivot only when all elements of A has relations to elements in other arrays,
#         e.g.,
#         assume A has 4 elements, then we only choose A as pivot if it has the below relations

#         A[0] = B[0]
#         A[1] = B[10]
#         A[2] = B[20]
#         A[3] = B[30]

#         A[4] = B[11]
#         B[11] = B[40]

#         """
#         ks = psInfo[0]

#         rs = [FlatArray.a_solve(pivot,k,psInfo)
#               for k in ks if k != pivot]

#         if None in rs:
#             return None

#         #create template, e.g. lambda p,a,b,p1,p2 = p[p1][p2] - 7a[2p1] + 8p3
#         arrs = [k for k in ks if k != 'coef' and k != pivot]
#         arrs = [pivot] + arrs  #pivot array is the first one
#         pivotIdxs = [str(k) for k in ks[pivot] if str(k) != 'coef']

#         #e.g. pivotD = {'A0':A0, 'coef': 1}
#         pivotD = dict([(str(k),(c if str(k) == 'coef' else k))
#                         for k,c in ks[pivot].items()])

#         rs = [(pivot,pivotD)] + rs
#         terms = [FlatArray.genTemplate(name,d) for name,d in rs]

#         rel = ' + '.join([t for t in terms if t is not None])
#         idxStr = ', '.join(arrs + pivotIdxs)

#         rs = 'lambda %s: %s == 0'%(idxStr,rel)

#         #extract the index info since this result only works for these indices
#         idxInfo = FlatArray.extractIdxInfo(pivot,psInfo)


#         logger.debug('Result (pivot %s): %s'%(pivot,rs))

#         return rs,idxInfo

#     @staticmethod
#     def extractIdxInfo(pivot,psInfo):
#         ps = [p[pivot] for p in psInfo]
#         ps = Miscs.keys_to_str([p for p in ps])
#         ps = [dict([(k,c) for k,c in p.items() if k != 'coef'])
#               for p in ps]
#         return ps


#     @staticmethod
#     def a_solve(pivot, solve_for, tcs):
#         """
#         pivot = 'A'
#         solve_for_arr = 'B'


#         0: A_0 - 7*B_0 == 0
#         1: A_1 - 7*B_2 - 3 == 0
#         2: A_2 - 7*B_4 - 6 == 0

#         Hypothesizes
#         B_coef = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)

#         B_i0 = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)

#         B_i1 = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)
#         """


#         logger.debug("a_solve: Assume '%s' is pivot"%pivot)
#         logger.debug("solve '%s' with respect to pivot with |tcs|=%d"%(solve_for,len(tcs)))


#         _getIdxs = lambda a,d: [k for k in d[a] if not 'coef' in str(k)]

#         #temp fix (5/27)
#         #in KeySetupEnc4, the traces for rk[:6] cause a bug since it generates eqts like
#         #  0: rk_4_0 == 0
#         #  7: rk_5_3 == 0
#         #  8: cipherKey_0 - rk_0_0 == 0
#         #  9: cipherKey_1 - rk_0_1 == 0
#         # The bug here is 0,...,7  has no cipherKey
#         # so the fix is to make sure the tc has those keys
        
#         mytcs = [tc for tc in tcs if pivot in tc and solve_for in tc] #tempfix
#         mytcs = [dict(tc[pivot].items() + tc[solve_for].items()) for tc in mytcs]
                 
#         idxs_ = _getIdxs(pivot,tcs[0])
#         pivot_idxs_n_const = [SR(1)] + idxs_
#         solve_for_keys= tcs[0][solve_for].keys()


#         rs_ = [(pivot_idxs_n_const,k,mytcs) for k in solve_for_keys]  #todo, wtf is this line for ?
#         rs = [Miscs.solve_eqts_(ts=pivot_idxs_n_const,rv=k,ds=mytcs)
#               for k in solve_for_keys]

#         rs = Miscs.keys_to_str(rs)  #so that the keys are string

#         try:
#             sol = CM.merge_dict(rs)
#             sol = (solve_for,sol)
#             return sol
#         except Exception:
#             return None


#     @staticmethod
#     def genTemplate(name,d):

#         if name == 'coef':
#             assert(len(d.values())==1)
#             coefVal = d.values()[0]
#             template = None if coefVal == 0 else '(%s)'%str(coefVal)
#         else:
#             idxVals= ['[%s]'%d[name+str(idx)] for idx in srange(len(d)-1)]

#             if d['coef'] == -1:
#                 coefStr = '-'
#             elif d['coef'] == 1:
#                 coefStr = ''
#             else:
#                 coefStr = str(d['coef']) + '*'

#             template = '(%s%s%s)'%(coefStr,name,''.join(idxVals))

#         return template


# class NestedArray(Solver):
#     """
#     Find NestedArray Invariant of the form  A[i] = B[e] where e = e1 | C[e]

#     EXAMPLES:

#     sage: from invgen import InvGen

#     sage: ig = InvGen("Traces/AES/Nested/paper_nested.tc",verbose=1)
#     *** InvGen ***
#     ...
#     *** ReadFile ***
#     read 'Traces/AES/Nested/paper_nested.tc'
#     number of traces (tcs) read: 1
#     0. |_tcs|: 1
#     1. |_tcs2|: 0
#     2. _vs: [A, B, C]
#     3. _xinfo:
#     0. All: ['A', 'B', 'C']
#     ...

#     sage: ig.verbose = 2
#     sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
#     seed 1 (test 0.829402 0.595912 0.429361)
#     sample_traces: chose |tcs1|=1, |tcs2|=0 (attempted 1/1 tcs)
#     ...
#     *** NestedArray ***
#     0. All: ['A', 'B', 'C']
#     1. Assume: []
#     2. Const: []
#     3. Expect: []
#     4. ExtFun: []
#     5. Global: []
#     6. Input: []
#     7. Output: []
#     8. ZDims:
#     0. A: 1
#     1. B: 1
#     2. C: 1
#     Generate Nestings
#     * gen_aexps [A,C,B]: 2 expressions generated
#     * Find valid nestings using reachability analysis
#     0. A[i1] == B[C[(i1)_]] has 1 relation(s)
#     lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]
#     1. A[i1] == B[(i1)_] has 1 relation(s)
#     lambda A,B,i1: A[i1] == B[-2*i1 + 5]
#     * Relations: 2
#     ...
#     Refine 2 candidate invariants
#     * rfilter(|ps|=2,|tcs|=1)
#     rfilter (before 2, after 2, diff 0)
#     ...
#     Detected Invariants for NestedArray:
#     0: lambda A,B,i1: A[i1] == B[-2*i1 + 5]
#     1: lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]


#     sage: ig = InvGen("Traces/AES/Nested/aes_addroundkey_vn.tc",verbose=1)
#     *** InvGen ***
#     ...
#     *** ReadFile ***
#     read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.tc'
#     number of traces (tcs) read: 100
#     read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.ext'
#     0. |_tcs|: 100
#     1. |_tcs2|: 0
#     2. _vs: [r_, rk, st]
#     3. _xinfo:
#     0. All: ['r_', 'rk', 'st']
#     1. Assume: []
#     2. Const: []
#     3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
#     4. ExtFun: ['xor']
#     5. Global: []
#     6. Input: ['st', 'rk']
#     7. Output: ['r_']
#     ...

#     sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
#     seed 1 (test 0.829402 0.595912 0.429361)
#     sample_traces: chose |tcs1|=1, |tcs2|=99 (attempted 1/100 tcs)
#     ...
#     *** NestedArray ***
#     * gen_extfuns: ext funs ['xor']
#     * getExtFunReps(['xor'],|avals|=32,doCartesianProd=False)
#     * fun: xor, fvals 152, idxs 224
#     0. All: ['r_', 'rk', 'st']
#     1. Assume: []
#     2. Const: []
#     3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
#     4. ExtFun: ['xor']
#     5. Global: []
#     6. Input: ['st', 'rk']
#     7. Output: ['r_']
#     8. ZDims:
#     0. r_: 2
#     1. rk: 2
#     2. st: 2
#     3. xor: 2
#     Generate array expressions (nestings)
#     * gen_aexps [r_,xor,st,rk]: 1 expressions generated
#     * Find valid nestings using reachability analysis
#     0. r_[i1][i2] == xor(st[(i1,i2)_][(i1,i2)_],rk[(i1,i2)_][(i1,i2)_]) has 1 relation(s)
#     lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])
#     * Relations: 1
#     ...
#     Refine 1 candidate invariants
#     * rfilter(|ps|=1,|tcs|=100)
#     rfilter (before 1, after 1, diff 0)
#     ...
#     Detected Invariants for NestedArray:
#     0: lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])


#     na = NestedArray(terms=ig.ss,tcs1=[ig.tcs[0]],tcs2=ig.tcs[1:],xinfo=ig.xinfo,verbose=1)
#     na.solve()


#     #paper_nested.tc example
#     sage: var('A B C')
#     (A, B, C)
#     sage: na = NestedArray(terms=None,tcs1=[{C: [8, 5, 6, 6, 2, 1, 4], B: [1, -3, 5, 1, 0, 7, 1], A: [7, 1, -3]}],tcs2=[],xinfo={'All': ['A', 'B', 'C'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []},verbose=1)
#     *** NestedArray ***
#     0. All: ['A', 'B', 'C']
#     1. Assume: []
#     2. Const: []
#     3. Expect: []
#     4. ExtFun: []
#     5. Global: []
#     6. Input: []
#     7. Output: []
#     8. ZDims:
#     0. A: 1
#     1. B: 1
#     2. C: 1


#     sage: na = NestedArray(terms=None,tcs1=[{'R': [128, 127, 126, 125], 'N':[128]}],tcs2=[],xinfo={'All': ['R'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': ['R[i]=sub(N,i)'], 'ExtFun': ['sub'], 'Input': [], 'Output': ['R']},verbose=1)
#     *** NestedArray ***
#     * gen_extfuns: 1 ext funs ['sub']
#     * getExtFunReps(['sub'],|avals|=5)
#     * fun: sub, fvals 15, idxs 25
#     sage: na.go()
#     Generate array expressions (nestings)* gen_aexps [R,sub,N]:
#     2 expressions generated
#     * Find valid nestings using reachability analysis
#     0. R[i1] == sub(N[(i1)_],(i1)_) has 1 relation(s)
#     lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
#     1. R[i1] == sub((i1)_,(i1)_) has 1 relation(s)
#     lambda R,sub,i1: R[i1] == sub(128,i1)
#     * Relations: 2
#     Time elapsed: 0.0424 s (solve)
#     Refine 2 candidate invariants
#     * rfilter skips
#     Time elapsed: 0.0001 s (refine)
#     Detected Invariants for NestedArray:
#     0: lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
#     1: lambda R,sub,i1: R[i1] == sub(128,i1)

#     """

#     def __init__(self,terms,tcs,xinfo):

#         super(NestedArray,self).__init__(
#             terms   = [],                      # not important
#             tcs     = Miscs.keys_to_str(tcs), # will be modified in preprocess
#             xinfo   = xinfo)


#     def mk_traces(self):
#         tcs,_ = get_sample(tcs     = self.tcs,
#                            tcsN    = 1,  #using only 1 array
#                            sampleP = 100,
#                            min_    = None)

#         tcs_extra = self.tcs #refine on all tcs
#         return tcs, tcs_extra


#     def solve(self): #nested arrays

#         print 'Preprocessing arrays'
#         self.preprocess(self.xinfo) #add ext funs, generate nodes, modify tcs


#         print "Generate array expressions (nestings)"
#         aexps = AEXP.gen_aexps(nodes   = self.trees,
#                                xinfo   = self.xinfo,
#                                data    = self.tcs[0])

#         print '* Find valid nestings using reachability analysis'
#         smtResults = []
#         for i,ae in Miscs.senumerate(aexps):
#             #logger.detail('%d. '%i, ae.lt, ' = ', ae.rt)

#             sRes = ae.peelme(data=self.tcs[0])

#             if sRes is not None:

#                 smtResults = smtResults + sRes


#                 logger.debug('%d. %s has %d relation(s)'%(i,ae,len(sRes)))
#                 logger.debug('\n'.join(sRes))


#         print '* Relations: %d'%(len(smtResults))

#         self.set_sols(smtResults)


#     def refine(self):

#         rf = Refine(ps=self.sols)
#         #print self.tcs_extra

#         rf.rfilter(tcs=self.tcs_extra)

#         self.set_sols(rf.ps)

#     ###### Helpers Function for Nested Array #####

#     def preprocess(self,xinfo):
#         """
#         Preprocesses input data
#         1) transforms external functions to special arrays
#         1) change array repr to value->index repr to speed up
#         array index lookup
#         2) generate nodes
#         """

#         assert isinstance(xinfo,dict)

#         #add new extfun variables
#         tcs = [ExtFun.gen_extfuns(tc=tc,xinfo=xinfo)
#                for tc in self.tcs]


#         #add new representations to arrs
#         tcs = [[(k,Miscs.getListIdxs(c) if isinstance(c,list) else c)
#                 for k,c in tc.items()]
#                for tc in tcs]
#         tcs = [dict(tc) for tc in tcs]
#         self.tcs = tcs

#         self.trees = [Tree({'root':k,
#                             'children': [None] * len(c.values()[0][0]),
#                             'commute': ExtFun(k).is_commute()})
#                       for k,c in self.tcs[0].items()]
#         self.xinfo = xinfo
