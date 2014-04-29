from abc import ABCMeta, abstractmethod
import multiprocessing as mp

from sage.all import (set_random_seed, version)

from vu_common import (VLog, pause, is_str, is_list, is_empty,
                       get_cur_time)

import dig_miscs
from dig_inv import Inv
logger = VLog('dig')

"""
Design notes:

Information should be output from this file and not too much from other files.
"""

class DIG(object):
    """
    Main class to generate invariants by making calls to other classes
    to get different types of invariants

    Examples:
    See usage example in classes Eqt, Ineqs, FlatArray, NestedArray
    """

    def __init__(self,filename,verbose=VLog.DEBUG):
    
        if __debug__:
            assert filename is None or is_str(filename), filename

        logger.level = verbose

        import dig_inv, refine, dig_arrays, dig_polynomials
        for f in [dig_inv, refine, dig_arrays, dig_polynomials, dig_miscs]:
            f.logger.set_level(logger.level)
        
        from platform import node, system, release, machine
        margs = [get_cur_time(time_only=False),version(),
                 ' '.join([node(),system(),release(),machine()])]
        logger.info("{}, {}, {}".format(*margs))
        
        if filename is not None:
            self._setup(filename)
        else:
            logger.warn('No filename given, manual setup')
    
    def _setup(self,filename):
        if __debug__:
            assert is_str(filename), filename

        rf = dig_miscs.ReadFile(filename)
        
        self.filename = rf.filename
        self.xinfo    = rf.xinfo
        
        self.ss_arr, self.tcs_arr = rf.ss_arr, rf.tcs_arr
        self.ss_num, self.tcs_num = rf.ss_num, rf.tcs_num
        
    
    def set_seed(self, seed=0):
        if __debug__:
            assert seed >= 0, seed

        self.seed = seed
        set_random_seed(self.seed)
        logger.debug('Set seed to: {}'.format(self.seed))

        
    def get_invs(self, deg=2):
        """
        Default method to obtain invariants
        By default, DIG finds flat/nested relations over arr vars
        and finds eqts/ieqs(deduction) over num vars.
        """

        rs = []
        if not is_empty(self.ss_arr):
            logger.debug('*** Generate Array Invs over {} ***\n'
                         .format(self.ss_arr))
            rs = rs + self.get_flat_array()
            rs = rs + self.get_nested_array()

        if not is_empty(self.ss_num):
            logger.debug('*** Generate Polynomial Invs over {} ***\n'
                         .format(self.ss_num))

            if __debug__:
                assert deg >= 1, deg

            terms = dig_miscs.gen_terms(deg, self.ss_num)
            logger.debug('deg={}, |ss_num|={}, |terms|={}'
                         .format(deg,len(self.ss_num),len(terms)))
            rs = rs + self.get_eqts(terms)
                
        return rs
                
    ### Arrays ###
    def get_flat_array(self):
        """
        Examples:
        ig = InvGen("Traces/AES/Flat/aes_State2Block.tc",verbose=1)
        ig.get_flat_array()
        """
        from dig_arrays import FlatArray
        solver = FlatArray(self.ss_arr,self.tcs_arr,self.xinfo)
        solver.go()
        return solver.sols


    def get_nested_array(self):
        """
        Examples:
        ig = InvGen('Traces/AES/Nested/aes_mul.tc',seed=0,verbose=1)
        ps = ig.getnested_array()
        """

        from dig_arrays import NestedArray
        solver = NestedArray(self.ss_arr,self.tcs_arr,self.xinfo)
        solver.go()
        return solver.sols

    ### Polynomials ###

    def get_eqts(self,terms=None):
        if terms is None:
            terms = self.ss_num

        from dig_polynomials import Eqt
        solver = Eqt(terms, self.tcs_num, self.xinfo)
        solver.go()
        sols = solver.sols

        if not (is_empty(sols) or is_empty(self.xinfo['Assume'])):
            #deduce new info if external knowledge (assumes) is avail
            from dig_polynomials import IeqDeduce
            solver = IeqDeduce(xinfo = self.xinfo,
                               eqts  = [s.p for s in sols])
            solver.solve()
            solver.print_sols()

            sols = sols + solver.sols

        return sols

    #Max/Min Plus Ieqs
    def _get_mpp(self,typ,terms=None,subset_siz=None):
        if terms is None:
            terms = self.ss_num

        import dig_polynomials as dp

        solver = dp.IeqMPPGen if 'gen' in typ else dp.IeqMPPFixed
        solver = solver(terms,self.tcs_num,self.xinfo) 

        if 'max_then_min' in typ:
            mpp_opt = dp.IeqMPP.opt_max_then_min
        elif 'min' in typ:
            mpp_opt = dp.IeqMPP.opt_min_plus
        else:
            mpp_opt = dp.IeqMPP.opt_max_plus
            
        solver.mpp_opt = mpp_opt
        solver.subset_siz = subset_siz

        solver.go()
        return solver.sols

    def get_ieqs_max_min_gen(self,terms=None,subset_siz=None):
        return self._get_mpp('gen max_then_min',terms,subset_siz)

    def get_ieqs_min_gen(self,terms=None,subset_siz=None):
        return self._get_mpp('gen min',terms,subset_siz)

    def get_ieqs_max_gen(self,terms=None,subset_siz=None):
        return self._get_mpp('gen max',terms,subset_siz)

    #Fixed
    def get_ieqs_max_min_fixed(self,terms=None,subset_siz=None):
        return self._get_mpp('fixed max_then_min',terms,subset_siz)

    def get_ieqs_min_fixed(self,terms=None,subset_siz=None):
        return self._get_mpp('fixed min',terms,subset_siz)

    def get_ieqs_max_fixed(self,terms=None,subset_siz=None):
        return self._get_mpp('fixed max',terms,subset_siz)

    def get_ieqs_max_min_fixed_2(self,terms=None):
        return self.get_ieqs_max_min_fixed(terms=terms,subset_siz=2)

    def get_ieqs_max_min_fixed_3(self,terms=None):
        return self.get_ieqs_max_min_fixed(terms=terms,subset_siz=3)

    #Classic Polyhedral Ieqs
    def _get_clp(self,typ,terms=None,subset_siz=None):
        if terms is None:
            terms = self.ss_num

        import dig_polynomials as dp
            
        if 'gen' in typ:
            solver = dp.IeqCLPGen(terms,self.tcs_num,self.xinfo)
        else:
            solver = dp.IeqCLPFixed(terms,self.tcs_num,self.xinfo)

        solver.subset_siz = subset_siz

        solver.go()
        return solver.sols

    def get_ieqs_cl_gen(self,terms=None,subset_siz=None):
        return self._get_clp('gen',terms,subset_siz)

    def get_ieqs_cl_fixed(self,terms=None,subset_siz=None):
        return self._get_clp('fixed',terms,subset_siz)

    def get_ieqs_cl_fixed_2(self,terms=None):
        """ Octagonal """
        return self._get_clp('fixed',terms,subset_siz=2)

    #Eqts and Max/Min
    def _get_eqts_ieqs_max_min(self, deg, subset_siz=None,is_fixed=True):
        def worker_mpp_gen(Q):
            rs = self.get_ieqs_max_min_gen(terms=None,subset_siz=subset_siz)
            Q.put(rs)
        def worker_mpp_fixed(Q):
            rs = self.get_ieqs_max_min_fixed(terms=None,subset_siz=subset_siz)
            Q.put(rs)
        def worker_eqts(Q):
            rs = self.get_invs(deg=deg)
            Q.put(rs)


        if is_fixed:
            worker_mpp = worker_mpp_fixed
        else:
            worker_mpp = worker_mpp_gen

        Q = mp.Queue()
        workers = [mp.Process(target=w, args=(Q,)) 
                   for w in [worker_mpp, worker_eqts]]

        for w in workers: w.start()
        rs = []
        for _ in workers:
            rs.extend(Q.get())

        return rs

    def get_eqts_ieqs_max_min_fixed_3(self, deg):
        return self._get_eqts_ieqs_max_min(deg=deg,subset_siz=3,
                                           is_fixed=True)
    def get_eqts_ieqs_max_min_fixed_2(self, deg):
        return self._get_eqts_ieqs_max_min(deg=deg,subset_siz=2,
                                           is_fixed=True)
    def get_eqts_ieqs_max_min_gen_3(self, deg):
        return self._get_eqts_ieqs_max_min(deg=deg,subset_siz=3,
                                           is_fixed=False)
    def get_eqts_ieqs_max_min_gen_2(self, deg):
        return self._get_eqts_ieqs_max_min(deg=deg,subset_siz=2,
                                           is_fixed=False)

class Solver(object):
    """
    Base class inherited by all inv solver classes
    """
    __metaclass__ = ABCMeta

    def __init__(self,terms,tcs,xinfo):

        logger.info('*** {} ***'.format(self.__class__.__name__))

        self.terms   = terms
        self.tcs    = tcs
        self.xinfo   = xinfo

        self.do_refine = True
        self.tcs_extra = []
        self._sols    = []

        logger.debug('|terms|={}, |tcs|={}'
                    .format(len(self.terms), len(self.tcs)))
                             
    def get_sols(self): 
        return self._sols
    
    def set_sols(self, sols):
        if __debug__:
            assert (is_list(sols) and 
                    all(isinstance(s,Inv) for s in sols)), sols

        self._sols = sols

    sols = property(get_sols,set_sols)

    @abstractmethod
    def mk_traces(self): return
        

    @abstractmethod
    def solve(self): return

    @abstractmethod
    def refine(self): return

    def print_sols(self):
        """
        Print solutions
        """
        logger.info('Detected {} invs for {}:'
                    .format(len(self.sols), self.__class__.__name__))

        Inv.print_invs(self.sols)

    def _go(self):
        """
        Shortcut to find, refine, and print invs (no mk_traces)
        """
        logger.info('Compute invs over {} tcs'.format(len(self.tcs)))
        
        self.solve()

        if self.do_refine:
            logger.info('Refine {} invs'.format(len(self.sols)))
            self.refine()

        self.print_sols()

        
    def go(self):
        """
        Shortcut to mk_traces, find, refine, and print invs
        """

        logger.info('Select traces')
        self.tcs, self.tcs_extra = self.mk_traces()
        self._go()




