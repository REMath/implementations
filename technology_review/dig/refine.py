from sage.all import (Combinations, SR, QQ, srange, operator)

from vu_common import (VLog, pause, is_list, is_empty, vset)
from sageutil import (get_vars)
from dig_inv import Inv, InvExp, InvEqt, InvMPP, InvIeq, InvArray


logger = VLog('refine')
logger.level = VLog.INFO

class Refine(object):
    """
    Refine result invariants using several techniques, including

    1) filtering
    2) inferring
    3) ranking
    """

    def __init__(self, ps):
        if __debug__:
            assert is_list(ps) and all(isinstance(p,Inv) for p in ps), ps
        
        self.ps = vset(ps)
        Refine.print_diff('vset', len(ps), len(self.ps))

    def get_ps(self): 
        return self._ps

    def set_ps(self, ps):
        if __debug__:
            assert all(isinstance(p,Inv) for p in ps), p 
        self._ps = ps

    ps = property(get_ps, set_ps)
    
    @staticmethod
    def print_diff(fn, len_before, len_after):
        ndiff = len_before - len_after
        if ndiff >= 1:
            logger.debug("{} (before {}, after {}, diff {})"
                         .format(fn, len_before, len_after, ndiff))

    def rrank(self):
        """
        Remove unlikely properties using simple heuristic
        """

        if len(self.ps) <= 1: 
            logger.debug('rrank skips (|ps|)={}'.format(len(self.ps)))
            return None

        logger.debug('rrank(|ps|={})'.format(len(self.ps)))

        old_len = len(self.ps)
        self.ps = [p for p in self.ps if p.get_score() <= 100]

        Refine.print_diff('rrank', old_len, len(self.ps))

    def rfilter_old(self, tcs):
        """
        Returns the subset of ps that satisfies all testcases tcs

        Examples:

        sage: logger.set_level(VLog.DEBUG)

        sage: var('y z')
        (y, z)

        sage: rf = Refine(map(InvIeq,[x^2 >= 0 , x-y >= 7]));rf.rfilter([{x:1,y:0}]);  sorted(rf.ps,key=str)
        refine:Debug:rfilter(|ps|=2, |tcs|=1)
        refine:Debug:rfilter (before 2, after 1, diff 1)
        [x^2 >= 0]

        sage: rf = Refine(map(InvIeq,[2*x -y >= 0])); rf.rfilter([{y: 14, x: 7}, {y: 13, x: 7}, {y: 6, x: 4}, {y: 1, x: 1}, {y: 2, x: 1}, {y: 5, x: 100}]); sorted(rf.ps,key=str)
        refine:Debug:rfilter(|ps|=1, |tcs|=6)
        [2*x - y >= 0]

        sage: rf = Refine(map(InvIeq,[2*x -y >= 0])); rf.rfilter([{y: 14, x: 7}, {y: 13, x: 7}, {y: 6, x: 4}, {y: 1, x: 1}, {y: 2, x: 1}, {y: 25, x: 9}, {y:25 , x*y: 15, x: 9}]); sorted(rf.ps,key=str)
        refine:Debug:rfilter(|ps|=1, |tcs|=7)
        refine:Debug:rfilter (before 1, after 0, diff 1)
        []

        ** This is by design
        sage: rf = Refine(map(InvIeq,[x^3 >= 0 , x-y >= 7])); rf.rfilter([{z:1}])
        refine:Debug:rfilter(|ps|=2, |tcs|=1)
        refine:Debug:rfilter (before 2, after 0, diff 2)
        sage: assert(rf.ps == [])

        sage: rf = Refine(map(InvMPP,[('lambda x: x>=10',''), ('lambda x,y: max(x,y)>12',''), ('lambda x: x>=10','')])); rf.rfilter([{x:20,y:0},{x:9,y:13}]); sorted(rf.ps,key=str)
        refine:Debug:vset (before 3, after 2, diff 1)
        refine:Debug:rfilter(|ps|=2, |tcs|=2)
        refine:Debug:rfilter (before 2, after 1, diff 1)
        ['lambda x,y: max(x,y)>12']


        sage: rf = Refine(map(InvMPP,[('lambda x: x>=10', ''), ('lambda x,y: max(x,y)>12','')])); rf.rfilter([{x:20,y:0}]); sorted(rf.ps,key=str)
        refine:Debug:rfilter(|ps|=2, |tcs|=1)
        ['lambda x: x>=10', 'lambda x,y: max(x,y)>12']


        sage: rf = Refine(map(InvMPP,[('lambda x: x>=10',''), ('lambda x,y: max(x,y)>12','')])); rf.rfilter([]); sorted(rf.ps,key=str)
        refine:Debug:rfilter skips (|ps|=2, |tcs|=0)
        ['lambda x: x>=10', 'lambda x,y: max(x,y)>12']


        """

        if is_empty(self.ps) or is_empty(tcs):
            logger.debug('rfilter skips (|ps|={}, |tcs|={})'
                         .format(len(self.ps), len(tcs)))
            return None

        logger.debug('rfilter(|ps|={}, |tcs|={})'
                     .format(len(self.ps), len(tcs)))
        
        if not isinstance(self.ps[0],InvExp):
            from dig_miscs import Miscs
            tcs = Miscs.keys_to_str(tcs)

        old_len = len(self.ps)
        self.ps = [p for p in self.ps if all(p.seval(tc) for tc in tcs)]

        Refine.print_diff('rfilter', old_len, len(self.ps))



    def rfilter(self,tcs,do_parallel=True):

        if is_empty(self.ps) or is_empty(tcs):
            logger.debug('rfilter skips (|ps|={}, |tcs|={})'
                         .format(len(self.ps), len(tcs)))
            return None

        logger.debug('rfilter(|ps|={}, |tcs|={})'
                     .format(len(self.ps), len(tcs)))
        
        if not isinstance(self.ps[0],InvExp):
            from dig_miscs import Miscs
            tcs = Miscs.keys_to_str(tcs)

        def wprocess(tasks,Q):
            rs = [p for p in tasks if all(p.seval(tc) for tc in tcs)]
            if Q is None: #no multiprocessing
                return rs
            else:
                Q.put(rs)
            
        tasks = self.ps

        if do_parallel:
            from vu_common import get_workloads
            from multiprocessing import (Process, Queue, 
                                         current_process, cpu_count)
            Q=Queue()
            workloads = get_workloads(tasks, 
                                      max_nprocesses=cpu_count(),
                                      chunksiz=2)

            logger.debug("workloads 'refine' {}: {}"
                         .format(len(workloads),map(len,workloads)))
                                 
            workers = [Process(target=wprocess,args=(wl,Q))
                       for wl in workloads]

            for w in workers: w.start()
            wrs = []
            for _ in workers: wrs.extend(Q.get())
        else:
            wrs = wprocess(tasks,Q=None)
        
        self.ps = wrs
        Refine.print_diff('rfilter', len(tasks), len(self.ps))

    def rinfer(self):
        """
        Return a (preferably minimal) subset of ps that
        infers all properties in ps.

        sage: logger.set_level(VLog.DEBUG)
            
        sage: var('a s t y')
        (a, s, t, y)

        sage: rf = Refine(map(InvEqt,[a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0, \
        a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0, \
        a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0]))
        sage: rf.rinfer()
        refine:Debug:rinfer(|ps|=6)
        refine:Debug:rinfer (before 6, after 2, diff 4)
        sage: assert \
        set([p.p for p in rf.ps]) == set([a - 1/2*t + 1/2 == 0, t^2 - 4*s + 2*t + 1 == 0]) or \
        set([p.p for p in rf.ps]) == set([a - 1/2*t + 1/2 == 0, a^2 - s + t == 0])


        sage: rf = Refine(map(InvIeq,[x-7>=0, x + y -2>=0, y+5 >= 0, -7 + x >= 0])); rf.rinfer(); sorted(rf.ps,key=str)
        refine:Debug:vset (before 4, after 3, diff 1)
        refine:Debug:rinfer(|ps|=3)
        refine:Debug:rinfer (before 3, after 2, diff 1)
        [x - 7 >= 0, y + 5 >= 0]


        sage: rf = Refine(map(InvEqt,[x+y==0])); rf.rinfer(); sorted(rf.ps,key=str)
        refine:Debug:rinfer skips (|ps|=1)
        [x + y == 0]
        
        """

        if len(self.ps) <= 1:
            logger.debug('rinfer skips (|ps|={})'.format(len(self.ps)))
            return None

        logger.debug('rinfer(|ps|={})'.format(len(self.ps)))

        ps = [p.p for p in self.ps if isinstance(p,InvExp)]

        if is_empty(ps):
            logger.warn('cannot do inferrence on non polynomial rels')
            return None

        
        self.ps = [InvEqt(p) if p.operator() == operator.eq else InvIeq(p)
                   for p in Refine.rinfer_helper(ps)]

        Refine.print_diff('rinfer', len(ps), len(self.ps))
                             

    ##### Helpers for Refine ###

    @staticmethod
    def rinfer_helper(ps):
        """
        Removes weak properties (e.g., remove q if p => q)

        Examples:

        sage: var('y a s t z b q d k x1')
        (y, a, s, t, z, b, q, d, k, x1)

        sage: Refine.rinfer_helper([x*x-y*y==0,x-y==0,x*x-y*y==0,2*x*y-2*y*y==0])
        [x - y == 0]


        #several possible (but should be equiv) solutions
        sage: Refine.rinfer_helper([a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0,a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0])
        [t^2 - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]

        alt solutions:
        [-2*a + t - 1 == 0, a^2 + 2*a - s + 1 == 0]
        [-1/4*t^2 + s - 1/2*t - 1/4 == 0, a - 1/2*t + 1/2 == 0]
        [t^2 - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]
        [a^2 - s + t == 0, a - 1/2*t + 1/2 == 0]

        sage: Refine.rinfer_helper([a*y - b == 0,a*z - a*x + b*q == 0,q*y + z - x == 0])
        [a*y - b == 0, q*y - x + z == 0]

        sage: Refine.rinfer_helper([x-7>=0, x + y -2>=0, y+5 >= 0])
        [x - 7 >= 0, y + 5 >= 0]

        sage: Refine.rinfer_helper([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        [a*y - b == 0, q*y + k - x == 0]

        sage: Refine.rinfer_helper([x-1>=0 , d*y - 6 >= 0, d - 1 >= 0, y - 6 >= 0, d*y - y >= 0, d*x - x >= 0, y*x - 6*x>=0 , y^2 - 36 >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0 , d*y - 6*d - y + 6 >= 0])
        [x - 1 >= 0, d - 1 >= 0, y - 6 >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0]

        Alt Sol:
        [d*x - x >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0, x - 1 >= 0, x*y - 6*x >= 0]

        sage: Refine.rinfer_helper([x+x1==0,x-x1==1])
        [x - 1/2 == 0, x1 + 1/2 == 0]

        Alt Sols:
        [x + x1 == 0, x - x1 == 1]    

        sage: Refine.rinfer_helper([x^2-1>=0,x-1>=0])
        [x - 1 >= 0]

        """

        #If there are too many ps and one involves a high degree
        #then likely SMT solver will screw up (e.g., loop forever)
        #so use Groebner basis (which only works for equalities)
        if all(p.operator() == operator.eq for p in ps):
            #Use Groebner basis
            return InvEqt.sreduce(ps)
            return ps_
        
        else:
            #Use SMT solving'
            return InvIeq.sreduce(ps)
