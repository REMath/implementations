import itertools
from collections import OrderedDict
from sage.all import (os, srange, SR, QQ, ZZ, RR, sage_eval, flatten,
                      var, operator, identity_matrix, Set, log, 
                      solve, shuffle, prod, deepcopy, Integer, lcm,
                      CartesianProduct, PolynomialRing, cached_function, 
                      oo)

import vu_common as CM
from vu_common import (VLog, pause, vset, iset, vpartition,
                       vall_uniq, iread, vwrite, dict2str,
                       isnum, is_str, is_list, is_dict, is_tuple,
                       is_bool,   
                       is_iterable, is_empty, list_str, file_basename)

from sageutil import is_sage_expr, is_sage_int, get_vars

logger = VLog('dig_miscs')
logger.set_level(VLog.INFO)

class ReadFile(object):
    """
    Read data file and other info (ss, tcs, xinfo)
    """
    def __init__(self, filename):
        """
        Read input file (trace data) and do some preprocessing

        Examples:
        sage: rf = ReadFile('../invgen/Traces/NLA/cohendiv.tcs')
        sage: rf.ss_num
        [a, b, q, r, x, y]
        sage: assert len(rf.tcs_num) == 2685
        sage: assert str(rf.xinfo['Assume'][0]) == 'r >= 2*b'
        """

        if __debug__:
            assert is_str(filename), filename
            import os.path
            assert os.path.exists(filename), \
                "file '{}' doesn't exist".format(filename)
            

        lines = ReadFile.read_n_filter(filename)
        (ss_arr, tcs_arr), (ss_num, tcs_num) = ReadFile.get_ss_tcs(lines)

        #get additional info
        base_fname = file_basename(filename)

        #extra info
        ext_file = base_fname + '.ext'

        if os.path.exists(ext_file):
            lines = ReadFile.read_n_filter(ext_file)
        else:
            lines = []

        xinfo = ReadFile.get_xinfo(lines)
        xinfo['All'] = map(str,ss_arr + ss_num)

        self.filename = filename
        self.ss_arr = ss_arr
        self.ss_num = ss_num
        self.tcs_arr = tcs_arr
        self.tcs_num = tcs_num
        self.xinfo = xinfo

        logger.debug("Read Info:\n" + 
                     dict2str(self.__dict__, 
                              print_size_only=['tcs_arr', 'tcs_num', 'ExtVar']))

    @staticmethod
    def test_csv(filename):
        import csv
        f = open(filename)
        try:
            reader = csv.reader(f,delimiter=' ')
            for row in reader:
                print row
        finally:
            f.close()

    @staticmethod
    def get_tcs_files(dirname, file_ext='.tcs'):
        return sorted(f for f in os.listdir(dirname) 
                      if f.endswith(file_ext))

    @staticmethod
    def split_file(filename):
        """
        Split file containing traces at n locations into n files.
        Each file contains traces for each location
        """
        lines = iread(filename)
        lines = ReadFile.filter_content(lines)
        lines = (ReadFile.formatter(l) for l in lines)

        locs = OrderedDict()
        for l in lines:
            try:
                idx = l.index(':')
                loc = l[:idx].strip()
                line = l[idx+1:].strip()
            except ValueError:
                logger.error("Wrong tcs format (missing ':'). Skip '{}'"
                             .format(filename))
                return

            if loc not in locs:
                locs[loc] = OrderedDict()

            if line not in locs[loc]:
                locs[loc][line] = None

        #write to multifiles
        base_fname = file_basename(filename)
        comment = "#Traces extracted from '{}\n".format(filename)

        logger.info('Found traces at {} locs: {}'
                    .format(len(locs), ', '.join(locs.keys())))

        for loc, lines in locs.iteritems():
            filename_out = "{}.{}.{}".format(base_fname,loc,'tcs')
            vwrite(filename_out, 
                   comment + "#loc: '{}'\n".format(loc) + '\n'.join(lines))
            logger.info("Written to file '{}'".format(filename_out))

    @staticmethod
    def split_files_in_dir(dirname):
        """
        Call split_file over files in dirname
        #sage: ReadFile.split_files_in_dir('../invgen/Traces/NLA_tosem/loopinvs/')
        """
        tcs_files = ReadFile.get_tcs_files(dirname)
        nfiles = len(tcs_files)
        for i,f in enumerate(tcs_files):
            f = os.path.join(dirname,f)
            logger.info('{}/{}. Parse tcs file {}'.format(i+1, nfiles, f))
            ReadFile.split_file(f)


    @staticmethod
    def exec_scripts_in_dir(dirname):
        """
        Run .sh files in dirname
        #sage: ReadFile.exec_scripts_in_dir('../invgen/Traces/NLA_tosem/')
        """

        def chdir(dirname):
            old_dir = os.path.abspath(os.curdir)
            os.chdir(dirname)
            print "changed dir from '{}' to '{}'".format(old_dir, dirname)

            return old_dir

        sh_files = ReadFile.get_tcs_files(dirname,'.sh')
        if not is_empty(sh_files):
            nfiles = len(sh_files)
            old_dir = chdir(dirname)

            for i,f in enumerate(sh_files):
                scmd = 'sh {}> {}'.format(f, file_basename(f) + '.tcs')
                logger.info("{}/{}. {}".format(i+1, nfiles, scmd))
                #os.system is easier than vcmd since it reports directly error
                os.system(scmd)  

            _ = chdir(old_dir)

    @cached_function
    def check_rounding(s,n_fract=7):
        """
        Returns True if the input number doesn't have rounding imprecision
        that is, if the number of fractional digit is < n_fract

        The reason for this is because in C
        0.0309375 / 2.0 gives 0.0155688 instead of 0.01546875

        Examples:
        sage: assert ReadFile.check_rounding('-12342.465223',n_fract=6) == False
        sage: assert ReadFile.check_rounding('-12342.465223',n_fract=7) == True
        sage: assert ReadFile.check_rounding('-12342.465223') == True
        sage: assert ReadFile.check_rounding('-12342.4652233') == False
        sage: assert ReadFile.check_rounding('[-12342.465223, -12342.4652233]') == False
        sage: assert ReadFile.check_rounding('[1, 2, 3.0001]',n_fract=4) == False
        sage: assert ReadFile.check_rounding('[1, 2, 3.0000]',n_fract=4) == True

        #invalid array format
        sage: ReadFile.check_rounding('[1, 2 3.0000]',n_fract=4)
        Traceback (most recent call last):
        ...
        AssertionError: '2 3.0000' is not a number

        """

        def _check_rounding(s, n_fract):
            if __debug__: 
                assert isnum(s), "'{}' is not a number".format(s) 

            rs = ('.' in s and
                  len(s.split('.')[1].rstrip('0')) >= n_fract)

            return not rs


        if ReadFile.is_array(s):
            s = s.replace('[','').replace(']','')
            s = [s_.strip() for s_ in s.split(',')]
            rs = all(_check_rounding(s_, n_fract) for s_ in s)
        else:
            rs = _check_rounding(s, n_fract)

        return rs

    @staticmethod
    def strToVar(s):
        """
        sage: ReadFile.strToVar('myvar')
        myvar
        
        sage: ReadFile.strToVar('0invalid')
        Traceback (most recent call last):
        ...
        AssertionError: 0invalid
        
        """
        if __debug__:
            assert s[0].isalpha(), s  #var has to start with alpha letter

        return var(s)


    @cached_function
    def strToRatOrList(s, is_num_val=None):

        if is_num_val is None:
            return (ReadFile.str2list(s) if ReadFile.is_array(s)
                    else ReadFile.str2rat(s))
        elif is_num_val:
            return ReadFile.str2rat(s)
        else:
            return ReadFile.str2list(s)
             

    @staticmethod
    def is_array(s): return s.startswith('[') and s.endswith(']')

    @staticmethod
    def str2list(s):
        """
        Converts a string containing a list of number to proper list format

        Examples:

        sage: ReadFile.str2list('[1,2,[4, 7, 13, [7,9]]] ')
        [1, 2, [4, 7, 13, [7, 9]]]

        """
        rs = Miscs.tmap(QQ,sage_eval(s))
        return rs


    @staticmethod
    def str2rat(s):
        """
        Convert the input 's' to a rational number if possible.
        Otherwise returns None

        Examples:

        sage: assert ReadFile.str2rat('.3333333') == 3333333/10000000
        sage: assert ReadFile.str2rat('3/7') == 3/7
        sage: assert ReadFile.str2rat('1.') == 1
        sage: assert ReadFile.str2rat('1.2') == 6/5
        sage: assert ReadFile.str2rat('.333') == 333/1000
        sage: assert ReadFile.str2rat('-.333') == -333/1000
        sage: assert ReadFile.str2rat('-12.13') == -1213/100

        #Returns None because cannot convert this str
        sage: ReadFile.str2rat('333333333333333s')
        dig_miscs:Warn:cannot convert 333333333333333s to rational

        Note: this version seems to be the *fastest*
        among several ones I've tried
        %timeit ReadFile.str2rat('322')

        """

        try:
            return QQ(s)
        except TypeError:
            pass

        try:
            return QQ(RR(s))
        except TypeError:
            logger.warn('cannot convert {} to rational'.format(s))
            return None

    @staticmethod
    def read_n_filter(filename):
        content = iread(filename)
        content = ReadFile.filter_content(content)
        return content

    @staticmethod
    def formatter(s):
        """
        sage: ReadFile.formatter('[1, 2, [3, 5]]')
        '[1,2,[3,5]]'
        """
        s_ = ', '; s__ = ','
        while s_ in s: s = s.replace(s_, s__)
        return s

    @staticmethod
    def filter_content(content, ignore_kws=['#','>>>','sage','$']):
        """
        Filter out unwanted stuff from file

        Examples:

        sage: len(list(ReadFile.filter_content(['Hello World','#Ignore Me1', \
        'Name is Vu $Ignore Me2','Hello World',' #  remove this line'])))
        2

        """
        content = (l.strip() for l in content)
        content = iset(content)
        content = (l for l in content
                   if not any(l.startswith(k) for k in ignore_kws))
        content = (l.split('#')[0] for l in content)
        content = (l.strip() for l in content)
        content = (l for l in content if l != '')
        return content


    @staticmethod
    def get_ss_tcs(content):
        """
        Get information from content about variables (ss), traces (tcs),
        and other extra info

        Examples:
        sage: logger.set_level(VLog.INFO)

        sage: (ss_arr,tcs_arr), (ss_num, tcs_num) = ReadFile.get_ss_tcs(['x y z w', '3 7 9.99999999 [8,9]', '7 8 12 [2,3]', '-1 9.2 8 [[5,7],[1,-2]]'])
        dig_miscs:Warn:possible rounding imprec values .. skip
        ['3', '7', '9.99999999', '[8,9]']
        dig_miscs:Warn:Skipping 1 tcs

        sage: ss_num
        [x, y, z]
        sage: ss_arr
        [w]
        sage: tcs_num
        [OrderedDict([(x, 7), (y, 8), (z, 12)]),
        OrderedDict([(x, -1), (y, 46/5), (z, 8)])]

        sage: _ = ReadFile.get_ss_tcs(['x y z w', '3 7 9 [8,9]', '7 8 12', '-1 9.2 [[5,7],[1,-2]]'])
        dig_miscs:Warn:# of vals 3 does not match # of vars 4 .. skip
        ['7', '8', '12']
        dig_miscs:Warn:# of vals 3 does not match # of vars 4 .. skip
        ['-1', '9.2', '[[5,7],[1,-2]]']
        dig_miscs:Warn:Skipping 2 tcs

        sage: _ = ReadFile.get_ss_tcs(['x y z w', '3 7 9 [8, 9]', '7 8 12', '-1 9.2 [[5,7],[1,-2]]'])
        Traceback (most recent call last):
        ...
        AssertionError: '[8,' is not a number
        """

        content = [l.split() for l in content] #'1 2 3' => ['1','2','3']
        ss = content[0] #var symbols are on the first line
        tcs = content[1:]  #the rest are traces

        #vars       
        assert not is_empty(ss), 'ss cannot be []'
        ss = map(ReadFile.strToVar, ss)

        #traces
        #checking for possible rounding imprecision
        ReadFile.check_rounding.clear_cache()
        nskip = 0
        tcs_ = []
        for tc in tcs:
            if not all(ReadFile.check_rounding(t) for t in tc):
                logger.warn('possible rounding imprec values .. skip\n{}'.format(tc))
                nskip = nskip + 1
                continue

            if len(tc) != len(ss):
                logger.warn('# of vals {} does not match # of vars {} .. skip\n{}'
                            .format(len(tc),len(ss), tc))
                nskip = nskip + 1
                continue
                
            tcs_.append(tc)

        tcs = tcs_

        if nskip > 0: 
            logger.warn('Skipping {} tcs'.format(nskip))

        assert not is_empty(tcs), 'tcs cannot be []'
        assert len(ss) == len(tcs[0])
        
        #determine types of symbols
        idx_arr, idx_num = [],[]
        for i,t in enumerate(tcs[0]):
            if ReadFile.is_array(t):
                idx_arr.append(i)
            else:
                idx_num.append(i)
                
        ReadFile.strToRatOrList.clear_cache()                        
        if len(idx_arr) == len(ss): #all array symbs
            ss_arr = ss
            ss_num = []
                        
            tcs_arr = [[ReadFile.strToRatOrList(t, is_num_val=False) 
                        for t in tc] 
                       for tc in tcs] 
                                                
            tcs_num = []
            
        elif len(idx_num) == len(ss): #all numerical symbs
            ss_arr = []
            ss_num = ss
            
            tcs_arr = []
            tcs_num = [[ReadFile.strToRatOrList(t, is_num_val=True) 
                        for t in tc] 
                       for tc in tcs]                        
                                                    
        else: #mixed types
            ss_arr = [ss[i] for i in idx_arr]        
            ss_num = [ss[i] for i in idx_num]
            
            tcs_arr, tcs_num = [], []
            for tc in tcs:
                tcs_arr.append([ReadFile.strToRatOrList(tc[i], is_num_val=False) 
                                for i in idx_arr])
                tcs_num.append([ReadFile.strToRatOrList(tc[i], is_num_val=True) 
                                for i in idx_num])

        tcs_arr = vset(tcs_arr, str)
        tcs_num = vset(tcs_num, str)

        tcs_arr = [OrderedDict(zip(ss_arr,tc)) for tc in tcs_arr]
        tcs_num = [OrderedDict(zip(ss_num,tc)) for tc in tcs_num]
        
        ss_arr = [s for s in sorted(ss_arr, key=str) if 'dummy' not in str(s)]
        ss_num = [s for s in sorted(ss_num, key=str) if 'dummy' not in str(s)]
      
        return (ss_arr, tcs_arr), (ss_num, tcs_num)


    @staticmethod
    def get_xinfo(content):
        """
        Examples:

        sage: var('x y g f d')
        (x, y, g, f, d)

        sage: sorted(ReadFile.get_xinfo(['l1', 'Assume: x >= y + 10', 'Assume: x + y > 20', \
        'Global: g','Global: f','Global: d']).items())
        [('Assume', [x >= y + 10, x + y > 20]), ('Const', []),
        ('Expect', []), ('ExtFun', []), ('ExtVar', []), 
        ('Global', ['g', 'f', 'd']),
        ('Input', []), ('Output', [])]

        sage: sorted(ReadFile.get_xinfo([]).items())
        [('Assume', []),
        ('Const', []), ('Expect', []), ('ExtFun', []), ('ExtVar', []),
        ('Global', []), ('Input', []), ('Output', [])]

        """

        xinfoKs = ['Assume', 'Expect', 'Global',
                   'Output', 'Input', 'Const', 
                   'ExtFun', 'ExtVar']

        xinfoVs = []

        for k in xinfoKs:
            content, v = vpartition(content,
                                    lambda l: l.lower().startswith(k.lower()))

            xinfoVs = xinfoVs + [v]

        try:
            xinfoVs = [[xi_.split(':')[1].strip() for xi_ in xi]
                       for xi in xinfoVs]
        except IndexError:
            msg = 'incorrect xinfo format (missing ":" somewhere ?)'
            msg = msg + '\n' + \
                '\n'.join([g for g in flatten(xinfoVs) if ':' not in g])
            raise AssertionError(msg)

        xinfo = OrderedDict([(k,v) for k,v in zip(xinfoKs,xinfoVs)])

        xinfo['Assume'] = [eval(assume) for assume in xinfo['Assume']]

        return xinfo


class Miscs(object):

    @staticmethod
    def keys_to_str(ls):
        """
        Convert key in dictionary to str, {a:5} => {'a' => 5}

        Input: list of dicts (could be some non-dict elem)
        Output: list of dicts with keys as string

        Examples:

        sage: Miscs.keys_to_str([{var('a'):5},{var('b'):7},5])
        [OrderedDict([('a', 5)]), OrderedDict([('b', 7)]), 5]

        """
        return [(OrderedDict([(str(k),c) for k,c in l.iteritems()])) 
                if is_dict(l) else l
                for l in ls]


    @staticmethod
    def get_sols(sols, sol_format):
        """
        Construct a list of properties from the inputs sols and sol_format


        Examples:

        #when sols are in dict form
        sage: var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        sage: Miscs.get_sols([{uk_0: -2*r14 + 7/3*r15, uk_1: -1/3*r15, \
        uk_4: r14, uk_2: r15, uk_3: -2*r14}],\
        uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        #when sols are not in dict form
        sage: Miscs.get_sols([[uk_0== -2*r14 + 7/3*r15, \
        uk_1== -1/3*r15, uk_4== r14, uk_2== r15, uk_3== -2*r14]],\
        uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        sage: Miscs.get_sols([],uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        []
        """
        if __debug__:
            assert is_sage_expr(sol_format), sol_format
        if sols is None or is_empty(sols):
            return []

        if len(sols) > 1:
            logger.warn('get_sols: len(sols) = {}'.format(len(sols)))
            logger.warn(sols)

        def f_eq(d):
            if is_list(d):
                f_ = sol_format
                for d_ in d:
                    f_ = f_.subs(d_)
                rhsVals = vset([d_.rhs() for d_ in d])
                uk_vars = get_vars(rhsVals)
            else:
                f_ = sol_format(d)
                uk_vars = get_vars(d.values()) #e.g., r15,r16 ...

            if is_empty(uk_vars):
                return f_

            iM = identity_matrix(len(uk_vars)) #standard basis
            rs = [OrderedDict(zip(uk_vars,l)) for l in iM.rows()]
            rs = [f_(r) for r in rs]
            return rs

        sols = flatten([f_eq(s) for s in sols])

        #remove trivial (tautology) str(x) <=> str(x)
        sols = [s for s in sols
                if not (s.is_relational() and str(s.lhs()) == str(s.rhs()))]

        return sols


    @staticmethod
    def gen_template(ts, rv, op=operator.eq, prefix=None,
                     ret_coef_vs=False):

        """
        Generates template from terms.

        Examples:

        sage: var('a,b,x,y')
        (a, b, x, y)

        sage: Miscs.gen_template(ts=[1, a, b, x, y],rv=0,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0

        sage: Miscs.gen_template(ts=[1, x, y],rv=0,\
        op=operator.gt,prefix=None,ret_coef_vs=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        sage: Miscs.gen_template(ts=[1, a, b, x, y],rv=None,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0

        sage: Miscs.gen_template(ts=[1, a, b, x, y],rv=0,prefix='hi')
        a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0

        sage: var('x1')
        x1
        sage: Miscs.gen_template(ts=[1, a, b, x1, y],rv=0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict in gen_template

        """

        if prefix is None:
            prefix = 'uk_'

        prefix = prefix + "%d"

        coefVars = [var(prefix%i) for i in srange(len(ts))]

        assert len(set(ts) & set(coefVars)) == 0,\
            'name conflict in gen_template'

        template = sum(map(prod,zip(coefVars,ts)))

        if rv is not None:
            template = op(template,rv) #eqt

        if ret_coef_vs:
            return template, coefVars
        else:
            return template


    @staticmethod
    def instantiate_template(template, tcs):
        """
        Instantiates a (potentially nonlinear) relation with traces to obtain
        a set of linear relations.

        Examples:

        sage: var('a,b,x,y,uk_0,uk_1,uk_2,uk_3,uk_4')
        (a, b, x, y, uk_0, uk_1, uk_2, uk_3, uk_4)

        sage: Miscs.instantiate_template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, \
        [{y: 4, b: 2, a: 13, x: 1}, {y: 6, b: 1, a: 10, x: 2}, {y: 8, b: 0, a: 7, x: 3}, \
        {y: 10, b: 4, a: 19, x: 4}, {y: 22, b: 30, a: 97, x: 10}, \
        {y: 28, b: 41, a: 130, x: 13}])
        [uk_0 + 13*uk_1 + 2*uk_2 + uk_3 + 4*uk_4 == 0,
        uk_0 + 10*uk_1 + uk_2 + 2*uk_3 + 6*uk_4 == 0,
        uk_0 + 7*uk_1 + 3*uk_3 + 8*uk_4 == 0,
        uk_0 + 19*uk_1 + 4*uk_2 + 4*uk_3 + 10*uk_4 == 0,
        uk_0 + 97*uk_1 + 30*uk_2 + 10*uk_3 + 22*uk_4 == 0,
        uk_0 + 130*uk_1 + 41*uk_2 + 13*uk_3 + 28*uk_4 == 0]

        """

        if __debug__:
            assert is_sage_expr(template), template
            assert is_list(tcs) and all(is_dict(tc) for tc in tcs), tcs

        #logger.debug('Create equations from {} traces'.format(len(tcs)))
        
        eqts = [template.subs(tc) for tc in tcs]
        eqts = vset(eqts) #sys of lin eqts
        return eqts


    @staticmethod
    def solve_eqts(ts,rv,ds):
        """
        shortcut of some functions often called together
        ts: terms
        ds: dictionary containing traces

        Examples:
        sage: var('x y')
        (x, y)
        sage: ts = [1, x, y, x^2, x*y, y^2]
        sage: rv = 0
        sage: ds = [{y: 1, x: 1}, {y: 2, x: 4}, {y: 4, x: 16}, {y: 0, x: 0}, {y: 8, x: 64}, {y: 9, x: 81}, {y: -1, x: 1}, {y: 5, x: 25}]
        sage: assert Miscs.solve_eqts(ts,rv,ds) == [y**2 - x == 0]

        """

        def _solve(eqts,ss):
            assert len(eqts) >= len(ss),\
                "eqts {} <= unknown coefs {}".format(len(eqts),len(ss))

            logger.debug('Solve {} (uniq) eqts for {} unknowns'
                         .format(len(eqts), len(ss)))

            rs = solve(eqts, *ss, solution_dict=True)
            return rs

        assert len(ds) >= len(ts),\
            "traces {} < terms {}".format(len(ds),len(ts))

        template, uks = Miscs.gen_template(ts=ts, rv=rv, ret_coef_vs=True)
        eqts = Miscs.instantiate_template(template, tcs=ds)
        try:
            rs = _solve(eqts,ss=uks)
            rs = Miscs.get_sols(rs,template)
            return rs
        except Exception as why:
            logger.warn(why)
            return []


    @staticmethod
    def solve_eqts_(ts,rv,ds):
        rs = Miscs.solve_eqts(ts,rv,ds)
        return rs if is_empty(rs) else {rs[0].rhs():rs[0].lhs()}


    @staticmethod
    def elim_denom(p):
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        Examples:

        sage: var('x y z')
        (x, y, z)

        sage: Miscs.elim_denom(3/4*x^2 + 7/5*y^3)
        28*y^3 + 15*x^2

        sage: Miscs.elim_denom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
        -252*x^2 - 7*z^2 >= 168*y + 24

        sage: Miscs.elim_denom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
        -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

        sage: Miscs.elim_denom(x + y == 0)
        x + y == 0

        """
        try:
            f = lambda g : [Integer(o.denominator()) for o in g.operands()]
            denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
            return p * lcm(denoms)
        except TypeError:
            return p

    @staticmethod
    def senumerate(ls):
        return ((ZZ(i),x) for i,x in enumerate(ls))

    #############################
    @staticmethod
    def _f(ls, op, is_real):
        """

        """
        if any(l is None for l in ls) or is_empty(ls):
            return None

        import z3
        from smt_z3py import SMT_Z3

        rs = [SMT_Z3.to_z3exp(l,is_real=is_real) if is_sage_expr(l) else l
              for l in ls]

        if len(rs) == 1:
            rs = rs[0]
        else:
            rs = z3.And(rs) if op == 'and' else z3.Or(rs)

        return rs

    @staticmethod
    def tmap(f,A):
        """
        Examples

        sage: Miscs.tmap(str,[1,2,[[3],5,[]],[6]])
        ['1', '2', [['3'], '5', []], ['6']]
        """
        if is_iterable(A):
            return [Miscs.tmap(f,a) for a in A]
        else:
            return f(A)

    @staticmethod
    def travel(A):
        """
        Examples:

        sage: Miscs.travel([1,[0,[5]],8,[8]])
        [([0], 1), ([1, 0], 0), ([1, 1, 0], 5), ([2], 8), ([3, 0], 8)]
        """
        if __debug__:
            assert A is not None, A
                    
        if is_empty(A): #if CM.is_none_or_empty(A):
            return []

        #if A is already the traveled info
        if is_tuple(A[0]):
            return A

        else:  #otherwise get the traveled info
            def _travel(A,idx,rs):
                for i,c in Miscs.senumerate(A):
                    if is_iterable(c):
                        rs = _travel(c,idx+[i],rs)
                    else:
                        rs = rs + [(idx+[i],c)]
                return rs

            results = _travel(A,[],[])
            return results

    @staticmethod
    def getListIdxs(A):
        """
        Return the (nested) order of A in dict format where dkey is value v
        of A and the dvalue is the list of indices I of A containing v

        Examples:

        sage: assert Miscs.getListIdxs([1,[0,[5]],8,[8]]) == \
        OrderedDict([(1, [(0,)]), (0, [(1, 0)]), (5, [(1, 1, 0)]), (8, [(2,), (3, 0)])])
        sage: assert Miscs.getListIdxs([]) == OrderedDict()
        """

        idxs_vals = Miscs.travel(A)
        vals_idxs = [(v,tuple(idx)) for idx,v in idxs_vals]
        return CM.create_dict(vals_idxs)

    @staticmethod
    def getVals(A):
        return [v for _,v in Miscs.travel(A)]

    @staticmethod
    def getIdxs(A):
        return [v for v,_ in Miscs.travel(A)]

    @staticmethod
    def getValFromIdx(A,idx):
        """
        Examples:

        sage: Miscs.getValFromIdx([1,[0,[5]],8,[8]],[3,0])
        8
        """
        R_ = A[idx[0]] if is_iterable(idx) else A[idx]
        if not is_list(idx) or len(idx)==1:
            return R_
        else:
            return Miscs.getValFromIdx(R_,idx[1:])


    @staticmethod
    def getIdxFromVal(A,v,idfun=lambda x:x):
        """
        Examples:

        sage: Miscs.getIdxFromVal([1,[0,[5]],8,[8]],'8',idfun=str)
        [[2], [3, 0]]
        sage: Miscs.getIdxFromVal(Miscs.travel([1,[0,[5]],8,[8]]),'8',idfun=str)
        [[2], [3, 0]]
        """
        return [idx for idx,c in Miscs.travel(A) if idfun(c)==v]


    @staticmethod
    def reach(vss, rdata):
        """
        Checks if values in vss can be found from rdata and performs
        branching if necessary in the case of multiple occurences.

        The output is a list of size == dim of rdata.

        Examples:

        sage: Miscs.reach([(8,), (15,), (7,)], \
        rdata = {8:[(10,), (4,)], 15:[(8,), (3,)], 7:[(2,)]})
        [[(10, 4), (8, 3), (2,)]]

        #10 is found at either (3,) or (8,), written as (3,8)
        #The output is a list of size 1 since the dim of rdata is 1
        sage: Miscs.reach([(10,)], rdata = {10:[(3,), (8,)]})
        [[(3, 8)]]

        #10 is found at either (3,7) or (8,2), written as [(3,8)],[(7,2)]
        sage: Miscs.reach([(10,)], rdata = {10:[(3,7),(8,2)]})
        [[(3, 8)], [(7, 2)]]

        #10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        sage: Miscs.reach([(10,4)], \
        rdata = {4:[(0,4)], 10:[(3,7),(8,2)]})
        [[(3, 8, 0)], [(7, 2, 4)]]

        #10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        #8 or 3 is found at either (2,6) or (1,2), written as [(2,1)],[(6,2)]
        #2 is found at either (2,0) or (1,7),  written as [(2,1)],[(0,7)]
        #all together, written as [[(3,8,0),(2,1),(2,1)], [(7,2,4),(6,2),(0,7)]]
        #The output is 2 lists. Each list has 3 (# of inputs) tuples.

        sage: Miscs.reach([(10,4),(8,3),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (0, 7)]]

        sage: Miscs.reach([(10,4),(8,3),(8,3)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (6, 2)]]

        sage: Miscs.reach([(10,5),(8,3),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8), (2, 1), (2, 1)], [(7, 2), (6, 2), (0, 7)]]

        sage: Miscs.reach([(10,4),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2,), (2, 1)], [(7, 2, 4), (6,), (0, 7)]]

        sage: Miscs.reach([(100,14),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []
        
        sage: Miscs.reach([(100,4),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(0,), (2,), (2, 1)], [(4,), (6,), (0, 7)]]

        sage: Miscs.reach([(100,4),(8,13),(100,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []
        
        """
        if __debug__:
            assert is_list(vss) and all(is_tuple(vs) for vs in vss), vss


        _getIdxs = lambda vs: [rdata[v] for v in vs if v in rdata]
        rs = [_getIdxs(vs) for vs in vss]


        if any(is_empty(r_) for r_ in rs):
            return []
        else:
            rs = [flatten(r_,list) for r_ in rs]
            rs = [zip(*r_) for r_ in rs]
            rs = zip(*rs)
            rs = [list(r_) for r_ in rs]
            assert len(rs) == len(rdata[rdata.keys()[0]][0])
            return rs


class Tree(object):

    def __init__(self, args):
        """
        Tree is a leaf (None or Expression)  or a dict {'root':, 'children':[..]}

        sage: Tree({'root':None,'children':[None,None]})
        Traceback (most recent call last):
        ...
        AssertionError: args['roots'] cannot be None

        sage: var('y')
        y
        sage: print Tree({'root':'B', 'children':[{'root':'C','children':[x + 2*y]}]})
        B[C[x + 2*y]]

        """

        if is_dict(args) and 'coef' not in args and 'first_idx' not in args:

            assert 'root' in args and 'children' in args, 'improper tree format: %s'%map(str,args)
            assert args.get('root') is not None, "args['roots'] cannot be None"
            assert is_list(args.get('children')), args
            assert not is_empty(args.get('children')), args.get('children')

            self.root = args.get('root')
            self.children = [c if isinstance(c,Tree) else Tree(c)
                             for c in args.get('children')]


            if 'commute' not in args or self.get_nchildren() == 1:
                self.commute = False
            else:
                self.commute = args.get('commute')

        else:  #leaf
            self.root = args
            self.children = None
            self.commute = False
            self.data = {}

    def __eq__(self,other):
        """
        sage: var('y')
        y
        sage: Tree(x+y+7) == Tree(7+x+y)
        True
        sage: Tree({'root':x+y+7,'children':[None]}) == Tree({'root':x+y+7,'children':[None,None]})
        False
        sage: Tree({'root':x+y+7,'children':[None]}) == Tree({'root':x+y+7,'children':[None]})
        True
        """
        return type(other) is type(self) and self.__dict__ == other.__dict__

    def __ne__(self,other):
        """
        sage: var('y')
        y
        sage: Tree(x+y+7) != Tree(7+x+y)
        False
        sage: Tree(x+y+7) != Tree(x+y)
        True
        """
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.__str__())

    def __str__(self, leaf_content=None):
        """
        Examples:
        sage: print Tree(None)
        None

        sage: print Tree({'root':'a','children':[None,None]})
        a[None][None]

        sage: print Tree({'root':'a','children':[None,{'root':'b','children':[None]}]})
        a[None][b[None]]

        sage: print Tree({'root':'xor','children':[None, \
        {'root':'b','children':[None]}, {'root':x,'children':[None]}]})
        xor(None,b[None],x[None])

        sage: print Tree(x^2 + 7)
        x^2 + 7

        sage: print Tree(x).__str__(leaf_content='hi')
        hi

        sage: var('y')
        y
        sage: print Tree(x).__str__(leaf_content={x:y+7})
        y + 7


        sage: print Tree({'root':'x','children':[None]})
        x[None]
        sage: print Tree({'root':x,'children':[None]})
        x[None]
        """
        try:
            children = [c.__str__(leaf_content=leaf_content) for c in self.get_children()]

            if self.get_root() in ExtFun.efdict:
                rs = '(%s)'%(','.join(children))
            else:
                rs = ''.join(['[%s]'%c for c in children])

            rs = str(self.get_root()) + rs
            return rs

        except Exception:
            if leaf_content is None:
                return str(self.get_root())
            else:
                if is_dict(leaf_content):
                    if is_sage_expr(self.get_root()):
                        return str(self.get_root()(leaf_content))
                    else:
                        str(self.get_root())
                else:
                    return str(leaf_content)


    def get_root(self):
        return self.root

    def get_nchildren(self):
        return len(self.children)

    def get_children(self):
        return self.children

    def is_commute(self):
        return self.commute

    @staticmethod
    def leaf_tree():
        return Tree(None)

    def is_node(self):
        """
        sage: Tree({'root':'a','children':[None,None]}).is_node()
        True
        """
        return all(c.is_leaf() for c in self.get_children())


    def is_leaf(self):
        """
        sage: Tree({'root':'a','children':[None,None]}).is_leaf()
        False
        """
        return self.get_children() is None

    ###



    def get_non_leaf_nodes(self, nl_nodes=[]):
        """
        Returns the *names* of the non-leaves nodes

        sage: print Tree({'root':'a','children':[None,None]}).get_non_leaf_nodes()
        ['a']

        sage: Tree({'root':'a','children':[None, \
        {'root':'b','children':[None,None]}, \
        {'root':'c','children':[None]}, \
        {'root':'d','children':[None,None]}]}).get_non_leaf_nodes()
        ['a', 'b', 'c', 'd']
        """
        if self.is_leaf():
            return nl_nodes
        else:
            nl_nodes_ = [c.get_non_leaf_nodes(nl_nodes)
                         for c in self.get_children()]
            nl_nodes = [self.get_root()] + flatten(nl_nodes_)
            return nl_nodes


    def get_leaves(self):
        """
        TOCHECK

        Examples:

        sage: Tree.leaf_tree().get_leaves()
        [(None, None, [])]

        sage: rs = Tree({'root':'A','children': [ \
        {'root':'C','children':[None,None]}, \
        {'root':'D','children':[None]}]}).get_leaves()

        sage: [(str(p),idx,tid) for p,idx,tid in rs]
        [('C[None][None]', 0, ['A', 0, 'C', 0]),
        ('C[None][None]', 1, ['A', 0, 'C', 1]),
        ('D[None]', 0, ['A', 1, 'D', 0])]
        """

        def _get_leaves(t,p,idx,tid):

            assert isinstance(t,Tree)

            if t.is_leaf():  #leaf
                return [(p,idx,tid)]
            else:
                results = [_get_leaves(child, t, idx_, tid + [t.get_root(), idx_])
                           for idx_, child in Miscs.senumerate(t.get_children())]

                results = flatten(results,list)
                return results


        return _get_leaves(self,p=None,idx=None,tid=[])




    def gen_root_trees(self, nodes, vss, blacklist, data):
        """
        Generates trees from nodes whose root is self.root

        blacklist {a: L} disallows a[b[..]] and a[[c..]]
        where {b,c} in L and only allows
        [a[x[..]]] where x is not in L

        so for example if we want to force a to be a Leaf then {a:L}
        where L is all variables (except None).
        This allows the removal of an extra whitelist

        also if we have {a: L} where L is all variablles (except a) then basically
        we disallow the tree with root 'a' since this says 'a' cannot have
        any children (including) leaf.


        Examples

        sage: t = Tree({'root':'a','children':[None,None]})
        sage: nodes = [Tree({'root':'b','children':[None,None]})]
        sage: map(str,t.gen_root_trees(nodes, vss=None, blacklist = {}, data={}))
        ['a[b[None][None]][b[None][None]]',
        'a[b[None][None]][None]',
        'a[None][b[None][None]]',
        'a[None][None]']

        sage: t = Tree({'root':'B','children':[None]})

        sage: nodes = [ \
        Tree({'root':'C','children':[None,None]}), \
        Tree({'root':'D','children':[None]})]

        sage: vss=[(8,),(15,),(7,)]
        sage: data = {'C':{8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]},\
        'D':{8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}, 'B':{8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}}

        sage: map(str,t.gen_root_trees(nodes,vss=vss, blacklist={}, data=data))
        ['B[C[D[None]][None]]', 'B[C[None][None]]', 'B[None]']

        """
        if __debug__:
            assert (is_list(nodes) and
                    all(isinstance(x,Tree) and x.is_node() for x in nodes)), nodes

            assert (vss is None or
                    (is_list(vss) and all(is_tuple(v) for v in vss)))

            assert is_dict(blacklist), blacklist


        if vss is not None:
            children_vss = Miscs.reach(vss, data[self.get_root()])
            if is_empty(children_vss):
                return []
        else:
            children_vss = [None] * self.get_nchildren()

        if nodes:

            children = nodes + [Tree.leaf_tree()]

            children = [c for c in children \
                            if self.get_root() not in blacklist or \
                            c.get_root() not in blacklist[self.get_root()]]


            #recursive call
            def _gt(r_, nodes_, vss_):
                if r_.is_leaf():
                    return [r_]
                else:
                    return r_.gen_root_trees(nodes=nodes_,vss=vss_,
                                             blacklist=blacklist,
                                             data=data)


            children = [[_gt(c, CM.vsetdiff(nodes,[c]), vs) for c in children]
                        for vs in children_vss]


            children = [flatten(c) for c in children]

            assert len(children) == self.get_nchildren()

            combs = CartesianProduct(*children)

            if self.is_commute():
                """
                (T1, T2, T3) is equiv to (T1, T3, T2)
                """
                combs = vset(combs,idfun=Set)


            rs = [Tree({'root':self.get_root(),
                        'children': c,
                        'commute': self.is_commute()})
                         for c in combs]

        else:
            rs = [Tree({'root':self.get_root(),
                        'children':[Tree.leaf_tree()] * self.get_nchildren(),
                        'commute': self.is_commute()})]


        return rs


    def gen_formula(self, v, data):
        """
        Generate a formula recursively to represent the data structure of tree based on
        input value v and data.


        sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
        (_B_0_C_0__i0, _B_0_C_0__i1)


        sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81,\
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7


        sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81, \
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))


        sage: Tree({'root':'add','children':[\
        {'root':'C', 'children':[{'root':'_add_0_C_','children':[100,200]}]},\
        {'root':'D', 'children':[{'root':'_add_1_D_','children':[100,200]}]}]}).gen_formula(v=17, \
        data = {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}})


        """

        if is_sage_expr(self.get_root()):
            return self.get_root() == v

        elif is_dict(self.get_root()) and 'first_idx' in self.get_root():
            #special case {'first_idx':i,'coef':z}
            if v == 0:
                t0 = self.get_root()['coef'] == 0
                t1 = self.get_root()['first_idx'] == 1
                return Miscs._f([t0,t1],'and',is_real=False)
            else:
                return self.get_root()['coef'] == v
        else:
            try:
                idxs = data[self.get_root()][v]
            except KeyError: #not reachable, no rel
                return None


            orRs = []
            for idx in idxs:
                andRs = []
                for v_,a_ in zip(idx,self.get_children()):
                    p_ = a_.gen_formula(v_,data)

                    if p_ is None:
                        andRs = None
                        break
                    andRs.append(p_)


                if andRs is not None:
                    assert len(andRs)>0
                    andRs = Miscs._f(andRs,'and',is_real=False)
                    orRs.append(andRs)

            orRs = Miscs._f(orRs,'or',is_real=False)
            return orRs

    ##### Static methods for Tree #####

    @staticmethod
    def gen_trees(nodes, vss, blacklist, data):
        """
        Generates nestings from a set of nodes. E.g., given nodes [a,b,c],
        returns all nestings, e.g. [{a,[b,c],{a,[c,b]}},{b,[a,c]} ..

        Examples:

        sage: nodes = [\
        Tree({'root':'A','children':[None]}), \
        Tree({'root':'B','children':[None,None]}), \
        Tree({'root':'C','children':[None,None,None]})]
        sage: len(Tree.gen_trees(nodes=nodes,vss=None,blacklist={},data={}))
        477

        """
        if __debug__:
            assert is_list(nodes) and \
                all(isinstance(x,Tree) and x.is_node() for x in nodes)

            assert vss is None or \
                (is_list(vss) and all(is_tuple(v) for v in vss))

            assert is_dict(blacklist), blacklist



        def _gt(t):
            ts = t.gen_root_trees(nodes     = CM.vsetdiff(nodes,[t]),
                                  vss       = vss,
                                  blacklist = blacklist,
                                  data      = data)
            return ts


        trees = [ _gt(node) for node in nodes]
        trees = flatten(trees)

        if __debug__:
            assert all(isinstance(t,Tree) for t in trees)


        return trees


class AEXP(object):

    def __init__(self,lt,rt):
        """
        Initialize AEXP (Array Expression) which has the form left_tree = right_tree,
        e.g.  A[None][None] = B[C[None][None]][D[None]]

        Examples:
        _ = AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        sage: _ = AEXP(Tree({'root':'v','children':[None]}), \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        sage: _ = AEXP({'root':'v','children':[{'root':'a','children':[None]}]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})
        Traceback (most recent call last):
        ...
        AssertionError: left tree has to be a node tree

        """


        if not isinstance(lt,Tree):
            lt = Tree(lt)
        if not isinstance(rt,Tree):
            rt = Tree(rt)

        assert lt.is_node(), 'left tree has to be a node tree'

        self.lt = lt
        self.rt = rt

    def __str__(self,leaf_content=None,do_lambda_format=False):
        """
        Returns the str of AEXP

        leaf_content: {},None,str
        Instantiates leaves of rt with leaf_content, e.g. A[x], leaf_info={x:5} => A[5]

        do_lambda_format: T/F
        Returns a lambda format of array expressions for evaluation

        Examples:

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]}).__str__()
        'v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,None,None]}]}).__str__(do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,None,x+7]}]}).__str__(leaf_content={x:5},do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[None][None][12]]'

        sage: var('y')
        y

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,{'root':'c',\
        'children':[x-y,None]}, x+7]}]}).__str__(leaf_content={x:5,y:7},\
        do_lambda_format=False)
        'v[i1] == a[x3[None][c[-2][None]][12]]'

        """

        def get_idx_strs(lt):
            """
            Examples
            #sage: Tree({'root':'xor','children':[None,None,None]}).get_str_formats()
            ([1, 2, 3], '[i1][i2][i3]', 'i1,i2,i3')
            """

            idxs = [(i+1) for i in srange(lt.get_nchildren())]
            iformat = ''.join(['[i%s]'%li for li in idxs]) #[i][j]
            aformat = ','.join(['i%s'%li for li in idxs])  #i,j
            return idxs, iformat, aformat

        l_idxs, l_iformat, l_aformat = get_idx_strs(self.lt)

        if leaf_content is None:
            r_idxs = "(%s)_"%l_aformat
            rt = self.rt.__str__(leaf_content=r_idxs)
        else:
            assert is_dict(leaf_content), leaf_content
            rt = self.rt.__str__(leaf_content=leaf_content)


        rs = '%s%s == %s'%(self.lt.root,l_iformat,rt)

        if do_lambda_format:
            l_idxs_ = ','.join(['i%s'%li for li in l_idxs])
            nodes = [self.lt.get_root()]  + vset(self.rt.get_non_leaf_nodes())
            lambda_ = 'lambda %s,%s' %(','.join(nodes),l_aformat)
            rs= '%s: %s'%(lambda_,rs)

        return rs


    def is_ok(self, xinfo):
        """
        Return True if this aexp is fine. Otherwise, returns False, which marks
        it for pruning.

        e.g., Those that do not contain the input variables
        """

        #all inputs must be in rt
        roots = self.rt.get_non_leaf_nodes()
        rs = all(iv in roots for iv in xinfo['Input'])
        return rs


    def gen_smt_formula(self, data):
        """
        todo: combine both gen_template & gen_formula

        returns a SMT formula from the aex wrt to data
        """
        pass


    def gen_template(self, idxs_vals=None, special=False):
        """
        special = True then it means we only have 1 data to compare against
        thus if the pass in indices of the leaves are 0's  , the result will be  z + 0*i = 0
        which then just gives z = 0, doesn't contribute to anything if we have only 1 data.
        Thus special flag turns the result z + 0*i = 0 into z = 0 and i = 1.

        Examples:

        sage: lt = Tree({'root':'R','children':[None,None,None]})
        sage: rt = Tree({'root': 'add', \
        'children': [{'root': 'C', 'children': [None]}, \
        {'root': 'D', 'children': [None]}]})
        sage: rs = AEXP(lt,rt).gen_template()
        sage: print rs.lt; print rs.rt
        R[None][None][None]
        add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i3*i3 + _add_0_C_0__i0],D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i3*i3 + _add_1_D_0__i0])



        sage: rs = AEXP({'root':'R','children':[None,None]}, \
        {'root':'add', 'children':[{'root':'C','children':[None]}, \
        {'root':'D','children':[None]}]}).gen_template()
        sage: print rs.lt; print rs.rt
        R[None][None]
        add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i0],D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i0])

        sage: rs = AEXP({'root':'R','children':[None,None]}, \
        {'root':'add', 'children':[None,None]}).gen_template(idxs_vals=[0,0],special=False)
        sage: print rs.lt; print rs.rt
        R[None][None]
        add(_add_0__i0,_add_1__i0)
        """
        if __debug__:
            assert not special or all(x == 0 for x in idxs_vals)
            assert idxs_vals is not None or not special


        if idxs_vals is None:
            ts = [1] + [var('i%d'%(i+1)) for i in srange(self.lt.get_nchildren())]
        else:
            ts = [1] + list(idxs_vals)

        rt = deepcopy(self.rt)  #make a copy

        leaves = rt.get_leaves()
        leaves = [(p,idx,tid) for p,idx,tid in leaves if p is not None]


        for p,idx,tid in leaves:
            prefix = '_%s__i'%'_'.join(map(str,tid))
            if special:
                c = {'first_idx':var(prefix+str(1)),'coef':var(prefix+str(0))}
            else:
                c = Miscs.gen_template(ts,rv=None,prefix=prefix)

            p.children[idx] = Tree(c)
            assert isinstance(p,Tree)

        #rt.replace_leaf(tid=[], special=special, ts=ts, verbose=verbose)

        return AEXP(lt=self.lt,rt=rt)



    def peelme(self, data):
        """
        Go through each nesting (aexp), generate a SMT formula, and checks its satisfiability.


        Examples:

        sage: data = {'C':{1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]},\
        'B': {0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]}}

        sage: AEXP({'root':'A','children':[None]}, \
        {'root': 'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]']

        sage: data = {'C':{0:[(0,),(3,)],9:[(1,),(8,)],7:[(2,),(5,)], 1:[(4,)],8:[(6,)],17:[(7,)]},\
        'B':{71:[(5,),(7,)],74:[(6,),(8,)],81:[(17,)]},\
        'A':{71:[(0,)],74:[(1,)],81:[(2,)]}}
        sage: AEXP({'root':'A','children':[None]},\
        {'root':'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[i1 + 5]]']

        sage: data = {'A':{17:[(0,0)],8:[(0,1)],12:[(1,0)],3:[(1,1)]},\
        'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add': {17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}}
        sage: rs = AEXP({'root':'A','children':[None]}, \
        {'root':'add','children':[{'root':'C' , 'children':[None]}, \
        {'root':'D','children':[None]}]}).peelme(data=data)

        sage: print '\n'.join(rs)
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[3])
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[3])


        """

        _gen_template = lambda iv,sp: \
            self.gen_template(idxs_vals=iv,special=sp)


        vi = [[(v,ids) for ids in idxs]
              for v,idxs in data[self.lt.get_root()].items()]
        vi = flatten(vi,list)

        sts = [_gen_template(ids,sp = len(vi) == 1).rt for _,ids in vi]

        formula = [rh.gen_formula(v,data) for (v,_),rh in zip(vi,sts)]

        formula = Miscs._f(formula,'and',is_real=False)


        if formula is None:
            return None


        #from common_z3 import get_models
        from z3util import get_models
        ms = get_models(formula,k=10)
        if not is_list(ms): #no model, formula is unsat, i.e. no relation
            return None

        assert not is_empty(ms)

        from smt_z3py import SMT_Z3
        ds = [SMT_Z3.get_constraints(m,result_as_dict=True) for m in ms]

        #generate the full expression
        template = _gen_template(None,False)

        rs = [template.__str__(leaf_content=d, do_lambda_format=True)
              for d in ds]

        if __debug__:
            assert all(is_str(x) for x in rs)

        return rs



    ##### Static methods for AEXP #####

    @staticmethod
    def gen_aexps(nodes, xinfo, data):
        """
        arrs = [a,b,c]
        returns a=allpostrees(b,c)  , b = allpostrees(a,b)  , etc

        sage: nodes = map(Tree,[ \
        {'root':'A','children':[None]}, \
        {'root':'B','children':[None]}, \
        {'root':'C','children':[None]}])

        sage: data = {'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]},\
        'B':{0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]}}
        sage: aexps = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []}, data=data)
        sage: print map(str,aexps)
        ['A[i1] == B[C[(i1)_]]', 'A[i1] == B[(i1)_]']

        sage: nodes = map(Tree,[{'root':'A','children':[None]}, {'root':'C','children':[None]}, {'root':'B','children':[None]}])



        sage: aexps = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []}, data={})
        sage: print '\n'.join(['{}. {}'.format(i,a) for i,a in enumerate(aexps)])
        0. A[i1] == C[B[(i1)_]]
        1. A[i1] == C[(i1)_]
        2. A[i1] == B[C[(i1)_]]
        3. A[i1] == B[(i1)_]
        4. C[i1] == A[B[(i1)_]]
        5. C[i1] == A[(i1)_]
        6. C[i1] == B[A[(i1)_]]
        7. C[i1] == B[(i1)_]
        8. B[i1] == A[C[(i1)_]]
        9. B[i1] == A[(i1)_]
        10. B[i1] == C[A[(i1)_]]
        11. B[i1] == C[(i1)_]


        sage: nodes = map(Tree,[ \
        {'root':'A','children':[None]}, \
        {'root':'C','children':[None]}, \
        {'root':'B','children':[None]}])

        sage: aexps = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': ['C']}, data={})
        sage: print '\n'.join(['{}. {}'.format(i,a) for i,a in enumerate(aexps)])
        0. C[i1] == A[B[(i1)_]]
        1. C[i1] == A[(i1)_]
        2. C[i1] == B[A[(i1)_]]
        3. C[i1] == B[(i1)_]

        """
        if __debug__:
            assert is_list(nodes) and \
                all(isinstance(x,Tree) and x.is_node() for x in nodes)
            assert is_dict(xinfo)


        blacklist = AEXP.gen_blacklist(xinfo)

        #Generate nestings
        def _gt(nodes, ln):
            if ln.get_root() not in data:
                vss = None
            else:
                vss = data[ln.get_root()].keys()
                assert all(not is_iterable(v) for v in vss)

                vss = map(lambda v: tuple([v]),vss)

            rs =  Tree.gen_trees(nodes=nodes,vss=vss,
                                 blacklist=blacklist,
                                 data=data)

            return rs

        #Construct an AEXP
        def _ga(x):
            t = Tree({'root':x.get_root(), 'children':[None] * x.get_nchildren(),
                      'commute': x.is_commute()})

            return t

        if xinfo['Output']:
            #x = a[b[...]], x in output vars and a,b not in output vars
            anodes, lnodes = \
                CM.vpartition(nodes, lambda x: x.get_root() in xinfo['Output'])

            aexps = [[AEXP(_ga(ln),rn) for rn in _gt(anodes,ln)] for ln in lnodes]

        else:
            aexps= [[AEXP(_ga(ln),rn) for rn in _gt(CM.vsetdiff(nodes,[ln]),ln)]
                    for ln in nodes]

        aexps = flatten(aexps)

        #filter out unlikely array expressions
        aexps = [ae for ae in aexps if ae.is_ok(xinfo)]

        logger.debug('* gen_aexps [%s]: %d expressions generated'\
                     %(','.join(map(lambda x: str(x.get_root()),nodes)),len(aexps)))

        logger.detail('\n'.join('%d. %s'%(i,ae) for i,ae in Miscs.senumerate(aexps)))

        return aexps

    @staticmethod
    def gen_blacklist(xinfo):
        """
        Takes advantage of user inputs to reduce the number of generated nestings

        Examples:

        sage: AEXP.gen_blacklist({'All':['R','A','B','D','E','xor','g'], \
        'Input':['A','B'],'Output':['R'],'Global':[],'Const':[], \
        'ExtFun':['xor'],'Global':['g']})
        OrderedDict([('A', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('B', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('xor', [None]), ('g', [None]),
                     ('R', ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None])])

        """

        allVars    = xinfo['All']
        inputVars  = xinfo['Input']
        outputVars = xinfo['Output']
        globalVars = xinfo['Global']
        constVars  = xinfo['Const']
        extFuns    = [x for x in xinfo['ExtFun']]

        #Inputs must be leaves
        #e.g., a[i] = x[y[i']] is not possible
        #e.g., a[i] = xor[x[i'][y[i']]
        inputsLeaves = [{inp:allVars} for inp in inputVars]

        #Const must be leaves
        constLeaves = [{c:allVars} for c in constVars]

        #Extfuns are never leaves
        #e.g.,  r[i] = a[b[xor[i'][i']]]  is not possible
        extfunsNotLeaves = [{ef:[None]} for ef in extFuns]

        #Globals are never leaves
        globalsNotLeaves = [{gv:[None]} for gv in globalVars]

        #Outputs should never be part of the tree
        outputsNotInTree = [{oup:allVars + [None]} for oup in outputVars]

        ds = inputsLeaves+constLeaves + extfunsNotLeaves + \
            globalsNotLeaves + outputsNotInTree
        rs = CM.merge_dict(ds)

        return rs



class ExtFun(object):

    efdict = {
            'add'     : (lambda x,y: QQ(ZZ(x) + ZZ(y)), 2, True),
            'sub'     : (lambda x,y: QQ(ZZ(x) - ZZ(y)), 2, False), #not commute
            'xor'     : (lambda x,y: QQ(ZZ(x).__xor__(ZZ(y))), 2, True),
            'xor_xor' : (lambda x,y,z: QQ(ZZ(x).__xor__(ZZ(y)).__xor__(ZZ(z))), 3, True),
            'mod4'    : (lambda x: QQ(ZZ(x) % 4),   1, True),
            'mod255'  : (lambda x: QQ(ZZ(x) % 255), 1, True),
            'mul4'    : (lambda x: QQ(ZZ(x) * 4),   1, True),
            'div4'    : (lambda x: QQ(ZZ(x) // 4),  1, True)
            }

    def __init__(self, fn):
        """
        fn = 'add'
        """
        if __debug__:
            assert is_str(fn), fn
        
        self.fn = fn.strip()
        

    def __eq__(self, other):
        return type(other) is type(self) and self.__dict__ == other.__dict__

    def __ne__(self,other):
        return not self.__eq__(other)

    def __str__(self):
        return self.get_fname()

    def __hash__(self):
        return self.get_fname().__hash__()

    def get_fname(self):
        return self.fn

    def get_fun(self):
        """
        sage: ExtFun('xor').get_fun()(*[7,15])
        8
        sage: ExtFun('xor').get_fun()(8,9)
        1
        sage: ExtFun('xor').get_fun()(18,-9)
        -27
        sage: ExtFun('sub').get_fun()(128,1)
        127
        sage: ExtFun('sub').get_fun()(0,1)
        -1
        sage: ExtFun('xor').get_fun()(10,128)
        138
        sage: ExtFun('xor').get_fun()(128,10)
        138
        sage: ExtFun('mod4').get_fun()(128)
        0
        sage: ExtFun('mod4').get_fun()(127)
        3
        sage: ExtFun('mod4').get_fun()(1377)
        1
        sage: ExtFun('mod4').get_fun()(1378)
        2
        sage: ExtFun('mod4').get_fun()(1379)
        3
        sage: ExtFun('mod4').get_fun()(1380)
        0
        sage: ExtFun('div4').get_fun()(127)
        31
        sage: ExtFun('div4').get_fun()(128)
        32
        sage: ExtFun('div4').get_fun()(126)
        31
        """
        return ExtFun.efdict[self.get_fname()][0]

    def get_nargs(self):
        """
        Returns the number of function arguments

        Examples:
        sage: ExtFun('sub').get_nargs()
        2
        sage: ExtFun('something').get_nargs()
        Traceback (most recent call last):
        ...
        KeyError: 'something'

        """
        return ExtFun.efdict[self.get_fname()][1]

    def is_commute(self):
        """
        Returns true if the function is commutative

        sage: ExtFun('sub').is_commute()
        False
        sage: ExtFun('add').is_commute()
        True
        sage: ExtFun('something').is_commute()
        False
        """
        try:
            return ExtFun.efdict[self.get_fname()][2]
        except KeyError:
            """
            If we don't know anything about the function, then
            the default is non commutative.
            """
            return False

    def gen_data(self, avals, doDict):
        """
        Note: did not use caching because caching makes it slower.
        Probably because these functions are too simple that
        doesn't worth the caching overhead
        Examples:

        sage: ExtFun('add').gen_data([1,7,9,-1],doDict=False)
        [2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1]

        sage: ExtFun('add').gen_data([[1,7,9,-1]],doDict=False)
        [2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1]

        sage: ExtFun('add').gen_data([[1,7,9,-1]],doDict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (8, [(1, 7), (9, -1)]), (10, [(1, 9)]), (0, [(1, -1)]), (14, [(7, 7)]), (16, [(7, 9)]), (6, [(7, -1)]), (18, [(9, 9)]), (-2, [(-1, -1)])]))])

        sage: ExtFun('sub').gen_data([[1,2],[5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        sage: ExtFun('sub').gen_data([[1,2,5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        sage: ExtFun('sub').gen_data([1,2,5,6], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]

        sage: ExtFun('sub').gen_data([[1,2],[5,6]],doDict=True)
        OrderedDict([('sub', OrderedDict([(0, [(1, 1), (2, 2), (5, 5), (6, 6)]), (-1, [(1, 2), (5, 6)]), (-4, [(1, 5), (2, 6)]), (-5, [(1, 6)]), (1, [(2, 1), (6, 5)]), (-3, [(2, 5)]), (4, [(5, 1), (6, 2)]), (3, [(5, 2)]), (5, [(6, 1)])]))])

        sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=False)
        [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1]

        sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (3, [(1, 2)]), (4, [(1, 3), (2, 2)]), (5, [(1, 4), (2, 3)]), (6, [(1, 5), (2, 4), (3, 3)]), (7, [(1, 6), (2, 5), (3, 4)]), (8, [(1, 7), (2, 6), (3, 5), (4, 4)]), (9, [(1, 8), (2, 7), (3, 6), (4, 5)]), (10, [(1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]), (11, [(2, 9), (3, 8), (4, 7), (5, 6)]), (12, [(3, 9), (4, 8), (5, 7), (6, 6)]), (13, [(4, 9), (5, 8), (6, 7)]), (14, [(5, 9), (6, 8), (7, 7)]), (15, [(6, 9), (7, 8)]), (16, [(7, 9), (8, 8)]), (17, [(8, 9)]), (18, [(9, 9)])]))])
        """

        avals = vset(flatten(avals))
        alists = [avals] * self.get_nargs()
        idxs = CartesianProduct(*alists).list()
        fun_vals = [self.get_fun()(*idx) for idx in idxs]

        if doDict: #create dict
            cs = zip(fun_vals,idxs)
            cs = [(fv,tuple(idx)) for (fv,idx) in cs]

            d= CM.create_dict(cs)

            if self.is_commute():
                #[(1,2),(2,1),(2,2)] => [(1,2),(2,2)]
                d = OrderedDict([(k,vset(v,Set)) for k, v in d.items()])

            rs = OrderedDict()
            rs[self.get_fname()]=d

            logger.debug('fun: %s, fvals %d, idxs %d'\
                         %(self.get_fname(),len(d.keys()),len(idxs)))


        else:   #returns fun_vals as well as the orig avals
            rs =  vset(fun_vals + avals)

        return rs
  

    @staticmethod
    def gen_ef_data(extfuns,avals):
        """
        create representations for extfuns
        Note: the order of F matters (see example below when add,xor,xor_xor gens 63
        but xor,add,xor_xor gens 124.

        Examples

        sage: logger.set_level(VLog.DEBUG)
        sage: rs = ExtFun.gen_ef_data(map(ExtFun,['add','xor','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        dig_miscs:Debug:gen_ef_data([add,xor,xor_xor],|avals|=4)
        dig_miscs:Debug:fun: add, fvals 30, idxs 64
        dig_miscs:Debug:fun: xor, fvals 8, idxs 64
        dig_miscs:Debug:fun: xor_xor, fvals 16, idxs 1331
        30

        sage: rs = ExtFun.gen_ef_data(map(ExtFun,['xor','add','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        dig_miscs:Debug:gen_ef_data([xor,add,xor_xor],|avals|=4)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 64
        dig_miscs:Debug:fun: add, fvals 30, idxs 64
        dig_miscs:Debug:fun: xor_xor, fvals 95, idxs 2197
        8
        """

        logger.debug('gen_ef_data([{}],|avals|={})'
                     .format(','.join(map(str,extfuns)),len(flatten(avals))))


        if len(extfuns) == 1:
            F_avals = [avals]
        else:
            assert vall_uniq(map(lambda f: f.get_fname(),extfuns)), \
                'extfuns list cannot contain duplicate'

            F_rest = [CM.vsetdiff(extfuns,[f]) for f in extfuns]

            F_avals = [ExtFun.get_outvals(tuple(fs),tuple(avals))
                       for fs in F_rest]


        F_d = [fn.gen_data(f_aval,doDict=True)
               for fn,f_aval in zip(extfuns,F_avals)]

        return F_d

    @cached_function
    def get_outvals(extfuns,avals):
        """
        Recursive function that returns the all possible input values

        [f,g,h],[avals] =>  f(g(h(avals)))

        Examples:

        sage: ExtFun.get_outvals(tuple(map(ExtFun,['sub'])),tuple([1,2,256]))
        [0, -1, -255, 1, -254, 255, 254, 2, 256]
        sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor','add'])),tuple([1,2,256]))
        [2, 3, 257, 4, 258, 512, 1, 256]
        sage: ExtFun.get_outvals(tuple(map(ExtFun,['add','xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        """

        if __debug__:
            assert len(extfuns) >= 1
            assert all(isinstance(f, ExtFun) for f in extfuns)


        if len(extfuns) > 1:
            avals = ExtFun.get_outvals(extfuns[1:],avals)
        else:
            avals = extfuns[0].gen_data(avals,doDict=False)

        return avals
    
    @staticmethod
    def gen_extfuns(tc, xinfo):
        """
        Returns a list of dicts representing extfuns
        The values of the extfuns are customized over the given tc
        
        Examples:
        
        sage: logger.set_level(VLog.DEBUG)
        
        sage: ExtFun.gen_extfuns(tc={'X':[1,7,9,15]}, xinfo={'ExtFun':['add'],'Output':[]})
        dig_miscs:Debug:gen_extfuns: 1 ext funs [add]
        dig_miscs:Debug:gen_ef_data([add],|avals|=4)
        dig_miscs:Debug:fun: add, fvals 9, idxs 16
        [OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (8, [(1, 7)]), (10, [(1, 9)]), (16, [(1, 15), (7, 9)]), (14, [(7, 7)]), (22, [(7, 15)]), (18, [(9, 9)]), (24, [(9, 15)]), (30, [(15, 15)])]))])]


        sage: _ = ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['sub', 'add']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [sub, add]
        dig_miscs:Debug:gen_ef_data([sub,add],|avals|=5)
        dig_miscs:Debug:fun: sub, fvals 21, idxs 100
        dig_miscs:Debug:fun: add, fvals 21, idxs 121

        sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [xor, mod255]
        dig_miscs:Debug:gen_ef_data([xor,mod255],|avals|=5)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 25
        dig_miscs:Debug:fun: mod255, fvals 8, idxs 8
        [OrderedDict([('xor', OrderedDict([(0, [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)]), (7, [(2, 5)]), (3, [(2, 1), (0, 3)]), (2, [(2, 0), (1, 3)]), (1, [(2, 3), (1, 0)]), (4, [(5, 1)]), (5, [(5, 0)]), (6, [(5, 3)])]))]), 
        OrderedDict([('mod255', OrderedDict([(0, [(0,)]), (7, [(7,)]), (3, [(3,)]), (2, [(2,)]), (1, [(1,)]), (4, [(4,)]), (5, [(5,)]), (6, [(6,)])]))])]
        
        
        sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [xor, mod255]
        dig_miscs:Debug:gen_ef_data([xor,mod255],|avals|=5)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 25
        dig_miscs:Debug:fun: mod255, fvals 8, idxs 8
        [OrderedDict([('xor', OrderedDict([(0, [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)]), (7, [(2, 5)]), (3, [(2, 1), (0, 3)]), (2, [(2, 0), (1, 3)]), (1, [(2, 3), (1, 0)]), (4, [(5, 1)]), (5, [(5, 0)]), (6, [(5, 3)])]))]), 
         OrderedDict([('mod255', OrderedDict([(0, [(0,)]), (7, [(7,)]), (3, [(3,)]), (2, [(2,)]), (1, [(1,)]), (4, [(4,)]), (5, [(5,)]), (6, [(6,)])]))])]


        sage: ExtFun.gen_extfuns({'R':[128,127,126,125], 'N':[128],'x': [0, 7]},{'Output': ['R'], 'ExtFun': ['sub']}) 
        dig_miscs:Debug:gen_extfuns: 1 ext funs [sub]
        dig_miscs:Debug:gen_ef_data([sub],|avals|=6)
        dig_miscs:Debug:fun: sub, fvals 25, idxs 36
        [OrderedDict([('sub', OrderedDict([(0, [(0, 0), (7, 7), (128, 128), (1, 1), (2, 2), (3, 3)]), (-7, [(0, 7)]), (-128, [(0, 128)]), (-1, [(0, 1), (1, 2), (2, 3)]), (-2, [(0, 2), (1, 3)]), (-3, [(0, 3)]), (7, [(7, 0)]), (-121, [(7, 128)]), (6, [(7, 1)]), (5, [(7, 2)]), (4, [(7, 3)]), (128, [(128, 0)]), (121, [(128, 7)]), (127, [(128, 1)]), (126, [(128, 2)]), (125, [(128, 3)]), (1, [(1, 0), (2, 1), (3, 2)]), (-6, [(1, 7)]), (-127, [(1, 128)]), (2, [(2, 0), (3, 1)]), (-5, [(2, 7)]), (-126, [(2, 128)]), (3, [(3, 0)]), (-4, [(3, 7)]), (-125, [(3, 128)])]))])]
        

        """
        if __debug__:
            assert is_dict(tc), tc
            assert is_dict(xinfo) and 'ExtFun' in xinfo, xinfo

        extfuns = map(ExtFun, xinfo['ExtFun'])

        if is_empty(extfuns):
            return []

        logger.debug('gen_extfuns: {} ext funs [{}]'
                     .format(len(extfuns), list_str(extfuns)))

        #don't consider values of 'output' arrays
        avals = [tc[a] for a in tc if a not in xinfo['Output']]

        #the range of the outputs are also included to have e.g. R[i] = sub(N,i)
        lo = map(len,[tc[a] for a in tc if a in xinfo['Output']])

        if not is_empty(lo):
            avals = avals + [range(max(lo))]

        avals = vset(flatten(avals))

        #generate new arrays representing external functions
        ds = ExtFun.gen_ef_data(extfuns,avals)
       
        return ds    
    
    
    @staticmethod
    def parse_extvar(ev):
        """
        Return a tuple (var, value)
        
        Examples:
        sage: ExtFun.parse_extvar('mpi 3.14')
        OrderedDict([(mpi, 157/50)])

        sage: ExtFun.parse_extvar(' r [1, 2,  3] ')
        OrderedDict([(r, [1, 2, 3])])

        sage: ExtFun.parse_extvar('0wrongvarname 3')
        Traceback (most recent call last):
        ...
        AssertionError: 0wrongvarname
        """
        ev = ev.strip()
        
        if __debug__:
            assert ev.count(' ') >= 1, ev

        idx = ev.find(' ')
        
        vname = ev[:idx].strip()
        vname = ReadFile.strToVar(vname)
        
        vval = ev[idx:].strip()
        vval = ReadFile.formatter(vval)
        vval = ReadFile.strToRatOrList(vval, is_num_val=None)
        return OrderedDict([(vname, vval)])
    
    @staticmethod
    def gen_extvars(xinfo):
        """
        Returns a list of dicts representing extvars
        
        [{v1: 3.14},  {v2: [1,2,3]}]
        
        sage: logger.set_level(VLog.DETAIL)
        
        sage: ExtFun.gen_extvars({'ExtVar' : ['mpi 3.1415', ' t 20.5 ',  'arr [1,[2,3,4]]']})
        dig_miscs:Debug:gen_extvar: 3 ext funs found in xinfo['ExtVar']
        dig_miscs:Detail:mpi 3.1415,  t 20.5 , arr [1,[2,3,4]]
        [OrderedDict([(mpi, 6283/2000)]), OrderedDict([(t, 41/2)]), OrderedDict([(arr, [1, [2, 3, 4]])])]

        sage: ExtFun.gen_extvars({'ExtVar' : []})
        []
        

        """
        if __debug__:
            assert is_dict(xinfo) and 'ExtVar' in xinfo, xinfo
            
        extvars = xinfo['ExtVar']
        if is_empty(extvars):
            return []

        logger.debug("gen_extvar: {} ext funs found in xinfo['ExtVar']"
                     .format(len(extvars)))
        logger.detail(list_str(extvars))

        extvars = map(ExtFun.parse_extvar, extvars)
        
        return extvars
            


def gen_terms(deg, ss):
    """
    Generates a list of terms from the given list of vars and deg
    the number of terms is len(rs) == binomial(len(ss)+d, d)

    Note This version using itertools is faster than
    Sage's MultichooseNK(len(ss)+1,deg)

    Examples:

    sage: ts = gen_terms(3,list(var('a b')))
    sage: assert ts == [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

    sage: ts = gen_terms(3,var('a b c d e f'))
    sage: ts
    [1, a, b, c, d, e, f,
    a^2, a*b, a*c, a*d, a*e, a*f,
    b^2, b*c, b*d, b*e, b*f, c^2, c*d, c*e, c*f,
    d^2, d*e, d*f, e^2, e*f, f^2, a^3, a^2*b, a^2*c, a^2*d, a^2*e,
    a^2*f, a*b^2, a*b*c, a*b*d, a*b*e, a*b*f, a*c^2, a*c*d, a*c*e,
    a*c*f, a*d^2, a*d*e, a*d*f, a*e^2, a*e*f, a*f^2,
    b^3, b^2*c, b^2*d, b^2*e, b^2*f, b*c^2, b*c*d, b*c*e, b*c*f, b*d^2,
    b*d*e, b*d*f, b*e^2, b*e*f, b*f^2, c^3, c^2*d, c^2*e, c^2*f, c*d^2,
    c*d*e, c*d*f, c*e^2, c*e*f, c*f^2, d^3, d^2*e, d^2*f, d*e^2, d*e*f,
    d*f^2, e^3, e^2*f, e*f^2, f^3]

    """
    if __debug__:
        assert deg >= 0, deg
        assert ss and all(s.is_symbol() for s in ss), ss

    ss_ = ([SR(1)] if is_list(ss) else (SR(1),)) + ss
    combs = itertools.combinations_with_replacement(ss_,deg)
    ts = [prod(c) for c in combs]
    return ts


def _gen_terms_mpp(ts,blacklist):
    """
    Generate mpp terms of the form
    max(c1+x1,...,cn+xn,c0) >= xi,
    where ci are in cs (e.g., 0,-oo for max plus)

    sage: var('x y z t s w')
    (x, y, z, t, s, w)

    sage: ts = _gen_terms_mpp([x,y,z,t,s],None); len(ts)
    145

    sage: ts = _gen_terms_mpp([x,y,z],None); ts; len(ts)
    [([x, y, 0], z),
    ([x, y], z),
    ([x, z, 0], y),
    ([x, z], y),
    ([x, 0], y),
    ([x, 0], z),
    ([x], y),
    ([x], z),
    ([y, z, 0], x),
    ([y, z], x),
    ([y, 0], x),
    ([y, 0], z),
    ([y], z),
    ([z, 0], x),
    ([z, 0], y),
    ([0], x),
    ([0], y),
    ([0], z)]
    18


    sage: ts = _gen_terms_mpp([x,y,z],['z']); ts; len(ts)
    [([x, y, 0], z),
    ([x, y], z),
    ([x, 0], z),
    ([x], z),
    ([y, 0], z),
    ([y], z),
    ([z, 0], x),
    ([z, 0], y),
    ([0], x),
    ([0], y)]
    10

    sage: ts = _gen_terms_mpp([x,y,z],['x','y']); ts; len(ts)
    [([x, y, 0], z),
    ([x, y], z),
    ([x, 0], z),
    ([x], z),
    ([y, 0], z),
    ([y], z),
    ([z, 0], x),
    ([z, 0], y),
    ([0], z)]
    9

    sage: ts = _gen_terms_mpp([x,y,z],['x','y','z']); len(ts)
    0

    sage: ts = _gen_terms_mpp([x,y,z,w],None); ts; len(ts)
    [([x, y, z, 0], w),
    ([x, y, z], w),
    ([x, y, w, 0], z),
    ([x, y, w], z),
    ([x, y, 0], z),
    ([x, y, 0], w),
    ([x, y], z),
    ([x, y], w),
    ([x, z, w, 0], y),
    ([x, z, w], y),
    ([x, z, 0], y),
    ([x, z, 0], w),
    ([x, z], y),
    ([x, z], w),
    ([x, w, 0], y),
    ([x, w, 0], z),
    ([x, w], y),
    ([x, w], z),
    ([x, 0], y),
    ([x, 0], z),
    ([x, 0], w),
    ([x], y),
    ([x], z),
    ([x], w),
    ([y, z, w, 0], x),
    ([y, z, w], x),
    ([y, z, 0], x),
    ([y, z, 0], w),
    ([y, z], x),
    ([y, z], w),
    ([y, w, 0], x),
    ([y, w, 0], z),
    ([y, w], x),
    ([y, w], z),
    ([y, 0], x),
    ([y, 0], z),
    ([y, 0], w),
    ([y], z),
    ([y], w),
    ([z, w, 0], x),
    ([z, w, 0], y),
    ([z, w], x),
    ([z, w], y),
    ([z, 0], x),
    ([z, 0], y),
    ([z, 0], w),
    ([z], w),
    ([w, 0], x),
    ([w, 0], y),
    ([w, 0], z),
    ([0], x),
    ([0], y),
    ([0], z),
    ([0], w)]
    54


    sage: ts = _gen_terms_mpp([x,y,z,w],['z','w']); ts; len(ts)
    [([x, y, 0], z),
    ([x, y, 0], w),
    ([x, y], z),
    ([x, y], w),
    ([x, 0], z),
    ([x, 0], w),
    ([x], z),
    ([x], w),
    ([y, 0], z),
    ([y, 0], w),
    ([y], z),
    ([y], w),
    ([z, w, 0], x),
    ([z, w, 0], y),
    ([z, w], x),
    ([z, w], y),
    ([z, 0], x),
    ([z, 0], y),
    ([w, 0], x),
    ([w, 0], y),
    ([0], x),
    ([0], y)]
    22

    sage: ts = _gen_terms_mpp([x,y,z,w],['x','y','z']); ts; len(ts)
    [([x, y, z, 0], w),
    ([x, y, z], w),
    ([x, y, 0], w),
    ([x, y], w),
    ([x, z, 0], w),
    ([x, z], w),
    ([x, 0], w),
    ([x], w),
    ([y, z, 0], w),
    ([y, z], w),
    ([y, 0], w),
    ([y], w),
    ([z, 0], w),
    ([z], w),
    ([w, 0], x),
    ([w, 0], y),
    ([w, 0], z),
    ([0], w)]
    18


    sage: ts = _gen_terms_mpp([x,y],None); ts; len(ts)
    [([x, 0], y), ([x], y), ([y, 0], x), ([0], x), ([0], y)]
    5
    """
    
    if blacklist and all(str(t) in blacklist for t in ts):
        return []

    ts_ext = list(ts) + [0]
    d = {}
    rs = []
    ccs = itertools.product(*([[0,oo]]*len(ts_ext)))
    for cs in ccs:
        lh = [c+t for c,t in zip(ts_ext,cs) if t != oo]
        
        #ignore oo >= x1 + c
        if not lh:
            continue
        
        #ignore x >= x + c ~> 0 >= c
        #ignore [y],x if [x],y already in
        if len(lh) == 1:
            l0 = lh[0]
            ts_ = []

            for t in ts:
                if l0 != t and (t,l0) not in d:
                    ts_.append(t)
                    d[(l0,t)] = None
                    
        else:
            #ignore (lh, xi)  if xi in lh, e.g., [x,y,0] x
            #this is because [x,y,0] x  is implied by [y,0] x
            ts_ = [t for t in ts if t not in lh]

        rs.extend([(lh,t) for t in ts_])

    if blacklist is None:
        return rs

    #remove ones in the blacklist
    #using dict as below is much faster
    S1 = dict([(t,None) for t in ts if str(t) in blacklist])
    S2 = dict([(t,None) for t in ts if str(t) not in blacklist])


    S1[0]=None
    S2[0]=None


    def is_ok(s1,s2):
        """
        Ok when
        subset(l,b1) and subset(r,b2)
        or subset(l,b2) and subset(r,b1)
        """
        is_subset = lambda s0,s1: all(s in s1 for s in s0)

        if is_subset(s1+s2,S1): #if all involved vars in blacklist
            return False

        if is_subset(s1,S1) and is_subset(s2,S2):
            return True
        
        if is_subset(s1,S2) and is_subset(s2,S1):
            return True
        
        return False

    rs = [(l,r) for (l,r) in rs if is_ok(l,[r])]

    return rs
    
     
def gen_terms_fixed_coefs(ts,subset_siz,blacklist,is_mpp):
    """
    Generates a list of terms with fixed coefficients
    Generate |cs|^|ts| exprs

    ts= [x,y,z]  , cs = [0,1]  |exrs| 2^3 = 8

    sage: var('x y z t s u')
    (x, y, z, t, s, u)

    sage: gen_terms_fixed_coefs([x,y^2],2,None,is_mpp=False)
    [-y^2 - x, -x, y^2 - x, -y^2, y^2, -y^2 + x, x, y^2 + x]
    
    
    sage: gen_terms_fixed_coefs([x,z],2,None,is_mpp=False)
    [-x - z, -x, -x + z, -z, z, x - z, x, x + z]
    
    sage: len(gen_terms_fixed_coefs([x,y,z,t,s,u],5,None,is_mpp=False))
    664
    
    sage: ts = gen_terms_fixed_coefs([x,y,z],2,None,is_mpp=True); ts; len(ts)
    [([x], y), ([0], x), ([0], y), ([x], z), ([0], z), ([y], z), ([x, 0], y), ([y, 0], x), ([x, 0], z), ([z, 0], x), ([y, 0], z), ([z, 0], y)]
    12

    
    sage: ts = gen_terms_fixed_coefs([x,y,z],3,None,is_mpp=True); ts; len(ts)
    [([x], y), ([x], z), ([y], z), ([0], x), ([0], y), ([0], z), ([x, y], z), ([x, z], y), ([x, 0], y), ([x, 0], z), ([y, z], x), ([y, 0], x), ([y, 0], z), ([z, 0], x), ([z, 0], y), ([x, y, 0], z), ([x, z, 0], y), ([y, z, 0], x)]
    18

    sage: ts = gen_terms_fixed_coefs([x,y],1,None,is_mpp=True); ts; len(ts)
    [([0], x), ([0], y)]
    2
    """

    if __debug__:
        assert vall_uniq(ts) and all(is_sage_expr(t) for t in ts), ts
        assert subset_siz <= len(ts), (len(ts), subset_siz)
        
                       
    rs = []
    for ts_subset in itertools.combinations(ts, subset_siz):
        if is_mpp:
            rs.extend(_gen_terms_mpp(ts_subset,blacklist=blacklist))
        else:
            css = itertools.product(*([[-1,0,1]]*len(ts_subset)))

            r = (sum(c*t for c,t in zip(ts_subset,cs))
                 for cs in css if not all(c == 0 for c in cs))

            rs.extend(r)

    
    if is_mpp:
        rs = vset(rs,idfun=repr)
        rs = sorted(rs, key=lambda (lh,_) : len(lh))
    else:
        rs = vset(rs)
    return rs


def get_traces(tcs,ntcs,ntcs_extra):
    """
    ntcs : number of traces
    ntcs : number of extra traces

    sage: l=range(10)
    sage: logger.set_level(VLog.DEBUG)
    
    sage: set_random_seed(0)
    sage: l1,l2= get_traces(l,7,3); l1,l2,l
    dig_miscs:Debug:Total traces 10, request (ntcs 7, ntcs_extra 3)
    dig_miscs:Debug:mk_traces: |tcs1|=7, |tcs2|=3 
    ([5, 9, 8, 6, 7, 3, 2], [0, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

    sage: logger.set_level(VLog.WARN)

    sage: set_random_seed(0)
    sage: l1,l2= get_traces(l,3,7); l1,l2
    ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1])

    sage: set_random_seed(0)
    sage: l1,l2= get_traces(l,10,2); l1,l2
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [])

    sage: set_random_seed(0)
    sage: l1,l2= get_traces(l,13,3); l1,l2
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [])

    sage: set_random_seed(0)
    sage: l1,l2= get_traces(l,8,5); l1,l2
    ([5, 9, 8, 6, 7, 3, 2, 0], [4, 1])

    sage: set_random_seed(0)
    sage: l1,l2= get_traces(l,0,3); l1,l2
    ([], [5, 9, 8])

    sage: l1,l2= get_traces(l,3,0); l1,l2
    ([3, 0, 2], [])

    """

    if __debug__:
        assert is_list(tcs) and tcs, tcs
        assert ntcs >= 0, ntcs
        assert ntcs_extra >= 0, ntcs_extra
    
    logger.debug('Total traces {}, '
                 'request (ntcs {}, ntcs_extra {})'
                 .format(len(tcs), ntcs, ntcs_extra))

    if len(tcs) <= ntcs:
        tcs1 = tcs[:]
        tcs2 = []
    else:
        #preserve the original tcs contents
        idxs = range(len(tcs))
        shuffle(idxs)
        tcs1 = [tcs[i] for i in idxs[:ntcs]]
        tcs2 = [tcs[i] for i in idxs[ntcs:ntcs+ntcs_extra]]

    logger.debug('mk_traces: |tcs1|={}, |tcs2|={} '
                 .format(len(tcs1), len(tcs2)))

    return tcs1, tcs2
    

def get_sample(tcs, tcsN, sampleP, min_, tcs2_min_siz=1000):
    print "DEPRECATED"
    sample_siz = int(round(tcsN * sampleP / 100.00))
    if min_ is not None and sample_siz < min_:
        sample_siz = min_

    rs = sample_traces(tcs=tcs, sample_siz=sample_siz, 
                       tcs2_min_siz=tcs2_min_siz)
    return rs


def sample_traces(tcs, sample_siz, tcs2_min_siz=1000):

    """
    preserveTcs: don't modify the input/orig tcs

    Note: much faster than using
    tcs1 = sample(tcs,sample_siz)
    tcs2 = [x for x in tcs if x not in tcs1] #very slow

    Examples:

    sage: logger.set_level(VLog.WARN)
    
    sage: set_random_seed(0)
    sage: l=range(10); l1,l2= sample_traces(l,13); l1,l2,l
    DEPRECATED
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

    sage: set_random_seed(0)
    sage: l=range(10); l1,l2= sample_traces(l,3); l1,l2,l
    DEPRECATED
    ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

    sage: set_random_seed(0)
    sage: l=range(10); l1,l2= sample_traces(l,3); l1,l2,l
    DEPRECATED
    ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

    sage: l=range(3); l1,l2= sample_traces(l,0)
    DEPRECATED
    sage: len(l1), len(l2)
    (0, 3)
    
    
    """

    print "DEPRECATED"

    if __debug__:
        assert tcs and is_list(tcs), tcs
        assert sample_siz >= 0, sample_siz

    if sample_siz >= len(tcs):
        tcs1 = tcs[:]
        tcs2 = []
    else:
        idxs = range(len(tcs))
        shuffle(idxs)
        tcs1 = [tcs[i] for i in idxs[:sample_siz]]
        tcs2 = [tcs[i] for i in idxs[sample_siz:]]

        if tcs2_min_siz is not None and len(tcs2) > tcs2_min_siz:
            logger.debug('set tcs2 to {}'.format(tcs2_min_siz))
            shuffle(tcs2)
            tcs2=tcs2[:tcs2_min_siz]

    logger.debug('sample_traces: |tcs1|={}, |tcs2|={} '
                 '(attempted {}/{} tcs)'
                 .format(len(tcs1), len(tcs2),sample_siz, len(tcs)))

    return tcs1, tcs2


def adjust_arr_sizs(arrs, max_num_elems):
    """
    sage: logger.set_level(VLog.WARN)
        
    sage: arrs = adjust_arr_sizs({'A':range(100),'B':range(200),'C':range(300)}, 200)
    sage: [len(c) for _, c in sorted(arrs.iteritems(), key= lambda (a,_): a)]
    [33, 67, 100]
    
    sage: arrs = adjust_arr_sizs({'A':[[1,2] for _ in range(50)],'B':range(200), 'C':range(300)}, 200)
    sage: [len(c) for _, c in sorted(arrs.iteritems(), key= lambda (a,_): a)]
    [16, 67, 100]

    
    """
    if __debug__:
        assert is_dict(arrs), arrs

    arrslensdims = []
    
    for a,c in arrs.iteritems():
        l = len(c)
        dl = 0   #[1,2,3] -> dl = 0
        
        if is_list(c[0]):  #two dims
            #[[1],[2],[3]]  -> dl = 1, #[[1,2],[3,4]] -> dl = 2
            dl = len(c[0])   
            l = l * dl
        
        arrslensdims.append((a,l,dl))
    
    sum_len = sum(l for _,l,_ in arrslensdims)
    
    if sum_len <= max_num_elems:
        return arrs
        
    arrs_new = OrderedDict()
    for a,l,dl in arrslensdims:
        l = round((max_num_elems*l)/sum_len)
        
        if dl >= 2:
            l = l / dl
        
        l = int(l)
        
        if len(arrs[a]) > l:
            #don't print this since otherwise too many outputs
            #logger.debug('Adjust size of arr {}, old {}, new {}'
            #             .format(a, len(arrs[a]), l))
            arrs_new[a] = arrs[a][:l]
        else:
            arrs_new[a] = arrs[a][:]

    return arrs_new


def is_growing_quickly(xs, ys, min_d):
    """
    Obtain growth rate of ys with respect to the counter xs

    # sage: get_growth_rate([1,2,3,4],[1,2,3,4])
    # [1.00000000000000, 1.00000000000000, 1.00000000000000]
    # sage: get_growth_rate([1,2,3,4],[1,2,3,5])
    # [1.00000000000000, 1.00000000000000, 1.16096404744368]
    # sage: get_growth_rate([4,1,2,3],[5,1,2,3])
    # [1.00000000000000, 1.00000000000000, 1.16096404744368]

    # sage: xs = range(10); get_grow_rate(xs,[x**3 for x in xs])
    # [3.00000000000000,
    # 3.00000000000000,
    # 3.00000000000000,
    # 3.00000000000000,
    # 3.00000000000000,
    # 3.00000000000000,
    # 3.00000000000000,
    # 3.00000000000000]
    # sage: xs = range(2); get_grow_rate(xs,[x**3 for x in xs])
    # []

    """
    if __debug__:
        assert (is_list(xs) and is_list(ys) and
                len(xs) >= 10 and len(xs) == len(ys)), (xs,ys)
        assert all(x>=2 for x in xs), xs # ctr values are non-neg (2+ for log)
        
    zip_xs_ys = itertools.izip(xs,ys)
    zip_xs_ys = sorted(zip_xs_ys, key = lambda (x,y): x)
    ds = [log(y,x).n() for x,y in zip_xs_ys] 

    #if it's not increasing, then return false
    if any(a > b for a,b in zip(ds,ds[1:])):
        return False
    
    #if not increasing quickly, return false    
    if any(d < min_d for d in ds):
        return False

    return True

def elim_ss(ss, tcs, min_d):
    """
    ss = monomials
    """

    ctr_ss = [s for s in tcs[0] if 'dummy_ctr' in str(s)]
    if is_empty(ctr_ss):
        return ss

    if len(ctr_ss) >= 2:
        logger.warn("more than 2 ctr symbols, use the 1st one '{}'"
                    .format(ctr_ss[0]))
    
    ctr_s = ctr_ss[0]

    best_ctr_idxs = []
    ctr_idxs = []
    n_reset = 0
    for i,t in enumerate(tcs):
        if len(best_ctr_idxs) > 50: 
            break
        
        cur_ctr_v = tcs[i][ctr_s]
        assert cur_ctr_v >= 0 #ctr values are non-neg

        if i>=1 and tcs[i-1][ctr_s] > cur_ctr_v: 
            if len(ctr_idxs) > len(best_ctr_idxs):
                best_ctr_idxs = ctr_idxs

            ctr_idxs = []

            n_reset = n_reset + 1
            if n_reset >= 10:
                break

        if cur_ctr_v >= 2: #only interested in value 2+
            ctr_idxs.append(i)

    if len(best_ctr_idxs) < 10:  #not enough data
        return ss

    tcs = [tcs[i] for i in best_ctr_idxs]
    s_tcs = dict([(s,[s.subs(t) for t in tcs]) for s in ss + [ctr_s]])

    xs = s_tcs[ctr_s]
    blacklist = [s for s in ss 
                 if is_growing_quickly(xs,s_tcs[s],min_d)]

    if not is_empty(blacklist):
        logger.debug('Remove {} fast-growing terms {}'
                     .format(len(blacklist),blacklist))
                         
    return [s for s in ss if s not in blacklist]
