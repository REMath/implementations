import time
from sage.all import (os, binomial)

from vu_common import pause, is_str, is_empty, vset
from dig import DIG, Inv
from dig_miscs import ReadFile


"""
Benchmark Scripts

Examples:
~/Dropbox/git/invgen/Traces/NLA/benchmark_small_test_dir

sage: sols = benchmark_dir('../invgen/Traces/NLA_ctr/multilocs/l0/', runs=10) 
sage: sols = benchmark_dir('../invgen/Traces/AES_tosem/multilocs/l0/', runs=10)

"""

def benchmark_dir(dirname,runs=1,start_from=0,use_specific_deg=False,read_only=False,do_parallel=True):

    """
    sols = benchmark_dir('../invgen/Traces/NLA/multi_locs/',runs=2,start_from=5)

    start_from: start from this file idx
    """

    if __debug__:
        assert runs >= 1, runs
        assert start_from >= 0, start_from

    print '\n********** BEGIN BENCHMARK **********'
    print "Trace Dir: '{}', {} run(s) per tcs file".format(dirname, runs)
    print '********** *************** **********\n'
    
    tcs_files = ReadFile.get_tcs_files(dirname)

    if start_from >= 1:
        print("Start from tcs idx {}. '{}'"
              .format(start_from, tcs_files[start_from]))
        tcs_files = tcs_files[start_from:]

    nfiles = len(tcs_files)

    sols = []

    for i, fn in enumerate(tcs_files):
        file_ = os.path.join(dirname, fn)
        print("\n***** {}/{}. (idx: {}) Generate invs from '{}' *****\n"
              .format(i+1, nfiles, start_from + i, fn))
        expect, sols_fn, sols_run = benchmark_file(file_, 
                                                   runs=runs, 
                                                   use_specific_deg=use_specific_deg, 
                                                   read_only=read_only,
                                                   do_parallel=do_parallel)
        sols = sols + [(file_,expect,sols_fn,sols_run)]

    if not read_only:
        print '\n***** BENCHMARK SUMMARY *****\n'
        for i,(f,expect,sols_fn,sols_run) in enumerate(sols):
            print_summary(f,expect,sols_fn,sols_run)


def benchmark_file(filename,runs,use_specific_deg,read_only,do_parallel):

    def get_deg_auto(nss, nts=200, max_deg=7):
        if __debug__:
            assert nss >= 1, nss
            assert nts >= nss, (nts, nss)
            assert max_deg >= 1, max_deg

        for d in range(1,max_deg+1):
            deg = d
            if binomial(nss+deg, deg) - 1 > nts:
                deg = d - 1
                break

        return deg
    
    def get_deg_specific(filename):
        deg3=['dijkstra', 
              'cohencu','prod4br','knuth',
              'geo3','ps3']
        deg4=['ps4']
        deg5=['ps5']
        deg6=['ps6']
        deg7=['ps7']
        
        if any(x in filename for x in deg7): 
            return 7
        elif any(x in filename for x in deg6): 
            return 6
        elif any(x in filename for x in deg5): 
            return 5
        elif any(x in filename for x in deg4): 
            return 4
        elif any(x in filename for x in deg3): 
            return 3
        else: 
            return 2

    def get_invs(ig, seed, deg):
        start_time = time.time()
        ig.set_seed(seed)

        #For MPP
        #rs = ig.get_ieqs_max_min_fixed()

        # if len(ig.ss_num) <= 3:
        #     print 'also getting general form, {} vars'.format(len(ig.ss_num))
        #     rs_ = ig.get_ieqs_max_min_gen()
        #     rs = rs_ + rs
        #     rs = vset(rs)
        #     print len(rs)


        #DO NOT USE fixed_3, will generate
        #lots of formulas that screw up Z3
        #stick with fixed_2
        #For NLA
        #rs = ig.get_eqts_ieqs_max_min_fixed_2(deg=deg)

        #eqts 
        rs = ig.get_invs(deg=deg)
        return rs, (time.time() - start_time)


    sols_filename = []
    start_time = time.time()
    ig = DIG(filename)
    print "Read time {}".format(time.time() - start_time)
    
    if read_only:
        return '', [], []

    if len(ig.ss_num) <= 1:
        deg = 1
    else:
        if any(x in filename for x in ['AesKeySetupEnc_w_LRA',
                                       'AesKeySetupDec_w_LRA']):
            deg = 1

        elif use_specific_deg:
            deg = get_deg_specific(filename)
            print 'Use *specific* max degree {}'.format(deg)
        else:
            if 'l_init' in filename:
                deg = 2
                print 'Use default max deg {} for l_init'.format(deg)
            else:
                deg = get_deg_auto(len(ig.ss_num))
                print 'Use *auto* max deg {}'.format(deg)
    
    sols_run = []
    for nr in range(runs):
        print '\n--- Run {}/{} ({}) ---\n'.format(nr+1,runs,filename)
        rs,etime = get_invs(ig, seed=nr, deg=deg)
        print etime

        sols_filename = sols_filename + [(nr,rs,deg,etime)]
        sols_run = sols_run + rs

    sols_run = vset(sols_run)
    expect = ig.xinfo['Expect']
    print_summary(filename,expect,sols_filename,sols_run)

    return expect, sols_filename, sols_run


def print_summary(filename,expect,sols_filename,sols_run):
    if is_empty(sols_filename):
        return

    print("\nSUMMARY ({})".format(filename))
    print("Expect ({}): {}".format(len(expect), ', '.join(map(str,expect))))
    time_total = 0.0
    for (nr,rs,deg,etime) in sols_filename:
        print '* Run {}, time {}, deg {}'.format(nr, etime, deg)
        Inv.print_invs(rs)
        time_total =  time_total + etime

    print('\nObtain {} unique results over {} run'
          .format(len(sols_run), len(sols_filename)))
    Inv.print_invs(sols_run,nice_format=False)

    time_str = '{0:.1f}'.format(time_total/len(sols_filename))
    print('TIME AVG {}, #invs {}, ({})\n'
          .format(time_str,len(sols_run), filename))


