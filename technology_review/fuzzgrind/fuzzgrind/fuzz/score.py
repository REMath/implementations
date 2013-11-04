#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import os
import random
import re
import subprocess
import sys


FUZZGRIND = './valgrind-3.4.1/build/bin/valgrind'


def random_score():
    return random.randint(0, 1024)


def score(progname, progarg, input_file, taint_stdin=False):
    arg_valgrind = [ FUZZGRIND, '--tool=lackey', '--basic-counts=yes' ]
    arg_prog = [ progname, input_file ]
    
    if not progarg:
        arg_prog = [ progname ]
        if not taint_stdin:
            arg_prog.append(input_file)
    else:
        progarg = re.sub('\$input', input_file, progarg)
        progarg = progarg.split()
        arg_prog = [ progname ] + progarg
    
    if not taint_stdin:
        stdin = None
    else:
        stdin = open(input_file, 'r')

    p = subprocess.Popen(arg_valgrind + arg_prog, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = p.communicate()
    
    for line in stderr.split('\n'):
        m = re.match('==\d+==\s+total:\s+([\d,]+)', line)
        if m:
            total = int(re.sub(',', '', m.group(1)))
            break
    
    return total
            
    
if __name__ == "__main__":
    total = score('/usr/bin/convert', '/tmp/bla.jpg')
    print total
