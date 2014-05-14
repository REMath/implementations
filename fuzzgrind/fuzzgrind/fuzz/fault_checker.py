#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import os
import re
import subprocess
import sys


def check_ptrace(arg_prog, stdin):
    PTRACE = 'fault_detection/ptrace'
    p = subprocess.Popen([ PTRACE ] + arg_prog, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = p.communicate()
    
    return p.returncode != 0


def check_crackme(arg_prog, stdin):
    p = subprocess.Popen(arg_prog, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = p.communicate()
    
    return 'OK' in stdout


def check_testcase(arg_prog, stdin):
    p = subprocess.Popen(arg_prog, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = p.communicate()
    
    return 'ok' in stdout


def check(progname, progarg, input_file, callback, taint_stdin=False):
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

    return callback(arg_prog, stdin)
            
    
if __name__ == "__main__":
    total = check('/usr/bin/convert', '/tmp/bla.jpg', check_ptrace)
    print total
