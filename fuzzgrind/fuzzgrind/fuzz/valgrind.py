#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


'''
Run Valgrind's plugin and parse resulting output
'''


import os
import re
import select
import signal
import subprocess
import sys
from ir_stmt import *
from ir_expr import *
from ir_type import *
from x86g_calculate_condition import x86g_calculate_condition


FUZZGRIND = './valgrind-3.4.1/build/bin/valgrind'


class Node:
    def __init__(self, op, arg, parent=None):
        self.op     = op
        self.arg    = arg
        self.expr   = []
        self.parent = parent


def get_args(s):
    '''
    Get expression arguments.
    eg: get_args('Sub32(a,0x1:I32),0x1:I32') -> ['Sub32(a,0x1:I32)', '0x1:I32']
    
    This function must be as fast as possible, because this is the bottleneck of 
    the expression parsing.
    
    @param s: expression
    @type  s: str
    @return   str list
    '''
    
    chunk = s.split(',')
    left = 0
    right = 0
    k = 0
    args = []
    
    for i in range(0, len(chunk)):
        c = chunk[i]
        left += c.count('(')
        right += c.count(')')
        if left == right:
            args.append(','.join(chunk[k:i+1]))
            k = i + 1
    
    return args


def simplify(e):
    '''Simplify an expression'''
    
    simplified = True
    original_expr = e # just for debugging purpose
    
    while simplified:
        simplified = False
        
        if isinstance(e, Iex_Unop):
            # 64to32(DivModU64to32(a,b)) -> a / b
            if e.op.op == '64to32' and isinstance(e.arg, Iex_Binop) and (e.arg.op.op == 'DivModU64to32' or e.arg.op.op == 'DivModS64to32'):
                if e.arg.op.op == 'DivModU64to32':
                    op = 'DivU32'
                elif e.arg.op.op == 'DivModS64to32':
                    op = 'DivS32'
                e = Iex_Binop(IRop(op), e.arg.arg1, e.arg.arg2, 32)
                simplified = True
                continue
            
            # 64HIto32(DivModU64to32(a,b)) -> a % b
            if e.op.op == '64HIto32' and isinstance(e.arg, Iex_Binop) and (e.arg.op.op == 'DivModU64to32' or e.arg.op.op == 'DivModS64to32'):
                if e.arg.op.op == 'DivModU64to32':
                    op = 'ModU32'
                elif e.arg.op.op == 'DivModS64to32':
                    op = 'ModS32'
                e = Iex_Binop(IRop(op), e.arg.arg1, e.arg.arg2, 32)
                simplified = True
                continue
                
            # 64HIto32(a@b) -> a
            m = re.match('64HIto32', e.op.op)
            if m:
                const = IRConst(32, IRType('I8'))
                e = Iex_Binop(IRop('Shr64'), e.arg, Iex_Const(const), 64)
                e = Iex_Unop(IRop('64to32'), e, 32)
                simplified = True
                continue
        
            # translate things like 32to1(1to32(a)) to (a)
            m = re.match('(\d+)[SU]*to(\d+)', e.op.op)
            if m and isinstance(e.arg, Iex_Unop):
                if re.match('%sU?to%s' % (m.group(2), m.group(1)), e.arg.op.op):
                    e = e.arg.arg
                    simplified = True
                    continue
            
            # translate things like 32to8(1to32(a)) to 1to8(a)
            m1 = re.match('(\d+)[SU]*to(\d+)', e.op.op)
            if m1 and isinstance(e.arg, Iex_Unop):
                m2 = re.match('(\d+)U?to%s' % m1.group(1), e.arg.op.op)
                if m2:
                    e = Iex_Unop(IRop('%sUto%s' % (m2.group(1), m1.group(2))), e.arg.arg, e.size)
                    simplified = True
                    continue
                    
            # GET always preceed PUT
            m = re.match('^GET:I(\d+)$', e.op.op)
            if m:
                assert(isinstance(e.arg, Iex_Unop) and e.arg.op.op == 'PUT')
                assert(e.arg.arg.size != None)
                size = int(m.group(1))
                if size == e.arg.arg.size:
                    e = e.arg.arg
                else:
                    e = Iex_Unop(IRop('%dUto%d' % (e.arg.arg.size, size)), e.arg.arg, size)
                simplified = True
                continue
                
            # LDle:I8(STle(LDle:I32(x))) -> LDle:I8(x)
            # we have to handle this case in order to not lose the conversion
            # from 32 to 8 bytes
            #
            # for example:
            # 32to1(1Uto32(CmpEQ32(8Uto32(GET:I8(PUT(GET:I32(PUT(8Uto32(LDle:I8(STle(LDle:I32(input(0)))))))))),0xff:I32)))
            # must be simplified to:
            # CmpEQ32(LDle:I8(input(0)),0xff:I32)
            # not to:
            # CmpEQ32(LDle:I32(input(0)),0xff:I32)
            m = re.match('LD(le|be):([^(]+)', e.op.op)
            if m:
                if isinstance(e.arg, Iex_Unop):
                    assert(e.arg.op.op == 'STle')
                    if isinstance(e.arg.arg, Iex_Load):
                        end = m.group(1)
                        ty = IRType(m.group(2))
                        e = Iex_Load(end, ty, e.arg.arg.addr, ty.size)
                        simplified = True
                        continue

            # simplify: LDle always preceed STle or input
            m = re.match('LD(le|be):([^(]+)', e.op.op)
            if m:
                end = m.group(1)
                ty = IRType(m.group(2))
                m = re.match('LD(le|be):([^(]+)', e.op.op)
                if m:
                    if isinstance(e.arg, Iex_Input):
                        e = Iex_Load(end, ty, e.arg, ty.size)
                    else:
                        assert(isinstance(e.arg, Iex_Unop) and e.arg.op.op == 'STle')
                        assert(e.arg.size != None)
                        if ty.size == e.arg.size:
                            e = e.arg.arg
                        else:
                            e = Iex_Unop(IRop('%dUto%d' % (e.arg.arg.size, ty.size)), e.arg.arg, ty.size)
                        simplified = True
                        continue
            
        elif isinstance(e, Iex_Binop):
            # simplify: Sub32(Sub32(a,0x1:I32),0x1:I32)
            # simplify: Add32(Add32(a,0x1:I32),0x1:I32)
            if re.match('Sub(\d+)', e.op.op) or re.match('Add(\d+)', e.op.op):
                if isinstance(e.arg1, Iex_Binop) and e.arg1.op.op == e.op.op:
                    if isinstance(e.arg2, Iex_Const) and isinstance(e.arg1.arg2, Iex_Const):
                        assert(e.arg2.size == e.arg1.arg2.size)
                        e.arg1.arg2.const.value += e.arg2.const.value
                        e.arg1.arg2.const.value %= 0x100000000 # we're on 32bits
                        e = e.arg1
                        simplified = True
                        continue
            
            if e.op.op == '32HLto64':
                e.op.op = 'Cat64'
                simplified = True
                continue

            # simplify: Shr32(64HIto32(MullU32(a,0xcccccccd:I32)),b) -> a / (10 * 2^(b-1))
            '''if e.op.op == 'Shr32' and e.arg1.op.op == '64HIto32' and e.arg1.arg.op.op == 'MullU32' and isinstance(e.arg1.arg.arg2, Iex_Const) and e.arg1.arg.arg2.const.value == 0xcccccccd and isinstance(e.arg2, Iex_Const):
                div = Iex_Const(IRConst(10 * (2 ** (e.arg2.const.value - 1)), IRType('I8')), 8)
                e = Iex_Binop(IRop('DivU32'), e.arg1.arg.arg1, div, e.size)
                simplified = True
                continue'''

    #print original_expr.pp(), (' ' * (50 - len(original_expr.pp()))), '=>', e.pp(), e.size
    
    return e
    

def parse_expr(e):
    n = Node('ROOT', [ e ])
    original_expr = e # just for debugging purpose
    
    while True:
        if len(n.expr) != len(n.arg):
            s = n.arg[len(n.expr)]
        
            if not s.find('(') > -1:
                m = re.match('(0x)?([0-9A-Fa-f]+):(.*)', s)
                assert(m != None)
                h = 10 + 6 * int(m.group(1) != None)
                value = int(m.group(2), h)
                ty = IRType(m.group(3))
                const = IRConst(value, ty)
                n.expr.append(Iex_Const(const, ty.size))
            else:
                op = s[:s.index('(')]
                arg = get_args(s[s.index('(')+1:s.rindex(')')])
                if op != 'input':
                    node = Node(op, arg, n)
                    n = node
                else:
                    assert(len(arg) == 1)
                    n.expr.append(Iex_Input(int(arg[0])))
                    n.expr[-1].size = -1
        else:
            expr = None
            
            if len(n.expr) == 1:
                arg = n.expr[0]
                size = None
                
                m = re.match('\d+[SUHI]*to(\d+)[SU]?', n.op)
                if m:
                    size = int(m.group(1))
                    
                if not size and n.op != 'ROOT':
                    assert arg.size != None, 'can\'t get size of something is the following expression:\n' + original_expr
                    size = arg.size
                expr = Iex_Unop(IRop(n.op), arg, size)
                expr = simplify(expr)
                
            elif len(n.expr) == 2:
                assert(n.expr[0].size != None or n.expr[1].size != None)
                arg1 = n.expr[0]
                arg2 = n.expr[1]
                size = 0
                m = re.match('Cat(\d+)', n.op)
                if m:
                    size = int(m.group(1))
                m = re.match('Mull[SU](\d+)', n.op)
                if m:
                    size = int(m.group(1)) * 2
                if not size:
                    if arg1.size != None:
                        size = arg1.size
                    else:
                        size = arg2.size
                expr = Iex_Binop(IRop(n.op), arg1, arg2, size)
                expr = simplify(expr)
        
            elif len(n.expr) == 4:
                assert(n.op == 'x86g_calculate_condition')
                assert(isinstance(n.expr[0], Iex_Const))
                assert(isinstance(n.expr[1], Iex_Const))
                cond = n.expr[0]
                cc_op = n.expr[1]
                 # XXX - arg, this is recursive
                 # fix x86g_calculate_condition.py
                expr = parse_expr(x86g_calculate_condition(cond, cc_op, n.expr[2].pp(), n.expr[3].pp()))
            
            else:
                print 'Wrong expression argument number (%d)' % (len(n.expr))
                assert(False)
                
            if n.parent:
                n = n.parent
                n.expr.append(expr)
            else:
                return n.expr[0]


def run_valgrind(progname, progarg, input_file, taint_stdin=False, max_constraint=-1):
    '''
    Run valgrind and write its output into a file
    
    @param progname:       name of program under test
    @type  progname:       str
    @param progarg:        program arguments
    @type  progarg:        str
    @param input_file:     input of program under test
    @type  input_file:     str
    @param taint_stdin:    is stdin tainted ?
    @type  taint_stdin:    boolean 
    @param max_constraint: maximum constraint number to read (-1 means infinite)
    @type  max_constraint: int
    @return output file name
    '''
    
    tmp_filename = '/tmp/valgrind_output_%d.txt' % os.getpid()
    
    if not progarg:
        arg_prog = [ progname ]
        if not taint_stdin:
            arg_prog.append(input_file)
    else:
        progarg = re.sub('\$input', input_file, progarg)
        progarg = progarg.split()
        arg_prog = [ progname ] + progarg
    
    if not taint_stdin:
        arg_valgrind = [ FUZZGRIND, '--tool=fuzzgrind', '--taint-file=yes', '--file-filter=' + input_file ]
        stdin = None
    else:
        arg_valgrind = [ FUZZGRIND, '--tool=fuzzgrind', '--taint-stdin=yes' ]
        stdin = open(input_file, 'r')

    fp = open(tmp_filename, 'w')
    p = subprocess.Popen(arg_valgrind + arg_prog, stdin=stdin, stdout=subprocess.PIPE, stderr=fp.fileno())
    
    if max_constraint == -1:
        p.wait()
    else:
        nb_constraint = 0
        poll = select.poll()
        # XXX - poll on stdout fail, we must poll on stderr but it's None
        poll.register(p.stdout, select.POLLIN)
        timeout = False
        while not timeout and nb_constraint < max_constraint:
            l = poll.poll(10000) # timeout in milliseconds
            timeout = True
            for f, event in l:
                if event & (select.POLLIN):
                    data = p.stdout.readlines()
                    nb_constraint += len(filter(lambda x: 'depending of input' in x, data))
                    timeout = False
        if not p.poll():
            try:
                os.kill(p.pid, signal.SIGKILL)
            except OSError:
                pass
            
    fp.close()
    
    return tmp_filename


if __name__ == '__main__':
    from stp import *
    
    #s = 'CmpEQ32(DivU32(Cat64(0x0:I64,Mul32(0x1:I32,Add32(Sub32(Add32(Shl32(8Uto32(LDle:I8(input(22))),0x8:I8),8Uto32(LDle:I8(input(23)))),0x2:I32),0x1000:I32))),Add32(Sub32(Add32(Shl32(8Uto32(LDle:I8(input(22))),0x8:I8),8Uto32(LDle:I8(input(23)))),0x2:I32),0x1000:I32)),0x1:I32)'
    s = 'CmpEQ32(DivS32(Cat64(Sar32(Mul32(16Uto32(Cat16(LDle:I8(input(305)),LDle:I8(input(304)))),0xc:I32),0x1f:I8),Mul32(16Uto32(Cat16(LDle:I8(input(305)),LDle:I8(input(304)))),0xc:I32)),0xc:I32),16Uto32(Cat16(LDle:I8(input(305)),LDle:I8(input(304)))))'
    #print s

    e = parse_expr(s)
    print e.pp()
    #sys.exit(0)

    stp = STP()
    stp.query += [ stp.from_expr_(e) ]
    print stp.pp()
    stp.execute()
