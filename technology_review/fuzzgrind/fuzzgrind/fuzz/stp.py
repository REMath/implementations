#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import re
import sys
import subprocess
from ir_expr import *
from x86g_calculate_condition import x86g_calculate_condition


STP_PROG = './stp/stp'


class STPShiftError(Exception):
    pass



def tobin(x, count=8):
    '''
    Integer to binary
    Count is number of bits
    http://code.activestate.com/recipes/219300/
    '''
    return ''.join(map(lambda y:str((x>>y) & 1), range(count-1, -1, -1)))


class STP_variable:
    '''Variable class. eg. x1'''
    
    def __init__(self, number, size):
        self.number = number
        self.size = size
    
    def pp(self):
        return 'x%d' % (self.number)
        
        
class STP_const:
    '''Constant class. eg. 0h6162'''

    def __init__(self, value, size):
        self.value = value
        self.size = size
    
    def pp(self):
        if self.size % 8 == 0:
            assert self.size > 0, 'self.size == %d < 0 !' % self.size
            format = '0h%%0%dx' % (self.size / 4)
            return format % self.value
        else:
            return '0b%s' % tobin(self.value, self.size)


class STP_function:
    '''Function class, representing all the STP functions'''
    
    def __init__(self, op, size, args):
        '''
        @param op:   function name
        @type  op:   str
        @param size: function arguments size
        @type  size: int
        @param args: function arguments
        @type  args: STP_function|STP_const|STP_variable list
        '''
                
        self.op = op
        self.size = size
        self.args = args
    
    def pp(self):
        '''
        Create a string of the function in the STP input format
        @return str
        '''
        
        if self.op in [ 'NOT', '~' ]:
            return '%s(%s)' % (self.op, self.args[0].pp())
        elif self.op in [ '@' ]:
            return '(%s%s%s)' % (self.args[0].pp(), self.op, self.args[1].pp())
        elif self.op in [ '@', '&', '=', '|' ]:
            return '(%s %s %s)' % (self.args[0].pp(), self.op, self.args[1].pp())
        elif self.op in [ 'BVLE', 'SBVLE', 'BVLT', 'SBVLT', 'BVXOR',  ]:
            return '%s(%s,%s)' % (self.op, self.args[0].pp(), self.args[1].pp())
        elif self.op in [ 'BVSUB', 'BVPLUS', 'BVMULT', 'BVMOD', 'SBVMOD', 'BVDIV', 'SBVDIV' ]:
            return '%s(%d,%s)' % (self.op, self.size, ','.join([ a.pp() for a in self.args ]))
        elif self.op in [ 'IF' ]:
            return '(IF (%s) THEN (%s) ELSE (%s) ENDIF)' % (self.args[0].pp(), self.args[1].pp(), self.args[2].pp())
        elif self.op in [ '<<', '>>' ]:
            return '(%s %s %d)' % (self.args[0].pp(), self.op, self.args[1].value)
        elif self.op in [ 'BVSX' ]:
            return '%s(%s,%d)' % (self.op, self.args[0].pp(), self.size)
        elif re.match('\[\d+:\d+\]', self.op):
            return '((%s)%s)' % (self.args[0].pp(), self.op)
        else:
            print 'STP_function failed, unknown op %s' % self.op
            sys.exit(-1)
            

def patch_var_size(query, var, new_size):
    '''
    @param query:    query to patch
    @type  query:    STP_function|STP_const|STP_variable
    @param var:      variable number
    @type  var:      int
    @type new_size:  int
    '''
    
    if isinstance(query, STP_function):
        new_args = [ patch_var_size(a, var, new_size) for a in query.args ]
        query.args = new_args
        return query
    elif isinstance(query, STP_variable):
        var = query
        assert(var.size < new_size)
        f = STP_function('[%d:%d]' % (var.size - 1, 0), var.size, [ query ])
        var.size = new_size
        return f
    else:
        return query
    
                    

def dirty_patch_size(query, max_size, signed=False):
    '''
    Convert the size of a STP expression.
    This function is needed, because all expression of the QUERY must be of the
    same length. 
    
    @param query:    query expression
    @type  query:    STP_function or STP_const or STP_variable
    @param max_size: size wanted
    @type  max_size: int
    @return query expression
    '''
    
    #print '?>', query.pp(), query.size, '=>', max_size

    if max_size == query.size:
        return query
    elif max_size < query.size:
        if isinstance(query, STP_function) and query.op in [ '=' ]:
            return query
        assert (isinstance(query, STP_variable) or query.op in [ 'IF', '@', 'BVPLUS', '~', 'BVSX', '&', '|', '>>', 'BVMULT', 'BVSUB', 'BVDIV', 'BVXOR' ]), 'Failed:\n%s' % query.pp()
        # return 0h00@x2 instead of ((0h000000@x2))[15:0]
        if isinstance(query, STP_function) and query.op == '@' and isinstance(query.args[0], STP_const) and query.args[0].value == 0:
            if query.args[1].size == max_size:
                return query.args[1]
            else:
                query.args[0].size = max_size - query.args[1].size
                query.size = max_size
                return query
        return STP_function('[%d:%d]' % (max_size - 1, 0), max_size, [ query ])
    else:
        if isinstance(query, STP_function):
            # (0h000000@(x1 = 0h62)) is invalid
            if query.op in [ '=' ]:
                new_args = [ dirty_patch_size(a, max_size) for a in query.args ]
                query.size = max_size
                query.args = new_args
                return query
            # (0h000000@(NOT(x1 = 0h62))) is invalid
            elif query.op == 'NOT':
                query.args = [ dirty_patch_size(a, max_size) for a in query.args ]
                return query
            else:
                assert query.op in [ 'IF', '@', 'BVPLUS', '~', 'BVSX', '&', '|', '>>', 'BVMULT', 'BVSUB' ] or query.op[0] == '[', query.op
                if not signed:
                    x = STP_function('BVSX', max_size, [ query ])
                else:
                    x = STP_function('@', max_size, [ STP_const(0, max_size - query.size), query ])
                #print '*>', x.pp()
                return x
                #print 'dirty_patch_size() failed on q.op (%s): %s' % (query.op, query.pp())
                #sys.exit(-1)
        elif isinstance(query, STP_variable):
            if not signed:
                return STP_function('@', max_size, [ STP_const(0, max_size - query.size), query ])
            else:
                return STP_function('BVSX', max_size, [ query ])
        elif isinstance(query, STP_const):
            return STP_const(query.value, max_size)


def is_predicate(e):
    '''
    Determine if the expression is a predicate function
    '''
    
    if not isinstance(e, STP_function):
        return False
    else:
        while e.op == 'NOT':
            e = e.args[0]
        return e.op in [ '=', 'BVLE', 'SBVLE', 'BVLT', 'SBVLT' ]
        

class STP:
    '''
    STP class, reprenting STP QUERY
    '''
    
    def __init__(self):
        self.var = {}
        self.query = []
        self.first_cmp = True
        
        
    def negate(self, i):
        if self.query[i].op == 'NOT':
            self.query[i] = self.query[i].args[0]
        else:
            self.query[i] = STP_function('NOT', self.query[i].size, [self.query[i]])


    def from_expr(self, e):
        '''
        Convert an expression to a STP query
        @type e: Iex
        '''

        if isinstance(e, Iex_Unop):
            m = re.match('(\d+)Uto(\d+)', e.op.op)
            if m:
                i = int(m.group(1))
                j = int(m.group(2))
                if j > i:
                    args = [STP_const(0, j - i), self.from_expr(e.arg)]
                    return STP_function('@', j, args)
                else:
                    args = [ self.from_expr(e.arg) ]
                    return STP_function('[%d:%d]' % (j - 1, 0), j, args)
                    
            m = re.match('(\d+)to(\d+)', e.op.op)
            if m:
                i = int(m.group(1))
                j = int(m.group(2))
                assert(j < i)
                args = [ self.from_expr(e.arg) ]
                return STP_function('[%d:%d]' % (j - 1, 0), j, args)

            m = re.match('(\d+)Sto(\d+)', e.op.op)
            if m:
                args = [ self.from_expr(e.arg) ]
                i = int(m.group(1))
                j = int(m.group(2))
                assert(i < j)
                return STP_function('BVSX', j, args)
                
            m = re.match('Not(\d+)', e.op.op)
            if m:
                args = [ self.from_expr(e.arg) ]
                
                if not is_predicate(args[0]):
                    return STP_function('~', int(m.group(1)), args)
                else:
                    return STP_function('NOT', int(m.group(1)), args)
                        
            # Clz32
            # http://acapulco.dyndns.org/manual/src/work/gcc-4.3.0/libgcc/config/libbid/bid_binarydecimal.c
            # http://article.gmane.org/gmane.comp.emulators.qemu/31052
            if e.op.op == 'Clz32':
                arg = self.from_expr(e.arg)
                args = []
                masks = [ 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 ]
                for i, mask in enumerate(masks):
                    a = STP_function('&', 32, [ arg, STP_const(mask, 32) ])
                    b = STP_function('&', 32, [ arg, STP_const((~mask) % 0x100000000, 32) ])
                    bvle = STP_function('BVLE', 1, [ a, b ])
                    x = STP_const(1 << i, 32)
                    y = STP_const(0, 32)
                    cond = STP_function('IF', 32, [ bvle, x, y ])
                    args.append(cond)
                nz = STP_function('BVPLUS', 32, args)
                z = STP_const(0, 32)
                cond = STP_function('=', 32, [ arg, STP_const(0, 32) ])
                return STP_function('IF', 32, [ cond, z, nz ])
                
        elif isinstance(e, Iex_Binop):
            m = re.match('Cmp([A-Z]{2})(\d+)([SU]?)', e.op.op)
            if m:
                # from_expr() is recursive, so remember its current value before
                # altering it
                first_cmp = self.first_cmp
                self.first_cmp = False
                
                op_stp = {
                    ('EQ', ''):  '=',
                    ('NE', ''):  '=',
                    ('LE', 'U'): 'BVLE',
                    ('LE', 'S'): 'SBVLE',
                    ('LT', 'U'): 'BVLT',
                    ('LT', 'S'): 'SBVLT',
                }
                op = m.group(1)
                size = int(m.group(2))
                signed = m.group(3)
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size, signed=='S')
                args[1] = dirty_patch_size(args[1], size, signed=='S')
                function = STP_function(op_stp[(op, signed)], 1, args)
                
                if op == 'NE':
                    function = STP_function('NOT', 1, [ function ])
                
                # It's possible that Valgrind returns an expression like this:
                # CmpEQ32(CmpEQ8(a,b),1).
                # Translate it to:
                # QUERY((IF (a = b) THEN 0b1 ELSE 0b0 ENDIF) = 0b1)
                if not first_cmp or True: # XXX
                    function = STP_function('IF', 1, [ function, STP_const(1, 1), STP_const(0, 1) ])
                
                return function
                
            m = re.match('And(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('&', size, args)
                
            m = re.match('Xor(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('BVXOR', size, args)
                
            m = re.match('Or(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('|', size, args)
                
            m = re.match('Add(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('BVPLUS', size, args)

            m = re.match('Mul(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size, signed=True)
                args[1] = dirty_patch_size(args[1], size, signed=True)
                return STP_function('BVMULT', size, args)
                
            m = re.match('MullS(\d+)', e.op.op)
            if m:
                size = int(m.group(1)) * 2
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size, signed=True)
                args[1] = dirty_patch_size(args[1], size, signed=True)
                return STP_function('BVMULT', size, args)
                
            m = re.match('MullU(\d+)', e.op.op)
            if m:
                size = int(m.group(1)) * 2
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('BVMULT', size, args)
                
            m = re.match('ModU(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                assert(size == 32)
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('BVMOD', size, args)
                
            m = re.match('ModS(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                assert(size == 32)
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size, signed=True)
                args[1] = dirty_patch_size(args[1], size, signed=True)
                return STP_function('SBVMOD', size, args)
                
            m = re.match('Sub(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('BVSUB', size, args)

            m = re.match('Shl(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                assert(isinstance(args[0], STP_const) or isinstance(args[1], STP_const))
                if isinstance(args[1], STP_const):
                    if args[1].value != 0:
                        args[0] = dirty_patch_size(args[0], size - args[1].value)
                        return STP_function('<<', size, args)
                    else:
                        return args[0]
                else:
                    raise STPShiftError('%s right member isn\'t a constant' % e.op.op)
                    #return STP_function('BVMULT', size, [ args[0].value, STP_function('BVMULT', size, [ STP_const(2, size), args[1] ]) ])
                    
            m = re.match('Shr(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                if isinstance(args[1], STP_const):
                    if args[1].value != 0:
                        return STP_function('>>', size, args)
                    else:
                        return args[0]
                else:
                    raise STPShiftError('%s right member isn\'t a constant' % e.op.op)
                    
            m = re.match('Sar(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                assert(isinstance(args[1], STP_const))
                sign_extended = STP_function('BVSX', args[0].size + 1, [ args[0] ])
                shifted = STP_function('>>', size, [ sign_extended, args[1] ])
                return STP_function('[%d:%d]' % (size - 1, 0), size, [ shifted ])
                
            m = re.match('Cat(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                return STP_function('@', size, args)
                
            m = re.match('DivU(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('BVDIV', size, args)
                
            m = re.match('DivS(\d+)', e.op.op)
            if m:
                size = int(m.group(1))
                args = [ self.from_expr(e.arg1), self.from_expr(e.arg2) ]
                args[0] = dirty_patch_size(args[0], size)
                args[1] = dirty_patch_size(args[1], size)
                return STP_function('SBVDIV', size, args)
                
            print 'STP.from_expr: unknow %s op in Iex_Binop' % e.op.op
            print '-' * 80
            print e.pp()
            print '-' * 80
            sys.exit(-1)
                
        elif isinstance(e, Iex_Const):
            return STP_const(e.const.value, e.const.ty.size)
            
        elif isinstance(e, Iex_Load):
            assert(isinstance(e.addr, Iex_Input))
            byte = e.addr.input
            size = e.ty.size
            # there can be nasty things if we load the same input with different
            # size (eg. LDle:I8(input(0)) AND LDle:I32(input(0)))
            if not self.var.has_key(byte):
                self.var[byte] = size
            elif self.var[byte] != size:
                if size > self.var[byte]:
                    self.query = [ patch_var_size(q, byte, size) for q in self.query ]
                    self.var[byte] = size
                else:
                    return STP_function('[%d:%d]' % (size - 1, 0), size, [ STP_variable(byte, size) ])
                
            return STP_variable(byte, size)
         
        print 'STP.from_expr_(%s) failed' % e.pp()
        sys.exit(-1)
        
        
    def from_expr_(self, e):
        '''
        STP needs a predicate in each constraint. Add a comparaison to 1 when
        necessary. 
        '''
        
        result = self.from_expr(e)
        if not is_predicate(result):
            return STP_function('=', 1, [ result, STP_const(1, result.size) ])
        else:
            return result
        

    def pp(self):
        var = ['x%d : BITVECTOR(%d);' % (k, v) for (k, v) in self.var.items()]
        max_size = max([ q.size for q in self.query ])
        query = [ dirty_patch_size(q, max_size) for q in self.query ]

        s = ''
        s += '\n'.join(var)
        s += '\n'
        s += 'QUERY(NOT(%s));' % ' AND '.join([ q.pp() for q in query ])
        s += '\n'
        
        return s


    def execute(self):
        '''Execute stp, giving in input a STP QUERY'''
        
        #print self.pp()
        fp = open('/tmp/stp_input.txt', 'w')
        fp.write(self.pp())
        fp.close()
    
        p = subprocess.Popen([ STP_PROG, '-p', ], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout, stderr) = p.communicate(self.pp())
        if stderr:
            print 'STP.execute() failed on :'
            print '-' * 80
            print self.pp(),
            print '-' * 80
            print stderr
            sys.exit(-1)
        else:
            self.result = stdout


    def interpret(self):
        '''
        Read stp output, and guess the solution if possible
        @return None if the QUERY is valid, solution otherwise.
                Solution is a dictionary of { byte_number: (value, size) }
        '''
        
        lines = self.result.split('\n')

        #if lines[0] == 'Invalid.':
        if lines[0] == 'Valid.':
            return None
        else:
            solution = {}
            for l in lines[1:-1]:
                l = re.sub('\s*', '', l)
                m = re.match('ASSERT\(x(\d+)=0hex([0-9a-zA-Z]+)\)', l)
                if m:
                    byte_number = int(m.group(1))
                    value = int(m.group(2), 16)
                    size = int(self.var[byte_number])
                    solution[byte_number] = (value, size)
                else:
                    print 'STP.interpret(%s) failed' % l
                    print ''.join(l)
                    sys.exit(-1)
            return solution
            
        
if __name__ == '__main__':
    from valgrind import *
    ss =  [ 'Not1(CmpEQ32(Add32(Sub32(Add32(Shl32(8Uto32(LDle:I8(input(22))),0x8:I8),8Uto32(LDle:I8(input(23)))),0x2:I32),0x1000:I32),0x0:I32))', ]
          
    stp = STP()
    
    for s in ss:
        e = parse_expr(s)
        stp.query += [ stp.from_expr_(e) ]
        stp.first_cmp = True
        
    print stp.pp()
