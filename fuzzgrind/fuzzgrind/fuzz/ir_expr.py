#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


'''
Intermediate Representation classes
'''

from ir_type import *

    
class Iex_Unop:
    def __init__(self, op, arg, size=None):
        '''
        @type op:   IRop
        @type arg:  IRExpr
        @type size: int
        '''
        self.name = 'unop'
        self.op = op
        self.arg = arg
        self.size = size
        
    #def __cmp__(self, other):
    #    return cmp(self.name, other.name) or \
    #           cmp((self.op, self.arg, self.size), (other.op, other.arg, other.size))

    def pp(self):
        return '%s(%s)' % (self.op.pp(), self.arg.pp())


class Iex_Binop:
    def __init__(self, op, arg1, arg2, size=None):
        '''
        @type op:   IRop
        @type arg1: IRExpr
        @type arg2: IRExpr
        '''
        self.name = 'binop'
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2
        self.size = size
        
    #def __cmp__(self, other):
    #    return cmp(self.name, other.name) or \
    #           cmp((self.op, self.arg1, self.arg2, self.size), (other.op, other.arg1, other.arg2, other.size))

    def pp(self):
        return '%s(%s,%s)' % (self.op.pp(), self.arg1.pp(), self.arg2.pp())


class Iex_Const:
    def __init__(self, const, size=None):
        '''
        @type const: IRConst
        '''
        self.name = 'const'
        self.const = const
        self.size = size
        
    #def __cmp__(self, other):
    #    return cmp(self.name, other.name) or \
    #           cmp((self.const, self.size), (other.const, other.size))

    def pp(self):
        return self.const.pp()


class Iex_Get:
    def __init__(self, ty, offset, size=None):
        self.name = 'get'
        self.offset = offset
        self.ty = ty
        self.size = size
        
    #def __cmp__(self, other):
    #    return cmp(self.name, other.name) or \
    #           cmp((self.offset, self.ty, self.size), (other.offset, other.ty, other.size))

    def pp(self):
        return 'GET:%s(%d)' % (self.ty.pp(), self.offset)


class Iex_Load:
    def __init__(self, end, ty, addr, size=None):
        self.name = 'load'
        self.end = end
        self.ty = ty
        self.addr = addr
        self.size = size
        
    #def __cmp__(self, other):
    #    return cmp(self.name, other.name) or \
    #           cmp((self.end, self.ty, self.addr, self.size), (other.end, other.ty, other.addr, other.size))

    def pp(self):
        return 'LD%s:%s(%s)' % (self.end, self.ty.pp(), self.addr.pp())
        

class Iex_Input:
    def __init__(self, input, size=None):
        self.name = 'input'
        self.input = input
        self.size = size
        
    #def __cmp__(self, other):
    #    return cmp(self.name, other.name) or \
    #           cmp((self.input, self.size), (other.input, other.size))
        
    def pp(self):
        return 'input(%d)' % self.input
