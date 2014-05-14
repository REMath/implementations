#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


'''
Types definition for the IR
'''

import re


class IRType:
    def __init__(self, t):
        '''
        @type t:  str
        @param t: I32 for example
        '''

        m = re.match('(?P<type>[I|U|F])(?P<size>\d+)', t)
        self.ty = m.group('type')
        self.size = int(m.group('size'))
        
    def __cmp__(self, other):
        return cmp((self.ty, self.size), (other.ty, other.size))

    def pp(self):
        return '%s%d' % (self.ty, self.size)


class IRTemp:
    def __init__(self, t):
        '''
        @type t: int
        '''
        self.t = t
        
    def __cmp__(self, other):
        return cmp(self.t, other.t)

    def pp(self):
        return 't%d' % self.t


class IRop:
    def __init__(self, op):
        '''
        @type op: str
        @parm op: example "32to1"
        '''
        self.op = op
        
    def __cmp__(self, other):
        return cmp(self.op, other.op)

    def pp(self):
        return self.op


class IRConst:
    def __init__(self, value, ty):
        '''
        @type value: int or float
        @type ty:    IRType
        '''
        self.value = value
        self.ty = ty
        
    def __cmp__(self, other):
        return cmp((self.value, self.ty), (other.value, other.ty))

    def pp(self):
        return '0x%x:%s' % (self.value, self.ty.pp())
