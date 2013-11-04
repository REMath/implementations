#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


class IRStmt:
    def __init__(self, tag, a, b, c):
        self.tag = tag
        if tag == 'NoOp':
            pass
        elif tag == 'IMark':
            self.stmt = IMark(a, b)            
        elif tag == 'AbiHint':
            pass
        elif tag == 'Put':
            pass
        elif tag == 'PutI':
            pass
        elif tag == 'WrTmp':
            self.stmt = WrTmp(a, b)
        elif tag == 'Store':
            pass
        elif tag == 'Dirty':
            pass
        elif tag == 'MBE':
            pass
        elif tag == 'Exit':
            pass


class Ist_IMark:
    def __init__(self, addr, l):
        self.addr = addr
        self.l = l


class Ist_WrTmp:
    def __init__(self, tmp, data):
        '''
        @type tmp:  IRTemp
        @type data: IRExpr
        '''
        self.tmp = tmp
        self.data = data

    def pp(self):
        return self.tmp.pp() + ' = ' + self.data.pp()


class Ist_Put:
    def __init__(self, offset, data):
        '''
        @type offset:  int
        @type data:    IRExpr
        '''
        self.offset = offset
        self.data = data

    def pp(self):
        return 'PUT(%d) = %s' % (self.offset, self.data.pp())


class Ist_Store:
    def __init__(self, end, addr, data):
        '''
        @type end:  str
        @type addr: IRExpr
        @type data: IRExpr
        '''
        self.end = end
        self.addr = addr
        self.data = data

    def pp(self):
        return 'ST%s(%s) = %s' % (self.end, self.addr.pp(), self.data.pp())
