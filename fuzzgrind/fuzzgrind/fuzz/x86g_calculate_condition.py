#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


def inverse(d):
    new_d = {}
    for (k, v) in d.items():
        new_d[v] = k
    return new_d
    

# valgrind/VEX/priv/guest-x86/gdefs.h
X86CCop = inverse({
    'X86G_CC_OP_COPY': 0,
    
    'X86G_CC_OP_ADDB': 1,
    'X86G_CC_OP_ADDW': 2,
    'X86G_CC_OP_ADDL': 3,
    
    'X86G_CC_OP_SUBB': 4,
    'X86G_CC_OP_SUBW': 5,
    'X86G_CC_OP_SUBL': 6,

    'X86G_CC_OP_ADCB': 7,
    'X86G_CC_OP_ADCW': 8,
    'X86G_CC_OP_ADCL': 9,

    'X86G_CC_OP_SBBB': 10,
    'X86G_CC_OP_SBBW': 11,
    'X86G_CC_OP_SBBL': 12,

    'X86G_CC_OP_LOGICB': 13,
    'X86G_CC_OP_LOGICW': 14,
    'X86G_CC_OP_LOGICL': 15,

    'X86G_CC_OP_INCB': 16,
    'X86G_CC_OP_INCW': 17,
    'X86G_CC_OP_INCL': 18,

    'X86G_CC_OP_DECB': 19,
    'X86G_CC_OP_DECW': 20,
    'X86G_CC_OP_DECL': 21,

    'X86G_CC_OP_SHLB': 22,
    'X86G_CC_OP_SHLW': 23,
    'X86G_CC_OP_SHLL': 24,

    'X86G_CC_OP_SHRB': 25,
    'X86G_CC_OP_SHRW': 26,
    'X86G_CC_OP_SHRL': 27,

    'X86G_CC_OP_ROLB': 28,
    'X86G_CC_OP_ROLW': 29,
    'X86G_CC_OP_ROLL': 30,

    'X86G_CC_OP_RORB': 31,
    'X86G_CC_OP_RORW': 32,
    'X86G_CC_OP_RORL': 33,

    'X86G_CC_OP_UMULB': 34,
    'X86G_CC_OP_UMULW': 35,
    'X86G_CC_OP_UMULL': 36,

    'X86G_CC_OP_SMULB': 37,
    'X86G_CC_OP_SMULW': 38,
    'X86G_CC_OP_SMULL': 39
})
    
X86Condcode = inverse({ 
    'X86CondO'      : 0,
    'X86CondNO'     : 1,
    'X86CondB'      : 2,
    'X86CondNB'     : 3,
    'X86CondZ'      : 4,
    'X86CondNZ'     : 5,
    'X86CondBE'     : 6,
    'X86CondNBE'    : 7,
    'X86CondS'      : 8,
    'X86CondNS'     : 9,
    'X86CondP'      : 10,
    'X86CondNP'     : 11,
    'X86CondL'      : 12,
    'X86CondNL'     : 13,
    'X86CondLE'     : 14,
    'X86CondNLE'    : 15,
    'X86CondAlways' : 16
})


SIZE = {
    'L': 32,
    'W': 16,
    'B': 8
}


def sub(size, cond, cc_dep1, cc_dep2):
    if cond == 'X86CondZ':
        if   size == 8:  return '1Uto32(CmpEQ8(32to8(%s),32to8(%s)))' % (cc_dep1, cc_dep2)
        elif size == 32: return '1Uto32(CmpEQ32(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'X86CondLE':
        if   size == 32: return '1Uto32(CmpLE32S(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'X86CondL':
        if   size == 32: return '1Uto32(CmpLT32S(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'X86CondB':
        if   size == 8:  return '1Uto32(CmpLT32U(8Uto32(%s),8Uto32(%s)))' % (cc_dep1, cc_dep2)
        elif size == 16: return '1Uto32(CmpLT32U(16Uto32(%s),16Uto32(%s)))' % (cc_dep1, cc_dep2)
        elif size == 32: return '1Uto32(CmpLT32U(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'X86CondBE':
        if   size == 8:  return '1Uto32(CmpLE32U(8Uto32(%s),8Uto32(%s)))' % (cc_dep1, cc_dep2)
        elif size == 16: return '1Uto32(CmpLE32U(16Uto32(%s),16Uto32(%s)))' % (cc_dep1, cc_dep2)
        elif size == 32: return '1Uto32(CmpLE32U(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'X86CondNBE':
        if   size == 8:  return '1Uto32(CmpLT32U(8Uto32(%s),8Uto32(%s)))' % (cc_dep1, cc_dep2)
        
    assert False, "Can't generate constraint for cond=%s, size=%d" % (cond, size)


def x86g_calculate_condition(cond, cc_op, cc_dep1, cc_dep2):
    cond = X86Condcode[cond.const.value]
    cc_op = X86CCop[cc_op.const.value]
    size = SIZE[cc_op[-1]]
    
    if 'SUB' in cc_op:
        e = sub(size, cond, cc_dep1, cc_dep2)
    else:
        assert False, cc_op
        
    return e
