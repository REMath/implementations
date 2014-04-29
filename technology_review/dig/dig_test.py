from dig import DIG
from vu_common import pause, list_str
from sage.all import var, set_random_seed


def cohendiv():
    dig = DIG('../invgen/Traces/NLA/cohendiv.tcs')
    rs = dig.getInvs(inv_typ='eqt', seed=0, vs=dig.vs, deg=2)

    q,y,rvu,x,a,b = var('q,y,rvu,x,a,b')
    expected_rs = [-q*y - rvu + x == 0, -a*y + b == 0, -q*y - 2*b + x >= 0, -2*a*y + rvu >= 0]
    assert set(expected_rs) == set([r.inv for r in rs]), rs

def sqrt1():
    dig = DIG('../invgen/Traces/NLA/sqrt1.tcs')
    rs = dig.getInvs(inv_typ='eqt', seed=0, vs=dig.vs, deg=2)
    assert list_str(rs) == '-1/4*t^2 - a + s - 3/4 == 0, -2*a + t - 1 == 0, 1/4*t^2 + a - nvu + 3/4 <= 0', rs

def knuth():


    dig = DIG('../invgen/Traces/NLA/knuth.tcs')
    rs = dig.getInvs(inv_typ='eqt', seed=0, vs=dig.vs, deg=3)
    assert list_str(rs) =='-k^2*t + k*t^2 == 0, 1/8*d^2*q + 1/2*d*k - 1/4*d*q - 1/2*d*rvu - nvu + rvu == 0, -k^2*t + t^3 == 0', rs
    #
    #'-k^2*t + k*t^2 == 0, 1/8*d^2*q + 1/2*d*k - 1/4*d*q - 1/2*d*rvu - nvu + rvu == 0, -k^2*t + t^3 == 0'  (seed 1)
    #'d1*k*t - d1*t^2 == 0, -k*rvu*t + rvu*t^2 == 0, -1/2*d^2*q - 2*d*k + d*q + 2*d*rvu + 4*nvu - 4*rvu == 0', rs

def aes_KeySetupEnc6():
    dig = DIG('../invgen/Traces/AES/Simple/aes_KeySetupEnc6.tc')
    rs = dig.getInvs(inv_typ='simple',seed=0)
    rs = rs[0].inv  #IExp

    expect_rs0a = 'lambda rk, cipherKey, rk1, rk0: (-rk[rk0][rk1]) + (cipherKey[4*rk0 + rk1]) == 0'
    expect_rs0b = 'lambda rk, cipherKey, rk1, rk0: (rk[rk0][rk1]) + (-cipherKey[4*rk0 + rk1]) == 0'
    expect_rs0c = 'lambda rk, cipherKey, rk0, rk1: (-rk[rk0][rk1]) + (cipherKey[4*rk0 + rk1]) == 0'
    expect_rs0d = 'lambda rk, cipherKey, rk0, rk1: (rk[rk0][rk1]) + (-cipherKey[4*rk0 + rk1]) == 0'
    expect_rs1 = [{'rk0': 4, 'rk1': 1},
                  {'rk0': 0, 'rk1': 1},
                  {'rk0': 3, 'rk1': 0},
                  {'rk0': 1, 'rk1': 1},
                  {'rk0': 2, 'rk1': 3},
                  {'rk0': 1, 'rk1': 0},
                     {'rk0': 5, 'rk1': 2},
                     {'rk0': 3, 'rk1': 3},
                     {'rk0': 4, 'rk1': 3},
                     {'rk0': 5, 'rk1': 0},
                     {'rk0': 0, 'rk1': 3},
                     {'rk0': 5, 'rk1': 3},
                     {'rk0': 1, 'rk1': 3},
                     {'rk0': 3, 'rk1': 1},
                     {'rk0': 2, 'rk1': 1},
                     {'rk0': 0, 'rk1': 2},
                     {'rk0': 2, 'rk1': 0},
                     {'rk0': 2, 'rk1': 2},
                     {'rk0': 0, 'rk1': 0},
                     {'rk0': 5, 'rk1': 1},
                     {'rk0': 3, 'rk1': 2},
                     {'rk0': 1, 'rk1': 2},
                     {'rk0': 4, 'rk1': 0},
                     {'rk0': 4, 'rk1': 2}]

    assert rs[0] in [expect_rs0a, expect_rs0b, expect_rs0c, expect_rs0d], rs[0]
    rs1 = [tuple(d.items()) for d in rs[1]]
    expect_rs1 = [tuple(d.items()) for d in expect_rs1]
    assert set(rs1) == set(expect_rs1), rs1

def paper_multidim():
    """
    TODO: sort the result so that it has the same output
    """

    dig = DIG('../invgen/Traces/AES/Simple/paper_multidim.tc')
    rs = dig.getInvs(inv_typ='simple',seed=0)

    #first result
    mrs = rs[0].inv  #IExp
    expect_rs0a = 'lambda A, B, A0: (-A[A0]) + (7*B[2*A0]) + (3*A0) == 0'
    expect_rs0b = 'lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0'
    expect_rs1 = [{'A0': 0}, {'A0': 2}, {'A0': 1}]

    assert mrs[0] in [expect_rs0a, expect_rs0b], rs[0]

    mrs1 = [tuple(d.items()) for d in mrs[1]]
    expect_rs1 = [tuple(d.items()) for d in expect_rs1]
    assert set(mrs1) == set(expect_rs1), mrs1

    #second result
    mrs = rs[1].inv  #IExp
    expect_rs0a = 'lambda B, A, B0: (7*B[B0]) + (-A[1/2*B0]) + (3/2*B0) == 0'
    expect_rs0b = 'lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0'
    expect_rs1 = [{'B0': 0}, {'B0': 4}, {'B0': 2}]

    assert mrs[0] in [expect_rs0a, expect_rs0b], rs[0]

    mrs1 = [tuple(d.items()) for d in mrs[1]]
    expect_rs1 = [tuple(d.items()) for d in expect_rs1]
    assert set(mrs1) == set(expect_rs1), mrs1

def paper_nested():
    dig = DIG('../invgen/Traces/AES/Nested/paper_nested.tc')
    rs = dig.getInvs(inv_typ='nested',seed=1)
    assert rs[0].inv == 'lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]', rs[0].inv
    assert rs[1].inv == 'lambda A,B,i1: A[i1] == B[-2*i1 + 5]', rs[1].inv

def aes_addroundkey_vn():
    dig = DIG('../invgen/Traces/AES/Nested/aes_addroundkey_vn.tc')
    rs = dig.getInvs(inv_typ='nested',seed=0)
    assert rs[0].inv == 'lambda r_,xor,st,rk,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])', rs[0].inv

def nested0():
    from dig_arrays import NestedArray
    na = NestedArray(terms=None,tcs1=[{'R': [128, 127, 126, 125], 'N':[128]}],tcs2=[],xinfo={'All': ['R'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': ['R[i]=sub(N,i)'], 'ExtFun': ['sub'], 'Input': [], 'Output': ['R']})


def test():
    #set_random_seed(0)
    #cohendiv()

    #set_random_seed(0)
    #sqrt1()

    #set_random_seed(0)
    #knuth()

    set_random_seed(0)
    aes_KeySetupEnc6()

#    set_random_seed(0)
#    paper_multidim()

    #set_random_seed(0)
    #paper_nested()

    #TODO: this has problem !
    #set_random_seed(1)
    #aes_addroundkey_vn()

