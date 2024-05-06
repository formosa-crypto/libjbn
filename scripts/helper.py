import random
import string

def strhex2int(x):
    """ integer from an hex-string (possibly with whitespaces) """
    n = int(x.translate({ord(c): None for c in string.whitespace}),16)
    return n

def bn_repr(n, nlimbs=0):
    """ returns the BN representation of a number """
    if nlimbs==0:
        nlimbs = (n.bit_length() - 1) // 64 + 1
    l = []
    for i in range(nlimbs):
        x = n % 2**64
        l.append(x)
        n = n >> 64
    return l

def bn2i(l):
    """ returns the number encoded in a BN """
    e = 0
    i = 0
    for x in l:
        i += x * 2**(e*64)
        e += 1
    return i

def bn_printC(l, var=None):
    """ print C definition of a BN """
    if var:
        print("uint64_t %s[%d] =" % (var, len(l)))
    assert (len(l)!=0), "empty BN"
    c = '{'
    for x in l:
        print(" %s 0x%016x" % (c, x))
        c = ','
    print(" };")
q

def bn_rnd(nlimbs):
    """ random BN """
    assert (nlimbs>0), "wrong BN size"
    l = []
    for i in range(nlimbs):
        l.append(random.randrange(2**64))
    return l

def bn_mul(x, y):
    """ multiply two BNs """
    assert (len(x)==len(y)), "BN size mismatch"
    m = bn2i(x)*bn2i(y)
    return bn_repr(m, 2*len(x))



def test_mul_data(nlimbs):
    """ generate random test data for mul """
    x = bn_rnd(nlimbs)
    bn_printC(x, "t")
    xx = bn_mul(x, x)
    bn_printC(xx, "tt")
    
