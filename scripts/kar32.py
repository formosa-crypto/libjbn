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
    


t = [ 0xfd21f4ed531c1001
 , 0xc9bb74a3d5f1bc0c
 , 0x114a28a58344cb79
 , 0x7017abd43ece2fd9
 , 0xfa2714b0e3aec5d0
 , 0x65810db43c135c21
 , 0x94e3303fae3bc06c
 , 0x4c1795b0f276a8d8
 , 0x256f11e69f2451ec
 , 0x4784a95025584d49
 , 0xdb66d5489e3a044f
 , 0x5bfa0174d8cbd413
 , 0xe7bf5e13f947fcff
 , 0xcf2dda20f9038563
 , 0xd1a6d273d2344d6f
 , 0xb3d27d7bdc048ddf
 , 0xad4976845890454d
 , 0x391765a152cfff39
 , 0xd1b42f83b1498f62
 , 0x0e4fa3a3b819caec
 , 0x43e3eb121b0b35e1
 , 0xcd6ac2b8c16b0aed
 , 0xe3257bbb8c03bc51
 , 0x49528489e8c0d92e
 , 0x2a8962ebac83f7d2
 , 0xe4e0dc790f524c62
 , 0x617a4ecd38d4bdba
 , 0x29d8fdc3faeafd21
 , 0xcda511a7b237a1a9
 , 0xeec07059caeafd7a
 , 0x402babd0f897da20
 , 0xe36cb65b684465a4
 ]

tt = [ 0x95b4bf4e27382001
 , 0xe00e21acf3cf1f66
 , 0xc6f442156eb15c90
 , 0xa865eeeb2cc9cd93
 , 0x0da8d6a1a4e5e4a2
 , 0x876845a4f4dd0d4b
 , 0x35f34d9b6002321d
 , 0xf552ffb9d8f36bb5
 , 0xc577b8f9292ef8c8
 , 0x9b0ca683e6d63ea1
 , 0x0a7b088106318a1a
 , 0xf5e1e80d57d71f56
 , 0xa9416f1faf7bb6ad
 , 0x0e1726de252bd874
 , 0xae61209943262154
 , 0x02ad0021764ed4f3
 , 0x111774509ad1271e
 , 0xadec8c751b8a1d11
 , 0x03385deb81afc746
 , 0x24af448cbb464e51
 , 0xd6b2e0ae6e346543
 , 0xebfac6b90fe6d1f7
 , 0x4071c6e87021962b
 , 0xc14e303337a7226b
 , 0x6f5994f9bf24bc62
 , 0xd40585c415046135
 , 0x055eaabd7ec9dff2
 , 0x41dafe970f6ec52d
 , 0x7020d9e19a830d9c
 , 0xfd44f69f9fd5379b
 , 0x50b29f8945e310e7
 , 0xf4fa41292de3cb27
 , 0xe41b072bb5058df4
 , 0x0d04703eb0cbbe72
 , 0x991bfa7ac48c6403
 , 0x423badccc6889752
 , 0xb37b63159dcfdbae
 , 0x6c356ed97256d395
 , 0x02ba2f94ede48603
 , 0x08f63ebd5d6ed8f1
 , 0xed2a53d87822d5e4
 , 0xbde0dc080a7f4843
 , 0x556c6912253057ff
 , 0xfb27a1d3f1d8c36a
 , 0xa554089e096f3b45
 , 0x9ca2be4d5fd0eb9c
 , 0x49df576d8ecfaa25
 , 0x09cde6829d1818c1
 , 0xbf48a5f3aee5f24b
 , 0xeee4ed1b0b03a12e
 , 0x492d81bf03aa239c
 , 0x8dd01ae06f92a2dd
 , 0x5507019eccab273e
 , 0xf7ab093ef073e8cb
 , 0xa8c1a328e426c34f
 , 0x2764e40370aaf27f
 , 0x25aa161b74fcc505
 , 0x6565242245c98ab0
 , 0x2972a73aeea5575a
 , 0x9d720fc794780358
 , 0xf3960c3d9b25dc24
 , 0xe7eaf7aa06286f07
 , 0x98010a6ce448ebd0
 , 0xca09f99079ef5edb
 ]

tval = bn2i(t)
ttval = bn2i(tt)

def sub_sa(a, b):
    ab = bn2i(a) - bn2i(b)
    sab = ab//abs(ab)
    return sab, bn_repr(abs(ab), 16)

def mul16(x, y):
    xy = bn_repr(bn2i(x)*bn2i(y), 32)
    return xy

def smul16(x, s):
    rval = (bn2i(x)*s)%2**(32*64)
    return bn_repr(rval, 32)

def add32(x, y):
    xy = bn2i(x)+bn2i(y)
    return bn_repr(xy,32)

def add32c(x, y):
    xy = bn2i(x)+bn2i(y)
    return xy>=2**(32*64), bn_repr(xy,32)

def cp16(x, c):
    return bn_repr(bn2i(x)+c, 16)

def kar(x, y):
    sa, a = sub_sa(x[:16],x[16:])
    sb, b = sub_sa(y[16:],y[:16])
    s = sa*sb
    t = mul16(a,b)
    t = smul16(t, s)
    rlo = mul16(x[:16], y[:16])
    rhi = mul16(x[16:], y[16:])
    c1, t = add32c(t, rlo)
    if (s>0): s=0
    s += c1
    c2, t = add32c(t, rhi)
    s += c2
    r = rlo + rhi
    c, rm = add32c(r[16:48],t)
    s += c
    print("s=",s,"   c1=",c1," c2=",c2," c=",c)
    print("r[48]= 0x%016x" % r[48])
    r = r[:16] + rm + cp16(r[48:],s)
    print("r[48]= 0x%016x" % r[48])
    for i in range(len(r)):
        if r[i]!=tt[i]:
            print("Check fail at %d: 0x%016x <> 0x%016x" % (i, r[i], tt[i]))
    return r
    
