#!/usr/bin/env python3
"""Test vectors for the fpc_* entry points (run-time contexts), for moduli
of N limbs: usage  gen_vectors.py N [SEED] > vectors.txt"""
import random
import sys

N = int(sys.argv[1])
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
W = 2 ** 64
R = W ** N


def is_prime(n):
    if n < 4:
        return n in (2, 3)
    d, s = n - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    for _ in range(32):
        x = pow(random.randrange(2, n - 1), d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def rand_prime(lo, hi):
    while True:
        p = random.randrange(lo, hi) | 1
        if is_prime(p):
            return p


def limbs(x):
    return [(x >> (64 * i)) % W for i in range(N)]


def ctx(P):
    return limbs(P) + limbs(R - P) + limbs(R % P) + limbs(R * R % P) + \
        [(-pow(P, -1, W)) % W]


moduli = [R - 1, 3, rand_prime(R // 2, R), rand_prime(2, 2 ** 64),
          rand_prime(R // 2 ** 70, R // 2 ** 65),          # top limb small
          random.randrange(R // 2, R) | 1,                 # odd, composite
          random.randrange(3, R // 2 ** 64) | 1]           # top limb zero
moduli += [rand_prime(R // 4, R) for _ in range(3)]
CASES = 20
out = [str(len(moduli))]
for P in moduli:
    prime = is_prime(P)
    Ri = pow(R, -1, P)
    out.append(" ".join("%x" % w for w in limbs(P) + ctx(P)))
    out.append("%d %d" % (CASES, 1 if prime else 0))
    for _ in range(CASES):
        a, b = random.randrange(P), random.randrange(P)
        e = random.randrange(R)
        x = a * Ri % P                       # the value a represents
        res = [(a + b) % P, (a - b) % P, a * b * Ri % P, a * a * Ri % P,
               a * R % P, a * Ri % P, pow(x, e, P) * R % P,
               pow(x, P - 2, P) * R % P if prime else 0]
        out.append(" ".join("%x" % w for v in [a, b, e] + res for w in limbs(v)))
print("\n".join(out))
