#!/usr/bin/env python3
"""Interpreter test of a MUL module and of the Montgomery field over it.

Writes a Jasmin program whose function `test` is run by `exec test ()`, i.e.
by the source-level interpreter of jasminc, at compile time: on any host
CPU, MULX/ADCX/ADOX included (Apple Silicon, where Rosetta does not run
them). Since the compiler is verified, this checks the code that is
emitted. `test` checks the multiplication and squaring of the MUL module
and, with --field, the context and the field operations (fp_mont over
that module: _ctx_init_, _mulm_, _sqrm_, _addm_, _subm_, _toM_, _fromM_ and
the five exponentiations), against values computed here; it returns the
OR of the XORs of every word against its expected value (0: all correct)
and the number of words checked. `make exec` runs it for the modules and
sizes of the Makefile.

usage: gen_exec_test.py N MODULE BINDING [--field] [--seed S] [--cases C]
  e.g. gen_exec_test.py 4 bn_mulxr@n.jinc fp_mul_os@fp.jinc --field
       (with fp_mul_ps@fp.jinc, the products tested are _ps_muln_/_ps_sqrn_)
       gen_exec_test.py 4 bn_mulsel@n.jinc fp_mul_sel@fp.jinc --field \
           --profile x86_64_adx.jinc
       (the selector, which needs a profile: _muln_/_sqrn_)
       gen_exec_test.py 4 bn_mulxr@n.jinc fp_mul_os@fp.jinc --field --pm
       (a pseudo-Mersenne field, fp_pm: 2^255-19 and moduli R - c,
       R/2 - c; its reduction _redPM_ is also tested alone, on inputs that
       make each of its folds carry)
       gen_exec_test.py 4 bn_mulsel@n.jinc fp_mul_ksqr@fp.jinc --field \
           --ksqr 1 --profile x86_64_adx.jinc --sqr-unroll-max 2
       (the squaring over the half size, bn_ksqr, with LEVELS levels of
       half scopes: its _kar_sqrn_ is tested alone, on operands whose
       halves are equal, one apart, zero or all ones; the field is bound
       with fp_mul_ksqr, which takes it above JBN_SQR_UNROLL_MAX, and so
       does a half scope for its own half, which --sqr-unroll-max shadows
       in the size scope, for the tests to take it at a small size)
"""
import argparse
import random

ap = argparse.ArgumentParser()
ap.add_argument("n", type=int)
ap.add_argument("module")
ap.add_argument("binding")
ap.add_argument("--field", action="store_true")
ap.add_argument("--seed", type=int, default=1)
ap.add_argument("--cases", type=int, default=4)
ap.add_argument("--exp", type=int, default=1, help="exponentiations per modulus")
ap.add_argument("--profile", help="a profile of src/amd64/ref/profiles (default: "
                "x86_64_adx.jinc for a MULX module, x86_64.jinc otherwise)")
ap.add_argument("--pm", action="store_true", help="the field is fp_pm (pseudo-Mersenne)")
ap.add_argument("--ksqr", type=int, default=0, metavar="LEVELS",
                help="instantiate bn_ksqr (the squaring over the half size) with "
                "LEVELS levels of half scopes; MODULE must be bn_mulsel@n.jinc "
                "and BINDING fp_mul_ksqr@fp.jinc")
ap.add_argument("--sqr-unroll-max", type=int, metavar="MAX",
                help="shadow JBN_SQR_UNROLL_MAX in the size scope (with --ksqr)")
args = ap.parse_args()

N = args.n
if args.ksqr:
    assert N % (1 << args.ksqr) == 0, "the size is not a multiple of 2^LEVELS"
    assert "bn_mulsel" in args.module and "fp_mul_ksqr" in args.binding
random.seed(args.seed)
W = 2 ** 64
R = W ** N
CTXLEN = 4 * N + 1


def limbs(x, n=N):
    return [(x >> (64 * i)) % W for i in range(n)]


def ctx(P):
    if args.pm:
        return limbs(P) + limbs(R - P) + limbs(1) + limbs(0) + [R % P]
    return limbs(P) + limbs(R - P) + limbs(R % P) + limbs(R * R % P) + \
        [(-pow(P, -1, W)) % W]


out = []
emit = out.append


def load(arr, words):
    for i, w in enumerate(words):
        emit("  t = 0x%x; %s[%d] = t;" % (w, arr, i))


def check(arr, words):
    for i, w in enumerate(words):
        emit("  t = %s[%d]; u = 0x%x; t ^= u; acc |= t; cnt += 1;" % (arr, i, w))


# a profile: for the selector bn_mulsel, and, with a field, for the
# constant-time exponentiation _expm_ of bn_exp (JBN_EXP_WINDOW)
profile = args.profile or ("x86_64_adx.jinc" if "mulx" in args.module else "x86_64.jinc")
emit('from Libjbn require "profiles/%s"' % profile)


def emit_ksqr(depth, ind):
    """KSQR of the scope at `depth` (0: the size under test): its half
    squaring is the one of the selector when the half scope is the last
    one; otherwise it is selected by the profile, between the selector
    and the KSQR of the half scope."""
    emit(ind + "namespace KSQR {")
    emit(ind + "  inline fn fun_ksqrn")
    emit(ind + "  ( reg mut ptr u64[nlimbs] r")
    emit(ind + "  , reg const ptr u64[H::nlimbs] a")
    emit(ind + "  ) -> reg ptr u64[nlimbs] {")
    if depth + 1 == args.ksqr:
        emit(ind + "    r = H::MUL::_sqrn_(r, a);")
    else:
        # as fp_mul_ksqr at the size of the field
        emit(ind + "    if (H::nlimbs <= JBN_SQR_UNROLL_MAX) {")
        emit(ind + "      r = H::MUL::_sqrn_(r, a);")
        emit(ind + "    } else {")
        emit(ind + "      r = H::KSQR::_kar_sqrn_(r, a);")
        emit(ind + "    }")
    emit(ind + "    return r;")
    emit(ind + "  }")
    emit(ind + '  from Libjbn require "bn_ksqr@2n.jinc"')
    emit(ind + "}")


def emit_half(depth, ind):
    """The scope of the half size at `depth` (1 .. LEVELS), nested."""
    emit(ind + "namespace H {")
    emit(ind + "  param int nlimbs = %d;" % (N >> depth))
    if depth < args.ksqr:
        emit_half(depth + 1, ind + "  ")
    emit(ind + '  namespace BN  { from Libjbn require "bn_base@n.jinc" }')
    emit(ind + '  namespace MUL { from Libjbn require "%s" }' % args.module)
    if depth < args.ksqr:
        emit_ksqr(depth, ind + "  ")
    emit(ind + "}")


emit("""namespace UTIL { from Libjbn require "bn_util.jinc" }
namespace H {
  param int nlimbs = %d;""" % N)
if args.sqr_unroll_max is not None:
    emit("  param int JBN_SQR_UNROLL_MAX = %d;" % args.sqr_unroll_max)
if args.ksqr:
    emit_half(1, "  ")
emit("""  namespace BN  { from Libjbn require "bn_base@n.jinc" }
  namespace RND { from Libjbn require "bn_rnd@n.jinc" }
  namespace MUL { from Libjbn require "%s" }""" % args.module)
if args.ksqr:
    emit_ksqr(0, "  ")
if args.field:
    emit("""  namespace FPM {
    from Libjbn require "%s"
    from Libjbn require "%s"
  }""" % (args.binding, "fp_pm@fp.jinc" if args.pm else "fp_mont@fp.jinc"))
emit("}")
emit("""
fn test() -> reg u64, reg u64 {
  stack u64[H::nlimbs] _a _b _e _r _p;
  stack u64[2*H::nlimbs] _r2;""")
if args.field:
    emit("  stack u64[H::FPM::CTXLEN] _c;")
    emit("  reg ptr u64[H::FPM::CTXLEN] c;")
emit("""  reg ptr u64[H::nlimbs] a b e r p;
  reg ptr u64[2*H::nlimbs] r2;
  reg u64 acc cnt t u;
  acc = 0; cnt = 0;""")

# plain products
MULN, SQRN = ("_ps_muln_", "_ps_sqrn_") if "fp_mul_ps" in args.binding \
    else ("_muln_", "_sqrn_") if "fp_mul_sel" in args.binding or args.ksqr \
    else ("_os_muln_", "_os_sqrn_")
for _ in range(args.cases + 2):
    x, y = random.randrange(R), random.randrange(R)
    if _ == 0:
        x = y = R - 1
    load("_a", limbs(x)); load("_b", limbs(y))
    emit("  a = _a; b = _b; r2 = _r2; r2 = H::MUL::%s(r2, a, b)" % MULN + "; _r2 = r2;")
    check("_r2", limbs(x * y, 2 * N))
    emit("  a = _a; r2 = _r2; r2 = H::MUL::%s(r2, a)" % SQRN + "; _r2 = r2;")
    check("_r2", limbs(x * x, 2 * N))

if args.ksqr:
    # the squaring over the half size alone: x = lo + B * hi, on which it
    # squares lo, hi and |lo - hi| and counts the borrows of three
    # subtractions
    B = W ** (N // 2)
    lo, hi = sorted(random.randrange(1, B - 1) for _ in range(2))
    h = random.randrange(B)
    halves = [(0, 0), (B - 1, B - 1), (h, h),                 # lo = hi
              ((h + 1) % B, h), ((h - 1) % B, h),             # one apart
              (0, B - 1), (B - 1, 0),                         # the largest |lo - hi|
              (h, 0), (0, h), (1, 0), (0, 1),                 # a zero half
              (lo, hi), (hi, lo),                             # lo < hi, lo > hi
              (lo, lo + 1), (hi, hi - 1)]
    halves += [(random.randrange(B), random.randrange(B)) for _ in range(args.cases)]
    for lo_, hi_ in halves:
        x = lo_ + B * hi_
        load("_a", limbs(x))
        emit("  a = _a; r2 = _r2; r2 = H::KSQR::_kar_sqrn_(r2, a); _r2 = r2;")
        check("_r2", limbs(x * x, 2 * N))

if args.field:
    def rand_odd(lo, hi):
        return random.randrange(lo, hi) | 1
    if args.pm:
        # R mod P < 2^32 and R < 3 P: R - c (R mod P = c), R/2 - c
        # (R mod P = 2c), at both ends of the range of c
        moduli = [R - 1, R - 189, R - (2 ** 32 - 1), R // 2 - 1,
                  R // 2 - (2 ** 31 - 1), R // 2 - random.randrange(1, 2 ** 20) * 2 - 1]
        if N == 4:
            moduli.insert(0, 2 ** 255 - 19)
        moduli = [P for P in moduli if P > 2 and P % 2 == 1]
        if N == 1:   # (2^31-1 > R/3 is not enough for R//2 - (2^31-1))
            moduli = [P for P in moduli if 3 * P > R]
    else:
        moduli = [R - 1, 3, rand_odd(R // 2, R), rand_odd(3, 2 ** 64)]
        if N > 1:
            moduli += [rand_odd(R // 2 ** 70, R // 2 ** 65), rand_odd(3, R // 2 ** 64)]
        if N == 4:
            moduli.append(2 ** 255 - 19)
    for P in moduli:
        Ri = 1 if args.pm else pow(R, -1, P)
        Rr = 1 if args.pm else R      # the representation: x -> x * Rr mod P
        if args.pm:
            assert R % P < 2 ** 32 and R < 3 * P
            emit("  _c = _c;")
        load("_p", limbs(P))
        emit("  p = _p; c = _c; c = H::FPM::_ctx_init_(c, p); _c = c;")
        check("_c", ctx(P))
        if args.pm:
            # the reduction alone, on a < R^2: R^2 - 1, random, and inputs
            # whose first fold leaves [s ; t] = [R - 1 ; 1], so that the
            # second fold carries and the third one is taken
            cP = R % P
            H = -(-R // cP)
            crafted = [R * R - 1, random.randrange(R * R), random.randrange(R * R)]
            if H < R:      # (not for c = 1)
                crafted.append((2 * R - 1 - cP * H) + R * H)
            for x in crafted:
                assert 0 <= x < R * R
                load("_r2", limbs(x, 2 * N))
                emit("  r2 = _r2; r = _r; c = _c; r = H::FPM::_redPM_(r, r2, c); _r = r;")
                check("_r", limbs(x % P))
        for k in range(args.cases):
            a, b = random.randrange(P), random.randrange(P)
            if k == 0:
                a = b = P - 1
            load("_a", limbs(a)); load("_b", limbs(b))
            for op, v in [("_mulm_(r, a, b, c)", a * b * Ri % P),
                          ("_addm_(r, a, b, c)", (a + b) % P),
                          ("_subm_(r, a, b, c)", (a - b) % P)]:
                emit("  a = _a; b = _b; r = _r; c = _c; r = H::FPM::%s; _r = r;" % op)
                check("_r", limbs(v))
            emit("  a = _a; r = _r; c = _c; r = H::FPM::_sqrm_(r, a, c); _r = r;")
            check("_r", limbs(a * a * Ri % P))
            emit("  a = _a; c = _c; a = H::FPM::_toM_(a, c); _r = a;")
            check("_r", limbs(a * Rr % P))
            emit("  a = _a; c = _c; a = H::FPM::_fromM_(a, c); _r = a;")
            check("_r", limbs(a * Ri % P))
            if k < args.exp + 2:
                # the LR exponentiation skips the zero top limbs of e
                e = [random.randrange(R), random.randrange(W), 0][k % 3] if k >= args.exp else random.randrange(R)
                load("_e", limbs(e))
                want = limbs(pow(a * Ri % P, e, P) * Rr % P)
                # the selected one (the window, by the profiles), then the two
                emit("  a = _a; e = _e; r = _r; c = _c; r = H::FPM::EXP::_expm_(r, a, e, c); _r = r;")
                check("_r", want)
                emit("  a = _a; e = _e; r = _r; c = _c; r = H::FPM::EXP::_expmML_(r, a, e, c); _r = r;")
                check("_r", want)
                emit("  a = _a; e = _e; r = _r; c = _c; r = H::FPM::EXP::_expmW_(r, a, e, c); _r = r;")
                check("_r", want)
                emit("  a = _a; e = _e; r = _r; c = _c; r = H::FPM::EXP::_expm_noct_(r, a, e, c); _r = r;")
                check("_r", want)
                emit("  a = _a; e = _e; r = _r; c = _c; r = H::FPM::EXP::_expmLR_noct_(r, a, e, c); _r = r;")
                check("_r", want)

emit("  return acc, cnt;\n}\n\nexec test ()")
print("\n".join(out))
