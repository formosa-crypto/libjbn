#!/usr/bin/env python3
"""Safety theories of libjbn from the safety extraction (proof/safety).

Every module of the abstract instantiation (src/amd64/ref/extracted/
libjbn_abs.jazz) is extracted with Jasmin's safety model at two dummy points,
A and B (src/amd64/ref/extracted/dummy{A,B}/dummy.jinc), into
proof/safety/extracted/{A,B}/<QUAL>_<module>_safety.ec (`make -C proof/safety
extract`).  With --safety-symbolic-params the parameters stay symbolic through
the simplification of the safety model, so the two extractions of a module
have the same tokens except where a parameter, or a size computed from the
parameters, is printed (as a numeral, or in the name of a byte-array theory
`BArrayN` / `SBArrayN_M`).  This script reads each such pair back as an
expression over the parameters.

Commands:
  align [MODULE...]   check that the extractions at A and B of each module
                      align token for token, and that every differing numeral
                      pair is one parameter or one size k*p + c (p a
                      parameter, c small): fails on any other difference and
                      on ambiguous pairs; prints the sizes found.
  lint [MODULE...]    report the calls that pass an uninitialised array (a
                      fresh one) where the callee's contract requires it
                      initialised (a contract the caller cannot meet).
  gen [THEORY...]     write, for each theory (keys of THEORIES, default all),
                      proof/safety/theories/<Name>_xtr.eca (the parameters,
                      the byte-array theories, the clones of the callee
                      theories, the module and its specifications, no lemma),
                      proof/safety/theories/<Name>_skeleton.ec (the lemmas to
                      prove in proof/safety/<Name>.eca, never checked), and
                      proof/safety/checkxtr/{A,B}/<Name>_checkxtr.ec (the
                      theory cloned at the point, one equivalence by sim per
                      procedure with the extraction, and the transfer of each
                      lemma to the extractor's own specification).

The theories mirror the correctness theories (proof/*.eca): each module is
an abstract theory over nlimbs (and nlimbsexp, the profile) whose callees
are clones of the other theories; a module with function parameters is a
functor M(P: MParam), whose specifications are module-free ops (_pre, _post:
an op cannot mention the declared module of a section) and whose lemmas are
stated in a section with the contracts of the parameters as declared
axioms.  The byte arrays of a theory are clones of ByteArray / SubByteArray
named after their sizes (BA_8n: 8*nlimbs bytes, SB_16n__8n: the 8*nlimbs-byte
slices of a 16*nlimbs-byte array, ...), passed on to the callee clones.
"""
import argparse
import os
import re
import sys
from collections import Counter, OrderedDict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SAFETY = os.path.join(ROOT, 'proof', 'safety')
XDIR = os.path.join(SAFETY, 'extracted')
DUMMY = os.path.join(ROOT, 'src', 'amd64', 'ref', 'extracted')

# the parameters: name in the theories <- name in dummy{A,B}/dummy.jinc
PARAMS = OrderedDict([
    ('nlimbs', 'DUMMY_NLIMBS'),
    ('nlimbsexp', 'DUMMY_NLIMBSEXP'),
    ('jbn_features', 'DUMMY_FEATURES'),
    ('jbn_reg_max', 'DUMMY_REG_MAX'),
    ('jbn_unroll_max', 'DUMMY_UNROLL_MAX'),
    ('jbn_sqr_unroll_max', 'DUMMY_SQR_UNROLL_MAX'),
    ('jbn_exp_window', 'DUMMY_EXP_WINDOW'),
])
# parameters a size may be an affine function of, and the bound on the
# constant term of such a size; a larger one (up to MAX_CONST_FAR) only when
# no expression has a small one (bn_mulxr's squaring reads back the words
# w + 10 <= 2*nlimbs from memory: the range 8*(2*nlimbs - 10))
SIZE_PARAMS = ('nlimbs', 'nlimbsexp')
MAX_CONST = 16
MAX_CONST_FAR = 96
MAX_COEF = 128                     # the table of bn_exp: 16*nlimbs words

TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9']*|\d+|\S")
BARRAY = re.compile(r'^BArray(\d+)$')
SBARRAY = re.compile(r'^SBArray(\d+)_(\d+)$')
SYSCALL = re.compile(r'^(randombytes)_(\d+)$')    # a system call on N bytes


def die(msg):
    sys.stderr.write('xtr_safety: ' + msg + '\n')
    sys.exit(1)


def read_point(p):
    path = os.path.join(DUMMY, 'dummy' + p, 'dummy.jinc')
    vals = dict(re.findall(r'param\s+int\s+(\w+)\s*=\s*(\d+)\s*;', open(path).read()))
    try:
        return OrderedDict((k, int(vals[v])) for k, v in PARAMS.items())
    except KeyError as e:
        die('%s: no value for %s' % (path, e))


PA, PB = read_point('A'), read_point('B')


# ---------------------------------------------------------------------------
# sizes: expressions over the parameters, as (param or None, coef, const)

def candidates(a, b, max_const=MAX_CONST):
    """The expressions taking the value a at point A and b at point B."""
    out = []
    for p in PARAMS:
        if (PA[p], PB[p]) == (a, b):
            out.append((p, 1, 0))
    for p in SIZE_PARAMS:
        da = PA[p] - PB[p]
        if da == 0 or (a - b) % da:
            continue
        k = (a - b) // da
        c = a - k * PA[p]
        if 1 <= k <= MAX_COEF and abs(c) <= max_const and (k, c) != (1, 0):
            out.append((p, k, c))
    return out


def show(e):
    p, k, c = e
    if k == 1 and c == 0:
        return p
    g = k if c == 0 else gcd(k, abs(c))
    # factor the gcd out: 32*n + 8 = 8 * (4 * n + 1)
    if g > 1 and c != 0:
        inner = show((p, k // g, c // g))
        return '(%d * %s)' % (g, inner if inner.startswith('(') else '(%s)' % inner)
    s = p if k == 1 else '(%d * %s)' % (k, p)
    if c > 0:
        return '(%s + %d)' % (s, c)
    if c < 0:
        return '(%s - %d)' % (s, -c)
    return s


def gcd(x, y):
    while y:
        x, y = y, x % y
    return x


def resolve(a, b, where, sizes):
    cs = candidates(a, b) or candidates(a, b, MAX_CONST_FAR)
    if not cs:
        die('%s: the numerals %d (A) / %d (B) are no parameter nor size' % (where, a, b))
    if len(cs) > 1:
        die('%s: the numerals %d (A) / %d (B) are ambiguous: %s (change point B)'
            % (where, a, b, ', '.join(show(c) for c in cs)))
    sizes[(a, b)] = cs[0]
    return cs[0]


# ---------------------------------------------------------------------------
# alignment of the two extractions of a module

def extraction(module, p):
    path = os.path.join(XDIR, p, module + '_safety.ec')
    if not os.path.exists(path):
        die('%s: missing (make -C proof/safety extract)' % os.path.relpath(path, ROOT))
    return open(path).read()


def body(text):
    """The extraction from its first module on (the header requires the array
    theories in the order of their sizes, which may differ between points)."""
    m = re.search(r'^module ', text, re.M)
    return text[m.start():] if m else text


def align(module, sizes, arrays):
    ta = TOKEN.findall(body(extraction(module, 'A')))
    tb = TOKEN.findall(body(extraction(module, 'B')))
    if len(ta) != len(tb):
        die('%s: %d tokens at A, %d at B' % (module, len(ta), len(tb)))
    diffs = Counter()
    for i, (x, y) in enumerate(zip(ta, tb)):
        if x == y:
            continue
        ctx = ' '.join(ta[max(0, i - 6):i + 4])
        where = '%s: token %d (... %s ...)' % (module, i, ctx)
        if x.isdigit() and y.isdigit():
            resolve(int(x), int(y), where, sizes)
        elif BARRAY.match(x) and BARRAY.match(y):
            e = resolve(int(BARRAY.match(x).group(1)), int(BARRAY.match(y).group(1)), where, sizes)
            arrays.add(('B', e))
        elif SBARRAY.match(x) and SBARRAY.match(y):
            ma, mb = SBARRAY.match(x), SBARRAY.match(y)
            big = resolve(int(ma.group(1)), int(mb.group(1)), where, sizes)
            small = resolve(int(ma.group(2)), int(mb.group(2)), where, sizes)
            arrays.add(('SB', big, small))
        elif SYSCALL.match(x) and SYSCALL.match(y) and SYSCALL.match(x).group(1) == SYSCALL.match(y).group(1):
            e = resolve(int(SYSCALL.match(x).group(2)), int(SYSCALL.match(y).group(2)), where, sizes)
            arrays.add(('B', e))
        elif re.match(r'^W?Array\d+$', x) and re.match(r'^W?Array\d+$', y):
            pass                        # the require line of old-model theories
        else:
            die('%s: %r (A) / %r (B) is no parameter nor size' % (where, x, y))
        diffs[(x, y)] += 1
    return len(ta), diffs


def cmd_align(args):
    sizes, arrays = {}, set()
    for m in args.modules:
        n, diffs = align(m, sizes, arrays)
        print('%-24s %6d tokens, %4d differing' % (m, n, sum(diffs.values())))
    print('\nparameters and sizes (A / B):')
    for (a, b), e in sorted(sizes.items(), key=lambda kv: (kv[1][0], kv[1][1], kv[1][2])):
        print('  %5d / %-5d %s' % (a, b, show(e)))
    print('\nbyte arrays:')
    for t in sorted(arrays, key=str):
        print('  ' + ('BArray %s' % show(t[1]) if t[0] == 'B'
                      else 'SBArray %s of %s' % (show(t[2]), show(t[1]))))


# ---------------------------------------------------------------------------
# the theories: one per module of the abstract instantiation
#   xtr         base name of the extraction (extracted/{A,B}/<xtr>_safety.ec)
#   prefix      prefix of the module's procedures in the extraction
#   name        name of the theory (proof/safety/<name>.eca, the lemmas;
#               theories/<name>_xtr.eca, generated)
#   calls       prefix -> theory key: the callee modules (clones)
#   params      the function parameters (stubs of libjbn_abs.jazz): module
#               type MParam, module M(P: MParam)
#   extparams   prefix -> procedures: procedures of another module that the
#               theory takes as members of MParam instead of a clone (fp_mont:
#               the selector's __mont_redM, so that it does not depend on the
#               five multiplication theories)
#   subinstances  sub-prefix -> theory, clone name, nested binding module,
#               bindings of its parameters, op substitutions
#   includes    an included theory (its procedures are in the module's
#               namespace): theory, clone name, nested module, bindings

THEORIES = OrderedDict([
    ('bn_util', dict(xtr='BNUTIL_bn_util', prefix='uTIL__', name='Bn_util_safety')),
    ('bn_base', dict(xtr='BN_bn_base', prefix='h__BN__', name='Bn_base_safety',
                     calls={'uTIL__': 'bn_util'})),
    ('bn_rnd', dict(xtr='BNRND_bn_rnd', prefix='h__RND__', name='Bn_rnd_safety',
                    calls={'h__BN__': 'bn_base'})),
    ('bn_mul', dict(xtr='BNMUL_bn_mul', prefix='h__MUL__UNR__', name='Bn_mul_safety',
                    calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'})),
    ('bn_mul_loop', dict(xtr='BNMULL_bn_mul_loop', prefix='h__MUL__LOOP__',
                         name='Bn_mul_loop_safety',
                         calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'})),
    ('bn_mulx', dict(xtr='BNMULX_bn_mulx', prefix='h__MUL__XUNR__', name='Bn_mulx_safety',
                     calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'})),
    ('bn_mulx_loop', dict(xtr='BNMULXL_bn_mulx_loop', prefix='h__MUL__XLOOP__',
                          name='Bn_mulx_loop_safety',
                          calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'})),
    ('bn_mulxr', dict(xtr='BNMULXR_bn_mulxr', prefix='h__MUL__XREG__', name='Bn_mulxr_safety',
                      calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'})),
    ('bn_mulsel', dict(xtr='BNMULSEL_bn_mulsel', prefix='h__MUL__', name='Bn_mulsel_safety',
                       calls={'h__MUL__UNR__': 'bn_mul', 'h__MUL__LOOP__': 'bn_mul_loop',
                              'h__MUL__XUNR__': 'bn_mulx', 'h__MUL__XLOOP__': 'bn_mulx_loop',
                              'h__MUL__XREG__': 'bn_mulxr'})),
    ('bn_mulreg', dict(xtr='BNMULREG_bn_mulreg', prefix='h__MULREG__', name='Bn_mulreg_safety')),
    # one level of Karatsuba, in the 2n scope: the half-size bn_base is a
    # clone, the procedures of the 2n-size one it calls are parameters
    ('bn_karatsuba', dict(xtr='BNKAR_bn_karatsuba', prefix='kAR__', name='Bn_karatsuba_safety',
                          calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                          params=['fun_kmuln'],
                          extparams={'bN__': ['_addU_', '_neg_', '_cmov_']})),
    # the squaring over the half size, in a 2n scope of its own (KSQR, whose
    # size is a literal): as bn_karatsuba, with the 2n-size _subU_ (KSQR::BN)
    # as a parameter
    ('bn_ksqr', dict(xtr='BNKSQR_bn_ksqr', prefix='kSQR__', name='Bn_ksqr_safety',
                     calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                     params=['fun_ksqrn'],
                     extparams={'kSQR__BN__': ['_subU_']})),
    ('bn_exp', dict(xtr='BNE_bn_exp', prefix='h__EXP__', name='Bn_exp_safety',
                    calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                    params=['fun_mulU', 'fun_sqrU'])),
    ('fp_base', dict(xtr='FP_fp_base', prefix='h__FP__', name='Fp_base_safety',
                     calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                     params=['fun_muln', 'fun_sqrn', 'fun_red'],
                     subinstances={'EXP__': dict(
                         theory='bn_exp', clone='BNE', nested='P_EXP',
                         bind=[('fun_mulU', 'fun_mulU'), ('fun_sqrU', 'fun_sqrU')],
                         ops={'nlimbsexp': 'nlimbs'})})),
    ('fp_mont', dict(xtr='FPM_fp_mont', prefix='h__FPM__', name='Fp_mont_safety',
                     calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                     params=['fun_muln', 'fun_sqrn'],
                     extparams={'h__MUL__': ['__mont_redM']},
                     includes=dict(theory='fp_base', clone='FPB', nested='P_FPB',
                                   bind=[('fun_muln', 'P.fun_muln'),
                                         ('fun_sqrn', 'P.fun_sqrn'),
                                         ('fun_red', 'fun_red')]))),
    ('fp_pm', dict(xtr='FPPM_fp_pm', prefix='h__FPPM__', name='Fp_pm_safety',
                   calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                   params=['fun_muln', 'fun_sqrn'],
                   includes=dict(theory='fp_base', clone='FPB', nested='P_FPB',
                                 bind=[('fun_muln', 'P.fun_muln'),
                                       ('fun_sqrn', 'P.fun_sqrn'),
                                       ('fun_red', 'fun_red')]))),
    # the export templates (src/amd64/ref/*_export@2n.jinc): top-level
    # procedures, over the library procedures they call (parameters)
    ('bn_base_export', dict(xtr='EXBN_bn_base_export', prefix='', name='Bn_base_export_safety',
                            calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'},
                            own_extra=['h__BN___store'])),
    ('bn_mul_export', dict(xtr='EXMUL_bn_mul_export', prefix='', name='Bn_mul_export_safety',
                           calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'}, own_prefixes=['bN__'],
                           pure_params=True,
                           extparams={'h__MUL__': ['_ps_muln', '_ps_sqrn_', '_os_muln']})),
    ('bn_mul_loop_export', dict(xtr='EXMULL_bn_mul_loop_export', prefix='',
                                name='Bn_mul_loop_export_safety',
                                calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'}, own_prefixes=['bN__'],
                                pure_params=True,
                                extparams={'h__MUL__': ['_os_muln', '_os_sqrn']})),
    ('bn_karatsuba_export', dict(xtr='EXKAR_bn_karatsuba_export', prefix='',
                                 name='Bn_karatsuba_export_safety',
                                 own_extra=['h__BN____load', 'h__BN___load', 'h__BN___load_',
                                            'bN____store', 'bN___store_'],
                                 pure_params=True,
                                 extparams={'h__KAR__': ['_kar_muln_']})),
    ('bn_ksqr_export', dict(xtr='EXKSQR_bn_ksqr_export', prefix='',
                            name='Bn_ksqr_export_safety',
                            own_extra=['h__BN____load', 'h__BN___load', 'h__BN___load_',
                                       'bN____store', 'bN___store_'],
                            pure_params=True,
                            extparams={'h__KSQR__': ['_kar_sqrn_']})),
    ('fp_mont_ctx_export', dict(xtr='EXFPC_fp_mont_ctx_export', prefix='',
                                name='Fp_mont_ctx_export_safety',
                                calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'}, pure_params=True,
                                extparams={'h__FPM__': ['_ctx_init_', '_addmU_', '_submU_', '_mulm_',
                                                        '_sqrm_', '_invm_', '_toM_', '_fromM_'],
                                           'h__FPM__EXP__': ['_expm_', '_expmML_', '_expm_noct_']})),
    ('fp_mont_export', dict(xtr='EXFP_fp_mont_export', prefix='', name='Fp_mont_export_safety',
                            calls={'uTIL__': 'bn_util', 'h__BN__': 'bn_base'}, pure_params=True,
                            extparams={'h__FPM__': ['_addmU_', '_submU_', '_mulm_', '_sqrm_',
                                                    '_invm_', '_toM_', '_fromM_'],
                                       'h__FPM__EXP__': ['_expm_', '_expmML_', '_expm_noct_', '_expmLR_noct_']},
                            globals={'h__FPM__glob_ctx': ('glob_ctx', 'BA_32n_8')})),
])

# clone names of the callee theories
CLONE = {'bn_util': 'BNUTIL', 'bn_base': 'BNB', 'bn_rnd': 'BNRND', 'bn_mul': 'BNMUL', 'bn_mul_loop': 'BNMULL',
         'bn_mulx': 'BNMULX', 'bn_mulx_loop': 'BNMULXL', 'bn_mulxr': 'BNMULXR',
         'bn_mulsel': 'BNMULSEL', 'bn_exp': 'BNE', 'fp_base': 'FPB'}

THYDIR = os.path.join(SAFETY, 'theories')
CHKDIR = os.path.join(SAFETY, 'checkxtr')
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")
SUFFIX = r'[0-9]+[ne](?:_m?[0-9]+)?'


def suffix(e):
    p, k, c = e
    s = '%d%s' % (k, {'nlimbs': 'n', 'nlimbsexp': 'e'}[p])
    return s + ('_%d' % c if c > 0 else '_m%d' % -c if c < 0 else '')


def parse_suffix(s):
    m = re.match(r'^(\d+)([ne])(?:_(m?)(\d+))?$', s)
    k, p = int(m.group(1)), {'n': 'nlimbs', 'e': 'nlimbsexp'}[m.group(2)]
    c = int(m.group(4) or 0) * (-1 if m.group(3) else 1)
    return (p, k, c)


def ba_name(e):
    return 'BA_' + suffix(e)


def sb_name(big, small):
    return 'SB_%s__%s' % (suffix(big), suffix(small))


def value(e, point):
    p, k, c = e
    return k * point[p] + c


def subst_expr(e, ops):
    """e with its parameter renamed by ops (sub-instances: nlimbsexp <- nlimbs)."""
    p, k, c = e
    return (ops.get(p, p), k, c)


def abstract_body(module):
    """The extraction at A from its first module on, every token that differs
    at B replaced by its expression (numerals) or by the name of its abstract
    byte-array theory."""
    a = body(extraction(module, 'A'))
    tb = TOKEN.findall(body(extraction(module, 'B')))
    spans = list(TOKEN.finditer(a))
    if len(spans) != len(tb):
        die('%s: the extractions do not align (make align)' % module)
    sizes, out, last = {}, [], 0
    for m, y in zip(spans, tb):
        x = m.group()
        if x == y:
            continue
        where = '%s: offset %d' % (module, m.start())
        if x.isdigit():
            rep = show(resolve(int(x), int(y), where, sizes))
        elif BARRAY.match(x):
            rep = ba_name(resolve(int(BARRAY.match(x).group(1)), int(BARRAY.match(y).group(1)),
                                  where, sizes))
        elif SBARRAY.match(x):
            ma, mb = SBARRAY.match(x), SBARRAY.match(y)
            rep = sb_name(resolve(int(ma.group(1)), int(mb.group(1)), where, sizes),
                          resolve(int(ma.group(2)), int(mb.group(2)), where, sizes))
        elif SYSCALL.match(x):
            ma, mb = SYSCALL.match(x), SYSCALL.match(y)
            rep = ma.group(1) + '_' + suffix(resolve(int(ma.group(2)), int(mb.group(2)),
                                                       where, sizes))
        else:
            die('%s: %r / %r (make align)' % (where, x, y))
        out.append(a[last:m.start()])
        out.append(rep)
        last = m.end()
    out.append(a[last:])
    return ''.join(out)


MODULE_OPEN = re.compile(r'^module M(\(SC:Syscall_t\))? = \{\s*$')
PROC_OPEN = re.compile(r'^  proc (\w+) \(')


def parse(text):
    """(procedures [(name, text)] in order, specs {name: (args, pre, post)},
    text before module M when it is a functor over the system calls)."""
    lines = text.splitlines(keepends=True)
    i = next((j for j, l in enumerate(lines) if MODULE_OPEN.match(l)), None)
    if i is None:
        die('module M not found')
    syscall = ''.join(lines[:i]) if MODULE_OPEN.match(lines[i]).group(1) else None
    i += 1
    procs, cur = [], None
    while not lines[i].startswith('}.'):
        l = lines[i]
        m = PROC_OPEN.match(l)
        if m:
            if cur:
                procs.append(cur)
            cur = [m.group(1), l]
        elif cur:
            cur[1] += l
        elif l.strip() and l.strip() != 'var tmp__trace : trace':
            die('unexpected line in module M: ' + l.rstrip())
        i += 1
    if cur:
        procs.append(cur)
    procs = [(n, t.rstrip() + '\n') for n, t in procs]
    rest = ''.join(lines[i + 1:])
    specs = {}
    for m in re.finditer(r'^op (\w+)_spec ((?:_\w+ ?)*)=\s*hoare \[M(?:\(Syscall\))?\.(\w+) :'
                         r'\s*(.*?)\s*==>\s*(.*?)\]\.', rest, re.M | re.S):
        name, args, proc, pre, post = m.groups()
        if name != proc:
            die('spec %s of %s' % (name, proc))
        specs[proc] = (args.split(), pre, post)
    return procs, specs, syscall


def signature(text):
    """(argument names and types, result type) of a procedure."""
    m = PROC_OPEN.match(text)
    i = m.end()
    d, j = 1, i
    while d:
        d += {'(': 1, ')': -1}.get(text[j], 0)
        j += 1
    args = [a.split(':') for a in ' '.join(text[i:j - 1].split()).split(',') if a.strip()]
    k = text.index(':', j)
    rty = ' '.join(text[k + 1:text.index('= {', k)].split())
    return [(n.strip(), t.strip()) for n, t in args], rty


def split_pre(pre):
    """(argument equalities, precondition) of a specification."""
    pre = pre.strip()
    if not pre.startswith('(('):
        return '', pre
    d = 0
    for j, c in enumerate(pre[1:], 1):
        d += {'(': 1, ')': -1}.get(c, 0)
        if d == 0:
            break
    rest = pre[j + 1:].strip()
    if not rest.startswith('/\\') or not rest.endswith(')'):
        die('unexpected precondition: ' + pre[:80])
    return pre[1:j + 1], rest[2:-1].strip()


def split_post(post):
    """(postcondition, index of the trace in the results; 0: the trace is the
    only result)."""
    m = re.match(r'^\((.*)\s*/\\\s*\(valid res(?:\.`(\d+))?\)\)$', post.strip(), re.S)
    if not m:
        die('unexpected postcondition: ' + post[:80])
    return m.group(1).strip(), int(m.group(2) or 0)


def trace_of(k):
    return 'res' if k == 0 else 'res.`%d' % k


AXIOMS = OrderedDict([
    ('nlimbs', [('gt0_nlimbs', '0 < nlimbs'), ('nlimbs_bnd', '64 * nlimbs < W64.modulus')]),
    ('nlimbsexp', [('gt0_nlimbsexp', '0 < nlimbsexp'),
                   ('nlimbsexp_bnd', '64 * nlimbsexp < W64.modulus')]),
])


class Theory:
    """A safety theory generated from the extractions of its module."""
    cache = {}

    def __init__(self, key):
        self.key, self.cfg = key, THEORIES[key]
        self.name = self.cfg['name']
        self.text = abstract_body(self.cfg['xtr'])
        self.procs, self.specs, self.syscall = parse(self.text)
        self.ptext = dict(self.procs)
        self.sig = {n: signature(t) for n, t in self.procs}
        self.callees = OrderedDict()            # clone -> (theory key, ops)
        self.callclone = {}                     # prefix -> clone
        for q, k in self.cfg.get('calls', {}).items():
            key, clone, ops = k if isinstance(k, tuple) else (k, CLONE[k], {})
            self.callees[clone] = (key, ops)
            self.callclone[q] = clone
        for sp, sub in self.cfg.get('subinstances', {}).items():
            self.callees[sub['clone']] = (sub['theory'], sub.get('ops', {}))
        inc = self.cfg.get('includes')
        if inc:
            self.callees[inc['clone']] = (inc['theory'], {})
        self.functor = bool(self.cfg.get('params') or self.cfg.get('extparams'))
        self.own = OrderedDict((s, n) for n, _ in self.procs
                               for k, s in [self.kind(n)] if k == 'own')

    @classmethod
    def get(cls, key):
        if key not in cls.cache:
            cls.cache[key] = Theory(key)
        return cls.cache[key]

    # -- what each procedure of the extraction is
    def kind(self, name):
        """(kind, short name): own, param, ext, sub:<sp>, included, call:<key>,
        or (None, name) for a name of no known module."""
        if name in self.cfg.get('own_extra', ()) or \
           any(name.startswith(q) for q in self.cfg.get('own_prefixes', ())):
            return 'own', name
        ps = {self.cfg['prefix']: ('self', None)}
        for q, k in self.cfg.get('calls', {}).items():
            ps[q] = ('call', self.callclone[q])
        for q in self.cfg.get('extparams', {}):
            ps.setdefault(q, ('ext', q))
        best = None
        for q, v in ps.items():
            if name.startswith(q) and (best is None or len(q) > len(best[0])):
                best = (q, v)
        if best is None:
            return None, name
        q, (what, arg) = best
        if q == '' and '__' in name:
            return None, name
        short = name[len(q):]
        if what == 'call':
            return 'call:' + arg, short
        if what == 'ext':
            return ('ext', short) if short in self.cfg['extparams'][q] else (None, name)
        if q in self.cfg.get('extparams', {}) and short in self.cfg['extparams'][q]:
            return 'ext', short
        if short in self.cfg.get('params', ()):
            return 'param', short
        for sp in self.cfg.get('subinstances', {}):
            if short.startswith(sp):
                return 'sub:' + sp, short[len(sp):]
        inc = self.cfg.get('includes')
        if inc and short in Theory.get(inc['theory']).own:
            return 'included', short
        return 'own', short

    # -- renaming of the identifiers of the extraction
    def rename(self, text, in_sig=False):
        globs = self.cfg.get('globals', {})
        def sub(m):
            x = m.group()
            if x in globs:
                return globs[x][0]
            if x.startswith('trace_'):
                k, short = self.kind(x[len('trace_'):])
                return 'trace_' + short if k == 'own' else x
            if '__' not in x:
                return x
            k, short = self.kind(x)
            if k is None:
                return x
            if k == 'own':
                return short
            if k in ('param', 'ext'):
                return short if in_sig else 'P.' + short
            if k.startswith('sub:'):
                s = self.cfg['subinstances'][k[4:]]
                return '%s.M(%s).%s' % (s['clone'], s['nested'], short)
            if k == 'included':
                inc = self.cfg['includes']
                return '%s.M(%s).%s' % (inc['clone'], inc['nested'], short)
            callee = Theory.get(self.callees[k[5:]][0])
            if callee.functor:
                die('%s calls the functor theory %s directly' % (self.key, callee.key))
            return '%s.M.%s' % (k[5:], short)
        out = IDENT.sub(sub, text)
        left = sorted(set(re.findall(r'\b\w*(?:h__\w+|uTIL__\w+)', out)))
        # own procedures that keep their names (own_prefixes, own_extra)
        left = [x for x in left if self.kind(re.sub(r'^trace_', '', x))[0] != 'own']
        if left:
            die('%s: names left after renaming: %s' % (self.key, ', '.join(left[:8])))
        return out

    def own_procs(self):
        return [(n, t) for n, t in self.procs if self.kind(n)[0] == 'own']

    def members(self):
        """[(member, extraction name)] of MParam."""
        return [(s, n) for n, _ in self.procs for k, s in [self.kind(n)] if k in ('param', 'ext')]

    def mparam_sigs(self):
        return [self.rename(self.ptext[n][:self.ptext[n].index('= {')].rstrip(), in_sig=True)
                for _, n in self.members()]

    def text_of_theory(self):
        """The text the theory keeps: its procedures, the signatures of its
        parameters, and the specifications of both."""
        parts = [t for _, t in self.own_procs()]
        parts += [self.ptext[n][:self.ptext[n].index('= {')] for _, n in self.members()]
        for n in list(self.own.values()) + [n for _, n in self.members()]:
            args, pre, post = self.specs[n]
            parts += [pre, post]
        return ''.join(parts)

    # -- parameters and arrays
    def arrays(self):
        """{name: ('BA', size) | ('SB', big, small)}: the byte arrays of the
        theory, its own and its callees' (the callee clones take them)."""
        if hasattr(self, '_arrays'):
            return self._arrays
        txt = self.text_of_theory()
        names = set(re.findall(r'\bBA_(%s)\b' % SUFFIX, txt))
        sbs = set(re.findall(r'\bSB_(%s__%s)\b' % (SUFFIX, SUFFIX), txt))
        for clone, (k, ops) in self.callees.items():
            for n, d in Theory.get(k).arrays().items():
                if d[0] == 'BA':
                    names.add(suffix(subst_expr(d[1], ops)))
                else:
                    sbs.add('%s__%s' % (suffix(subst_expr(d[1], ops)), suffix(subst_expr(d[2], ops))))
        for s in sbs:
            names.update(s.split('__'))
        arr = OrderedDict()
        for s in sorted(names, key=lambda s: (parse_suffix(s)[0], parse_suffix(s)[1], parse_suffix(s)[2])):
            arr['BA_' + s] = ('BA', parse_suffix(s))
        for s in sorted(sbs):
            b, sm = s.split('__')
            arr['SB_' + s] = ('SB', parse_suffix(b), parse_suffix(sm))
        self._arrays = arr
        return arr

    def params(self):
        if hasattr(self, '_params'):
            return self._params
        ps = set()
        for d in self.arrays().values():
            ps.update(e[0] for e in d[1:])
        txt = self.rename(self.text_of_theory())
        ps.update(p for p in PARAMS if re.search(r'\b%s\b' % p, txt))
        for clone, (k, ops) in self.callees.items():
            ps.update(ops.get(p, p) for p in Theory.get(k).params())
        if ps:
            ps.add('nlimbs')
        self._params = [p for p in PARAMS if p in ps]
        return self._params


HEADER = ('require import AllCore IntDiv CoreMap List Distr.\n'
          'from Jasmin require import JModel_x86.\n'
          'import SLH64.\n'
          'from Jasmin require import Jcheck JSafety JByte_array JMemory.\n')


def concrete_arrays(text):
    return sorted(set(re.findall(r'\b(S?BArray\d+(?:_\d+)?)\b', text)),
                  key=lambda s: [int(x) for x in re.findall(r'\d+', s)])


def at_point(d, point):
    return ('BArray%d' % value(d[1], point) if d[0] == 'BA'
            else 'SBArray%d_%d' % (value(d[1], point), value(d[2], point)))


def clone_block(key, clone, ops):
    """`clone <callee theory> as <clone> with ...`, passing the parameters and
    the byte arrays on."""
    callee = Theory.get(key)
    lines = ['op %s <- %s' % (p, ops.get(p, p)) for p in callee.params()]
    for n, d in callee.arrays().items():
        tgt = (ba_name(subst_expr(d[1], ops)) if d[0] == 'BA'
               else sb_name(subst_expr(d[1], ops), subst_expr(d[2], ops)))
        lines.append('theory %s <- %s' % (n, tgt))
    proofs = []
    for p in callee.params():
        for an, _ in AXIOMS.get(p, []):
            proofs.append('%s by exact %s' % (an, an.replace(p, ops.get(p, p))))
    out = 'clone %s as %s' % (callee.name, clone)
    if lines:
        out += ' with\n  ' + ',\n  '.join(lines)
    if proofs:
        out += '\n  proof ' + ',\n        '.join(proofs)
    return out + '.\n'


def nested_text(s):
    return '  module %s = {\n%s\n  }\n' % (
        s['nested'], '\n'.join('    proc %s = %s' % b for b in s['bind']))


def gen_theory(thy):
    cfg = thy.cfg
    procs_txt = [thy.rename(t) for _, t in thy.own_procs()]
    out = ['(* GENERATED by scripts/xtr_safety.py from proof/safety/extracted/{A,B}/\n'
           '   %s_safety.ec: do not edit (make -C proof/safety gen). The lemmas are\n'
           '   proved in proof/safety/%s.eca. *)\n' % (cfg['xtr'], thy.name), HEADER]
    conc = concrete_arrays(thy.rename(thy.text_of_theory()))
    if conc:
        out.append('require import %s.\n' % ' '.join(conc))
    if thy.callees:
        names = OrderedDict((Theory.get(k).name, 1) for k, _ in thy.callees.values())
        out.append('require %s.\n' % ' '.join(names))
    out.append('\n')
    for p in thy.params():
        out.append('op %s : int.\n' % p)
        out += ['axiom %s : %s.\n' % a for a in AXIOMS.get(p, [])]
    out.append('\n' if thy.params() else '')
    for n, d in thy.arrays().items():
        if d[0] == 'BA':
            out.append('clone ByteArray as %s with op size <= %s.\n' % (n, show(d[1])))
        else:
            out.append('clone SubByteArray as %s\n  with theory Asmall <= %s, theory Abig <= %s.\n'
                       % (n, ba_name(d[2]), ba_name(d[1])))
    out.append('\n' if thy.arrays() else '')
    for clone, (k, ops) in thy.callees.items():
        out.append(clone_block(k, clone, ops) + '\n')
    for x, (short, arr) in cfg.get('globals', {}).items():
        out.append('(* the global %s of the program, abstract *)\nop %s : %s.t.\n\n' % (x, short, arr))
    if thy.functor:
        out.append('module type MParam = {\n%s\n}.\n\n' % '\n'.join(thy.mparam_sigs()))
        out.append('module M(P: MParam) = {\n  var tmp__trace : trace\n')
    elif thy.syscall:
        # a functor over the system calls (bn_rnd): the specifications are
        # over its instance on the model of the system calls, as the extractor's
        out.append(thy.syscall.strip() + '\n\n')
        out.append('module M(SC: Syscall_t) = {\n  var tmp__trace : trace\n')
    else:
        out.append('module M = {\n  var tmp__trace : trace\n')
    pending = list(cfg.get('subinstances', {}).values())
    if cfg.get('includes'):
        pending.append(cfg['includes'])
    for rt in procs_txt:
        for s in list(pending):
            if '(%s)' % s['nested'] in rt:
                out.append(nested_text(s))
                pending.remove(s)
        out.append(rt)
    out += [nested_text(s) for s in pending]
    inc = cfg.get('includes')
    if inc:
        for short in Theory.get(inc['theory']).own:
            out.append('  proc %s = %s.M(%s).%s\n' % (short, inc['clone'], inc['nested'], short))
    out.append('}.\n\n')
    if thy.functor:
        out.append('(* the specifications, as module-free pre- and postconditions (an op\n'
                   '   cannot mention the declared module of a section) *)\n\n')
    for short, n in list(thy.own.items()) + (thy.members() if thy.functor else []):
        out.append(spec_text(thy, short, n))
    return ''.join(out)


def modname(thy, qual=''):
    """The module of the specifications of a theory without function
    parameters (qual: the clone of the theory, in the glue)."""
    return ('%sM(%sSyscall)' % (qual, qual)) if thy.syscall else qual + 'M'


def spec_text(thy, short, n):
    args, pre, post = thy.specs[n]
    pre, post = thy.rename(pre), thy.rename(post)
    if not thy.functor:
        return 'op %s_spec %s =\n   hoare [%s.%s :\n   %s ==>\n   %s].\n\n' % (
            short, ' '.join(args), modname(thy), short, pre, post)
    types, rty = thy.sig[n]
    eqs, precond = split_pre(pre)
    postcond, k = split_post(post)
    targs = ' '.join('(%s : %s)' % (a, thy.rename(t, in_sig=True)) for a, (_, t) in zip(args, types))
    pargs = targs
    if 'Glob.mem_v' in precond:
        precond = precond.replace('Glob.mem_v', '_mem_v')
        targs = '(_mem_v : global_mem_v_t) ' + targs
    if 'Glob.mem_v' in postcond:
        die('%s: a postcondition on the memory' % n)
    postcond = re.sub(r'\bres\b', '_res', postcond)
    return ('op %s_pre %s =\n  %s.\n\nop %s_post %s (_res : %s) =\n  %s.\n\n'
            % (short, targs, precond or 'true', short, pargs, thy.rename(rty, in_sig=True), postcond))


def hoare_stmt(thy, short, n, modexpr, qual=''):
    """The lemma of a procedure of a functor theory, over modexpr."""
    args, pre, post = thy.specs[n]
    _, precond = split_pre(thy.rename(pre))
    _, k = split_post(thy.rename(post))
    a = ('Glob.mem_v ' if 'Glob.mem_v' in precond else '') + ' '.join(args)
    tup = ', '.join(args) if len(args) != 1 else args[0]
    return ('hoare [%s.%s :\n    arg = (%s) /\\ %s%s_pre %s\n    ==> %s%s_post %s res /\\ valid %s]'
            % (modexpr, short, tup, qual, short, a, qual, short, ' '.join(args), trace_of(k)))





def gen_skeleton(thy):
    out = ['(* GENERATED by scripts/xtr_safety.py: the lemmas of %s, to prove in\n'
           '   proof/safety/%s.eca (a starting point, never checked). *)\n' % (thy.name, thy.name),
           HEADER, 'require import ByteArrayInit JbnSafetyLib.\nrequire %s_xtr.\n\n' % thy.name,
           'clone include %s_xtr.\n\n' % thy.name]
    for c in concrete_arrays(thy.rename(thy.text_of_theory())):
        out.append(('clone ByteArrayLib as BL%s with theory A <- %s.\n' if c.startswith('B')
                    else 'clone SubByteArrayInit as SBI%s with theory SB <- %s.\n')
                   % (c[c.index('Array') + 5:], c))
    for n, d in thy.arrays().items():
        out.append('clone ByteArrayLib as BL_%s with theory A <- %s.\n' % (n[3:], n) if d[0] == 'BA'
                   else 'clone SubByteArrayInit as SBI_%s with theory SB <- %s.\n' % (n[3:], n))
    out.append('\n')
    if thy.functor:
        out.append('section.\n\ndeclare module P <: MParam%s.\n\n'
                   % (' {-Glob}' if thy.cfg.get('pure_params') else ''))
        for short, n in thy.members():
            out.append('declare axiom %s_h %s :\n  %s.\n\n'
                       % (short, ' '.join(thy.specs[n][0]), hoare_stmt(thy, short, n, 'P')))
    for short, n in thy.own.items():
        a = ' '.join(thy.specs[n][0])
        if thy.functor:
            out.append('lemma %s_proof %s :\n  %s.\nproof.\nhint +safety.\nproc.\nadmit.\nqed.\n\n'
                       % (short, a, hoare_stmt(thy, short, n, 'M(P)')))
        else:
            out.append('lemma %s_proof %s : %s_spec %s.\nproof.\nhint +safety.\n'
                       'rewrite /%s_spec; proc.\nadmit.\nqed.\n\n' % (short, a, short, a, short))
    if thy.functor:
        out.append('end section.\n')
    return ''.join(out)


def gen_checkxtr(thy, pname):
    point = PA if pname == 'A' else PB
    cfg = thy.cfg
    out = ['(* GENERATED by scripts/xtr_safety.py: %s at the dummy point %s is the\n'
           '   extraction proof/safety/extracted/%s/%s_safety.ec (one equivalence by sim\n'
           '   per procedure), and its lemmas establish the extractor\'s own\n'
           '   specifications%s. *)\n'
           % (thy.name, pname, pname, cfg['xtr'],
              ' (under the specifications of the stubs)' if thy.functor else ''), HEADER]
    arrs = [at_point(d, point) for d in thy.arrays().values()]
    out.append('require import %s.\n' % ' '.join(arrs + ['%s_safety' % cfg['xtr']]))
    out.append('require %s.\n\n' % thy.name)
    lines = ['op %s <- %d' % (p, point[p]) for p in thy.params()]
    lines += ['theory %s <- %s' % (n, at_point(d, point)) for n, d in thy.arrays().items()]
    lines += ['op %s <- %s' % (short, x) for x, (short, _) in cfg.get('globals', {}).items()]
    ax = [an for p in thy.params() for an, _ in AXIOMS.get(p, [])]
    out.append('clone %s as T' % thy.name + (' with\n  ' + ',\n  '.join(lines) if lines else '')
               + ('\n  proof ' + ', '.join('%s by done' % a for a in ax) if ax else '') + '.\n\n')
    target, stubs = modname(thy, 'T.'), []
    if thy.functor:
        out.append('module Stubs = {\n%s\n}.\n\n' % '\n'.join(
            '  proc %s = M.%s' % (s, n) for s, n in thy.members()))
        target = 'T.M(Stubs)'
        for short, n in thy.members():
            a = ' '.join(thy.specs[n][0])
            out.append('lemma stub_%s :\n  (forall %s, %s_spec %s) =>\n  forall %s,\n  %s.\n'
                       'proof.\nmove=> h %s; have := h %s; rewrite /%s_spec => hh.\n'
                       'by conseq hh => /> /#.\nqed.\n\n'
                       % (short, a, n, a, a, hoare_stmt(thy, short, n, 'Stubs', 'T.'), a, a, n))
            stubs.append((short, n, a))
    for short, n in thy.own.items():
        a = ' '.join(thy.specs[n][0])
        out.append('equiv eq%s: %s.%s ~ %s.%s : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.\n'
                   'proof. by proc; inline *; sim. qed.\n\n' % (short, modname(thy), n, target, short))
        if thy.functor:
            hyps = ''.join('(forall %s, %s_spec %s) =>\n  ' % (sa, sn, sa) for _, sn, sa in stubs)
            # a precondition on the memory: the right memory of the
            # equivalence is a witness that smt finds once the precondition
            # operator is unfolded
            mem = 'Glob.mem_v' in split_pre(thy.rename(thy.specs[n][1]))[1]
            closer = ('=> /> &1 *; rewrite /T.%s_pre /= /#' % short) if mem else '=> /> /#'
            out.append('lemma %s_safety :\n  %sforall %s, %s_spec %s.\nproof.\nmove=> %s %s.\n'
                       'have h := T.%s_proof Stubs %s %s.\nrewrite /%s_spec.\n'
                       'by conseq eq%s h %s.\nqed.\n\n'
                       % (n, hyps, a, n, a, ' '.join('h_' + s for s, _, _ in stubs), a, short,
                          ' '.join('(stub_%s h_%s)' % (s, s) for s, _, _ in stubs), a, n, short, closer))
        else:
            out.append('lemma %s_safety %s : %s_spec %s.\nproof.\nhave h := T.%s_proof %s.\n'
                       'rewrite /%s_spec; rewrite /T.%s_spec in h.\nby conseq eq%s h => /> /#.\nqed.\n\n'
                       % (n, a, n, a, short, a, n, short, short))
    return ''.join(out)


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    old = open(path).read() if os.path.exists(path) else None
    if old != text:
        open(path, 'w').write(text)
        print('wrote ' + os.path.relpath(path, ROOT))


def cmd_gen(args):
    for k in args.theories or list(THEORIES):
        if k not in THEORIES:
            die('unknown theory ' + k)
        thy = Theory.get(k)
        # the concrete byte arrays it uses (u64[3]: BArray24), as the extractor writes them
        for c in concrete_arrays(thy.rename(thy.text_of_theory())):
            write(os.path.join(THYDIR, c + '.ec'), open(os.path.join(XDIR, 'A', c + '.ec')).read())
        write(os.path.join(THYDIR, thy.name + '_xtr.eca'), gen_theory(thy))
        write(os.path.join(THYDIR, thy.name + '_skeleton.ec'), gen_skeleton(thy))
        for p in ('A', 'B'):
            write(os.path.join(CHKDIR, p, thy.name + '_checkxtr.ec'), gen_checkxtr(thy, p))



def lint_module(module):
    """Calls that pass an uninitialised bitmap (a fresh init_arr 0, possibly
    copied) where the callee's specification requires it initialised: a
    contract the caller cannot meet."""
    text = body(extraction(module, 'A'))
    procs, specs, _ = parse(text)
    problems = []
    for name, ptxt in procs:
        zero = set()
        for line in ptxt.split(';'):
            m = re.match(r'\s*(b_\w+) <-\s*\(?\s*(.*?)\)?\s*$', line, re.S)
            if m:
                v, rhs = m.group(1), ' '.join(m.group(2).split())
                if re.match(r'\(?BArray\d+\.init_arr \(W8\.of_int 0\)\)?$', rhs) or rhs in zero:
                    zero.add(v)
                else:
                    zero.discard(v)
                continue
            m = re.search(r'<@ (\w+) \((.*)\)\s*$', line, re.S)
            if not m or m.group(1) not in specs:
                continue
            callee, args = m.group(1), [a.strip() for a in ' '.join(m.group(2).split()).split(',')]
            sargs, pre, _ = specs[callee]
            for a, sa in zip(args, sargs):
                if a in zero and re.search(r'is_init %s \d+ (?!0\b)' % re.escape(sa), ' '.join(pre.split())):
                    problems.append('%s: %s passes the uninitialised %s to %s (%s)'
                                    % (module, name, a, callee, sa))
            # a call returns new bitmaps
            for v in re.findall(r'\b(b_\w+)\b', line.split('<@')[0]):
                zero.discard(v)
    return problems


def cmd_lint(args):
    probs = [p for m in args.modules for p in lint_module(m)]
    for p in probs:
        print(p)
    if probs:
        die('%d calls cannot meet their callee\'s contract' % len(probs))
    print('lint: no call passes an uninitialised array where it is required')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    a = sub.add_parser('align')
    a.add_argument('modules', nargs='+')
    g = sub.add_parser('gen')
    g.add_argument('theories', nargs='*')
    l = sub.add_parser('lint')
    l.add_argument('modules', nargs='+')
    args = ap.parse_args()
    {'align': cmd_align, 'gen': cmd_gen, 'lint': cmd_lint}[args.cmd](args)


if __name__ == '__main__':
    main()
