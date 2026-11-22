#!/usr/bin/env python3
"""
xtr_sync.py -- keep the modules `M` of the EasyCrypt theories in sync with
the Jasmin library modules they specify.

The proofs are about the *generic* library code. `src/amd64/ref/extracted/`
extracts every module, at dummy parameters (nlimbs = 11, see
`libjbn_abs.jazz` and `preamb@n.jinc`), to a concrete EasyCrypt module `M`
per module (`BN_bn_base.ec`, ...; old array model). This script turns such
an extraction into the *abstract* `module M` of the corresponding theory:

  * keeps the procedures of the module (namespace prefix, e.g. `h__BN__`)
    and strips the prefix from their names;
  * redirects calls to other modules to the theories that specify them
    (e.g. `uTIL____cf_mask` -> `BNUTIL_M.__cf_mask`);
  * replaces the dummy sizes by the parameters (`W64.t Array11.t` -> `BN.t`,
    `11` -> `nlimbs`, ...);
  * function parameters (the stubs `fun_*` of libjbn_abs.jazz, key
    `params`) become procedures of a module parameter: `M` is generated as
    a functor `module M(P: MParam)`, with the module type `MParam` of the
    stubs' signatures, and calls `P.fun_*`;
  * a sub-instance (a module required in a sub-namespace, e.g. EXP in
    fp_base, key `subinstances`) is the functor of its own theory applied
    to a nested module that binds its parameters (e.g.
    `BNE.M(P_EXP)._expm_`); its procedures are not part of `M`;
  * a module required in the same namespace (fp_base in fp_mont, key
    `includes`) likewise, and its procedures are re-exported by aliases
    (`proc _mulm_ = FPB.M(P_FPB)._mulm_`);
  * a module required in a sub-namespace that has a theory of its own and
    no parameter (the four multiplication modules in the selector
    bn_mulsel) is an entry of `calls` whose prefix extends the module's
    own (e.g. `h__MUL__UNR__` in `h__MUL__`): its procedures are not part
    of `M`, and calls to them go to that theory's module;
  * system calls (#randombytes, in bn_rnd): the extraction is a functor
    `M(SC: Syscall_t)`, and so is the generated module; its calls
    `SC.<name>` are renamed by the key `syscalls` (the extracted names
    carry the dummy size, e.g. `randombytes_11W64`), and the theory
    defines the module type `Syscall_t` and a module `Syscall` with the
    renamed procedures.

Modes (THEORY is a key of THEORIES below):

  print THEORY            the abstract `module M = { ... }.` on stdout
  update THEORY...        rewrite the generated block of each theory file
                          (between the BEGIN/END markers)
  check THEORY...         exit 1 if a generated block is out of date
  checkxtr THEORY -o F    write the sanity check F: the theory cloned at the
                          dummy size, and `M.<prefix>f ~ T.M.f` proved by
                          `sim` for every procedure

Guard: the dummy sizes are recognised as literals, which is only sound if
the library sources never use them as genuine constants; the script aborts
if a library source contains one of them.
"""

import argparse
import glob
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
XTR_DIR = os.path.join(ROOT, 'src/amd64/ref/extracted')
LIB_DIR = os.path.join(ROOT, 'src/amd64/ref')

# Dummy parameters of libjbn_abs.jazz / preamb@n.jinc, and the literals they
# induce. Each must be mapped wherever it occurs in a kept procedure.
DUMMY_LITERALS = {
    '11': 'nlimbs',
    '12': '(nlimbs + 1)',
    '22': '(2 * nlimbs)',
    '13': 'nlimbsexp',
    # the dummy profile (preamb@n.jinc)
    '17': 'jbn_unroll_max',
    '19': 'jbn_features',
    '23': 'jbn_reg_max',
}
# derived sizes that must not survive in an abstract module (unmapped)
SUSPICIOUS_LITERALS = ('44', '88', '96', '104', '176')

THEORIES = {
    'bn_util': dict(
        source='bn_util.jinc',
        xtr='BNUTIL_bn_util.ec',
        prefix='uTIL__',
        target='proof/Bn_util.ec',
        calls={},
        arrays={},
        concrete=True,               # Bn_util is a concrete theory
    ),
    'bn_base': dict(
        source='bn_base@n.jinc',
        xtr='BN_bn_base.ec',
        prefix='h__BN__',
        target='proof/Bn_base.eca',
        calls={'uTIL__': 'BNUTIL_M.'},
        # Array<N>: (type of W64.t Array<N>.t, theory path, check instantiation)
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A')},
    ),
    'bn_mul': dict(
        source='bn_mul@n.jinc',
        xtr='BNMUL_bn_mul.ec',
        prefix='h__MUL__UNR__',          # instantiated by the selector
        target='proof/Bn_mul.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A'),
                'Array12': ('W64.t BN1.t', 'BN1', 'BN1')},
    ),
    'bn_mul_loop': dict(
        source='bn_mul_loop@n.jinc',
        xtr='BNMULL_bn_mul_loop.ec',
        prefix='h__MUL__LOOP__',
        target='proof/Bn_mul_loop.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A')},
    ),
    'bn_mulx': dict(
        source='bn_mulx@n.jinc',
        xtr='BNMULX_bn_mulx.ec',
        prefix='h__MUL__XUNR__',
        target='proof/Bn_mulx.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A')},
    ),
    'bn_mulx_loop': dict(
        source='bn_mulx_loop@n.jinc',
        xtr='BNMULXL_bn_mulx_loop.ec',
        prefix='h__MUL__XLOOP__',
        target='proof/Bn_mulx_loop.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A')},
    ),
    'bn_mulxr': dict(
        source='bn_mulxr@n.jinc',
        xtr='BNMULXR_bn_mulxr.ec',
        prefix='h__MUL__XREG__',
        target='proof/Bn_mulxr.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A')},
    ),
    'bn_mulsel': dict(
        source='bn_mulsel@n.jinc',
        xtr='BNMULSEL_bn_mulsel.ec',
        prefix='h__MUL__',
        target='proof/Bn_mulsel.eca',
        # the five modules it instantiates in sub-namespaces
        calls={'h__MUL__UNR__': 'BNMUL_M.', 'h__MUL__LOOP__': 'BNMULL_M.',
               'h__MUL__XUNR__': 'BNMULX_M.', 'h__MUL__XLOOP__': 'BNMULXL_M.',
               'h__MUL__XREG__': 'BNMULXR_M.'},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A')},
        clone_ops=['op jbn_features <- 19', 'op jbn_reg_max <- 23',
                   'op jbn_unroll_max <- 17'],
    ),
    'bn_exp': dict(
        source='bn_exp@exp.jinc',
        xtr='BNE_bn_exp.ec',
        prefix='h__EXP__',
        target='proof/Bn_exp.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        params=['fun_mulU', 'fun_sqrU'],
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array13': ('BNexp.t', 'BNexp.A', 'BNexp.A'),
                'Array45': ('W64.t FPC.CTX.t', 'FPC.CTX', 'FPC.CTX'),
                # the table of the windowed exponentiation: 16*nlimbs words
                'Array176': ('W64.t TBL.t', 'TBL', 'TBL')},
        clone_ops=['op nlimbsexp <- 13'],
    ),
    'bn_rnd': dict(
        source='bn_rnd@n.jinc',
        xtr='BNRND_bn_rnd.ec',
        prefix='h__RND__',
        target='proof/Bn_rnd.eca',
        calls={'h__BN__': 'BNB_M.'},
        syscalls={'randombytes_11W64': 'randombytes_W64'},
        # WArray88: the bytes sampled by the system call (checkxtr only)
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'WArray88': ('BN_WAbytes.t', 'BN_WAbytes', 'BigN.BN_WAbytes')},
    ),
    'fp_base': dict(
        source='fp_base@fp.jinc',
        xtr='FP_fp_base.ec',
        prefix='h__FP__',
        target='proof/Fp_base.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        params=['fun_muln', 'fun_sqrn', 'fun_red'],
        subinstances={'h__FP__EXP__': dict(
            module='BNE.M(P_EXP)', nested='P_EXP',
            bind=[('fun_mulU', 'fun_mulU'), ('fun_sqrU', 'fun_sqrU')])},
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A'),
                'Array45': ('W64.t FPC.CTX.t', 'FPC.CTX', 'FPC.CTX')},
    ),
    'fp_mont': dict(
        source='fp_mont@fp.jinc',
        xtr='FPM_fp_mont.ec',
        prefix='h__FPM__',
        target='proof/Fp_mont.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.', 'h__MUL__': 'BNMUL_M.'},
        params=['fun_muln', 'fun_sqrn'],
        clone_ops=['op jbn_features <- 19', 'op jbn_reg_max <- 23',
                   'op jbn_unroll_max <- 17'],
        includes=dict(theory='fp_base', module='FPB.M(P_FPB)', nested='P_FPB',
                      bind=[('fun_muln', 'P.fun_muln'), ('fun_sqrn', 'P.fun_sqrn'),
                            ('fun_red', 'fun_red')]),
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A'),
                'Array45': ('W64.t FPC.CTX.t', 'FPC.CTX', 'FPC.CTX')},
    ),    'fp_pm': dict(
        source='fp_pm@fp.jinc',
        xtr='FPPM_fp_pm.ec',
        prefix='h__FPPM__',
        target='proof/Fp_pm.eca',
        calls={'uTIL__': 'BNUTIL_M.', 'h__BN__': 'BNB_M.'},
        params=['fun_muln', 'fun_sqrn'],
        includes=dict(theory='fp_base', module='FPB.M(P_FPB)', nested='P_FPB',
                      bind=[('fun_muln', 'P.fun_muln'), ('fun_sqrn', 'P.fun_sqrn'),
                            ('fun_red', 'fun_red')]),
        arrays={'Array11': ('BN.t', 'BN.A', 'BigN.BN.A'),
                'Array22': ('BN2.t', 'BN2.A', 'BigN.BN2.A'),
                'Array45': ('W64.t FPC.CTX.t', 'FPC.CTX', 'FPC.CTX')},
    ),
}

BEGIN = '(* BEGIN generated by scripts/xtr_sync.py'
END = '(* END generated *)'

MODULE_M_OPEN = re.compile(r'^module M(?:\(SC\s*:\s*Syscall_t\))?\s*=\s*\{\s*$')
MODULE_CLOSE = re.compile(r'^\}\.\s*$')
PROC_OPEN = re.compile(r'^  proc\s+([A-Za-z_0-9]+)\b')
PROC_CLOSE = re.compile(r'^  \}\s*$')


def die(msg):
    sys.exit('xtr_sync: error: ' + msg)


def split_module_m(lines):
    """Procedures of `module M` as [(name, text)], in extraction order."""
    i = 0
    while i < len(lines) and not MODULE_M_OPEN.match(lines[i]):
        i += 1
    if i == len(lines):
        die('`module M = {` not found')
    i += 1
    procs, cur = [], None
    while i < len(lines) and not MODULE_CLOSE.match(lines[i]):
        line = lines[i]
        m = PROC_OPEN.match(line)
        if m and cur is None:
            cur = (m.group(1), [line])
        elif cur is not None:
            cur[1].append(line)
            if PROC_CLOSE.match(line):
                procs.append((cur[0], ''.join(cur[1])))
                cur = None
        elif line.strip():
            die('unexpected line in module M: ' + line.rstrip())
        i += 1
    if cur is not None:
        die('unterminated proc ' + cur[0])
    return procs


def strip_comments(text):
    text = re.sub(r'/\*.*?\*/', ' ', text, flags=re.S)
    return re.sub(r'//[^\n]*', ' ', text)


def guard_sources():
    """Abort if a library source uses a dummy literal as a constant."""
    bad = []
    for f in sorted(glob.glob(os.path.join(LIB_DIR, '*.jinc'))):
        code = strip_comments(open(f).read())
        for lit in list(DUMMY_LITERALS) + list(SUSPICIOUS_LITERALS):
            if re.search(r'(?<![\w.])%s(?![\w.])' % lit, code):
                bad.append('%s: %s' % (os.path.relpath(f, ROOT), lit))
    if bad:
        die('library sources contain dummy-size literals, so the abstraction '
            'would be unsound; change the dummy sizes of libjbn_abs.jazz:\n  '
            + '\n  '.join(bad))


def included_names(cfg):
    """Short names of the procedures of the included theory (and of its
    sub-instances), which the extraction of `cfg` contains under its own
    prefix."""
    inc = cfg.get('includes')
    if not inc:
        return set(), ()
    icfg = THEORIES[inc['theory']]
    _, kept = generate(inc['theory'])
    names = {n[len(icfg['prefix']):] for n, _ in kept}
    subs = tuple(p[len(icfg['prefix']):] for p in icfg.get('subinstances', {}))
    return names, subs


def classify(short, cfg):
    """What a procedure of the module's namespace is: a parameter stub, a
    procedure of an included module, or its own."""
    if short in cfg.get('params', ()):
        return 'param'
    names, subs = included_names(cfg)
    if short in names or short.startswith(subs) if subs else short in names:
        return 'included'
    return 'own'


def abstract_proc(name, text, cfg):
    prefix = cfg['prefix']
    subinst = cfg.get('subinstances', {})
    inc = cfg.get('includes')
    # names: header and call sites
    # every name with a module prefix (the proc itself, calls with `<@` and
    # calls to unit procedures, which have none) is renamed; sub-instance
    # prefixes extend the module's own, so they are tried first
    prefixes = sorted(subinst, key=len, reverse=True) + [prefix] + list(cfg['calls'])
    sub_calls = sorted((p for p in cfg['calls'] if p.startswith(prefix)),
                       key=len, reverse=True)

    def rename(m):
        tok = m.group(0)
        for p in sorted(subinst, key=len, reverse=True):
            if tok.startswith(p):
                return subinst[p]['module'] + '.' + tok[len(p):]
        for p in sub_calls:
            if tok.startswith(p):
                return cfg['calls'][p] + tok[len(p):]
        if tok.startswith(prefix):
            short = tok[len(prefix):]
            kind = classify(short, cfg)
            if kind == 'param':
                return 'P.' + short
            if kind == 'included':
                return inc['module'] + '.' + short
            return short
        for p, mod in cfg['calls'].items():
            if tok.startswith(p):
                return mod + tok[len(p):]
        return tok
    text = re.sub(r'\b(?:%s)\w+' % '|'.join(map(re.escape, prefixes)), rename, text)
    # the procedure's own name, in its header, is never a call
    text = re.sub(r'^(  proc\s+)(?:P\.|%s\.)?' % re.escape(inc['module']) if inc
                  else r'^(  proc\s+)P\.', r'\1', text, count=1)
    # system calls
    sysc = cfg.get('syscalls', {})
    text = re.sub(r'\bSC\.(\w+)', lambda m: 'SC.' + sysc.get(m.group(1), m.group(1)), text)
    left = [c for c in re.findall(r'\bSC\.(\w+)', text) if c not in sysc.values()]
    if left:
        die('%s calls the system calls %s, which have no mapping '
            '(THEORIES[...]["syscalls"])' % (name, sorted(set(left))))
    left = re.findall(r'\b(?:h__[A-Z]\w*|[a-z][A-Z][A-Z0-9]*__\w+)', text)
    if left:
        die('%s refers to %s, which has no mapping (THEORIES[...]["calls"])'
            % (name, sorted(set(left))))
    # sizes: array types and theories, then literals
    for arr, (ty, path, _) in cfg['arrays'].items():
        text = text.replace('W64.t %s.t' % arr, ty)
        text = re.sub(r'\b%s\.' % arr, path + '.', text)
    for lit, par in DUMMY_LITERALS.items():
        text = re.sub(r'(?<![\w.])%s(?![\w.])' % lit, par, text)
    # nothing size-specific may remain
    left = re.findall(r'\bW?Array(?!3\b)\d+\b|(?<![\w.])(?:%s)(?![\w.])'
                      % '|'.join(SUSPICIOUS_LITERALS), text)
    if left:
        die('%s: unmapped size-specific names %s' % (name, sorted(set(left))))
    if re.search(r'\bh__glob_|\bglob_', text):
        die('%s uses a dummy global; add a mapping for it' % name)
    return text


def signature(text):
    """`proc f (args) : ty` of a (renamed) procedure."""
    m = re.match(r'\s*proc\s+(.*?)\s*=\s*\{', text, re.S)
    return re.sub(r'\s+', ' ', m.group(1))


def generate(theory):
    cfg = THEORIES[theory]
    xtr = os.path.join(XTR_DIR, cfg['xtr'])
    if not os.path.exists(xtr):
        die('%s not found; run `make -C src/amd64/ref extract`' % xtr)
    procs = split_module_m(open(xtr).read().splitlines(keepends=True))
    prefix = cfg['prefix']
    subinst = cfg.get('subinstances', {})
    sub_calls = tuple(p for p in cfg['calls'] if p.startswith(prefix))
    mine = [(n, t) for n, t in procs if n.startswith(prefix)
            and not n.startswith(tuple(subinst) + sub_calls)]
    if not mine:
        die('no procedure with prefix %s in %s' % (prefix, cfg['xtr']))
    params = cfg.get('params', [])
    stubs = {n[len(prefix):]: abstract_proc(n, t, cfg) for n, t in mine
             if classify(n[len(prefix):], cfg) == 'param'}
    missing = [f for f in params if f not in stubs]
    if missing:
        die('%s: parameters %s not in the extraction (add them to its list of '
            'procedures)' % (theory, missing))
    kept = [(n, t) for n, t in mine if classify(n[len(prefix):], cfg) == 'own']
    procs_txt = [(n[len(prefix):], abstract_proc(n, t, cfg)) for n, t in kept]
    # nested modules binding the parameters of sub-instances / includes, each
    # placed before its first use
    nested = [(s['module'], s['nested'], s['bind']) for s in subinst.values()]
    inc = cfg.get('includes')
    if inc:
        nested.append((inc['module'], inc['nested'], inc['bind']))
    body = []
    pending = list(nested)
    for short, txt in procs_txt:
        for nest in list(pending):
            if nest[0] + '.' in txt:
                body.append(nested_module(nest))
                pending.remove(nest)
        body.append(txt)
    body += [nested_module(n) for n in pending]
    if inc:
        own = {s for s, _ in procs_txt}
        names, _ = included_names(cfg)
        icfg = THEORIES[inc['theory']]
        _, ikept = generate(inc['theory'])
        body += ['  proc %s = %s.%s\n' % (n, inc['module'], n)
                 for n in (k[len(icfg['prefix']):] for k, _ in ikept) if n not in own]
    head = ('%s from src/amd64/ref/extracted/%s\n'
            '   (%s); do not edit: run `make -C proof update` *)\n'
            % (BEGIN, cfg['xtr'], cfg['source']))
    if params and cfg.get('syscalls'):
        die('%s: parameters and system calls together are not supported' % theory)
    if params:
        mtype = ('module type MParam = {\n'
                 + ''.join('  proc %s\n' % signature(stubs[f]) for f in params)
                 + '}.\n\n')
        head += mtype + 'module M(P: MParam) = {\n'
    elif cfg.get('syscalls'):
        head += 'module M(SC: Syscall_t) = {\n'
    else:
        head += 'module M = {\n'
    return head + ''.join(body) + '}.\n' + END + '\n', kept


def nested_module(nest):
    _, name, bind = nest
    return ('  module %s = {\n' % name
            + ''.join('    proc %s = %s\n' % (f, g) for f, g in bind)
            + '  }\n')


def locate_block(text, path):
    b = text.find(BEGIN)
    e = text.find(END, b if b >= 0 else 0)
    if b < 0 or e < 0:
        die('%s has no generated block (%s ... %s)' % (path, BEGIN, END))
    return b, e + len(END) + (1 if text[e + len(END):e + len(END) + 1] == '\n' else 0)


def cmd_update(theories, check_only):
    stale = []
    for t in theories:
        block, _ = generate(t)
        path = os.path.join(ROOT, THEORIES[t]['target'])
        text = open(path).read()
        b, e = locate_block(text, path)
        if text[b:e] == block:
            continue
        if check_only:
            stale.append(THEORIES[t]['target'])
        else:
            open(path, 'w').write(text[:b] + block + text[e:])
            print('updated %s' % THEORIES[t]['target'], file=sys.stderr)
    if stale:
        print('out of date (run `make -C proof update`): ' + ', '.join(stale),
              file=sys.stderr)
        sys.exit(1)


def checkxtr(theory):
    cfg = THEORIES[theory]
    _, kept = generate(theory)
    mod = os.path.splitext(cfg['xtr'])[0]
    thy = os.path.splitext(os.path.basename(cfg['target']))[0]
    arrays = sorted(cfg['arrays'])
    out = ['(* generated by scripts/xtr_sync.py: the abstract module M of %s,'
           % thy,
           '   instantiated at the dummy sizes of the extraction, is the',
           '   extracted code of %s *)' % cfg['source'], '',
           'require import AllCore IntDiv CoreMap List.',
           'from Jasmin require import JModel_x86.',
           'import SLH64.', '',
           'require import %s.' % mod]
    if arrays:
        out.append('require import %s.' % ' '.join(arrays))
    out.append('require %s.' % thy)
    out.append('')
    if cfg.get('concrete'):
        target = '%s.M' % thy
    else:
        inst = (['op nlimbs <- 11'] + cfg.get('clone_ops', [])
                + ['theory %s <= %s' % (cfg['arrays'][a][2], a) for a in arrays])
        out += ['clone %s as T' % thy,
                ' with ' + ',\n      '.join(inst),
                ' proof gt0_nlimbs by done.', '']
        target = 'T.M'
    if cfg.get('params'):
        out += ['(* the stubs of libjbn_abs.jazz, as the module parameter *)',
                'module Stubs = {']
        out += ['  proc %s = M.%s%s' % (f, cfg['prefix'], f) for f in cfg['params']]
        out += ['}.', '']
        target += '(Stubs)'
    xm = 'M'
    if cfg.get('syscalls'):
        # the extracted module and the theory's, each with its system calls
        xm = 'M(Syscall)'
        target += '(T.Syscall)'
    for name, _ in kept:
        short = name[len(cfg['prefix']):]
        out += ['equiv eq%s: %s.%s ~ %s.%s : ={arg, Glob.mem} ==> ={res, Glob.mem}.' % (short, xm, name, target, short),
                'proof. by proc; inline *; sim. qed.', '']
    return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('mode', choices=('print', 'update', 'check', 'checkxtr'))
    ap.add_argument('theories', nargs='*', default=None,
                    help='theories (default: all): ' + ', '.join(THEORIES))
    ap.add_argument('-o', '--output', help='output file (checkxtr)')
    args = ap.parse_args()
    theories = args.theories or list(THEORIES)
    for t in theories:
        if t not in THEORIES:
            die('unknown theory %s (known: %s)' % (t, ', '.join(THEORIES)))
    guard_sources()
    if args.mode == 'print':
        for t in theories:
            sys.stdout.write(generate(t)[0])
    elif args.mode in ('update', 'check'):
        cmd_update(theories, args.mode == 'check')
    else:
        if len(theories) != 1 or not args.output:
            die('checkxtr takes one theory and -o FILE')
        with open(args.output, 'w') as f:
            f.write(checkxtr(theories[0]))


if __name__ == '__main__':
    main()
