# libjbn

A big-number (multi-limb) and prime-field arithmetic library written in
[Jasmin](https://github.com/jasmin-lang/jasmin), with correctness proofs in
[EasyCrypt](https://github.com/EasyCrypt/easycrypt).

The library code is *generic*: almost everything is parametrised by the
number of 64-bit limbs (`nlimbs`) and, for the field code, by the modulus
and a few auxiliary constants and functions. Jasmin has no parametric
modules yet (see the proposal in
[jasmin-lang/jasmin#519](https://github.com/jasmin-lang/jasmin/issues/519)),
so this repository emulates them:

* on the **code side**, with *Jasmin namespaces*: a library module is a
  template, a plain Jasmin file `<module>@<tag>.jinc` that is `require`d
  inside a namespace, which becomes the instance; its parameters are found
  by Jasmin's ordinary name lookup, and the tag says which kind of
  namespace it needs;
* on the **proof side**, with *abstract (parametrised) EasyCrypt theories*
  whose parameters are later instantiated by cloning.

This document describes that workflow.


## Overview

```
 src/amd64/ref/<module>@<tag>.jinc   library modules (templates): generic code
                                 whose free names (nlimbs, fun_muln, BN::,
              │                  H::BN::, ...) are its parameters
              │  require "<module>@<tag>.jinc" inside namespaces
              │
    ┌─────────┴────────────────────────────┐
    ▼                                      ▼
 wiring file of a program         src/amd64/ref/extracted/libjbn_abs.jazz
 (examples/.../*.jazz)            (every module, dummy parameters, stubs)
    │ jasminc                              │ jasmin2ec --array-model=old
    ▼                                      ▼
 .s + C test programs             src/amd64/ref/extracted/*.ec
 (examples/)                               │ manual rewriting
                                           │ (proof/extracted_ths/Readme.md)
                                           ▼
                                  proof/*.eca   abstract EasyCrypt theories
                                           │ clone with concrete parameters,
                                           │ relate to concrete code (equiv ... by sim)
                                           ▼
                                  proofs about a concrete instance
                                  (e.g. proof/UsageExample.ec)
```

There is no code-generation step: instances are written in Jasmin.


## Repository layout

| Path | Contents |
|---|---|
| `src/amd64/ref/*@*.jinc` | The library modules, i.e. templates (see [Library modules](#1-library-modules) and [File names](#file-names)). |
| `src/amd64/ref/params/` | Contexts of concrete moduli (`sike/`, `nistp/`, `rfc3526/`), one file per modulus: `glob_ctx` (see [Field contexts](#field-contexts)), plus application constants (generators, curve coefficients). |
| `src/amd64/ref/extracted/` | Abstract instantiation and extraction used by the proofs (see [Extraction](#3-extraction-for-the-proofs)). |
| `src/amd64/ref/legacy/` | Kept for reference: pre-modular multiplication code and its C tests; `mjazz/`, the former template-based instantiation (`mjazz_proc.py`, `templates/`, and the modules in the proposed #519 parametric-module syntax). |
| `proof/` | EasyCrypt development: value semantics (`JBigNumber.ec`) and one abstract theory per module (`*.eca`). |
| `examples/` | Concrete programs with C test programs: `simple_tests/{sike,rsa_pss,mults,fp_ctx}`, `schnorr-zk/`. |
| `scripts/` | `xtr_sync.py` (generated modules of the theories, section 4), `fp_ctx.py` (field contexts of given moduli). |
| `test/misc/` | Generator of field instances for many moduli (compilation tests); `bench/` uses its output. |
| `bench/`, `ext/` | Benchmarks, external code (`randombytes`). |
| `src/attic/`, `proof/attic/` | Older code and proofs, kept for reference. |


## 1. Library modules

### Modules

Each module starts with a comment giving its *signature*: the names it
expects to find in scope and the names it provides.

| Module (file `<module>.jinc`) | Contents | Instance (namespace) | Expects in scope |
|---|---|---|---|
| `bn_util` | flag/mask helpers, 3-limb accumulators used by multiplication | `UTIL` (top level) | — |
| `bn_base@n` | load/store, comparison, (conditional) moves and swaps, add/sub/neg with carry, `cminusP`, `pack2` | `BN` | `nlimbs`, `UTIL::` |
| `bn_rnd@n` | uniform sampling (`_rnd_`; `_rsample_`: rejection sampling below a public bound, each sample being masked to the bit length of the bound) | `RND` | `nlimbs`, `BN::` |
| `bn_mul@n` | operand-scanning (`os`) and product-scanning (`ps`) multiplication and squaring; Montgomery reduction `__mont_redM` (constants: `P \|\| R-P` packed in an array, and `-P^-1 mod 2^64`) | `MUL` | `nlimbs`, `BN::`, `UTIL::` |
| `bn_mulreg@n` | operand-scanning multiplication with the second operand in registers | `MULREG` | `nlimbs` |
| `bn_mul_loop@n` | the `MUL` module with a run-time loop over the rows: operand-scanning multiplication and squaring, row-wise Montgomery reduction `__mont_redM` (same contract and constants); rows with `mul`/`adc` (see [Unrolled or looped](#unrolled-or-looped-multiplication-and-reduction)) | `MUL`, in the place of `bn_mul` | `nlimbs`, `BN::` |
| `bn_mulx_loop@n` | the same module, with `mulx`/`adcx`/`adox` rows (BMI2 and ADX) | `MUL`, in the place of `bn_mul` | `nlimbs`, `BN::` |
| `bn_karatsuba@2n` | one Karatsuba level on top of a given multiplication | `KAR` (in the 2n scope) | `nlimbs` (2n), `H::nlimbs` (n), `fun_kmuln`, `BN::`, `H::BN::`, `UTIL::` |
| `bn_exp@exp` | modular exponentiation (constant-time and not) | `EXP` (inside a field) | `nlimbs`, `nlimbsexp`, `CTXLEN`, `CTX_ONE`, `fun_mulU`, `fun_sqrU` (both take the context), `BN::`, `UTIL::` |
| `fp_ctx@n` | layout of a field context (`CTX_P`, `CTX_MP`, `CTX_ONE`, `CTX_R2`, `CTX_U0`, `CTXLEN`) | required by `fp_base` | `nlimbs` |
| `fp_base@fp` | prime-field operations, generic in the reduction; each takes the context of its modulus | a field (e.g. `FPM`), shared by all moduli of the size | `nlimbs`, `fun_muln`, `fun_sqrn`, `fun_red`, `BN::`, `RND::`, `UTIL::` |
| `fp_mont@fp` | Montgomery-form field (`_redM_`, `_fromM_`, `_toM_`, `_ctx_init_`) plus all of `fp_base` | a field (e.g. `FPM`) | as `fp_base` (except `fun_red`), plus `MUL::` |
| `fp_mul_ps@fp` | binds `fun_muln`/`fun_sqrn` to product-scanning multiplication | inside a field | `nlimbs`, `MUL::` |
| `fp_mul_os@fp` | binds `fun_muln`/`fun_sqrn` to the operand-scanning multiplication of `bn_mul_loop`/`bn_mulx_loop` | inside a field | `nlimbs`, `MUL::` |
| `*_export@2n` | `export fn` wrappers forming the C interface: `fp_mont_export` (static modulus `H::FPM::glob_ctx`), `fp_mont_ctx_export` (context argument, `fpc_*`) | top level | see the file headers |

### File names

The name of a Jasmin file says whether it is a template and, if so, where
it must be required:

| Name | Kind |
|---|---|
| `<name>@<tag>.jinc` | template (open file): has free names; required inside a namespace of the kind given by the tag |
| `<name>.jinc` | closed include: no free names (e.g. `bn_util.jinc`, `rsa_keys.jinc`) |
| `<name>.jazz` | program: a wiring file that instantiates templates, compiled by `jasminc` |

| Tag | Required in | Names expected in scope |
|---|---|---|
| `@n` | a module slot of a size scope (`BN`, `RND`, `MUL`, `MULREG`), or any namespace whose `nlimbs` is the size (context files `params/**/*@n.jinc`, `fp_ctx@n.jinc`) | `nlimbs`, `UTIL`, other instances of the same scope |
| `@2n` | a 2n scope (or the top level acting as one) | `nlimbs` (2n), the half scope `H` (`H::nlimbs`, `H::BN`, …) |
| `@fp` | a field namespace (`FPM`), one per size and choice of multiplication and reduction | the size scope's names, `fun_muln`/`fun_sqrn` |
| `@exp` | an exponentiation sub-namespace (`EXP`) | `nlimbs`, `nlimbsexp`, `CTXLEN`/`CTX_ONE`, `fun_mulU`/`fun_sqrU`, `BN`, `UTIL` |

The tag gives the kind of context, which is stable; the header of each file
lists the exact names it uses. `@` is used as separator because `::`, or
any `:`, breaks make prerequisites and is not portable to Windows.

Two modules instantiate others themselves, because the instance depends on
their own functions (they correspond to `clone ... with` inside the
EasyCrypt theories):

* `fp_base` defines `fun_mulU`/`fun_sqrU` (inline wrappers of its
  `_mulmU_`/`_sqrmU_`) and then `namespace EXP { param int nlimbsexp =
  nlimbs; require "bn_exp@exp.jinc" }`; inversion (`_invm_`, `_invmU_`)
  uses `EXP::`.
* `fp_mont` defines `fun_red` (wrapper of `_redM_`) and then requires
  `fp_base` *in its own namespace*, so a Montgomery field `FPM` provides
  both `FPM::_toM_` and `FPM::_addm_`.

### How names are resolved

The scheme relies on the following properties of Jasmin namespaces
(checked with Jasmin 2026.09):

* **Lookup goes outward.** A name, qualified (`BN::f`, `H::BN::f`) or not,
  is searched in the current namespace, then in each enclosing namespace,
  then at the top level. When a namespace closes, its names are added to
  the parent with its prefix (`BN::f`; nested ones become `H::BN::f`).
* **`require` is per namespace.** A file is loaded at most once *per
  namespace*, so the same module can be instantiated in several namespaces.
* **Parameters can be redefined from the outer value**:
  `namespace BN2 { param int nlimbs = 2*nlimbs; ... }` reads the outer
  `nlimbs` on the right-hand side.
* **Functions cannot be shadowed.** A function cannot be declared if a
  function with the same (unqualified) name is visible from an enclosing
  namespace. Globals and parameters may be shadowed.
* **No aliases, no forward references.** A namespace has a single name and
  a function must be defined before it is used.
* **A global cannot be initialised from another global**, so constants must
  be defined directly under the names the modules expect.
* Exported functions get symbols with `::` replaced by `__`
  (`A::B::f` becomes `A__B__f`); exports at the top level keep their name.

### Naming conventions

* `__f`: inline implementation (loops, the actual code).
* `_f`: non-inline function wrapping `__f`.
* `_f_`: inline wrapper (copies its arguments in and out); this is the
  preferred entry point for users of the library.
* suffix `U` (e.g. `_addU_`): in-place ("update") variant; the first
  argument is overwritten with the result. Otherwise the result array is a
  separate first argument (e.g. `_add_(r, a, b)`).
* Parameters are ordered *results first*.


## 2. Instantiation (wiring files)

A program instantiates the modules it needs in a *wiring file*, a plain
Jasmin file of namespaces and `require`s. Every module is instantiated
**exactly once per set of parameters**; the layout follows three rules.

1. **One size scope per limb count.** A *size scope* is a namespace
   holding `param int nlimbs` and at most one instance of each module at
   that size (`BN`, `RND`, `MUL`, `MULREG`, `KAR`), plus a field namespace
   (`FPM`) per choice of multiplication and reduction, shared by every
   modulus of that size (moduli are values: [contexts](#field-contexts)).
   `UTIL` is instantiated once, at the top level.
2. **Halving nesting.** When a module needs sizes n and 2n, the n scope is
   the child `H` of the 2n scope. Inner scopes are defined (and closed)
   first: instances are created bottom-up, smallest size first, while the
   nesting goes from the largest scope (outermost) to the smallest.
3. **Two-size modules live in the larger scope.** `bn_karatsuba` and the
   `bn_mul`/`bn_karatsuba` export files are required in the 2n scope and
   reach size n through `H` (`H::BN::`, `H::MUL::`, `H::KAR::`,
   `H::nlimbs`). The top level of a program is its largest scope, so the
   export files sit at the top level and the C symbols are unqualified.

The halving nesting is what makes sharing possible: in a recursive
Karatsuba multiplication the 16-limb `BN` is the half size of the 32-limb
level and the full size of the 16-limb level; both levels reach the same
instance, as `H::BN` and `BN` respectively. (With flat, sibling instances a
module could not refer to "its" `BN`, since namespaces cannot be aliased.)

**Function parameters** (`fun_muln`, `fun_kmuln`, …) are inline wrappers
defined by the wiring in the scope where the module is required; they cost
nothing at run time. `fp_mul_ps@fp.jinc` provides the usual choice for
fields. Because functions cannot be shadowed, a wrapper must not be visible
from an enclosing namespace when an inner one defines the same name: define
the outer level's wrapper *after* the inner namespace has closed.

### Unrolled or looped multiplication and reduction

The loops of the library are Jasmin `for` loops, which the compiler unrolls.
For the single loops of `bn_base` the code is linear in `nlimbs`; for the
nested loops of `bn_mul` (multiplication, squaring, Montgomery reduction)
it is quadratic, and these three routines are most of a large instance.

`bn_mul_loop@n.jinc` and `bn_mulx_loop@n.jinc` provide the same three
operations with a run-time `while` over the rows of operand scanning; only
the row is unrolled, so the code is linear in `nlimbs`. They take the place
of `bn_mul` as the `MUL` instance of a size scope; the field code is
unchanged, since `fp_mont` only uses `MUL::__mont_redM`, `fun_muln` and
`fun_sqrn`:

```
  namespace MUL { from Libjbn require "bn_mul_loop@n.jinc" }   // was bn_mul@n.jinc
  namespace FPM {
    from Libjbn require "fp_mul_os@fp.jinc"                    // was fp_mul_ps@fp.jinc
    from Libjbn require "fp_mont@fp.jinc"
  }
```

`bn_mul_loop` uses `mul`/`adc` only, as the product-scanning code;
`bn_mulx_loop` uses `mulx`/`adcx`/`adox` (two carry chains per row) and
needs a CPU with BMI2 and ADX.

Size of a whole field instance with run-time moduli (the `fpc_*` entry
points of `examples/simple_tests/fp_ctx`; bytes of code, Jasmin 2026.09):

| `nlimbs` | `bn_mul` (unrolled) | `bn_mul_loop` | `bn_mulx_loop` |
|---:|---:|---:|---:|
| 4 | 5 536 | 4 919 | 5 114 |
| 8 | 10 683 | 7 541 | 7 558 |
| 16 | 26 842 | 13 144 | 12 927 |
| 32 | 90 132 | 26 351 | 26 055 |
| 64 | 326 500 | 52 929 | 50 969 |
| 96 | 709 300 | 79 544 | 77 570 |
| 128 | (not built) | 106 058 | 104 208 |

At 32 limbs the three routines take 16 567 instructions unrolled, 1 247
with `bn_mul_loop` and 791 with `bn_mulx_loop`; what remains is mostly the
exponentiations, whose loop over the limbs of the exponent is still
unrolled. Compilation of the 96-limb instance takes about 5 minutes
unrolled and 9 seconds looped.

What is *not* settled:

* **Speed.** No measurement on x86-64 hardware exists yet
  (`make -C examples/simple_tests/fp_ctx bench` times `fpc_mul`, `fpc_sqr`
  and `fpc_exp` for the three modules, from 4 to 64 limbs). Under Rosetta
  (which says nothing about instruction caches or decoding on a real x86-64
  CPU, and cannot run `bn_mulx_loop`), `fpc_mul` with `bn_mul_loop` is
  within 20% of the unrolled product scanning from 4 to 32 limbs (faster up
  to 16 limbs, 9% slower at 32) and 41% faster at 64.
* **Proofs.** The looped modules have no theory in `proof/`: they are
  tested, not proved (section 5).
* **Speculative constant time.** `jasmin-ct --sct --after=unroll` accepts
  the unrolled multiplication, squaring and reduction as they are, given
  an export wrapper that initialises the misspeculation flag and protects
  its pointers. (Checked before unrolling, the compile-time `if` of
  `__ps_sqrn` counts as a branch.) It rejects the looped ones ("this
  function call destroys MSFs") until the flag is threaded through them:
  an extra `#[msf]` argument and result, and two `#update_msf` (one per
  row, one after the loop); with these they are accepted. That changes
  their signatures, hence those of `fun_muln`, `fun_sqrn` and `fun_red`.
  The exponentiations, which already loop at run time, need the same
  whatever the multiplication. Plain constant time (`jasmin-ct --infer`)
  is accepted for all variants. None of these annotations is in the
  library yet.

### Field contexts

The field code does not depend on the modulus: every field operation takes
the *context* of its modulus P as its last argument, an array
`u64[CTXLEN]` (`fp_ctx@n.jinc`, R = 2^(64*nlimbs)):

```
ctx = [ P | R-P | R mod P | R^2 mod P | -P^-1 mod 2^64 ]     (4*nlimbs+1 words)
```

The first `2*nlimbs` words are the packed constants of `MUL::__mont_redM`.
A context is either

* **static**: a global `glob_ctx`, from a file of `src/amd64/ref/params/`
  (or one generated by `scripts/fp_ctx.py gen N P`), required in any
  namespace whose `nlimbs` is the size; code passes it as `ctx = glob_ctx;`
  (a register holding its address). The limb count is stated once, by the
  wiring; a mismatch is a type error;
* **computed at run time** by `FPM::_ctx_init_(ctx, P)` (constant time:
  Newton's iteration for `-P^-1 mod 2^64`, modular doublings of 1 for
  `R mod P` and `R^2 mod P`), e.g. through the C entry point
  `fpc_ctx_init` of `fp_mont_ctx_export@2n.jinc`.

All operations are constant time in their operands and in the context,
except `_rnd_` (rejection sampling against P) and `_invm(U)_` (Fermat
inversion with the variable-time exponentiation on P-2), which assume a
public modulus.

Example (`examples/simple_tests/sike/bn_sike434.jazz`):

```
namespace UTIL { from Libjbn require "bn_util.jinc" }

namespace H {                                   // working size
  param int nlimbs = 7;
  namespace BN  { from Libjbn require "bn_base@n.jinc" }
  namespace RND { from Libjbn require "bn_rnd@n.jinc" }
  namespace MUL { from Libjbn require "bn_mul@n.jinc" }
  namespace FPM {
    from Libjbn require "fp_mul_ps@fp.jinc"             // fun_muln, fun_sqrn
    from Libjbn require "fp_mont@fp.jinc"
    from Libjbn require "params/sike/sike434@n.jinc"    // glob_ctx, the modulus
  }                                                     // of the fp_* exports
}

from Libjbn require "bn_base_export@2n.jinc" "fp_mont_export@2n.jinc"
```

`examples/simple_tests/mults/kar_32_*.jazz` show the halving nesting over
several levels; `examples/schnorr-zk/src/bn_modp2048.jinc` and
`examples/simple_tests/rsa_pss/rsapss.jazz` several moduli sharing one
field namespace (contexts `FPM::P::glob_ctx`, `FPM::Q::glob_ctx`); and
`examples/simple_tests/fp_ctx` moduli given at run time (and, in
`fp_ctx_loop*.jazz`, the looped multiplication and reduction).

Compile with the library bound to the include name `Libjbn`:

```
jasminc -lazy-regalloc -I Libjbn=src/amd64/ref -o <name>.s <name>.jazz
```

`make check` in `src/amd64/ref` typechecks all modules (through the
extraction harness below).


## 3. Extraction for the proofs

The proofs are about the *generic* code, so every module is instantiated
once with placeholder parameters and the result is extracted to EasyCrypt.
All of this lives in `src/amd64/ref/extracted/`:

* `libjbn_abs.jazz`: the abstract instantiation, laid out by the rules of
  section 2 (top level = 2n scope, `H` = n scope): `UTIL`, `H::BN`,
  `H::RND`, `H::MUL`, `H::MULREG`, `H::EXP`, `H::FP`, `H::FPM`, `BN`
  (2n) and `KAR`. Function parameters are stubs, declared inside the
  namespace of the module that takes them;
* `preamb@n.jinc`: the placeholder parameter `nlimbsexp = 13`, required
  inside `H`, whose `nlimbs` is 11 (contexts then have 45 words);
* `Makefile`: the list of procedures extracted from each module and the
  extraction command.

```
cd src/amd64/ref
make extract
```

produces `extracted/<QUAL>_<module>.ec` (`BNUTIL_bn_util.ec`,
`BN_bn_base.ec`, …, `FPM_fp_mont.ec`), one call per module:

```
jasmin2ec --array-model=old -I Libjbn=.. -f 'H::BN::_load_' ... -o BN_bn_base.ec libjbn_abs.jazz
```

The proofs rely on the **old array model** (`--array-model=old`).
Leakage (constant-time) extraction is currently not part of the pipeline.
The extractor joins namespace paths with `__` and lower-cases the first
letter (`H::BN::_add_` becomes `h__BN___add_`). The generated files,
including the `Array*.ec`/`WArray*.ec` theories, stay in `extracted/`
(git-ignored): the proofs load them (section 4).

Sub-instances are extracted concretely: in `FP_fp_base.ec`, the
exponentiation used by `_invm_` calls the field's own `_mulmU_`; in
`FPM_fp_mont.ec`, `fun_red` calls `_redM_`.


## 4. Abstract theories (`proof/`)

### Value semantics: `JBigNumber.ec`

* `bn_seq`: value of a list of limbs, plus generic lemmas on limb
  arithmetic (`bn_seq_cmp`, `addc_to_uint`, `addc3P`, `dbl_mulu`, …).
* `abstract theory BN`, parametrised by `nlimbs`: the type `BN.t`
  (an array of `nlimbs` words), its value `bn`, prefixes `bnk`,
  carry/borrow views (`bn_withcarry`, `bn_withborrow`), conversions
  (`bn_ofint`), sampling (`bn_rnd`), and the lemmas used by the proofs.
* `abstract theory BigN`: clones `BN` for `nlimbs` and, as `BN2`, for
  `2*nlimbs`.

### One theory per module

| Theory | Parameters | Corresponds to |
|---|---|---|
| `Bn_util.ec` | none (concrete theory) | `bn_util` |
| `Bn_base.eca` | `nlimbs` (clones `BigN` and `Bn_util`) | `bn_base` |
| `Bn_mul.eca` | `nlimbs` (clones `BigN`, `Bn_util` and `Bn_base`) | `bn_mul` |
| `Bn_rnd.eca` | `nlimbs` | `bn_rnd` (not yet rewritten, see the status) |
| `Fp_ctx.eca` | `nlimbs` | `fp_ctx` (layout of a context: `ctxP`, `ctxMP`, `ctxONE`, `ctxR2`, `ctxU0`; `ctx_mod p c`, `ctx_mont p c`) |
| `Bn_exp.eca` | `nlimbs`, `nlimbsexp` (with `64 * nlimbsexp < W64.modulus`), an abstract monoid over contexts (`mok`, `mdom`, `mmul`; the unit is the context's ONE); module parameter `fun_mulU`, `fun_sqrU` | `bn_exp` |
| `Fp_base.eca` | `nlimbs` (with `64 * nlimbs < W64.modulus`), an abstract reduction `red p x = x * redK p mod p` (`redK`, `red_ctx`); module parameter `fun_muln`, `fun_sqrn`, `fun_red` | `fp_base` (its exponentiation is `Bn_exp` in the monoid of representatives) |
| `Fp_mont.eca` | `nlimbs` (with `64 * nlimbs < W64.modulus`); module parameter `fun_muln`, `fun_sqrn` | `fp_mont` (`Fp_base` with `redK p = R^-1 mod p`) |

The field theories take no modulus: every contract quantifies over a ghost
modulus `p` and requires the context argument to be a context of `p`
(`ctx_mod p ctx`, `ctx_mont p ctx`). The results are stated modulo `p`, so
they also cover composite moduli (RSA); `_ctx_init_` establishes
`ctx_mont p` for any odd `1 < p < R`.

Function parameters (`fun_*`) become *module parameters*: the module is a
functor `M(P: MParam)`, and the contracts are proved in a section, under
`declare axiom`s for the parameters (losslessness and a `hoare`
specification). Outside the section, a contract is generalised over the
parameter module and these axioms (in declaration order). A sub-instance
(the exponentiation inside `Fp_base`) is a nested module of `M(P)` passed
to the sub-theory's functor, e.g. `BNE.M(M(P).P_EXP)`; `Fp_mont` includes
`Fp_base` as `FPB.M(M(P).P_FPB)` and proves its parameter `fun_red` from
`_redM_`.

Each theory contains the module `M` obtained from the extracted code, then,
for each user-callable procedure `ppp`:

* `ppp_ll`: `islossless M.ppp`;
* `ppp_h`: the functional specification as a `hoare` judgement;
* `ppp_ph`: the same as a `phoare ... = 1%r` judgement (from the two above),
  where it is needed.

Inner loops and wrappers get their own `_h` lemmas when needed (e.g.
`__addc1U_h` for the loop of `_addcU_`).

### Keeping the theories in sync with the code

The module `M` of a theory is *the abstraction of the code extracted from
the dummy instance* of its Jasmin module (section 3). For `Bn_util.ec`,
`Bn_base.eca`, `Bn_mul.eca`, `Bn_exp.eca`, `Fp_base.eca` and `Fp_mont.eca`
it is generated, between the markers
`(* BEGIN generated by scripts/xtr_sync.py ... *)` and
`(* END generated *)`, by `scripts/xtr_sync.py`, which:

* keeps the procedures of the module (namespace prefix, e.g. `h__BN__`) and
  strips the prefix (`h__BN___add_` becomes `_add_`);
* redirects calls to other modules to the theories that specify them
  (`uTIL____cf_mask` becomes `BNUTIL_M.__cf_mask`, `h__BN___cminusP_` in
  `bn_mul` becomes `BNB_M._cminusP_`);
* replaces the dummy sizes by the parameters (`W64.t Array11.t` becomes
  `BN.t`, `Array22` becomes `BN2`, `11` becomes `nlimbs`, …);
* turns the calls to the function-parameter stubs into calls to the
  module parameter (`P.fun_red`), with a `module type MParam` built from
  the stubs' signatures, and the calls to sub-instances and included
  modules into calls to the nested modules described above.

The literals of the dummy sizes are only recognised safely if the library
never uses them as constants; the script checks this on the sources.
A table at the top of the script describes each theory; adding one (e.g.
`Bn_rnd`) means adding an entry and the markers.

From `proof/`:

* `make update`: re-extract and regenerate the modules `M`;
* `make check-sync`: fail if a module `M` is out of date (a change of the
  sources not propagated, or a hand edit of a generated block);
* `make checkxtr`: sanity checks, as in formosa-keccak: each theory is
  cloned at the dummy sizes (`op nlimbs <- 11`, `theory BigN.BN.A <=
  Array11`, …) and `equiv M.<prefix>f ~ T.M.f : ={arg, Glob.mem} ==>
  ={res, Glob.mem}` is proved by `proc; inline *; sim` for every
  procedure (for a functor theory, `T.M(Stubs)`, with `Stubs` the
  extracted stubs). This confirms that the generated module *is* the extracted
  code, independently of the text transformation.

### Using the theories for a concrete instance

`proof/UsageExample.ec` shows the intended use (it predates the contexts
and the functor modules, and does not load; the steps are unchanged):

1. extract the concrete program (`proof/extracted/XtrCode.ec`, with
   `nlimbs = 11`);
2. clone the abstract theories with the concrete parameters, mapping the
   array theories onto the extracted ones
   (`theory BN.A <= Array11`, `theory BN2.A <= Array22`, …) and the
   globals onto the extracted constants (`op glob_P <- XtrCode.glob_P`, …);
3. prove that each cloned procedure equals the extracted one
   (`equiv ... : ={arg} ==> ={res} by sim`), so the abstract
   specifications apply to the concrete code.

### Checking the proofs

```
make -C proof            # check-sync, checkxtr, and compile the theories
make -C proof check      # only compile the theories
```

The theories are compiled with `-I . -I ../src/amd64/ref/extracted` (the
extraction provides `Array3`, used by `Bn_util`); `proof/.dir-locals.el`
sets the same include paths for Proof General.


## 5. Examples

Each directory under `examples/` holds wiring files (`.jazz` programs, plus `.jinc` includes), C
test programs and a Makefile that runs `jasminc` and the C compiler:

```
cd examples/simple_tests/sike     # or rsa_pss, mults, ../schnorr-zk/src
make            # compile and link (rebuilds when a library module changes)
make clean
```

| Example | What it tests |
|---|---|
| `simple_tests/sike` | Montgomery field arithmetic for the SIKE primes (434, 503, 610, 751 bits) |
| `simple_tests/rsa_pss` | 2048-bit RSA: `dec(enc(t)) == t`, CRT decryption |
| `simple_tests/fp_ctx` | moduli given at run time (7 and 16 limbs): `fpc_ctx_init` and every `fpc_*` operation, against Python (`make run`); each size is built twice, with `bn_mul` (`fp_ctx*.jazz`) and with `bn_mul_loop` (`fp_ctx_loop*.jazz`) |
| `simple_tests/mults` | 32-limb multiplication: `ps`, `os`, `osreg` and Karatsuba variants; the row-looped `os` of `bn_mul_loop` and `bn_mulx_loop` (`testmul_os_loop.c`, against a C reference) |
| `schnorr-zk` | a Schnorr zero-knowledge protocol over the RFC 3526 2048-bit group |

The test programs print `TESTING <name>:` followed by `...OK!`, or by the
expected and obtained values.

The code is x86-64. On macOS the Makefiles compile with
`gcc -arch x86_64` and the programs run under Rosetta. Rosetta does not
support the ADX instructions (`mulx`/`adcx`/`adox`) used by the
operand-scanning multiplications, so the `os`/`osreg` tests in
`simple_tests/mults` must be run on an x86-64 machine (Broadwell or later);
this includes `testmul_os_mulx_loop_32`, but not `testmul_os_loop_32`.
Override the compiler with `make GCC=...` if needed.

`test/misc/params.c` generates, for a given modulus, the constants *and*
the wiring of a Montgomery field instance (used by `test/misc` and
`bench/`); it needs GMP.


## Toolchain

* Jasmin compiler `jasminc` and extractor `jasmin2ec` (tested with 2026.09;
  namespaces are required);
* EasyCrypt with the Jasmin `eclib` (tested with r2026.10);
* a C compiler targeting x86-64 (and GMP for `test/misc`).


## Current status and known issues

*(as of November 2026)*

* `JBigNumber.ec`, `Bn_util.ec`, `Bn_base.eca`, `Bn_mul.eca`, `Fp_ctx.eca`,
  `Bn_exp.eca`, `Fp_base.eca` and `Fp_mont.eca` check, and their modules `M`
  are generated from the extraction (`make -C proof`). None of them has
  admits.
  * `Bn_mul.eca` proves the correctness of the product-scanning
    multiplication and squaring (`_ps_muln_`, `_ps_sqrn_`) and of the
    Montgomery reduction `__mont_redM`, under the parameter axiom
    `nlimbs_bnd: 4 * nlimbs < W64.modulus` (the top word of the 3-word
    accumulator counts carries); for the operand-scanning procedures only
    losslessness is proved.
  * `Bn_exp.eca` proves the three exponentiations (right-to-left
    `_expm_noct_`, the Montgomery ladder `_expm_`, left-to-right
    `_expmLR_noct_`) in an abstract monoid.
  * `Fp_base.eca` proves the field operations for an abstract reduction,
    and `Fp_mont.eca` instantiates it with the Montgomery reduction and
    proves `_redM_`, `_toM_`, `_fromM_` and `_ctx_init_` (Newton's
    iteration for U0, doublings for R mod p and R^2 mod p).
  * The parameter axioms `64 * nlimbs < W64.modulus` (`Fp_base`,
    `Fp_mont`) and `64 * nlimbsexp < W64.modulus` (`Bn_exp`) bound the
    loop counters (`32 * nlimbs` doublings, the signed limb index of
    `_expmLR_noct_`).
* The examples whose operand-scanning code uses ADX/MULX (e.g.
  `simple_tests/mults/testmul_*os*`) stop with "Illegal instruction" under
  Rosetta 2 on Apple silicon; they need a native x86-64 CPU with ADX/BMI2.
* `bn_mul_loop` and `bn_mulx_loop` are not extracted and have no theory.
  `bn_mul_loop` is tested natively (`simple_tests/mults`,
  `simple_tests/fp_ctx`). `bn_mulx_loop` has not been run on a CPU yet: its
  generated assembly was only checked with an interpreter of the few
  instructions it uses.
* `Bn_rnd.eca` and `UsageExample.ec` do not load: they require
  `MLeakage.ec`, which uses `leakages_t`, no longer provided by the Jasmin
  `eclib`. `Bn_rnd` is not synchronised with the extraction yet (it still
  uses the manual rewriting of `proof/extracted_ths/`), so `Fp_base`'s
  `_rnd_` (which calls it) has no contract.
* `proof/extracted/Makefile` (the concrete `XtrCode` extraction) still uses
  the old `jasminc -ec` interface.
* All examples build; see [Examples](#5-examples) for the tests that cannot
  run under Rosetta.
