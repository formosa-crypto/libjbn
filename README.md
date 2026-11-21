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
 (examples/)                               │ scripts/xtr_sync.py (section 4,
                                           │ "Keeping the theories in sync")
                                           ▼
                                  proof/*.eca   abstract EasyCrypt theories
                                           │ clone with concrete parameters,
                                           │ relate to concrete code (equiv ... by sim)
                                           ▼
                                  proofs about a concrete instance
                                  (e.g. examples/simple_tests/rsa_pss/proof)
```

There is no code-generation step: instances are written in Jasmin.


## Repository layout

| Path | Contents |
|---|---|
| `src/amd64/ref/*@*.jinc` | The library modules, i.e. templates (see [Library modules](#1-library-modules) and [File names](#file-names)). |
| `src/amd64/ref/profiles/` | Profiles: the CPU features and the unrolling threshold of a target (see [Profiles](#profiles-and-the-selection-of-the-multiplication)). |
| `src/amd64/ref/params/` | Contexts of concrete moduli (`sike/`, `nistp/`, `rfc3526/`), one file per modulus: `glob_ctx` (see [Field contexts](#field-contexts)), plus application constants (generators, curve coefficients). |
| `src/amd64/ref/extracted/` | Abstract instantiation and extraction used by the proofs (see [Extraction](#3-extraction-for-the-proofs)). |
| `proof/` | EasyCrypt development: value semantics (`JBigNumber.ec`) and one abstract theory per module (`*.eca`). |
| `examples/` | Concrete programs with C test programs: `simple_tests/{sike,rsa_pss,mults,fp_ctx}`, `schnorr-zk/`. |
| `scripts/` | `xtr_sync.py` (generated modules of the theories, section 4), `fp_ctx.py` (field contexts of given moduli). |
| `test/misc/` | Generator of field instances for many moduli (compilation tests); `bench/` uses its output. |
| `bench/`, `ext/` | Benchmarks, external code (`randombytes`). |


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
| `bn_mulx@n` | `bn_mulx_loop` unrolled (a `for` over the rows), for small sizes, with a squaring of its own (BMI2 and ADX) | `MUL`, in the place of `bn_mul` | `nlimbs`, `BN::` |
| `bn_mulxr@n` | `bn_mulx` with its accumulator in a register array: the rows load and store no word of the result (up to 6 limbs in a field; see [Registers](#small-sizes-the-accumulator-in-registers-bn_mulxr)) (BMI2 and ADX) | `MUL`, in the place of `bn_mul` | `nlimbs`, `BN::` |
| `bn_mulsel@n` | the selector: `_muln_`, `_sqrn_` and `__mont_redM` of one of the five modules above, chosen at compile time from the profile and the size (see [Profiles](#profiles-and-the-selection-of-the-multiplication)); instantiates the five itself | `MUL`, in the place of `bn_mul` | `nlimbs`, `BN::`, `UTIL::`, a profile |
| `jbn_features` | the feature bits (`JBN_FEATURE_BMI2`, `JBN_FEATURE_ADX`, `JBN_FEATURES_MULX`) | top level, required by a profile | — |
| `bn_karatsuba@2n` | one Karatsuba level on top of a given multiplication | `KAR` (in the 2n scope) | `nlimbs` (2n), `H::nlimbs` (n), `fun_kmuln`, `BN::`, `H::BN::`, `UTIL::` |
| `bn_exp@exp` | modular exponentiation (constant-time and not) | `EXP` (inside a field) | `nlimbs`, `nlimbsexp`, `CTXLEN`, `CTX_ONE`, `fun_mulU`, `fun_sqrU` (both take the context), `BN::`, `UTIL::` |
| `fp_ctx@n` | layout of a field context (`CTX_P`, `CTX_MP`, `CTX_ONE`, `CTX_R2`, `CTX_U0`, `CTXLEN`) | required by `fp_base` | `nlimbs` |
| `fp_base@fp` | prime-field operations, generic in the reduction; each takes the context of its modulus | a field (e.g. `FPM`), shared by all moduli of the size | `nlimbs`, `fun_muln`, `fun_sqrn`, `fun_red`, `BN::`, `RND::`, `UTIL::` |
| `fp_mont@fp` | Montgomery-form field (`_redM_`, `_fromM_`, `_toM_`, `_ctx_init_`) plus all of `fp_base` | a field (e.g. `FPM`) | as `fp_base` (except `fun_red`), plus `MUL::` |
| `fp_pm@fp` | pseudo-Mersenne field, in normal representation: moduli with `R mod P < 2^32` and `R < 3P` (2^255-19 at 4 limbs), reduced by folding the high half with one row of multiplications by `R mod P` (`_redPM_`, `_ctx_init_`; `_toM_`/`_fromM_` are the identity) plus all of `fp_base` (see [Pseudo-Mersenne fields](#pseudo-mersenne-fields-fp_pm)) | a field, in the place of `fp_mont` | as `fp_base` (except `fun_red`) |
| `fp_mul_ps@fp` | binds `fun_muln`/`fun_sqrn` to product-scanning multiplication | inside a field | `nlimbs`, `MUL::` |
| `fp_mul_os@fp` | binds `fun_muln`/`fun_sqrn` to the operand-scanning multiplication of `bn_mul_loop`/`bn_mulx_loop`/`bn_mulx`/`bn_mulxr` | inside a field | `nlimbs`, `MUL::` |
| `fp_mul_sel@fp` | binds `fun_muln`/`fun_sqrn` to those of `bn_mulsel` | inside a field | `nlimbs`, `MUL::` |
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
nothing at run time. `fp_mul_sel@fp.jinc` provides the usual choice for
fields (with `bn_mulsel`, next section). Because functions cannot be
shadowed, a wrapper must not be visible from an enclosing namespace when an
inner one defines the same name: define the outer level's wrapper *after*
the inner namespace has closed.

### Profiles and the selection of the multiplication

Five modules provide the multiplication, squaring and Montgomery reduction
(next sections): `bn_mul` and `bn_mul_loop` with `mul`/`adc`, `bn_mulx` and
`bn_mulx_loop` with `mulx`/`adcx`/`adox`, each either unrolled or looping
over its rows, and `bn_mulxr`, `bn_mulx` with its accumulator in registers,
for small sizes. Which one is fastest depends on the CPU and on the size.
`bn_mulsel@n.jinc` chooses among them at compile time, from three
parameters set by a **profile**:

* `JBN_FEATURES`: the CPU features that may be used, as a sum of the bits
  of `jbn_features.jinc` (`JBN_FEATURE_BMI2`, `JBN_FEATURE_ADX`); the
  `mulx` rows need both (`JBN_FEATURES_MULX`);
* `JBN_REG_MAX`: with BMI2 and ADX, `bn_mulxr` is used up to this size
  (at most 6, see [Registers](#small-sizes-the-accumulator-in-registers-bn_mulxr));
* `JBN_UNROLL_MAX`: the code of a size scope is unrolled when `nlimbs <=
  JBN_UNROLL_MAX`, and loops over its rows above.

|  | `nlimbs <= JBN_REG_MAX` | `nlimbs <= JBN_UNROLL_MAX` | above |
|---|---|---|---|
| BMI2 and ADX | `bn_mulxr` | `bn_mulx` | `bn_mulx_loop` |
| otherwise | — | `bn_mul` (product scanning) | `bn_mul_loop` |

| Profile (`src/amd64/ref/profiles/`) | `JBN_FEATURES` | `JBN_REG_MAX` | `JBN_UNROLL_MAX` | for |
|---|---|---|---|---|
| `x86_64.jinc` | none | 0 | 64 | any x86-64 CPU (and Rosetta) |
| `x86_64_adx.jinc` | BMI2, ADX | 5 | 16 | Intel Broadwell and later, AMD Zen and later |

The thresholds come from the timings of the next section, on one CPU (an
Intel Core i7-14700K): with `mulx` the unrolled code is faster up to 16
limbs and much slower from 32 (sizes in between were not timed); with
`mul`, the two are within 3% of each other on an exponentiation up to 16
limbs (either way), and the unrolled code is faster at 32 and 64 limbs (8%
and 16%), the largest size timed. `JBN_REG_MAX` comes from the timings of
[Small sizes](#small-sizes-the-accumulator-in-registers-bn_mulxr):
`bn_mulxr` is faster than `bn_mulx` at 4 and 5 limbs, and at 6 only when
the field multiplications are independent of each other. The header of
each profile gives the figures.

A program requires one profile at its top level, before the instances,
and uses the selector as its `MUL` and `fp_mul_sel` in its fields:

```
from Libjbn require "profiles/x86_64_adx.jinc"

namespace UTIL { from Libjbn require "bn_util.jinc" }

namespace H {
  param int nlimbs = 16;
  // param int JBN_UNROLL_MAX = 0;      // (optional) smallest code at this size
  namespace BN  { from Libjbn require "bn_base@n.jinc" }
  namespace RND { from Libjbn require "bn_rnd@n.jinc" }
  namespace MUL { from Libjbn require "bn_mulsel@n.jinc" }
  namespace FPM {
    from Libjbn require "fp_mul_sel@fp.jinc"
    from Libjbn require "fp_mont@fp.jinc"
  }
}
```

* **One decision per size scope.** The multiplication, squaring and
  reduction of a size scope come from the same module: they share the
  instruction cache (at 32 limbs the unrolled `mulx` multiplication alone
  is within 7% of the looped one, but `fpc_mul`, with the reduction, is
  81% slower).
* **Overriding.** A size scope may shadow `JBN_UNROLL_MAX` (parameters can
  be shadowed, functions cannot): 0 forces the looped code at that size
  (e.g. for code size), a large value the unrolled code. A program can
  still wire one of the four modules directly as its `MUL` (with
  `fp_mul_ps` or `fp_mul_os`), as most examples of section 5 do.
* **Cost.** The tests are on parameters: the compiler emits the selected
  module only, and the other three are type-checked but cost nothing (the
  32-limb selector with an unselected unrolled module compiles in 0.2 s).
  The code is that of the selected module wired directly, up to register
  allocation: in the four selector instances of
  `examples/simple_tests/fp_ctx`, the same instructions except for register
  moves (from 8 more to 52 fewer `mov`s than the direct wiring).
* **Proofs.** The theories are proved for every profile: `Bn_mulsel`
  proves its contracts for the four branches, and `Fp_mont` uses its
  `__mont_redM` (section 4).

The selector's procedures are inline (`_muln_`, `_sqrn_`, `__mont_redM`):
one call, to the non-inline function of the selected module.

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

`bn_mulx@n.jinc` is `bn_mulx_loop` with a `for` over the rows: the same
rows and the same names, in straight-line code again quadratic in `nlimbs`.
It is meant for small sizes, where the unrolled `mulx` multiplication is
the faster one (see the timings below), and it is wired in the same way.
Being unrolled, it differs from the looped module in two places:

* a squaring of its own, `a^2 = 2 X + D`: the products `a[i]*a[j]`, `i < j`,
  are accumulated by rows that get shorter with `i`, then `X` is doubled
  on one carry chain while the squares `a[i]^2` are added on the other
  (`nlimbs (nlimbs+1) / 2` multiplications instead of `nlimbs^2`);
* a reduction whose first row reads the argument (no initial copy) and
  which keeps the word that defines the next multiplier in a register, so
  that the dependency from one row to the next does not go through
  memory.

Size of a whole field instance with run-time moduli (the `fpc_*` entry
points of `examples/simple_tests/fp_ctx`; bytes of code, Jasmin 2026.09):

| `nlimbs` | `bn_mul` (unrolled) | `bn_mul_loop` | `bn_mulx_loop` | `bn_mulx` (unrolled) |
|---:|---:|---:|---:|---:|
| 4 | 5 482 | 4 864 | 5 001 | 5 668 |
| 8 | 10 665 | 7 596 | 7 674 | 11 169 |
| 16 | 26 902 | 13 089 | 13 194 | 30 236 |
| 32 | 90 123 | 26 369 | 25 861 | 105 933 |
| 64 | 326 482 | 52 929 | 52 238 | 392 317 |
| 96 | 709 349 | 79 486 | 77 573 | (not built) |
| 128 | (not built) | 106 040 | 102 711 | (not built) |

At 32 limbs the three routines take 16 567 instructions unrolled, 1 247
with `bn_mul_loop` and 791 with `bn_mulx_loop`; what remains is mostly the
exponentiations, whose loop over the limbs of the exponent is still
unrolled. Compilation of the 96-limb instance takes about 5 minutes
unrolled and 9 seconds looped.

What is *not* settled:

* **Speed.** Measured on one CPU only, an Intel Core i7-14700K, with
  `taskset -c 2 make -C examples/simple_tests/fp_ctx bench`, which times
  `fpc_mul`, `fpc_sqr` and `fpc_exp` for the three modules (wall-clock
  time, best of a few runs; the unrolled module was not built above 64
  limbs):

  | `nlimbs` | `fpc_mul` (ns): `bn_mul` | `bn_mul_loop` | `bn_mulx_loop` | `fpc_exp` (µs): `bn_mul` | `bn_mul_loop` | `bn_mulx_loop` |
  |---:|---:|---:|---:|---:|---:|---:|
  | 4 | 26.0 | 25.8 | 22.2 | 14.1 | 13.8 | 12.0 |
  | 8 | 86.8 | 83.2 | 63.8 | 87.9 | 85.1 | 66.0 |
  | 16 | 313 | 286 | 208 | 591 | 589 | 425 |
  | 32 | 1 138 | 1 143 | 693 | 4 383 | 4 714 | 2 868 |
  | 64 | 4 305 | 4 694 | 2 670 | 33 941 | 39 387 | 22 155 |
  | 96 | – | 10 885 | 5 978 | – | 134 654 | 74 495 |
  | 128 | – | 19 935 | 10 293 | – | 328 049 | 172 910 |

  * `bn_mulx_loop` is the fastest of the three at every size. On `fpc_exp`
    it is 15% faster than the unrolled `bn_mul` at 4 limbs, 25% at 8, 28%
    at 16 and 35% at 32 and 64, and its cost per limb product does not
    grow up to 128 limbs. The two differ in instructions and in scanning
    order as well as in the loop, so this does not say that the loop is
    what makes it faster: see the multiplications alone, below.
  * `bn_mul_loop`, which uses the instructions of the unrolled code, is
    within 3% of it on `fpc_exp` up to 16 limbs (slightly faster at 4 and
    8, equal at 16), then slower: 8% at 32 limbs, 16% at 64. On `fpc_mul`
    alone it is faster up to 16 limbs (by 1%, 4% and 9%), equal at 32 and
    9% slower at 64.
  * The looped modules have no squaring of their own (`_os_sqrn` is a
    multiplication), whereas the unrolled `fpc_sqr` is 8% to 16% faster
    than `fpc_mul`: this accounts for the loss of `bn_mul_loop` on
    `fpc_exp` at 32 limbs, and for about half of it at 64.
  * The unrolled code shows no penalty for its size: its `fpc_mul` grows
    by 3.8 from 32 to 64 limbs.

  Rosetta is no guide here: it had `bn_mul_loop` 41% faster than the
  unrolled code at 64 limbs.

  The loop kind and the instructions are separated by the schoolbook
  multiplications alone, since `bn_mul` has an unrolled operand scanning
  with MULX/ADCX/ADOX (`_os_muln`; there is no such squaring or
  reduction). Same CPU, `taskset -c 2 make -C examples/simple_tests/mults
  bench`, in ns (entry points that copy 6 `nlimbs` words, the same code in
  the four columns):

  | `nlimbs` | `bn_mul` ps, MUL, unrolled | `bn_mul_loop` os, MUL, looped | `bn_mul` os, MULX, unrolled | `bn_mulx_loop` os, MULX, looped |
  |---:|---:|---:|---:|---:|
  | 4 | 9.5 | 11.1 | 9.9 | 10.2 |
  | 8 | 38.1 | 38.4 | 27.9 | 32.3 |
  | 16 | 140.0 | 136.3 | 95.8 | 107.5 |
  | 32 | 542.3 | 540.6 | 346.4 | 331.9 |
  | 64 | 2 119 | 2 268 | 2 616 | 1 299 |

  * The gain of `bn_mulx_loop` comes from the instructions, not from the
    loop: with the same instructions, the looped multiplication is 3%
    slower than the unrolled one at 4 limbs, 16% at 8 and 12% at 16.
  * It is 4% faster at 32 limbs and twice as fast at 64, where the
    unrolled MULX code breaks down: its cost per limb product nearly
    doubles from 32 to 64 limbs, as the routine goes from 33 675 to
    139 851 bytes (7 467 at 16 limbs; the looped one is 3 590 bytes at 64).
    The unrolled product scanning (93 751 bytes at 64 limbs) does not
    break down; a likely reason, not checked with performance counters,
    is that the MULX code needs about twice as many instruction bytes per
    unit of time, more than can be fetched once the routine no longer
    fits the 32 KB instruction cache.
  * With MUL/ADC the loop kind (and scanning order) changes the
    multiplication by less than 3% from 8 to 32 limbs; the looped one is
    17% slower at 4 limbs and 7% at 64.
  * At 4 limbs the four multiplications are within 17% and product
    scanning is the fastest: the gain of `bn_mulx_loop` on `fpc_mul` at
    that size is in the reduction.

  So neither kind is the best at every size. With MULX/ADCX/ADOX,
  unrolled multiplication is ahead up to 16 limbs and looped from 32 on.

  `bn_mulx`, written after these measurements, gives the field operations
  an unrolled MULX squaring and reduction. Against `bn_mulx_loop` (same
  CPU and commands, a later run; `mulx_unr` and `mulx` in both `bench`
  targets; in `mults`, the `bn_mul` operand scanning of the table above is
  now labelled `os`, and `bn_mulx` multiplies in the same time, within 3%):

  | `nlimbs` | `fpc_mul` (ns): `bn_mulx` | `bn_mulx_loop` | `fpc_sqr` (ns): `bn_mulx` | `bn_mulx_loop` | `fpc_exp` (µs): `bn_mulx` | `bn_mulx_loop` | squaring alone (ns): `bn_mulx` | `bn_mulx_loop` |
  |---:|---:|---:|---:|---:|---:|---:|---:|---:|
  | 4 | 20.1 | 22.4 | 17.7 | 21.2 | 11.0 | 11.9 | 7.4 | 9.2 |
  | 8 | 60.8 | 64.0 | 51.8 | 62.1 | 58.5 | 65.4 | 18.8 | 30.1 |
  | 16 | 198.7 | 209.6 | 162.5 | 202.8 | 379.9 | 424.6 | 60.9 | 104.6 |
  | 32 | 1 256 | 693 | 982 | 687 | 4 548 | 2 856 | 199.3 | 324.8 |
  | 64 | 5 167 | 2 644 | 3 975 | 2 619 | 37 436 | 22 052 | 1 416 | 1 279 |

  * Up to 16 limbs `bn_mulx` is the fastest module: on `fpc_exp`, 8%
    faster than `bn_mulx_loop` at 4 limbs and 11% at 8 and 16 (22%, 33%
    and 36% faster than the unrolled `bn_mul`).
  * From 32 limbs on it is the wrong choice: on `fpc_exp`, 59% slower than
    `bn_mulx_loop` at 32 limbs and 70% at 64.
  * That is a matter of code size. Whenever the unrolled MULX code run by
    a call does not fit the 32 KB instruction cache, the time is the one
    of fetching it at 52 to 54 bytes per ns: `fpc_mul` and `fpc_sqr` at 32
    and 64 limbs (multiplication or squaring, plus reduction: 66 and 51 KB
    at 32 limbs, 276 and 211 KB at 64), and the multiplication and the
    squaring alone at 64 limbs (140 and 75 KB). Code that fits runs at 75
    to 95 bytes per ns; the product-scanning code of `bn_mul` needs 40 to
    44, which is why its size costs nothing. (From sizes and times; not
    checked with performance counters.) The multiplication and the
    reduction of `bn_mulx` are 15 KB together at 16 limbs, and would reach
    32 KB at about 24 limbs: sizes between 16 and 32 are not measured.
  * The squaring is where most of the gain is: alone, it is 20% faster
    than the looped module's (a multiplication) at 4 limbs, 38% at 8, 42%
    at 16 and 39% at 32, where its 19 KB still fit; on `fpc_sqr`, 17% at 4
    and 8 limbs and 20% at 16.
  * The reduction gains little from being unrolled. Taking `fpc_mul`
    minus the multiplication alone as its cost, it is 10.7 against 12.2
    ns at 4 limbs, 32.9 against 31.6 at 8 and 102 against 103 at 16: the
    register that carries the first word of the window pays at 4 limbs
    at most.

  Karatsuba (`bn_karatsuba`, one or two levels over each of the four
  multiplications above; same CPU, `make bench-kar` in the same
  directory) against the best schoolbook multiplication of each
  instruction set, in ns:

  | `nlimbs` | MUL/ADC: schoolbook | Karatsuba | MULX/ADCX/ADOX: schoolbook | Karatsuba |
  |---:|---:|---:|---:|---:|
  | 16 | 136.3 (looped) | 146.7 (1 level, ps) | 95.8 (unrolled) | 114.1 (1 level, unrolled) |
  | 32 | 540.6 (looped) | 467.4 (1 level, looped) | 331.9 (looped) | 353.1 (1 level, unrolled) |
  | 64 | 2 119 (ps) | 1 544 (2 levels, looped) | 1 299 (looped) | 1 155 (1 level, looped) |

  * With MULX/ADCX/ADOX, Karatsuba is 19% slower at 16 limbs, 6% slower
    at 32 and 11% faster at 64. On a field multiplication at 64 limbs,
    where the Montgomery reduction (which Karatsuba does not touch) is
    half of the time, that would be about 5%.
  * With MUL/ADC it pays earlier: 8% slower at 16 limbs, 14% faster at 32
    and 27% faster at 64.
  * One level costs about 4 to 5 ns per limb of the half size, on top of
    the three products (66 ns at 32 limbs, 159 ns at 64).
  * One level over the unrolled 32-limb MULX multiplication is 1 449 ns,
    worse than over the looped one although the two are within 4% alone.

  So Karatsuba does not change the choice up to 32 limbs; at 64 limbs it
  is a gain on the multiplication only, and there is no Karatsuba
  squaring.
* **Proofs.** The four modules are proved, with one contract
  (`Bn_mul.eca`, `Bn_mul_loop.eca`, `Bn_mulx.eca`, `Bn_mulx_loop.eca`;
  section 4), and so is `bn_mulxr` (`Bn_mulxr.eca`, next section).
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

### Small sizes: the accumulator in registers (`bn_mulxr`)

`bn_mulxr@n.jinc` has the rows of `bn_mulx` (same names, contracts and
wiring), with its accumulator in a register array instead of the memory of
the result: no row loads or stores the words it accumulates, and a word is
stored once, when it is final. At 4 limbs the multiplication is the shape
of curve25519's `mul4`: 16 `mulx`, the second operand read as a memory
operand, the 8 words of the product in registers, and 8 stores. Only the
window of a row is live, so the registers needed grow with `nlimbs`: the
multiplication needs `nlimbs + 8`, the reduction `nlimbs + 9` (window, top
word, carry, `rdx`, `lo`, `hi`, zero, three pointers), the squaring
keeps its products above the diagonal in registers up to 5 limbs and
stores the low words that would not fit from 6 on.

**The registers of the callers count.** Jasmin allocates the registers of
the whole program at once: a register live across a call, in any caller,
is not available to the callee. The field code used to keep several (the
context, the result pointer, the exponentiation's word of the exponent and
pointers), so that `bn_mulxr`'s reduction did not fit from 3 limbs on.
The callers now keep nothing in registers across the calls of a field
multiplication: `_mulm_`, `_mulmU_`, `_sqrm_`, `_sqrmU_` (`fp_base`) save
the context and the result pointer across `fun_muln`/`fun_sqrn`, and the
exponentiations (`bn_exp`: `_expm`, `_expm_noct`, the LR ones) save their
state, in `stack` variables as the exports already did. That is a few
stack accesses per field operation, for every module. On the i7-14700K,
against the tables of [Unrolled or
looped](#unrolled-or-looped-multiplication-and-reduction) (measured
before), it costs 1% to 3% on `fpc_exp` at 4 limbs (`bn_mul` 14.1 → 14.4
µs, `bn_mul_loop` 13.8 → 14.2, `bn_mulx` 11.0 → 11.1, `bn_mulx_loop`
11.9 → 12.1), and nothing measurable from 8 limbs on (within 1.5% either
way, as between two runs); `fpc_mul` is 1% to 4% faster than before at 4
limbs. With it, a field over
`bn_mulxr` compiles up to 6 limbs (7 does not: the reduction needs 16
registers); the multiplication and squaring alone, up to 8 (and more).

It is selected under BMI2 and ADX up to `JBN_REG_MAX` (5 in
`x86_64_adx.jinc`, from the timings below), and wired directly as the
`MUL` of a size scope with `fp_mul_os`.

The code, in the field instances of `fp_ctx` (instructions, and `mov`s to
or from memory, of each routine; Jasmin 2026.09):

| `nlimbs` | routine | `bn_mulx` | `bn_mulxr` |
|---:|---|---:|---:|
| 4 | `_os_muln` | 87, 36 | 63, 12 |
| 4 | `_os_sqrn` | 72, 33 | 54, 15 |
| 4 | `_redM` | 122, 33 | 103, 10 |
| 6 | `_os_muln` | 191, 78 | 131, 18 |
| 6 | `_os_sqrn` | 141, 63 | 105, 27 |
| 6 | `_redM` | 236, 71 | 189, 14 |

The exponentiation's own code is the same over both (at 6 limbs, 309 and
303 instructions, 128 `mov`s to or from memory each). The entry points
over `bn_mulxr` save the six callee-saved registers, against one over
`bn_mulx`: 10 more `mov`s per call of an `fpc_*` function.

**Timings** (Intel Core i7-14700K, one core; `make bench` in
`examples/simple_tests/fp_ctx`, variants `mulx_unr` and `mulxr`).
`fpc_mul` and `fpc_sqr` are timed with independent calls, on the same
arguments, which may overlap (the throughput), and chained, each call on
the result of the previous one (`BENCH_CHAINED=1`: the latency).
`fpc_exp` is a chain either way, timed once in each run:

| `nlimbs` | calls | `fpc_mul` (ns): `bn_mulx` | `bn_mulxr` | `fpc_sqr` (ns): `bn_mulx` | `bn_mulxr` | `fpc_exp` (µs): `bn_mulx` | `bn_mulxr` |
|---:|---|---:|---:|---:|---:|---:|---:|
| 4 | independent | 19.4 | 17.4 | 17.6 | 15.5 | 11.1 | 10.4 |
| 4 | chained | 24.2 | 23.7 | 22.3 | 21.2 | 11.2 | 10.5 |
| 5 | independent | 27.3 | 25.7 | 24.2 | 22.2 | 18.3 | 18.1 |
| 5 | chained | 31.3 | 31.5 | 28.3 | 27.9 | 18.0 | 18.1 |
| 6 | independent | 36.8 | 34.9 | 32.5 | 29.9 | 27.2 | 28.4 |
| 6 | chained | 39.8 | 40.6 | 35.5 | 35.0 | 28.0 | 28.6 |

* With independent calls `bn_mulxr` is faster at every size: by 10% and
  12% (`fpc_mul`, `fpc_sqr`) at 4 limbs, 6% and 8% at 5, 5% and 8% at 6.
* Chained, most of that is gone: 2% and 5% at 4 limbs, within 1% at 5.
  At 6 limbs it is 2% slower on `fpc_mul`, and slower on `fpc_exp` in both
  runs (4% and 2%). Between runs, the times vary by about 3% (`fpc_exp` of
  `bn_mulx` at 6 limbs: 27.2 and 28.0 µs).
* Hence `JBN_REG_MAX = 5`: at 4 and 5 limbs `bn_mulxr` loses nowhere, at 6
  it gains on throughput only. A size scope whose field multiplications
  are mostly independent of each other (curve formulas) may shadow it with
  6.
* A reading of these figures, not checked with performance counters: the
  memory traffic that `bn_mulxr` removes is off the critical path of a
  call. A chained call takes the time of the carry chains of
  MULX/ADCX/ADOX and of the reduction, whose rows depend on each other
  (each multiplier is read from the result of the previous row), and
  these are the same in both modules.

The multiplications and squarings alone (`make bench` in
`examples/simple_tests/mults`, variant `mulxr`) were not timed.

What is not settled:

* **Fusing.** The field multiplication is still a multiplication into a
  2n-word temporary and a separate reduction, two calls. Fusing them (one
  routine, multiplication rows interleaved with reduction rows, as for
  curve25519 where the whole field multiplication stays in registers)
  needs `nlimbs + 9` registers, so up to 6 limbs, and a change of the
  parameters of `fp_base` (a field multiplication `fun_mulm` instead of
  `fun_muln` and `fun_red`): not done. From the timings above, the gain
  should be mostly in throughput: fusing keeps the dependency between the
  rows of the reduction, and removes a call, the temporary and a reload,
  memory traffic of the kind whose removal by `bn_mulxr` gained little
  in latency. The latency is gained by a shorter reduction: that of
  `fp_pm` is one row (next section).
* **Proofs.** `proof/Bn_mulxr.eca` proves the contracts of `Bn_mul` for
  it, with no admits (the rows of `Bn_mulx.eca`, over the register array;
  the squaring's invariant keeps the copied low words of X equal in `r`
  and `t`); `Bn_mulsel.eca` covers its branch. `fp_pm` has no theory yet.

### Pseudo-Mersenne fields (`fp_pm`)

`fp_pm@fp.jinc` is a field in the place of `fp_mont`, for the moduli whose
reduction curve25519 uses: with `R = 2^(64 nlimbs)`, `c = R mod P < 2^32`
and `R < 3P` (2^255-19 at 4 limbs: `c = 38`, `R = 2P + 38`; `R - c` and
`R/2 - c`; not secp256k1, whose `c` is 33 bits, nor the Solinas primes
P-256 and P-384). Since `R = c (mod P)`, a product `L + R H` is folded into
`L + c H` (one row of `nlimbs` multiplications, where the Montgomery
reduction takes `nlimbs^2`), its top word again (`c t < 2^64`), and a last
carry (masked, which cannot carry); then `P` is subtracted twice when not
below it. The representation is the number itself and is canonical (below
`P`), as `fp_base` requires; curve25519 code keeps values below 2^256 and
reduces fully on output only, which is faster but would break that
invariant.

* It is generic in the multiplication (`fp_mul_ps`, `fp_mul_os`,
  `fp_mul_sel`), and in the size.
* Its context has the layout of `fp_ctx@n.jinc`: `P`, `R - P`, `1` (the
  representation of one), an unused slot (0), and `c` in the slot of `U0`;
  `_ctx_init_` computes it (`c` as `(R - P) - P` when not below `P`).
* `_toM_` and `_fromM_` are the identity, so that `fp_mont_ctx_export`
  serves both kinds of field (`fpc_toM`, `fpc_fromM`).
* Not done: a theory (`Fp_pm.eca`) and its extraction; the fold fused with
  the multiplication rows in one routine (with the parameters of `fp_base`
  above).

**Timings** (Intel Core i7-14700K, one core; `make bench` in
`examples/simple_tests/fp_ctx`). The modulus of `fp_pm` is 2^(64n-1)-19,
which is 2^255-19 at 4 limbs (the code is the same for any `c`); the
Montgomery field has a random modulus of the same size. Over `bn_mulxr`
(variants `mulxr` and `pm_mulxr`), with independent and chained calls as
in the previous section:

| `nlimbs` | calls | `fpc_mul` (ns): Montgomery | `fp_pm` | `fpc_sqr` (ns): Montgomery | `fp_pm` | `fpc_exp` (µs): Montgomery | `fp_pm` |
|---:|---|---:|---:|---:|---:|---:|---:|
| 4 | independent | 17.4 | 16.3 | 15.5 | 14.4 | 10.4 | 8.6 |
| 4 | chained | 23.7 | 21.1 | 21.2 | 19.5 | 10.5 | 8.8 |
| 5 | independent | 25.7 | 21.6 | 22.2 | 18.9 | 18.1 | 14.2 |
| 5 | chained | 31.5 | 26.5 | 27.9 | 22.8 | 18.1 | 14.2 |
| 6 | independent | 34.9 | 29.8 | 29.9 | 26.5 | 28.4 | 20.9 |
| 6 | chained | 40.6 | 31.9 | 35.0 | 27.7 | 28.6 | 21.0 |

Over `bn_mul` (MUL/ADC, product scanning; variants `unr` and `pm_unr`;
independent calls):

| `nlimbs` | `fpc_mul` (ns): Montgomery | `fp_pm` | `fpc_sqr` (ns): Montgomery | `fp_pm` | `fpc_exp` (µs): Montgomery | `fp_pm` |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 25.7 | 17.7 | 21.6 | 14.4 | 14.4 | 9.9 |
| 5 | 39.0 | 24.0 | 32.5 | 19.0 | 25.1 | 16.2 |
| 6 | 51.8 | 34.4 | 44.8 | 26.6 | 39.8 | 23.6 |
| 8 | 87.6 | 57.8 | 77.1 | 42.8 | 89.2 | 49.1 |
| 16 | 313.0 | 173.8 | 269.0 | 125.9 | 597.3 | 316.0 |
| 32 | 1 138.5 | 607.3 | 995.3 | 422.7 | 4 385.8 | 2 195.7 |
| 64 | 4 310.4 | 2 229.3 | 3 940.2 | 1 931.4 | 33 947.8 | 17 106.1 |

* 2^255-19 takes 8.6 µs per exponentiation over `bn_mulxr`: 17% less than
  a Montgomery field over the same module (10.4 µs), and 23% less than
  over `bn_mulx` (11.1 µs), the module selected at 4 limbs before
  `bn_mulxr`.
* The gain holds when the calls are chained, and grows with the size:
  chained, `fpc_mul` is 11%, 16% and 21% faster at 4, 5 and 6 limbs, and
  `fpc_exp` 16%, 22% and 27%. Unlike that of `bn_mulxr`, this gain is on
  the critical path: the reduction is one row of multiplications instead
  of `nlimbs` rows that depend on each other.
* Without MULX, over `bn_mul`, `fp_pm` is 31% to 33% faster than the
  Montgomery field at 4 limbs, on every operation, and takes about half
  the time of its `fpc_exp` from 16 limbs on. It is faster on `fpc_exp`
  than every Montgomery variant timed, the MULX ones included, at every
  size: 9.9 µs at 4 limbs against 10.4 for `bn_mulxr`, 17.1 ms at 64
  limbs against 22.1 for `bn_mulx_loop`.

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
several levels; `examples/schnorr-zk/src/bn_modp2048.jinc` several moduli sharing one
field namespace (contexts `FPM::P::glob_ctx`, `FPM::Q::glob_ctx`);
`examples/simple_tests/rsa_pss/rsa2048.jazz` the same for p and q, with
the contexts computed from an RSA key pair (`_ctx_init_`) and kept in
expanded keys; and
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
  (2n) and `KAR`. `H::MUL` is the selector `bn_mulsel`, so the four
  multiplication modules are `H::MUL::UNR` (`bn_mul`), `H::MUL::LOOP`,
  `H::MUL::XUNR` and `H::MUL::XLOOP`, and the field `H::FPM` uses the
  selector's `__mont_redM`. Function parameters are stubs, declared
  inside the namespace of the module that takes them;
* `preamb@n.jinc`: the placeholder parameters, required inside `H`, whose
  `nlimbs` is 11 (contexts then have 45 words): `nlimbsexp = 13`, and the
  profile `JBN_FEATURES = 19`, `JBN_UNROLL_MAX = 17`;
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
  arithmetic (`bn_seq_cmp`, `addc_to_uint`, `addc3P`, `dbl_mulu`,
  `mulu_to_uint`, the product-and-carry steps `mac1P`/`mac2P`, …) and on
  Montgomery reduction (`mont_low0`, `montred_math`), shared by the
  multiplication theories.
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
| `Bn_mul_loop.eca`, `Bn_mulx.eca`, `Bn_mulx_loop.eca` | `nlimbs` (the looped ones with `4 * nlimbs < W64.modulus`, as `Bn_mul`: the row index is a word) | `bn_mul_loop`, `bn_mulx`, `bn_mulx_loop`: the contracts of `Bn_mul` (`_os_muln_`, `_os_sqrn_`, `__mont_redM`) |
| `Bn_mulxr.eca` | `nlimbs` | `bn_mulxr`: the contracts of `Bn_mul` |
| `Bn_mulsel.eca` | `nlimbs`, the profile `jbn_features`, `jbn_reg_max`, `jbn_unroll_max` (any values; clones the five theories above) | `bn_mulsel`: `_muln_`, `_sqrn_`, `__mont_redM`, proved for the five branches |
| `Bn_rnd.eca` | `nlimbs`; the system call `#randombytes` (`Syscall`) | `bn_rnd`: `_rnd_` is a uniform sample; `_rsample_` a uniform sample below the bound (`_rsample__eq`), and `__bnd_mask` covers the numbers below it |
| `Fp_ctx.eca` | `nlimbs` | `fp_ctx` (layout of a context: `ctxP`, `ctxMP`, `ctxONE`, `ctxR2`, `ctxU0`; `ctx_mod p c`, `ctx_mont p c`) |
| `Bn_exp.eca` | `nlimbs`, `nlimbsexp` (with `64 * nlimbsexp < W64.modulus`), an abstract monoid over contexts (`mok`, `mdom`, `mmul`; the unit is the context's ONE); module parameter `fun_mulU`, `fun_sqrU` | `bn_exp` |
| `Fp_base.eca` | `nlimbs` (with `64 * nlimbs < W64.modulus`), an abstract reduction `red p x = x * redK p mod p` (`redK`, `red_ctx`); module parameter `fun_muln`, `fun_sqrn`, `fun_red` | `fp_base` (its exponentiation is `Bn_exp` in the monoid of representatives) |
| `Fp_mont.eca` | `nlimbs` (with `64 * nlimbs < W64.modulus`), the profile `jbn_features`, `jbn_unroll_max`; module parameter `fun_muln`, `fun_sqrn` | `fp_mont` (`Fp_base` with `redK p = R^-1 mod p`; its reduction is that of `Bn_mulsel`) |

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
`Bn_base.eca`, the five multiplication theories, `Bn_exp.eca`,
`Fp_base.eca` and `Fp_mont.eca` it is generated, between the markers
`(* BEGIN generated by scripts/xtr_sync.py ... *)` and
`(* END generated *)`, by `scripts/xtr_sync.py`, which:

* keeps the procedures of the module (namespace prefix, e.g. `h__BN__`) and
  strips the prefix (`h__BN___add_` becomes `_add_`);
* redirects calls to other modules to the theories that specify them
  (`uTIL____cf_mask` becomes `BNUTIL_M.__cf_mask`, `h__BN___cminusP_` in
  `bn_mul` becomes `BNB_M._cminusP_`);
* replaces the dummy sizes by the parameters (`W64.t Array11.t` becomes
  `BN.t`, `Array22` becomes `BN2`, `11` becomes `nlimbs`, …), and the
  dummy profile by `jbn_features` (19) and `jbn_unroll_max` (17);
* maps the modules instantiated in sub-namespaces of the selector
  (`h__MUL__UNR__`, …) to their own theories (`BNMUL_M`, …);
* turns the calls to the function-parameter stubs into calls to the
  module parameter (`P.fun_red`), with a `module type MParam` built from
  the stubs' signatures, and the calls to sub-instances and included
  modules into calls to the nested modules described above;
* keeps a module that makes system calls (`bn_rnd`: `#randombytes`) a
  functor over them, `M(SC: Syscall_t)`, with size-independent names
  (`randombytes_11W64` becomes `randombytes_W64`); the theory defines
  `Syscall_t` and `Syscall`.

The literals of the dummy sizes are only recognised safely if the library
never uses them as constants; the script checks this on the sources.
A table at the top of the script describes each theory; adding one means
adding an entry and the markers.

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

`examples/simple_tests/rsa_pss/proof/` does it for the RSA example
(`rsa2048.jazz`; `make` there, about 30 s):

1. extract the concrete program (`xtr/RsaPssXtr.ec`: `jasmin2ec
   --array-model=old`, as for the library, from its entry points);
2. clone the theories at the sizes of the program (`RsaPss_inst.ec`:
   `Fp_mont` at 16 and 32 limbs, `Bn_exp` for exponents of 4 limbs),
   mapping the array theories onto the extracted ones
   (`theory BigN.BN.A <= Array16`, `theory BigN.BN2.A <= Array32`,
   `theory FPC.CTX <= Array65`) and the profile ops onto the values of the
   program's profile; a module binds each field's multiplication to the
   selector of the same clone (`B16`, `B32`);
3. prove that each extracted procedure the program calls is the theory's
   (`equiv ... : ={arg, Glob.mem} ==> ={res, Glob.mem}`, by `proc; inline
   *; sim`), and carry its contract over (`conseq` with the equivalence
   and the contract);
4. prove the program's own procedures from these contracts
   (`RsaPss.ec`), and the facts about its constants (`RsaPss_keys.ec`).

For RSA, the contracts hold for any well-formed expanded key (`wf_pk`,
`wf_sk` in `RsaPss_keys.ec`: Montgomery contexts of n, p and q, and the
values of e, dP, dQ, qInv): `rsa_enc` gives `m^e mod n`; `rsa_dec`, for
`c < p*q` and `qInv * q = 1 (mod p)`, a result below `p*q`, congruent to
`c^dP` modulo p and to `c^dQ` modulo q. `rsa_init` builds well-formed
expanded keys of the example key pair (from the contract of
`_ctx_init_`), whose facts (n = p*q, qInv) are computed by the
simplifier.

The extraction asks two things of the program:

* a size given by an expression (`2*nlimbsP`) is extracted as such, and
  its loops then bound the index by a variable, which `sim` does not
  relate to the literal of the theory: give the `nlimbs` of each size
  scope as a literal, or as a parameter that is one (`nlimbsN = 32`);
* the program uses the selector (`bn_mulsel`, with a profile), as the
  theories do (`Fp_mont.eca` reduces with it): code that wires `bn_mul`
  directly is the same up to the selection, which `sim` does not see
  through.

The globals are extracted as abbreviations of literal arrays, which the
simplifier normalises (negative words, for instance): the proofs refer to
them through `op`s (`pkT`, `skT` in `RsaPss_keys.ec`). The values of the
key are `op [opaque]`, unfolded by name only: otherwise a simplification
(that of `conseq`, for instance) may try to evaluate `x ^ dP_val` by
unrolling the power.

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
| `simple_tests/rsa_pss` | 2048-bit RSA from a key pair (`rsa_keys.jinc`: pk = (n, e), sk = (p, q, dP, dQ, qInv); layout in `rsa2048_params.jinc`): expanded keys with the contexts of n, p and q (PK = (ctx_n, e), SK = (ctx_p, ctx_q, dP, dQ, qInv)), computed once by `rsa_init`; RSAVP1 and RSASP1 by the CRT on them (`rsa2048@libjbn.jinc`; profile `x86_64`, the selector); `make run` checks the expanded keys and both primitives against values computed in Python, and their round trips; `proof/`: their correctness in EasyCrypt from the contracts of the library (`make` there; see [Using the theories for a concrete instance](#using-the-theories-for-a-concrete-instance)) |
| `simple_tests/fp_ctx` | moduli given at run time (7 and 16 limbs): `fpc_ctx_init` and every `fpc_*` operation, against Python (`make run`); each size is also built with `bn_mul_loop` (`fp_ctx_loop*.jazz`, in `make run`) and with `bn_mulx_loop` and `bn_mulx` (`fp_ctx_mulx_loop*.jazz`, `fp_ctx_mulx*.jazz`; `make run-mulx`, which needs BMI2 and ADX); and with the selector `bn_mulsel`, once per module (`fp_ctx_sel*.jazz`, profile `x86_64`, in `make run`; `fp_ctx_selx*.jazz`, profile `x86_64_adx`, in `make run-mulx`; the 16-limb ones shadow the threshold); with `bn_mulxr` at 4, 5 and 6 limbs (`fp_ctx_mulxr*.jazz`, in `make run-mulx`); pseudo-Mersenne fields (`fp_pm`, 2^255-19 among the moduli) at 4 and 6 limbs, over `bn_mul` (`fp_ctx_pm*.jazz`, in `make run`) and over `bn_mulxr` (`fp_ctx_pmxr*.jazz`, in `make run-mulx`), with `vectors_pm*.txt` (`gen_vectors.py N SEED pm`); `make exec` runs the same checks in the interpreter of `jasminc`, on any host (`gen_exec_test.py`, below); `make bench` times the five modules, and `fp_pm` over `bn_mul` and over `bn_mulxr` (variants `pm_unr`, `pm_mulxr`; modulus 2^(64n-1)-19); `fpc_mul` and `fpc_sqr` are timed on the same arguments at each call (throughput), or, with `BENCH_CHAINED=1`, each call on the result of the previous one (latency, as in `fpc_exp`) |
| `simple_tests/mults` | 32-limb multiplication: `ps`, `os`, `osreg` and Karatsuba variants; the `os` multiplication and squaring of `bn_mul_loop`, `bn_mulx_loop` and `bn_mulx` (`testmul_os_loop.c`, against a C reference); `make bench` (with `bn_mulxr`: variant `mulxr`) and `make bench-kar` time the multiplications and squarings alone |
| `schnorr-zk` | a Schnorr zero-knowledge protocol over the RFC 3526 2048-bit group |

The test programs print `TESTING <name>:` followed by `...OK!`, or by the
expected and obtained values.

The code is x86-64. On macOS the Makefiles compile with
`gcc -arch x86_64` and the programs run under Rosetta. Rosetta does not
support the ADX instructions (`mulx`/`adcx`/`adox`) used by the
operand-scanning multiplications, so the `os`/`osreg` tests in
`simple_tests/mults` must be run on an x86-64 machine (Broadwell or later);
this includes `testmul_os_mulx_loop_32` and `testmul_os_mulx_32` (but not
`testmul_os_loop_32`), and `make run-mulx` in `simple_tests/fp_ctx`.
Override the compiler with `make GCC=...` if needed.

Where they cannot run, `make exec` in `simple_tests/fp_ctx` checks the same
modules in the interpreter of `jasminc` (`exec`), which runs the source
program at compile time, MULX/ADCX/ADOX included; since the compiler is
verified, this checks the emitted code. `gen_exec_test.py` writes a
program that loads inputs, calls a module's multiplication and squaring
and the field operations over it (Montgomery, or `--pm`; the selector
with `--profile`), and returns the OR of the differences with the values
computed in Python (0 when correct) and the number of words checked.
`EXEC_TESTS` lists the modules and sizes; it takes about 5 minutes, mostly
the exponentiations.

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

* `JBigNumber.ec`, `Bn_util.ec`, `Bn_base.eca`, `Bn_mul.eca`,
  `Bn_mul_loop.eca`, `Bn_mulx.eca`, `Bn_mulx_loop.eca`, `Bn_mulxr.eca`,
  `Bn_mulsel.eca`, `Fp_ctx.eca`, `Bn_exp.eca`, `Fp_base.eca` and
  `Fp_mont.eca` check, and
  their modules `M` are generated from the extraction (`make -C proof`).
  None of them has admits.
  * `Bn_rnd.eca` checks too, and its module is generated as well (a functor
    over the system call `#randombytes`, `M(SC: Syscall_t)`, with `Syscall`
    drawing random bytes as the extraction does). `_rnd_` is a uniform
    sample (`rndspec_eq`), and `_rsample_` a uniform sample below the bound
    (`_rsample__eq`): `__bnd_mask` covers the numbers below the bound (the
    bits of its top limb smeared downwards, `bnd_mask_h`, `mask_covers`),
    the masked samples are uniform over the numbers the mask covers
    (`dmask_uni`), and the rejection sampling from them is the uniform
    distribution below the bound (`dmask_excepted`, then `WhileSampling` of
    the EasyCrypt library).
  * `Bn_base.eca` has memory contracts for `_load_` and `_store_`
    (`_load__mem_h`, `_store__mem_h`: the words read or written at
    `ap + 8*i`, and the rest of memory unchanged); `Fp_base.eca` a
    contract of `_mulmU_` for operands whose product is below `p * R`
    (`_mulmU__wide_h`), and `Fp_mont.eca` one of `_toM_` for any operand
    below `R` (`_toM__any_h`).
  * The RSA example is proved correct
    (`examples/simple_tests/rsa_pss/proof`, no admits; besides the
    axioms of the Jasmin array and memory model, none): `rsa_init` builds
    well-formed expanded keys of the example key pair; for any
    well-formed expanded keys, `rsa_enc` returns `m^e mod n`, and
    `rsa_dec`, for `c < p*q` and `qInv * q = 1 (mod p)`, a result below
    `p*q` congruent to `c^dP` modulo p and to `c^dQ` modulo q. That this
    is `c^d mod n`, and that decryption inverts encryption, needs p and q
    prime and Fermat's little theorem: not done.
  * `Bn_mul_loop.eca`, `Bn_mulx_loop.eca` and `Bn_mulx.eca` prove the
    contracts of `Bn_mul` for the other three modules: losslessness and
    correctness of `_os_muln_`, `_os_sqrn_` and `__mont_redM`. The rows
    carry the pending value of the next word (a word, or a word plus the
    carries of the CF and OF chains), which a bound on the row keeps from
    overflowing; the reductions track the sum of the multipliers as a
    ghost. `Bn_mulx.eca` also proves its squaring (`a^2 = 2 X + D`, the
    products above the diagonal by rows, then the doubling pass) and its
    reduction, whose first row reads the argument (a ghost "window").
  * `Bn_mulsel.eca` proves the selector's `_muln_`, `_sqrn_` and
    `__mont_redM` for every profile, from the contracts of the four
    modules (one per branch).
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
    and `Fp_mont.eca` instantiates it with the Montgomery reduction of the
    selector and proves `_redM_`, `_toM_`, `_fromM_` and `_ctx_init_`
    (Newton's iteration for U0, doublings for R mod p and R^2 mod p), for
    every profile.
  * The parameter axioms `64 * nlimbs < W64.modulus` (`Fp_base`,
    `Fp_mont`) and `64 * nlimbsexp < W64.modulus` (`Bn_exp`) bound the
    loop counters (`32 * nlimbs` doublings, the signed limb index of
    `_expmLR_noct_`).
* The examples whose operand-scanning code uses ADX/MULX (e.g.
  `simple_tests/mults/testmul_*os*`) stop with "Illegal instruction" under
  Rosetta 2 on Apple silicon; they need a native x86-64 CPU with ADX/BMI2.
* `bn_mul_loop` and `bn_mulx_loop` are proved (above), and tested
  (`simple_tests/mults`, `simple_tests/fp_ctx`);
  `bn_mulx_loop` only where BMI2 and ADX are available (its tests passed
  on an Intel Core i7-14700K): `testmul_os_mulx_loop_32` in `mults`,
  `make run-mulx` in `fp_ctx`.
* `bn_mulx` is proved as well. Its tests passed on the same CPU (`testmul_os_mulx_32` in `mults`, at 32 limbs; `make
  run-mulx` in `fp_ctx`, at 7 and 16 limbs); at the other sizes its
  generated assembly was checked with an interpreter of the few
  instructions it uses (multiplication, squaring and reduction against
  Python, from 1 to 32 limbs; the `fpc_*` entry points of a field instance
  on the vectors of `fp_ctx`, at 1 to 5 limbs). `jasmin-ct` accepts it, and
  `jasmin-ct --sct --after=unroll` as well, as the other unrolled code.
* `Fp_base`'s `_rnd_`, which calls `_rsample_`, is not in its theory, and
  has no contract (`_rsample_` has one, in `Bn_rnd.eca`).
* `proof/extracted/Makefile` (the concrete `XtrCode` extraction) still uses
  the old `jasminc -ec` interface.
* All examples build; see [Examples](#5-examples) for the tests that cannot
  run under Rosetta.
