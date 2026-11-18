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
  plain `.jinc` file that is `require`d inside a namespace, which becomes
  the instance; its parameters are found by Jasmin's ordinary name lookup;
* on the **proof side**, with *abstract (parametrised) EasyCrypt theories*
  whose parameters are later instantiated by cloning.

This document describes that workflow.


## Overview

```
 src/amd64/ref/<module>.jinc     library modules: generic code whose free names
                                 (nlimbs, glob_P, fun_muln, BN::..., H::BN::...)
              │                  are its parameters
              │  require "<module>.jinc" inside namespaces
              │
    ┌─────────┴────────────────────────────┐
    ▼                                      ▼
 wiring file of a program         src/amd64/ref/extracted/libjbn_abs.jazz
 (e.g. examples/.../*.jinc)       (every module, dummy parameters, stubs)
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
| `src/amd64/ref/*.jinc` | The library modules (see [Library modules](#1-library-modules)). |
| `src/amd64/ref/params/` | Constants of concrete prime fields (`sike/`, `nistp/`, `rfc3526/`), one file per modulus, under the names the field modules expect. |
| `src/amd64/ref/extracted/` | Abstract instantiation and extraction used by the proofs (see [Extraction](#3-extraction-for-the-proofs)). |
| `src/amd64/ref/legacy/` | Kept for reference: pre-modular multiplication code and its C tests; `mjazz/`, the former template-based instantiation (`mjazz_proc.py`, `templates/`, and the modules in the proposed #519 parametric-module syntax). |
| `proof/` | EasyCrypt development: value semantics (`JBigNumber.ec`) and one abstract theory per module (`*.eca`). |
| `examples/` | Concrete programs with C test programs: `simple_tests/{sike,rsa_pss,mults}`, `schnorr-zk/`. |
| `test/misc/` | Generator of field instances for many moduli (compilation tests); `bench/` uses its output. |
| `bench/`, `ext/` | Benchmarks, external code (`randombytes`). |
| `src/attic/`, `proof/attic/` | Older code and proofs, kept for reference. |


## 1. Library modules

### Modules

Each module starts with a comment giving its *signature*: the names it
expects to find in scope and the names it provides.

| Module | Contents | Instance (namespace) | Expects in scope |
|---|---|---|---|
| `bn_util` | flag/mask helpers, 3-limb accumulators used by multiplication | `UTIL` (top level) | — |
| `bn_base` | load/store, comparison, (conditional) moves and swaps, add/sub/neg with carry, `cminusP`, `pack2` | `BN` | `nlimbs`, `UTIL::` |
| `bn_rnd` | uniform sampling (`_rnd_`, `_rsample_`) | `RND` | `nlimbs`, `BN::` |
| `bn_mul` | operand-scanning (`os`) and product-scanning (`ps`) multiplication and squaring; Montgomery reduction `__mont_redM` | `MUL` | `nlimbs`, `BN::`, `UTIL::` |
| `bn_mulreg` | operand-scanning multiplication with the second operand in registers | `MULREG` | `nlimbs` |
| `bn_karatsuba` | one Karatsuba level on top of a given multiplication | `KAR` (in the 2n scope) | `nlimbs` (2n), `H::nlimbs` (n), `fun_kmuln`, `BN::`, `H::BN::`, `UTIL::` |
| `bn_exp` | modular exponentiation (constant-time and not) | `EXP` (inside a field) | `nlimbs`, `nlimbsexp`, `glob_exp0`, `fun_mulU`, `fun_sqrU`, `BN::`, `UTIL::` |
| `fp_base` | prime-field operations, generic in the reduction | a field (e.g. `FPM`) | `nlimbs`, `nlimbsexp`, `glob_P`, `glob_mP`, `glob_exp0`, `glob_Pm2`, `fun_muln`, `fun_sqrn`, `fun_red`, `BN::`, `RND::`, `UTIL::` |
| `fp_mont` | Montgomery-form field (`_redM_`, `_fromM_`, `_toM_`) plus all of `fp_base` | a field (e.g. `FPM`, `FQM`) | as `fp_base` (except `fun_red`), plus `glob_P0i`, `glob_rMP`, `MUL::` |
| `fp_mul_ps` | binds `fun_muln`/`fun_sqrn` to product-scanning multiplication | inside a field | `nlimbs`, `MUL::` |
| `*_export` | `export fn` wrappers forming the C interface | top level | see the file headers |

Two modules instantiate others themselves, because the instance depends on
their own functions (they correspond to `clone ... with` inside the
EasyCrypt theories):

* `fp_base` defines `fun_mulU`/`fun_sqrU` (inline wrappers of its
  `_mulmU_`/`_sqrmU_`) and then `namespace EXP { require "bn_exp.jinc" }`;
  inversion (`_invm_`, `_invmU_`) uses `EXP::`.
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
   that size (`BN`, `RND`, `MUL`, `MULREG`, `KAR`), plus any number of
   fields (`FPM`, `FQM`, …), each with its own constants. `UTIL` is
   instantiated once, at the top level.
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
nothing at run time. `fp_mul_ps.jinc` provides the usual choice for
fields. Because functions cannot be shadowed, a wrapper must not be visible
from an enclosing namespace when an inner one defines the same name: define
the outer level's wrapper *after* the inner namespace has closed.

**Field constants** live in `src/amd64/ref/params/`, one file per modulus,
under the expected names (`glob_P`, `glob_mP`, `glob_P0i`, `glob_Pm2`,
`glob_exp0`, `glob_rMP`), typed with the enclosing `nlimbs`; the file is
required inside the field namespace. The limb count is stated once, by the
wiring; a mismatch is a type error.

Example (`examples/simple_tests/sike/bn_sike434.jinc`):

```
namespace UTIL { from Libjbn require "bn_util.jinc" }

namespace H {                                   // working size
  param int nlimbs = 7;
  namespace BN  { from Libjbn require "bn_base.jinc" }
  namespace RND { from Libjbn require "bn_rnd.jinc" }
  namespace MUL { from Libjbn require "bn_mul.jinc" }
  namespace FPM {
    param int nlimbsexp = nlimbs;
    from Libjbn require "params/sike/sike434.jinc"   // glob_P, glob_mP, ...
    from Libjbn require "fp_mul_ps.jinc"             // fun_muln, fun_sqrn
    from Libjbn require "fp_mont.jinc"
  }
}

from Libjbn require "bn_base_export.jinc" "fp_mont_export.jinc"
```

`examples/simple_tests/mults/kar_32_*.jinc` show the halving nesting over
several levels, and `examples/schnorr-zk/src/bn_modp2048.jinc` two fields
sharing one size scope (there the top level is the size scope itself).

Compile with the library bound to the include name `Libjbn`:

```
jasminc -lazy-regalloc -I Libjbn=src/amd64/ref -o <name>.s <name>.jinc
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
* `preamb.jinc`: the placeholder constants (`nlimbsexp = 13`, zero globals
  `glob_P`, `glob_mP`, …), required inside `H`, whose `nlimbs` is 11;
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
letter (`H::BN::_add_` becomes `h__BN___add_`); the prefix of each module
is listed in `proof/extracted_ths/Readme.md`. The generated `Array*.ec` and
`WArray*.ec` theories are removed by the final `make clean` step.

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
| `Bn_rnd.eca` | `nlimbs` | `bn_rnd` |
| `Bn_exp.eca` | `nlimbs`, `nlimbsexp`, `glob_exp0`, the multiplication operator | `bn_exp` |
| `Fp_base.eca` | `nlimbs`, `glob_P`, `glob_mP`, `glob_exp0`, `glob_Pm2`, the reduction operator, `prime P` | `fp_base` |
| `Fp_mont.eca` | the above plus `glob_P0i` | `fp_mont` |

Each theory contains the module `M` obtained from the extracted code, then,
for each user-callable procedure `ppp`:

* `ppp_ll`: `islossless M.ppp`;
* `ppp_h`: the functional specification as a `hoare` judgement;
* `ppp_ph`: the same as a `phoare ... = 1%r` judgement (from the two above).

Inner loops and wrappers get their own `_h` lemmas when needed (e.g.
`__addc1U_h` for the loop of `_addcU_`).

### From extracted code to an abstract theory

The extracted code (section 3) is concrete: `nlimbs` is inlined as `11`,
arrays are `Array11`/`Array22`, procedure names carry the namespace path.
It is turned into the module of an abstract theory by **manual
rewriting**, documented in `proof/extracted_ths/Readme.md`:

* `W64.t Array11.t` becomes `BN.t` (and `Array22` becomes `BN2`);
* `11` (the placeholder `nlimbs`) becomes `nlimbs`, and `13` becomes `nlimbsexp`;
* namespace prefixes are removed (`h__BN___add_` becomes `_add_`,
  `uTIL____addacc3` becomes `__addacc3`, …).

Global constants and function parameters become abstract operators (or
module parameters) of the theory.

### Using the theories for a concrete instance

`proof/UsageExample.ec` shows the intended use:

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

From `proof/`:

```
easycrypt compile -I . -I JExtract:extracted -I JPExtract:extracted_ths Bn_base.eca
```

(`proof/.dir-locals.el` sets the same include paths for Proof General.)


## 5. Examples

Each directory under `examples/` holds wiring files (`.jinc`/`.jazz`), C
test programs and a Makefile that runs `jasminc` and the C compiler:

```
cd examples/simple_tests/sike     # or rsa_pss, mults, ../schnorr-zk/src
make            # compile and link (rebuilds when a library module changes)
make clean
```

| Example | What it tests |
|---|---|
| `simple_tests/sike` | Montgomery field arithmetic for the SIKE primes (434, 503, 610, 751 bits) |
| `simple_tests/rsa_pss` | 2048-bit RSA: `dec(enc(t)) == t` |
| `simple_tests/mults` | 32-limb multiplication: `ps`, `os`, `osreg` and Karatsuba variants |
| `schnorr-zk` | a Schnorr zero-knowledge protocol over the RFC 3526 2048-bit group |

The test programs print `TESTING <name>:` followed by `...OK!`, or by the
expected and obtained values.

The code is x86-64. On macOS the Makefiles compile with
`gcc -arch x86_64` and the programs run under Rosetta. Rosetta does not
support the ADX instructions (`mulx`/`adcx`/`adox`) used by the
operand-scanning multiplications, so the `os`/`osreg` tests in
`simple_tests/mults` must be run on an x86-64 machine (Broadwell or later).
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

* `JBigNumber.ec`, `Bn_util.ec` and `Bn_base.eca` check. `Bn_base.eca`
  still admits the correctness of `_muln_`, `_sqrn_` and `__mont_redM`.
* `Bn_rnd.eca`, `Bn_exp.eca`, `Fp_base.eca`, `Fp_mont.eca` and
  `UsageExample.ec` do not load: they require `MLeakage.ec`, which uses
  `leakages_t`, no longer provided by the Jasmin `eclib`.
* The module embedded in `Bn_base.eca` predates the move of the
  multiplication code to `bn_mul` (it still contains `__muln`, `__sqrn` and
  `__mont_redM`); it has been kept in sync with the source by hand.
* The theories were written against the template-based extraction; their
  procedure names are unaffected, but `Fp_base`/`Fp_mont` extracted code now
  contains the concrete sub-instances described in section 3.
* `proof/extracted/Makefile` (the concrete `XtrCode` extraction) still uses
  the old `jasminc -ec` interface.
* All examples build; see [Examples](#5-examples) for the tests that cannot
  run under Rosetta.
