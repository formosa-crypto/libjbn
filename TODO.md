
## Usability & conventions

+ [Done] parameter order convention: change to "results first".
+ [Done] systematic definition of `_xxx_` procedure variants (preferred user access to the library code)
- `for` vs `while` in mult/red: four modules (`bn_mul`, `bn_mulx` unrolled; `bn_mul_loop`, `bn_mulx_loop` with a run-time loop over the rows -- see README, "Unrolled or looped", which has the timings on an i7-14700K).
  + [Done] selection at compile time: `bn_mulsel` (the `MUL` of a size scope, with `fp_mul_sel` in the field) chooses from a profile (`profiles/x86_64.jinc`, `profiles/x86_64_adx.jinc`: `JBN_FEATURES`, `JBN_UNROLL_MAX`, which a size scope may shadow) -- see README, "Profiles and the selection of the multiplication". The theories are proved for every profile (`Bn_mulsel.eca`, `Fp_mont.eca`).
  + [Done] proofs of the three new modules (`Bn_mul_loop.eca`, `Bn_mulx.eca`, `Bn_mulx_loop.eca`: the contracts of `Bn_mul`, no admits). Still to do:
  - the thresholds of the profiles come from one CPU: time 16 to 32 limbs with MULX (the crossover is expected near 24), above 64 limbs without, and a second CPU (AMD, or an older Intel; the crossover depends on the size of the instruction cache);
  - move the examples (sike, rsa_pss, schnorr-zk) to the selector and a profile (they still wire `bn_mul` directly, which remains possible);
  - the register that carries the first word of the window in the reduction of `bn_mulx` pays at 4 limbs at most: not worth porting to the looped modules;
  - Karatsuba in the field multiplication: measured on the multiplication alone (README), with MULX it loses up to 32 limbs and gains 11% at 64 (about 5% of `fpc_mul`); with MUL/ADC it gains 14% at 32 limbs and 27% at 64. Worth wiring into a field only for 64 limbs and more, or where BMI2/ADX cannot be required; it has no squaring;
  - a squaring of their own for the looped modules (they square by multiplying): the largest gain left from 32 limbs on. The unrolled squaring of `bn_mulx` alone is 39% faster than the looped multiplication at 32 limbs (199 against 325 ns). Until it exists, a 32-limb field could take `fun_sqrn` from a `bn_mulx` instance (19 KB, which still fits the instruction cache) and the rest from `bn_mulx_loop`: not tried;
  - run-time loop over the limbs of the exponent in `_expm`/`_expm_noct` (now the largest routines of a looped instance).


## Proof

+ [In progress] add statements for ll and correctness lemmas "for all procedures" (after changes on the conventions...)
- (medium term) port existing proofs to the new framework
- add ct verification ([Done] generalize the extraction "heuristics/scripts" to deal with leakage)
+ [In progress] move sampling code/lemmas from `Bn_base` into `Bn_rnd`

## Code (nice to have)

- test code...
- GMP baseline 
- a good profile of the efficiency/size of multiplication code and reductions
+ [In progress] efficient operand-scanning multiplication (with upto 4/5/6 limbs... -- base: curve25519) -- see README, "Small sizes: the accumulator in registers" and "Pseudo-Mersenne fields":
  + [Done] `bn_mulxr`: the rows of `bn_mulx` with the accumulator in registers (a field up to 6 limbs; selected by `bn_mulsel` up to `JBN_REG_MAX`); for it, the field code and the exponentiations keep nothing in registers across the calls of a field multiplication (`fp_base`, `bn_exp`; `Bn_exp.eca`, `Fp_base.eca` adapted);
  + [Done] `fp_pm`: pseudo-Mersenne fields (R mod P < 2^32, R < 3P: 2^255-19), folding with one row of multiplications, canonical, generic in the multiplication;
  + [Done] `make exec` (fp_ctx): the field tests in the interpreter of jasminc, on any host (MULX included);
  - time `bn_mulxr` against `bn_mulx` at 4, 5, 6 limbs (`make bench` in fp_ctx and mults, variant `mulxr`; needs BMI2/ADX), and set `JBN_REG_MAX`; also the cost of the stack saves of the callers on the other modules; and `fp_pm` against the Montgomery field (variants `pm_mulxr` against `mulxr`, `pm_unr` against `unr`);
  - the fused field multiplication (multiplication and Montgomery rows interleaved, CIOS, `nlimbs + 9` registers: up to 6 limbs; for `fp_pm`, the rows and the fold in one routine): needs `fp_base` to take `fun_mulm`/`fun_sqrm` (field products) instead of `fun_muln`/`fun_sqrn`/`fun_red`;
  - theory of `fp_pm` (`Fp_pm.eca`) and its extraction; the lazy representation of curve25519 (values below 2^256, freeze on output) does not fit `fp_base`'s invariant;
  - secp256k1 (c = 2^32+977: a two-word second fold).
- [In progress] karatsuba
+ [Done] rsample masks each sample to the bit length of bnd (a bound shorter than the array is met with probability > 1/2); its theory `Bn_rnd.eca` is still to be revived


