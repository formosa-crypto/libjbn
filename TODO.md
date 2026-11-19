
## Usability & conventions

+ [Done] parameter order convention: change to "results first".
+ [Done] systematic definition of `_xxx_` procedure variants (preferred user access to the library code)
- `for` vs `while` in mult/red: both exist now (`bn_mul` unrolled; `bn_mulx` unrolled; `bn_mul_loop`, `bn_mulx_loop` with a run-time loop over the rows -- see README, "Unrolled or looped", which has the timings on an i7-14700K). Still to do:
  - choose the defaults. Where BMI2/ADX can be required: `bn_mulx` (unrolled) up to 16 limbs, 8% to 11% faster than `bn_mulx_loop` on `fpc_exp`, and `bn_mulx_loop` from 32 limbs on, where `bn_mulx` is 59% slower (its code no longer fits the instruction cache). Without them, `bn_mul_loop` and the unrolled `bn_mul` are within 3% up to 16 limbs and the unrolled one is faster above. Missing: sizes between 16 and 32 limbs (the crossover is expected near 24), and a second CPU (AMD, or an older Intel; the crossover depends on the size of the instruction cache);
  - the register that carries the first word of the window in the reduction of `bn_mulx` pays at 4 limbs at most: not worth porting to the looped modules;
  - Karatsuba in the field multiplication: measured on the multiplication alone (README), with MULX it loses up to 32 limbs and gains 11% at 64 (about 5% of `fpc_mul`); with MUL/ADC it gains 14% at 32 limbs and 27% at 64. Worth wiring into a field only for 64 limbs and more, or where BMI2/ADX cannot be required; it has no squaring;
  - a squaring of their own for the looped modules (they square by multiplying): the largest gain left from 32 limbs on. The unrolled squaring of `bn_mulx` alone is 39% faster than the looped multiplication at 32 limbs (199 against 325 ns). Until it exists, a 32-limb field could take `fun_sqrn` from a `bn_mulx` instance (19 KB, which still fits the instruction cache) and the rest from `bn_mulx_loop`: not tried;
  - prove the variants that are kept (`_os_muln`, row-wise `__mont_redM`), with the contracts of `Bn_mul.eca`;
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
- efficient operand-scanning multiplication (with upto 4/5/6 limbs... -- base: curve25519)
- [In progress] karatsuba
+ [Done] rsample masks each sample to the bit length of bnd (a bound shorter than the array is met with probability > 1/2); its theory `Bn_rnd.eca` is still to be revived


