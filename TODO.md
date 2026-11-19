
## Usability & conventions

+ [Done] parameter order convention: change to "results first".
+ [Done] systematic definition of `_xxx_` procedure variants (preferred user access to the library code)
- `for` vs `while` in mult/red: both exist now (`bn_mul` unrolled; `bn_mul_loop`, `bn_mulx_loop` with a run-time loop over the rows -- see README, "Unrolled or looped", which has the timings on an i7-14700K). Still to do:
  - choose the defaults: of the three existing modules the timings favour `bn_mulx_loop` at every size (4 to 128 limbs) where BMI2/ADX can be required; without them, `bn_mul_loop` and the unrolled `bn_mul` are within 3% up to 16 limbs and the unrolled one is faster above; a second CPU (AMD, or an older Intel) is missing;
  - `bn_mulx` (unrolled MULX/ADCX/ADOX multiplication, squaring and reduction, for small sizes) is written but only checked with an interpreter: run its tests on a CPU with BMI2/ADX (`testmul_os_mulx_32` in `mults`, `make run-mulx` in `fp_ctx`) and time it (`mulx_unr` in `make bench` of `fp_ctx` and of `mults`) before keeping it. On the multiplication alone, the looped MULX code was 16% and 12% slower than the unrolled one at 8 and 16 limbs (3% at 4), 4% faster at 32 and twice as fast at 64;
  - if keeping the first word of the window in a register pays in the reduction of `bn_mulx`, do the same in `bn_mulx_loop` and `bn_mul_loop` (their multiplier is reloaded from memory at each row);
  - Karatsuba in the field multiplication: measured on the multiplication alone (README), with MULX it loses up to 32 limbs and gains 11% at 64 (about 5% of `fpc_mul`); with MUL/ADC it gains 14% at 32 limbs and 27% at 64. Worth wiring into a field only for 64 limbs and more, or where BMI2/ADX cannot be required; it has no squaring;
  - a squaring of their own for the looped modules (they square by multiplying, which is all of what `bn_mul_loop` loses to the unrolled code on `fpc_exp` at 32 limbs, and about half at 64);
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


