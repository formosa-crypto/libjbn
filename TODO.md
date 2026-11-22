
## Usability & conventions

+ [Done] parameter order convention: change to "results first".
+ [Done] systematic definition of `_xxx_` procedure variants (preferred user access to the library code)
- `for` vs `while` in mult/red: four modules (`bn_mul`, `bn_mulx` unrolled; `bn_mul_loop`, `bn_mulx_loop` with a run-time loop over the rows -- see README, "Unrolled or looped", which has the timings on an i7-14700K).
  + [Done] selection at compile time: `bn_mulsel` (the `MUL` of a size scope, with `fp_mul_sel` in the field) chooses from a profile (`profiles/x86_64.jinc`, `profiles/x86_64_adx.jinc`: `JBN_FEATURES`, `JBN_UNROLL_MAX`, which a size scope may shadow) -- see README, "Profiles and the selection of the multiplication". The theories are proved for every profile (`Bn_mulsel.eca`, `Fp_mont.eca`).
  + [Done] proofs of the three new modules (`Bn_mul_loop.eca`, `Bn_mulx.eca`, `Bn_mulx_loop.eca`: the contracts of `Bn_mul`, no admits). Still to do:
  - the thresholds of the profiles come from one CPU: time 16 to 32 limbs with MULX (the crossover is expected near 24), above 64 limbs without, and a second CPU (AMD, or an older Intel; the crossover depends on the size of the instruction cache);
  - move the examples (sike, schnorr-zk) to the selector and a profile (they still wire `bn_mul` directly, which remains possible; [Done] rsa_pss, which its proof needs);
  - the register that carries the first word of the window in the reduction of `bn_mulx` pays at 4 limbs at most: not worth porting to the looped modules;
  - Karatsuba in the field multiplication: measured on the multiplication alone (README), with MULX it loses up to 32 limbs and gains 11% at 64 (about 5% of `fpc_mul`); with MUL/ADC it gains 14% at 32 limbs and 27% at 64. Worth wiring into a field only for 64 limbs and more, or where BMI2/ADX cannot be required; it has no squaring;
  - a squaring of their own for the looped modules (they square by multiplying): the largest gain left from 32 limbs on. The unrolled squaring of `bn_mulx` alone is 39% faster than the looped multiplication at 32 limbs (199 against 325 ns). Until it exists, a 32-limb field could take `fun_sqrn` from a `bn_mulx` instance (19 KB, which still fits the instruction cache) and the rest from `bn_mulx_loop`: not tried;
  - run-time loop over the limbs of the exponent in `_expm`/`_expm_noct` (now the largest routines of a looped instance).


## Proof

+ [Done] correctness of the RSA example (`examples/simple_tests/rsa_pss/proof`): the library theories at its sizes, the extracted code proved equal to theirs, the key facts computed, and the contracts of `rsa_init` (well-formed expanded keys, from `_ctx_init__h`), RSAVP1/`rsa_enc` and RSASP1/`rsa_dec` (for any well-formed expanded key); no admits. `rsa_dec` gives `c^d mod n` for distinct primes p, q (`rsa_dec_h`, `IntDiv.Fermat_little`; for the example key, primality is a hypothesis). Still to do: `dec(enc m) = m` (from `e * d = 1 (mod lcm(p-1, q-1))`, `ed_inv` in `RsaPss_keys.ec`); the same for sike and schnorr-zk (after moving them to the selector)

## Safety

+ [Done] safety proofs of every library module and export template (`proof/safety`, README section 5): parametric (extraction at two dummy points, `scripts/xtr_safety.py`), checked at both points (`checkxtr`), no admits; the RSA example safe end to end (`examples/simple_tests/rsa_pss/proof/safety`). Still to do:
- upstream the fix of the safety extractor for the carry flag of shifts (Jasmin branch `safety-shift-flags`, over `safety-symbolic-params`), and move to a released extractor;
- run the MULX/ADX code (`bn_mulx`, `bn_mulx_loop`, `bn_mulxr`, the `os` Karatsuba of `mults`, `make run-mulx` in `fp_ctx`) on an x86-64 CPU with ADX: the `#[safety]` annotations changed the register allocation of `jasminc`, and these programs cannot run under Rosetta;
- measure whether the annotations cost time (`make bench` in `mults` and `fp_ctx`, before and after: the register allocation changed);
- the safety of the other examples (sike, schnorr-zk, fp_ctx, mults), as for RSA; `fp_ctx` through the theory of `fp_mont_ctx_export`, which no program glue uses yet;
- `fp_base`'s `_rnd_` (not extracted), and the commented-out entry points (`bn_kar_sqrn`, `bn_os_sqrn`);
- at an instance, a listing that every specification of the program's extraction is established (the RSA glue transfers the lemmas of the library procedures the RSA code calls; their callees are covered inside these lemmas);
- generate the instance glue: `RsaPssSafety_inst.ec` was drafted by a script that is not in the repository.

## Code (nice to have)

- test code...
- GMP baseline 
- a good profile of the efficiency/size of multiplication code and reductions
+ [In progress] efficient operand-scanning multiplication (with upto 4/5/6 limbs... -- base: curve25519) -- see README, "Small sizes: the accumulator in registers" and "Pseudo-Mersenne fields":
  + [Done] `bn_mulxr`: the rows of `bn_mulx` with the accumulator in registers (a field up to 6 limbs; selected by `bn_mulsel` up to `JBN_REG_MAX`); for it, the field code and the exponentiations keep nothing in registers across the calls of a field multiplication (`fp_base`, `bn_exp`; `Bn_exp.eca`, `Fp_base.eca` adapted);
  + [Done] `fp_pm`: pseudo-Mersenne fields (R mod P < 2^32, R < 3P: 2^255-19), folding with one row of multiplications, canonical, generic in the multiplication;
  + [Done] `make exec` (fp_ctx): the field tests in the interpreter of jasminc, on any host (MULX included);
  + [Done] timings on the i7-14700K (README; `make bench` in fp_ctx, with a chained mode, `BENCH_CHAINED=1`, for the latency): `bn_mulxr` is faster than `bn_mulx` at 4 and 5 limbs; at 6 only with independent calls (5-8%), and 2-4% slower on `fpc_exp`, hence `JBN_REG_MAX = 5`. The stack saves cost 1-3% on `fpc_exp` at 4 limbs, nothing measurable from 8. `fp_pm` (2^255-19 at 4 limbs) is 16-27% faster than the Montgomery field over `bn_mulxr` on `fpc_exp` at 4-6 limbs, chained calls included, and takes half the time of `unr` from 16 limbs over `bn_mul`;
  + [Done] correctness theory of `fp_pm` (`proof/Fp_pm.eca`, no admits): `_redPM_` returns `a mod p` for any `a` of 2n words, `_ctx_init_` builds the context of any odd p with R mod p < 2^32 and R < 3P, and the field operations are those of `Fp_base` with the reduction modulo p;
  - time the multiplications alone (`make bench` in mults, variant `mulxr`): not run;
  - the fused field multiplication (multiplication and Montgomery rows interleaved, CIOS, `nlimbs + 9` registers: up to 6 limbs; for `fp_pm`, the rows and the fold in one routine): needs `fp_base` to take `fun_mulm`/`fun_sqrm` (field products) instead of `fun_muln`/`fun_sqrn`/`fun_red`. Expected gain mostly in throughput, little in latency (it keeps the dependency between the rows of the Montgomery reduction; README);
  - `fp_pm` over `bn_mulx` (unrolled), from 7 limbs: not in the bench (only `pm_unr` there);
  - the lazy representation of curve25519 (values below 2^256, freeze on output) does not fit `fp_base`'s invariant;
  - secp256k1 (c = 2^32+977: a two-word second fold).
+ [Done] conditional operations of `bn_base` with fewer passes: the ladder `_expm` swaps once per bit (by the xor of the bit with the previous one) instead of twice; `_cminusP_` (the end of every reduction but that of `bn_mulxr`) and `_caddU_` (modular subtraction) take two passes over the array instead of three (`_add_` into a temporary, then `_cmov_`). Proofs adapted (`Bn_base.eca`, `Bn_exp.eca` and their safety proofs). Still to do:
  - time it on x86 (`make bench` in `fp_ctx`, before and after): in the tables of the README the part of a ladder step that is not a multiplication is 1% to 3% of `fpc_exp`, which bounds the gain from 8 limbs on;
  - a fixed-window exponentiation with a constant-time table lookup in the place of the ladder (about 1.25 multiplications per bit instead of 2): most of the gap to `mpz_powm_sec` in `bench/results-canon.md`;
- `_ctx_init_` (128*nlimbs modular doublings) is slow: computing the contexts took 91% of RSAVP1 in the RSA example (7% of RSASP1), now [Done] kept in expanded keys (`rsa_init`, 260 us under Rosetta against 18 us for `rsa_enc`); R^2 mod P could come from 2R mod P by log2(64*nlimbs) Montgomery squarings (and R mod P = R - P when P has its top bit set);
- `_ctx_init_` inlined on a part of a reg ptr argument at a non-zero offset is refused by the stack allocation of jasminc 2026.09.0 ("the region associated to variable ... is partial"; `_mov_` there, or `_ctx_init_` on a stack array, is accepted): the RSA example wraps it in local functions (`_ctx_init_N`, `_ctx_init_P`). Find which statement causes it; report it if it is a bug;
- [In progress] karatsuba
+ [Done] rsample masks each sample to the bit length of bnd (a bound shorter than the array is met with probability > 1/2); its theory `Bn_rnd.eca` is [Done]: its module is generated from the extraction, and `_rsample__eq` (a uniform sample below the bound) proved, mask included


