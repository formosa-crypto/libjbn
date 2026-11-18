
We need to perform a manual transformation on the files extracted from
the libjbn modules in order to emulate the treatment prescribed in
https://github.com/jasmin-lang/jasmin/issues/519.

# Starting point

The code is extracted by `make` in `../../src/amd64/ref/extracted/`
(old array model). Every library module is instantiated once, in its
own namespace, by the harness `libjbn_abs.jazz`, following the same
layout as any libjbn program (see the top-level README): the top level
is the 2n scope, `H` is the size scope n.

- Integer parameters and globals are dummies (`preamb@n.jinc`, required
  inside `H`): `nlimbs = 11` (so `2*nlimbs` appears as `22`, or as
  `2 * 11`), `nlimbsexp = 13`, and `glob_P`, `glob_mP`, `glob_P0i`,
  `glob_Pm2`, `glob_exp0`, `glob_rMP` filled with zeros.
- Function parameters (`fun_mulU`, `fun_sqrU`, `fun_muln`, `fun_sqrn`,
  `fun_red`, `fun_kmuln`) are stubs, declared in `libjbn_abs.jazz`
  inside the namespace of the module that takes them (Jasmin does not
  allow a function to shadow one visible from an enclosing namespace).
- Sub-instances are not abstract: `fp_base` applies `bn_exp` to its own
  `_mulmU_`/`_sqrmU_` (sub-namespace `EXP`, wrappers `fun_mulU`,
  `fun_sqrU`), and `fp_mont` includes `fp_base` with `fun_red` bound to
  `_redM_`. In the theories these correspond to `clone Bn_exp as BNE`
  (in `Fp_base`) and `clone Fp_base as FPB` (in `Fp_mont`).

Upon extraction, `param int` is currently inlined in the extracted
code and global constants are EC's `abbrev`s. Notice that types might
depend on integer parameters (array sizes), leading to the inclusion
(import) of multiple instances of the `Array` and/or `WArray`
theories.

Additionally, there might be `SystemCalls` (and specifically for
random number generation), that again are instantiated for the
concrete sizes needed, that can depend on integer parameters. For now,
we choose to avoid this dependency (hence, circumventing some libjbn
functions such as `bn_rnd` -- these can be handled with a specific theory...)


# Transformation

- Parametric array instances: each array size depending on parameters
  is replaced by a new instance of the `Array` theory. Assuming the
  definitions
  ```
  op nlimbs: int.
  clone export PolyArray as Ap1
   with op size <- nlimbs.
  type bignum = W64.t Ap1.t.
  clone export PolyArray as Ap2
   with op size <- 2*nlimbs.
  type bignum2 = W64.t Ap2.t.
  ```
  One shall perform the following rewritings (`XX` is the value of
  extracted `nlimbs` -- e.g. `11`):
  ```
       W64.t ArrayXX.t  ==>  bignum
	   W64.t Array2XX.t  ==>  bignum2
	   ArrayXX  ==>  Ap1
	   Array2XX  ==>  Ap2
   ```
- [not now] ...and possibly their byte variants...
  ```
     Array8XX.t (u64[8*nlimbs]) ==> Ap3.t
     WArray8XX.t (cast) ==> Awp3
     (? remove SC module parameter ?)
  ```
- Undo the inlining of integer parameters (e.g. `nlimbs`): this is
  done by replacing the placeholder used in `preamb@n.jinc` (see
  above) by the original parameter:
  ```
	  11 (nlimbs parameter)  ==>  nlimbs
	  13 (nlimbsext parameter)  ==>  nlimbsexp
  ```
- Remove the namespace prefix. jasmin2ec writes `A::B::f` as `aA__B__f`
  (path components joined by `__`, first letter lowercased); since
  libjbn procedure names start with `_`, there are three or four
  underscores after the prefix. The prefix of each module instance
  in `libjbn_abs.jazz` (and the qualifier it replaces in the old,
  template-based extraction) is:
  ```
      uTIL__           (was bNUTIL)   bn_util
      h__BN__          (was bN)       bn_base, size nlimbs
      bN__             (was bN2)      bn_base, size 2*nlimbs
      h__RND__         (was bNRND)    bn_rnd
      h__MUL__         (was bNMUL)    bn_mul
      h__MULREG__      (was bNMULREG) bn_mulreg
      kAR__            (was bNKAR)    bn_karatsuba
      h__EXP__         (was bNE)      bn_exp (abstract fun_mulU/fun_sqrU)
      h__FP__          (was fP)       fp_base (abstract fun_red/fun_muln/fun_sqrn)
      h__FP__EXP__     (was bNE)      bn_exp applied inside fp_base
      h__FPM__         (was fPM/fP)   fp_mont, with fp_base included
      h__FPM__EXP__    (was bNE)      bn_exp applied inside fp_mont's fp_base
      h__glob_         (was glob_)    dummy globals
  ```
  The stubs keep their parameter name behind the prefix (e.g.
  `h__FP__fun_red`, `kAR__fun_kmuln`).
