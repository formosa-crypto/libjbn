
We need to perform a manual transformation on the file extracyed from
the original `*.mjazz` files in order to emulate the treatment
prescribed in https://github.com/jasmin-lang/jasmin/issues/519.

# Starting point

The code was extracted into
`../../src/amd64/red/mjazz_extracted/`, with parameters replaced
by dummy definitions (file `preamb.jinc`):

```
param int nlimbs = 11;
param int nlimbsexp = 13;

u64[nlimbs] glob_P = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
u64[nlimbs] glob_mP = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
u64 glob_P0i = 0;
u64[nlimbsexp] glob_Pm2 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
u64[nlimbs] glob_exp0 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
u64[nlimbs] glob_rMP = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

fn fun_mulU( reg mut ptr u64[nlimbs] r, reg const ptr u64[nlimbs] a) -> reg ptr u64[nlimbs] { return r; }
fn fun_sqrU( reg mut ptr u64[nlimbs] r) -> reg ptr u64[nlimbs] { return r; }
fn fun_red( reg const ptr u64[2*nlimbs] a, reg mut ptr u64[nlimbs] r) -> reg ptr u64[nlimbs] { return r; }
```

Upon extraction, `param int` is currently inlined in the extracted
code and global constants are EC's `abbrev`s. Notice that types might
depend on integer parameters (array sizes), leading to the inclusion
(import) of multiple instances of the `Array` and/or `WArray`
theories.

Additionally, there might be `SystemCalls` (and specifically for
random number generation), that again are instantiated for the
concrete sizes needed that can depend on integer parameters. For now,
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
  done by replacing the placeholder used in `preamb.jinc` (shown
  above) by the original parameter:
  ```
	  11 (nlimbs parameter)  ==>  nlimbs
	  13 (nlimbsext parameter)  ==>  nlimbsexp
  ```
- Remove the qualifier prefix (e.g. `BN`, `BNE`, `FP`, `FPM`)
  ```
	  bN  ==>  
	  fP  ==>  
	  ...
  ```
