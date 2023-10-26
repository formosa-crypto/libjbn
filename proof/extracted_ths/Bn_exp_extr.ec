require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


(* Theory Parameters *)
op nlimbs: int.
op nlimbsexp: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
(*type bignum = W64.t Ap1.t.*)
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.
clone export PolyArray as Apexp
 with op size <- nlimbsexp.
(*type bignumexp = W64.t Apexp.t.*)


op glob_exp0 : W64.t Ap1.t.

module type MParam = {
  proc fun_mulU (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t
  proc fun_sqrU (r:W64.t Ap1.t) : W64.t Ap1.t
}.


from JPExtract require Bn_base_extr.

clone Bn_base_extr as BNbase_extr
 with op nlimbs <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2.

module BN = BNbase_extr.M. 

module M(P: MParam) = {
  proc _expm_noct (a:W64.t Ap1.t, b:W64.t Apexp.t, r:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    var aux: int;
    
    var _b:W64.t Apexp.t;
    var exp0:W64.t Ap1.t;
    var _x:W64.t Ap1.t;
    var x:W64.t Ap1.t;
    var j:int;
    var t:W64.t;
    var _k:W64.t;
    var zf:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    _b <- witness;
    _x <- witness;
    exp0 <- witness;
    x <- witness;
    _b <- b;
    exp0 <- glob_exp0;
    r <@ BN.__copy2 (exp0, r);
    x <- _x;
    x <@ BN.__copy2 (a, x);
    _x <- x;
    j <- 0;
    while (j < nlimbsexp) {
      b <- _b;
      t <- b.[j];
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- SHR_64 t (W8.of_int 1);
      x <- _x;
      if (cf) {
        r <- r;
        x <- x;
        r <@ P.fun_mulU (r, x);
      } else {
        
      }
      x <- x;
      x <@ P.fun_sqrU (x);
      _x <- x;
      ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- SHR_64 t (W8.of_int 1);
        x <- _x;
        if (cf) {
          r <- r;
          x <- x;
          r <@ P.fun_mulU (r, x);
        } else {
          
        }
        x <- x;
        x <@ P.fun_sqrU (x);
        _x <- x;
        ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      }
      j <- j + 1;
    }
    return (r);
  }
  
  proc _expm (a:W64.t Ap1.t, b:W64.t Apexp.t, x0:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    var aux: int;
    
    var _b:W64.t Apexp.t;
    var exp0:W64.t Ap1.t;
    var _x1:W64.t Ap1.t;
    var x1:W64.t Ap1.t;
    var j:int;
    var t:W64.t;
    var _k:W64.t;
    var zf:bool;
    var cf:bool;
    var _t:W64.t;
    var mask:W64.t;
    var _mask:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    _b <- witness;
    _x1 <- witness;
    exp0 <- witness;
    x1 <- witness;
    _b <- b;
    exp0 <- glob_exp0;
    x0 <@ BN.__copy2 (exp0, x0);
    x1 <- _x1;
    x1 <@ BN.__copy2 (a, x1);
    aux <- (- 1);
    j <- (nlimbsexp - 1);
    while (aux < j) {
      b <- _b;
      t <- b.[j];
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- SHL_64 t (W8.of_int 1);
      _t <- t;
      mask <@ BN.bNUTIL__cf_mask (cf);
      (x0, x1) <@ BN.__cswap_mask (mask, x0, x1);
      _mask <- mask;
      x0 <- x0;
      x1 <- x1;
      x1 <@ P.fun_mulU (x1, x0);
      x0 <- x0;
      x0 <@ P.fun_sqrU (x0);
      mask <- _mask;
      (x0, x1) <@ BN.__cswap_mask (mask, x0, x1);
      t <- _t;
      ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- SHL_64 t (W8.of_int 1);
        _t <- t;
        mask <@ BN.bNUTIL__cf_mask (cf);
        (x0, x1) <@ BN.__cswap_mask (mask, x0, x1);
        _mask <- mask;
        x0 <- x0;
        x1 <- x1;
        x1 <@ P.fun_mulU (x1, x0);
        x0 <- x0;
        x0 <@ P.fun_sqrU (x0);
        mask <- _mask;
        (x0, x1) <@ BN.__cswap_mask (mask, x0, x1);
        t <- _t;
        ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      }
      j <- j - 1;
    }
    return (x0);
  }
}.

