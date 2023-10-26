require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
(*type bignum = W64.t Ap1.t.*)
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.
(*type bignum2 = W64.t Ap2.t.*)


op glob_P: W64.t Ap1.t.
op glob_mP: W64.t Ap1.t.
op glob_exp0: W64.t Ap1.t.
op glob_Pm2: W64.t Ap1.t.

module type MParam = {
  proc fun_red (a:W64.t Ap2.t, r:W64.t Ap1.t) : W64.t Ap1.t
}.

from JPExtract require Bn_base_extr.
clone Bn_base_extr as BNbase_extr
 with op nlimbs <- nlimbs,
      theory Ap1 <= Ap1,
      theory Ap2 <= Ap2.
module BN = BNbase_extr.M. 

from JPExtract require Bn_exp_extr.
clone Bn_exp_extr as BNexp_extr
 with op nlimbs <- nlimbs,
      op nlimbsexp <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2,
      theory Apexp <- Ap1,
      theory BNbase_extr <- BNbase_extr.
module BNE = BNexp_extr.M. 




module M(P: MParam) = {
  proc __chk_bnds (a:W64.t Ap1.t, err:W64.t) : W64.t = {
    
    var p:W64.t Ap1.t;
    var cf:bool;
    var t:W64.t;
    p <- witness;
    p <- glob_P;
    cf <@ BN.__lt_cf (a, p);
    t <@ BN.bNUTIL__cf_mask (cf);
    t <- NOT_64 t;
    err <- (err `|` t);
    return (err);
  }
  
  proc __addmU (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    tmp <- witness;
    (cf, a) <@ BN.__addU (a, b);
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    tmp <- glob_mP;
    a <@ BN.__cminusP (lastbit, a, tmp);
    return (a);
  }
  
  proc _addmU (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    
    
    a <@ __addmU (a, b);
    return (a);
  }
  
  proc __submU (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var cf:bool;
    var tmp:W64.t Ap1.t;
    tmp <- witness;
    (cf, a) <@ BN.__subU (a, b);
    tmp <- glob_P;
    a <@ BN.__caddU (cf, a, tmp);
    return (a);
  }
  
  proc _submU (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    
    
    a <@ __submU (a, b);
    return (a);
  }
  
  proc _mulm (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN.__muln (a, b, tmp);
    r <@ P.fun_red (tmp, r);
    return (r);
  }
  
  proc _mulmU (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN.__muln (a, b, tmp);
    tmp <- tmp;
    a <- a;
    a <@ P.fun_red (tmp, a);
    a <- a;
    return (a);
  }
  
  proc _sqrm (a:W64.t Ap1.t, r:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN.__sqrn (a, tmp);
    tmp <- tmp;
    a <- a;
    r <@ P.fun_red (tmp, r);
    a <- a;
    return (r);
  }
  
  proc _sqrmU (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN.__sqrn (a, tmp);
    a <@ P.fun_red (tmp, a);
    return (a);
  }

  module Pexp = {
   proc fun_mulU = _mulmU
   proc fun_sqrU = _sqrmU
  }

  proc __invm (a:W64.t Ap1.t, r:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var pm2:W64.t Ap1.t;
    pm2 <- witness;
    pm2 <- glob_Pm2;
    r <@ BNE(Pexp)._expm_noct (a, pm2, r);
    return (r);
  }
}.

