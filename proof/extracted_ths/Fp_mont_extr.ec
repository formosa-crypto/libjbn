require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require export MLeakage.


(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
type bignum = W64.t Ap1.t.
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.
type bignum2 = W64.t Ap2.t.


op glob_P: bignum.
op glob_mP: bignum.
op glob_exp0: bignum.
op glob_Pm2: bignum.
op glob_P0i: W64.t.
op glob_rMP: bignum.

from JPExtract require Bn_util_extr.
clone Bn_util_extr as BNutil_extr.
module BNUTIL_M = BNutil_extr.M. 
module BNUTIL_MLeak = BNutil_extr.MLeak.

from JPExtract require Bn_base_extr.
clone Bn_base_extr as BNbase_extr
 with op nlimbs <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2,
      theory BNutil_extr <- BNutil_extr.
module BN_M = BNbase_extr.M. 
module BN_MLeak = BNbase_extr.MLeak. 

from JPExtract require Fp_base_extr.
clone Fp_base_extr as FPbase_extr
 with op nlimbs <- nlimbs,
      op glob_P <- glob_P,
      op glob_mP <- glob_mP,
      op glob_Pm2 <- glob_Pm2,
      op glob_exp0 <- glob_exp0,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2,
      theory BNutil_extr <- BNutil_extr,
      theory BNbase_extr <- BNbase_extr.
module FP_M = FPbase_extr.M.
module FP_MLeak = FPbase_extr.MLeak.



module M = {

  proc _redM (r:W64.t Ap1.t, a:W64.t Ap2.t) : W64.t Ap1.t = {
    
    var _P0i:W64.t;
    
    _P0i <- glob_P0i;
    r <@ BN_M.__mont_redM (r, a, glob_P, glob_mP, _P0i);
    return (r);
  }
  
  proc _redM_ (r:W64.t Ap1.t, a:W64.t Ap2.t) : W64.t Ap1.t = {
    
    
    
    r <- r;
    a <- a;
    r <@ _redM (r, a);
    r <- r;
    return (r);
  }
  
  proc _fromM_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp2:W64.t Ap1.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp2 <- witness;
    tmp2 <- (Ap1.init (fun i => _tmp.[0 + i]));
    tmp2 <@ BN_M._mov_ (tmp2, a);
    _tmp <- Ap2.init
            (fun i => if 0 <= i < 0 + nlimbs then tmp2.[i-0] else _tmp.[i]);
    tmp2 <- (Ap1.init (fun i => _tmp.[nlimbs + i]));
    tmp2 <@ BN_M._set0_ (tmp2);
    _tmp <- Ap2.init
            (fun i => if nlimbs <= i < nlimbs + nlimbs then tmp2.[i-nlimbs] else _tmp.[i]);
    tmp <- _tmp;
    a <@ _redM_ (a, tmp);
    return (a);
  }

  module P_FP = { proc fun_red = _redM_ }
  
  proc _toM_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var rMP:W64.t Ap1.t;
    rMP <- witness;
    rMP <- glob_rMP;
    a <@ FP_M(P_FP)._mulmU_ (a, rMP);
    a <- a;
    return (a);
  }
}.


module MLeak = {
  
  proc _redM (r:W64.t Ap1.t, a:W64.t Ap2.t) : W64.t Ap1.t = {
    var aux: W64.t;
    var aux_0: W64.t Ap1.t;
    
    var _P0i:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- glob_P0i;
    _P0i <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_M.__mont_redM (r, a, glob_P, glob_mP, _P0i);
    r <- aux_0;
    return (r);
  }
  
  proc _redM_ (r:W64.t Ap1.t, a:W64.t Ap2.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    var aux_0: W64.t Ap2.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- a;
    a <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _redM (r, a);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc _fromM_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    var aux_0: W64.t Ap2.t;
    
    var _tmp:W64.t Ap2.t;
    var tmp2:W64.t Ap1.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp2 <- witness;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- (Ap1.init (fun i => _tmp.[0 + i]));
    tmp2 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_MLeak._mov_ (tmp2, a);
    tmp2 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- tmp2;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    _tmp <- Ap2.init
            (fun i => if 0 <= i < 0 + nlimbs then aux.[i-0] else _tmp.[i]);
    LEAK.leakages <- LeakAddr([nlimbs]) :: LEAK.leakages;
    aux <- (Ap1.init (fun i => _tmp.[nlimbs + i]));
    tmp2 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_MLeak._set0_ (tmp2);
    tmp2 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- tmp2;
    LEAK.leakages <- LeakAddr([nlimbs]) :: LEAK.leakages;
    _tmp <- Ap2.init
            (fun i => if nlimbs <= i < nlimbs + nlimbs then aux.[i-nlimbs] else _tmp.[i]);
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- _tmp;
    tmp <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _redM_ (a, tmp);
    a <- aux;
    return (a);
  }
  
  module P_FP = { proc fun_red = _redM_ }
  
  proc _toM_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    var rMP:W64.t Ap1.t;
    rMP <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- glob_rMP;
    rMP <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ FP_MLeak(P_FP)._mulmU_ (a, rMP);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
}.

