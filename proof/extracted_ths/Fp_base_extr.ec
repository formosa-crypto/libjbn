require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

require import MLeakage.
 
(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.


op glob_P: W64.t Ap1.t.
op glob_mP: W64.t Ap1.t.
op glob_exp0: W64.t Ap1.t.
op glob_Pm2: W64.t Ap1.t.


module type MParam = {
  proc fun_red (r:W64.t Ap1.t, a:W64.t Ap2.t) : W64.t Ap1.t
}.


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

from JPExtract require Bn_exp_extr.
clone Bn_exp_extr as BNexp_extr
 with op nlimbs <- nlimbs,
      op nlimbsexp <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2,
      theory Apexp <- Ap1,
      theory BNutil_extr <- BNutil_extr,
      theory BNbase_extr <- BNbase_extr.
module BNE_M = BNexp_extr.M. 
module BNE_MLeak = BNexp_extr.MLeak. 


module M(P: MParam) = {

  proc _chk_bnds_ (err:W64.t, a:W64.t Ap1.t) : W64.t = {
    
    var p:W64.t Ap1.t;
    var cf:bool;
    var t:W64.t;
    p <- witness;
    p <- glob_P;
    cf <@ BN_M._lt_cf_ (a, p);
    t <@ BNUTIL_M.__cf_mask (cf);
    t <- NOT_64 t;
    err <- (err `|` t);
    return (err);
  }
  
  proc _addm_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    tmp <- witness;
    (cf, r) <@ BN_M._add_ (r, a, b);
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    tmp <- glob_mP;
    r <@ BN_M._cminusP_ (r, tmp, lastbit);
    return (r);
  }
  
  proc _addmU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    tmp <- witness;
    (cf, a) <@ BN_M._addU_ (a, b);
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    tmp <- glob_mP;
    a <@ BN_M._cminusP_ (a, tmp, lastbit);
    return (a);
  }
  
  proc _subm_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    
    var cf:bool;
    var tmp:W64.t Ap1.t;
    tmp <- witness;
    (cf, r) <@ BN_M._sub_ (r, a, b);
    tmp <- glob_P;
    r <@ BN_M._caddU_ (r, cf, tmp);
    return (r);
  }
  
  proc _submU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var cf:bool;
    var tmp:W64.t Ap1.t;
    tmp <- witness;
    (cf, a) <@ BN_M._subU_ (a, b);
    tmp <- glob_P;
    a <@ BN_M._caddU_ (a, cf, tmp);
    return (a);
  }
  
  proc _mulm_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN_M._muln_ (tmp, a, b);
    r <@ P.fun_red (r, tmp);
    return (r);
  }
  
  proc _mulmU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN_M._muln_ (tmp, a, b);
    a <@ P.fun_red (a, tmp);
    return (a);
  }
  
  proc _sqrm_ (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN_M._sqrn_ (tmp, a);
    r <@ P.fun_red (r, tmp);
    return (r);
  }
  
  proc _sqrmU_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN_M._sqrn_ (tmp, a);
    a <@ P.fun_red (a, tmp);
    return (a);
  }
  
  module P_BNEXP = { proc fun_mulU = _mulmU_ 
                     proc fun_sqrU = _sqrmU_ }
  
  proc _invmU_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var pm2:W64.t Ap1.t;
    pm2 <- witness;
    pm2 <- glob_Pm2;
    a <@ BNE_M(P_BNEXP)._expmU_noct_ (a, pm2);
    return (a);
  }
}.





module MLeak(P: MParam) = {
  proc _chk_bnds_ (err:W64.t, a:W64.t Ap1.t) : W64.t = {
    var aux_0: bool;
    var aux_1: W64.t;
    var aux: W64.t Ap1.t;
    
    var p:W64.t Ap1.t;
    var cf:bool;
    var t:W64.t;
    p <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- glob_P;
    p <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_MLeak._lt_cf_ (a, p);
    cf <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <@ BNUTIL_MLeak.__cf_mask (cf);
    t <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- NOT_64 t;
    t <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- (err `|` t);
    err <- aux_1;
    return (err);
  }
  
  proc _addm_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    var aux: bool;
    var aux_1: W64.t;
    var aux_0: W64.t Ap1.t;
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ BN_MLeak._add_ (r, a, b);
    cf <- aux;
    r <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- (W64.of_int 0);
    lastbit <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_1) <- adc_64 lastbit (W64.of_int 0) cf;
     _0 <- aux;
    lastbit <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- glob_mP;
    tmp <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_MLeak._cminusP_ (r, tmp, lastbit);
    r <- aux_0;
    return (r);
  }
  
  proc _addmU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: bool;
    var aux_1: W64.t;
    var aux_0: W64.t Ap1.t;
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ BN_MLeak._addU_ (a, b);
    cf <- aux;
    a <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- (W64.of_int 0);
    lastbit <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_1) <- adc_64 lastbit (W64.of_int 0) cf;
     _0 <- aux;
    lastbit <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- glob_mP;
    tmp <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_MLeak._cminusP_ (a, tmp, lastbit);
    a <- aux_0;
    return (a);
  }
  
  proc _subm_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    var cf:bool;
    var tmp:W64.t Ap1.t;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ BN_MLeak._sub_ (r, a, b);
    cf <- aux;
    r <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- glob_P;
    tmp <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_MLeak._caddU_ (r, cf, tmp);
    r <- aux_0;
    return (r);
  }
  
  proc _submU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    var cf:bool;
    var tmp:W64.t Ap1.t;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ BN_MLeak._subU_ (a, b);
    cf <- aux;
    a <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- glob_P;
    tmp <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_MLeak._caddU_ (a, cf, tmp);
    a <- aux_0;
    return (a);
  }
  
  proc _mulm_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_MLeak._muln_ (tmp, a, b);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ P.fun_red (r, tmp);
    r <- aux_0;
    return (r);
  }
  
  proc _mulmU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_MLeak._muln_ (tmp, a, b);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ P.fun_red (a, tmp);
    a <- aux_0;
    return (a);
  }
  
  proc _sqrm_ (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_MLeak._sqrn_ (tmp, a);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ P.fun_red (r, tmp);
    r <- aux_0;
    return (r);
  }
  
  proc _sqrmU_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    var _tmp:W64.t Ap2.t;
    var tmp:W64.t Ap2.t;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_MLeak._sqrn_ (tmp, a);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ P.fun_red (a, tmp);
    a <- aux_0;
    return (a);
  }
  
  module P_BNEXP = { proc fun_mulU = _mulmU_
                     proc fun_sqrU = _sqrmU_ }

  proc _invmU_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap1.t;
    
    var pm2:W64.t Ap1.t;
    pm2 <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- glob_Pm2;
    pm2 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BNE_MLeak(P_BNEXP)._expmU_noct_ (a, pm2);
    a <- aux_0;
    return (a);
  }
}.

