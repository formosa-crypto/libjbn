require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


(* Theory Parameters *)
op nlimbs: int.
op nlimbsexp: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.
clone export PolyArray as Apexp
 with op size <- nlimbsexp.


op glob_exp0 : W64.t Ap1.t.

module type MParam = {
  proc fun_mulU (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t
  proc fun_sqrU (r:W64.t Ap1.t) : W64.t Ap1.t
}.


from JPExtract require Bn_util_extr Bn_base_extr.

clone Bn_util_extr as BNutil_extr.

module BNUTIL_M = BNutil_extr.M. 
module BNUTIL_MLeak = BNutil_extr.MLeak.

clone Bn_base_extr as BNbase_extr
 with op nlimbs <- nlimbs,
      theory Ap1 <- Ap1,
      theory Ap2 <- Ap2,
      theory BNutil_extr <- BNutil_extr.

module BN_M = BNbase_extr.M. 
module BN_MLeak = BNbase_extr.MLeak.


from JExtract require export MLeakage.
 


module M(P: MParam) = {
  proc _expm_noct (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Apexp.t) : 
  W64.t Ap1.t = {
    var aux: int;
    
    var _b:W64.t Apexp.t;
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
    x <- witness;
    _b <- b;
    x <- _x;
    x <@ BN_M._mov_ (x, a);
    _x <- x;
    j <- 0;
    while (j < nlimbsexp) {
      b <- _b;
      t <- b.[j];
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- SHR_64 t (W8.of_int 1);
      x <- _x;
      if (cf) {
        r <@ P.fun_mulU (r, x);
      } else {
        
      }
      x <@ P.fun_sqrU (x);
      _x <- x;
      ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- SHR_64 t (W8.of_int 1);
        x <- _x;
        if (cf) {
          r <@ P.fun_mulU (r, x);
        } else {
          
        }
        x <@ P.fun_sqrU (x);
        _x <- x;
        ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      }
      j <- j + 1;
    }
    return (r);
  }
  
  proc _expm_noct_ (r:W64.t Ap1.t, a:W64.t Ap1.t,
                       b:W64.t Apexp.t) : W64.t Ap1.t = {
    
    
    
    r <@ BN_M._mov_ (r, glob_exp0);
    a <- a;
    b <- b;
    r <@ _expm_noct (r, a, b);
    r <- r;
    return (r);
  }
  
  proc _expmU_noct_ (a:W64.t Ap1.t, b:W64.t Apexp.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap1.t;
    var tmp:W64.t Ap1.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ BN_M._mov_ (tmp, a);
    a <@ BN_M._mov_ (a, glob_exp0);
    a <@ _expm_noct_ (a, tmp, b);
    return (a);
  }
  
  proc _expm (x0:W64.t Ap1.t, x1:W64.t Ap1.t, b:W64.t Apexp.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux: int;
    
    var _b:W64.t Apexp.t;
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
    _b <- b;
    aux <- (- 1);
    j <- (nlimbsexp - 1);
    while (aux < j) {
      b <- _b;
      t <- b.[j];
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- SHL_64 t (W8.of_int 1);
      _t <- t;
      mask <@ BNUTIL_M.__cf_mask (cf);
      (x0, x1) <@ BN_M._cswap_mask_ (x0, x1, mask);
      _mask <- mask;
      x1 <@ P.fun_mulU (x1, x0);
      x0 <@ P.fun_sqrU (x0);
      mask <- _mask;
      (x0, x1) <@ BN_M._cswap_mask_ (x0, x1, mask);
      t <- _t;
      ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- SHL_64 t (W8.of_int 1);
        _t <- t;
        mask <@ BNUTIL_M.__cf_mask (cf);
        (x0, x1) <@ BN_M._cswap_mask_ (x0, x1, mask);
        _mask <- mask;
        x1 <@ P.fun_mulU (x1, x0);
        x0 <@ P.fun_sqrU (x0);
        mask <- _mask;
        (x0, x1) <@ BN_M._cswap_mask_ (x0, x1, mask);
        t <- _t;
        ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      }
      j <- j - 1;
    }
    return (x0, x1);
  }
  
  proc _expm_ (x0:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Apexp.t) : 
  W64.t Ap1.t = {
    
    var _x1:W64.t Ap1.t;
    var x1:W64.t Ap1.t;
    var exp0:W64.t Ap1.t;
    var  _0:W64.t Ap1.t;
     _0 <- witness;
    _x1 <- witness;
    exp0 <- witness;
    x1 <- witness;
    x1 <- _x1;
    x1 <@ BN_M._mov_ (x1, a);
    exp0 <- glob_exp0;
    x0 <@ BN_M._mov_ (x0, exp0);
    b <- b;
    (x0,  _0) <@ _expm (x0, x1, b);
    x0 <- x0;
    return (x0);
  }
  
  proc _expmU_ (a:W64.t Ap1.t, b:W64.t Apexp.t) : W64.t Ap1.t = {
    
    var x1:W64.t Ap1.t;
    var  _0:W64.t Ap1.t;
     _0 <- witness;
    x1 <- witness;
    x1 <@ BN_M._mov_ (x1, a);
    a <@ BN_M._mov_ (a, glob_exp0);
    b <- b;
    (a,  _0) <@ _expm (a, x1, b);
    a <- a;
    return (a);
  }
}.



module MLeak(P: MParam) = {

  proc _expm_noct (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Apexp.t) : 
  W64.t Ap1.t = {
    var aux_7: bool;
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_1: int;
    var aux_2: W64.t;
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Apexp.t;
    
    var _b:W64.t Apexp.t;
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
    x <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    _b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- _x;
    x <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BN_M._mov_ (x, a);
    x <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- x;
    _x <- aux_0;
    LEAK.leakages <- LeakFor(0,nlimbsexp) :: LeakAddr([]) :: LEAK.leakages;
    j <- 0;
    while (j < nlimbsexp) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux <- _b;
      b <- aux;
      LEAK.leakages <- LeakAddr([j]) :: LEAK.leakages;
      aux_2 <- b.[j];
      t <- aux_2;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <- (W64.of_int 64);
      _k <- aux_2;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_7, aux_6, aux_5, aux_4, aux_3, aux_2) <- SHR_64 t (W8.of_int 1);
       _0 <- aux_7;
      cf <- aux_6;
       _1 <- aux_5;
       _2 <- aux_4;
       _3 <- aux_3;
      t <- aux_2;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- _x;
      x <- aux_0;
      LEAK.leakages <- LeakCond(cf) :: LeakAddr([]) :: LEAK.leakages;
      if (cf) {
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_0 <@ P.fun_mulU (r, x);
        r <- aux_0;
      } else {
        
      }
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <@ P.fun_sqrU (x);
      x <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- x;
      _x <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_7, aux_6, aux_5, aux_4, aux_2) <- DEC_64 _k;
       _4 <- aux_7;
       _5 <- aux_6;
       _6 <- aux_5;
      zf <- aux_4;
      _k <- aux_2;
      LEAK.leakages <- LeakCond((! zf)) :: LeakAddr([]) :: LEAK.leakages;
      
      while ((! zf)) {
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_7, aux_6, aux_5, aux_4, aux_3, aux_2) <- SHR_64 t (W8.of_int 1);
         _0 <- aux_7;
        cf <- aux_6;
         _1 <- aux_5;
         _2 <- aux_4;
         _3 <- aux_3;
        t <- aux_2;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_0 <- _x;
        x <- aux_0;
        LEAK.leakages <- LeakCond(cf) :: LeakAddr([]) :: LEAK.leakages;
        if (cf) {
          LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
          aux_0 <@ P.fun_mulU (r, x);
          r <- aux_0;
        } else {
          
        }
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_0 <@ P.fun_sqrU (x);
        x <- aux_0;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_0 <- x;
        _x <- aux_0;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_7, aux_6, aux_5, aux_4, aux_2) <- DEC_64 _k;
         _4 <- aux_7;
         _5 <- aux_6;
         _6 <- aux_5;
        zf <- aux_4;
        _k <- aux_2;
      LEAK.leakages <- LeakCond((! zf)) :: LeakAddr([]) :: LEAK.leakages;
      
      }
      j <- j + 1;
    }
    return (r);
  }
  
  proc _expm_noct_ (r:W64.t Ap1.t, a:W64.t Ap1.t,
                       b:W64.t Apexp.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    var aux_0: W64.t Apexp.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_M._mov_ (r, glob_exp0);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- b;
    b <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _expm_noct (r, a, b);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc _expmU_noct_ (a:W64.t Ap1.t, b:W64.t Apexp.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    var _tmp:W64.t Ap1.t;
    var tmp:W64.t Ap1.t;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_M._mov_ (tmp, a);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BN_M._mov_ (a, glob_exp0);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _expm_noct_ (a, tmp, b);
    a <- aux;
    return (a);
  }
  
  proc _expm (x0:W64.t Ap1.t, x1:W64.t Ap1.t, b:W64.t Apexp.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_0: int;
    var aux_1: W64.t;
    var aux_8: W64.t Ap1.t;
    var aux_7: W64.t Ap1.t;
    var aux: W64.t Apexp.t;
    
    var _b:W64.t Apexp.t;
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
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    _b <- aux;
    LEAK.leakages <- LeakFor((- 1),(nlimbsexp - 1)) :: LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (nlimbsexp - 1);
    j <- (- 1);
    while (aux_0 < j) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux <- _b;
      b <- aux;
      LEAK.leakages <- LeakAddr([j]) :: LEAK.leakages;
      aux_1 <- b.[j];
      t <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- (W64.of_int 64);
      _k <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_6, aux_5, aux_4, aux_3, aux_2, aux_1) <- SHL_64 t (W8.of_int 1);
       _0 <- aux_6;
      cf <- aux_5;
       _1 <- aux_4;
       _2 <- aux_3;
       _3 <- aux_2;
      t <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- t;
      _t <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <@ BNUTIL_M.__cf_mask (cf);
      mask <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_8, aux_7) <@ BN_M._cswap_mask_ (x0, x1, mask);
      x0 <- aux_8;
      x1 <- aux_7;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- mask;
      _mask <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_8 <@ P.fun_mulU (x1, x0);
      x1 <- aux_8;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_8 <@ P.fun_sqrU (x0);
      x0 <- aux_8;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- _mask;
      mask <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_8, aux_7) <@ BN_M._cswap_mask_ (x0, x1, mask);
      x0 <- aux_8;
      x1 <- aux_7;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- _t;
      t <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_6, aux_5, aux_4, aux_3, aux_1) <- DEC_64 _k;
       _4 <- aux_6;
       _5 <- aux_5;
       _6 <- aux_4;
      zf <- aux_3;
      _k <- aux_1;
      LEAK.leakages <- LeakCond((! zf)) :: LeakAddr([]) :: LEAK.leakages;
      
      while ((! zf)) {
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_6, aux_5, aux_4, aux_3, aux_2, aux_1) <- SHL_64 t (W8.of_int 1);
         _0 <- aux_6;
        cf <- aux_5;
         _1 <- aux_4;
         _2 <- aux_3;
         _3 <- aux_2;
        t <- aux_1;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_1 <- t;
        _t <- aux_1;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_1 <@ BNUTIL_M.__cf_mask (cf);
        mask <- aux_1;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_8, aux_7) <@ BN_M._cswap_mask_ (x0, x1, mask);
        x0 <- aux_8;
        x1 <- aux_7;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_1 <- mask;
        _mask <- aux_1;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_8 <@ P.fun_mulU (x1, x0);
        x1 <- aux_8;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_8 <@ P.fun_sqrU (x0);
        x0 <- aux_8;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_1 <- _mask;
        mask <- aux_1;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_8, aux_7) <@ BN_M._cswap_mask_ (x0, x1, mask);
        x0 <- aux_8;
        x1 <- aux_7;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_1 <- _t;
        t <- aux_1;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_6, aux_5, aux_4, aux_3, aux_1) <- DEC_64 _k;
         _4 <- aux_6;
         _5 <- aux_5;
         _6 <- aux_4;
        zf <- aux_3;
        _k <- aux_1;
      LEAK.leakages <- LeakCond((! zf)) :: LeakAddr([]) :: LEAK.leakages;
      
      }
      j <- j - 1;
    }
    return (x0, x1);
  }
  
  proc _expm_ (x0:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Apexp.t) : 
  W64.t Ap1.t = {
    var aux_1: W64.t Ap1.t;
    var aux: W64.t Ap1.t;
    var aux_0: W64.t Apexp.t;
    
    var x1:W64.t Ap1.t;
    var  _0:W64.t Ap1.t;
     _0 <- witness;
    x1 <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <@ BN_M._mov_ (x1, a);
    x1 <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <@ BN_M._mov_ (x0, glob_exp0);
    x0 <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- b;
    b <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_1, aux) <@ _expm (x0, x1, b);
    x0 <- aux_1;
     _0 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- x0;
    x0 <- aux_1;
    return (x0);
  }
  
  proc _expmU_ (a:W64.t Ap1.t, b:W64.t Apexp.t) : W64.t Ap1.t = {
    var aux_1: W64.t Ap1.t;
    var aux: W64.t Ap1.t;
    var aux_0: W64.t Apexp.t;
    
    var x1:W64.t Ap1.t;
    var  _0:W64.t Ap1.t;
     _0 <- witness;
    x1 <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <@ BN_M._mov_ (x1, a);
    x1 <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <@ BN_M._mov_ (a, glob_exp0);
    a <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- b;
    b <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_1, aux) <@ _expm (a, x1, b);
    a <- aux_1;
     _0 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- a;
    a <- aux_1;
    return (a);
  }
}.

