require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

require import MLeakage.
from JExtract require export Array3.

(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.


(** REMOVED...
require import Array3 Array11 Array13 Array22 Array88.
require import WArray24 WArray88 WArray104 WArray176.

abbrev glob_rMP = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].

abbrev glob_exp0 = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].

abbrev glob_Pm2 = Array13.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0].

abbrev glob_P0i = W64.of_int 0.

abbrev glob_mP = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].

abbrev glob_P = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].
*)


(************************************************************

 Rewritings:

  "W64.t Array11.t" -> "W64.t Ap1.t"
  "Array11" -> "Ap1"
  "W64.t Array22.t" -> "W64.t Ap2.t"
  "Array22" -> "Ap2"
  "11" -> "nlimbs"
  [remove procedurs from BNUTIL]
  "bNUTIL" -> "BNUTIL_M."
  "" -> "" (remove qualifier)

*************************************************************)

from JPExtract require Bn_util_extr.

clone Bn_util_extr as BNutil_extr.

module BNUTIL_M = BNutil_extr.M. 
module BNUTIL_MLeak = BNutil_extr.MLeak. 

module M = {
  proc __load (a:W64.t Ap1.t, ap:W64.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _load (a:W64.t Ap1.t, ap:W64.t) : W64.t Ap1.t = {
    
    
    
    a <@ __load (a, ap);
    return (a);
  }
  
  proc _load_ (a:W64.t Ap1.t, ap:W64.t) : W64.t Ap1.t = {
    
    
    
    a <- a;
    ap <- ap;
    a <@ _load (a, ap);
    a <- a;
    return (a);
  }
  
  proc __store (ap:W64.t, a:W64.t Ap1.t) : unit = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))) (t);
      i <- i + 1;
    }
    return ();
  }
  
  proc _store_ (ap:W64.t, a:W64.t Ap1.t) : unit = {
    
    
    
    ap <- ap;
    a <- a;
    __store (ap, a);
    return ();
  }
  
  proc __eq_zf (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    var aux: int;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    acc <- (W64.of_int 0);
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      t <- (t `^` b.[i]);
      acc <- (acc `|` t);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    return (zf);
  }
  
  proc _eq_zf (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    
    var zf:bool;
    
    zf <@ __eq_zf (a, b);
    return (zf);
  }
  
  proc _eq_zf_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    
    var zf:bool;
    
    a <- a;
    b <- b;
    zf <@ _eq_zf (a, b);
    return (zf);
  }
  
  proc _eq_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t = {
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    zf <@ _eq_zf_ (a, b);
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc __test0_zf (a:W64.t Ap1.t) : bool = {
    var aux: int;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    acc <- a.[0];
    i <- 1;
    while (i < nlimbs) {
      acc <- (acc `|` a.[i]);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    return (zf);
  }
  
  proc _test0_zf_ (a:W64.t Ap1.t) : bool = {
    
    var zf:bool;
    
    a <- a;
    zf <@ __test0_zf (a);
    return (zf);
  }
  
  proc _test0_ (a:W64.t Ap1.t) : W64.t = {
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var zf:bool;
    
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    zf <@ _test0_zf_ (a);
    res_0 <- (zf ? is_zero : res_0);
    return (res_0);
  }
  
  proc __copy (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var r:W64.t Ap1.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc __mov (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc _mov (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    
    
    r <@ __mov (r, a);
    return (r);
  }
  
  proc _mov_ (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    
    
    r <- r;
    a <- a;
    r <@ _mov (r, a);
    r <- r;
    return (r);
  }
  
  proc __cmov (a:W64.t Ap1.t, cond:bool, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      t <- (cond ? b.[i] : t);
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _cmov (a:W64.t Ap1.t, cond:bool, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    
    
    a <@ __cmov (a, cond, b);
    return (a);
  }
  
  proc _cmov_ (a:W64.t Ap1.t, cond:bool, b:W64.t Ap1.t) : W64.t Ap1.t = {
    
    
    
    a <- a;
    b <- b;
    a <@ _cmov (a, cond, b);
    a <- a;
    return (a);
  }
  
  proc __cswap_mask (x:W64.t Ap1.t, y:W64.t Ap1.t, mask:W64.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var tmp1:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      tmp1 <- x.[i];
      tmp1 <- (tmp1 `^` y.[i]);
      tmp1 <- (tmp1 `&` mask);
      x.[i] <- (x.[i] `^` tmp1);
      y.[i] <- (y.[i] `^` tmp1);
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc _cswap_mask (x:W64.t Ap1.t, y:W64.t Ap1.t, mask:W64.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    
    
    
    (x, y) <@ __cswap_mask (x, y, mask);
    return (x, y);
  }
  
  proc _cswap_mask_ (x:W64.t Ap1.t, y:W64.t Ap1.t, mask:W64.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    
    
    
    x <- x;
    y <- y;
    (x, y) <@ _cswap_mask (x, y, mask);
    x <- x;
    y <- y;
    return (x, y);
  }
  
  proc _cswap_cf_ (x:W64.t Ap1.t, y:W64.t Ap1.t, cf:bool) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    
    var mask:W64.t;
    
    mask <@ BNUTIL_M.__cf_mask (cf);
    (x, y) <@ _cswap_mask_ (x, y, mask);
    return (x, y);
  }
  
  proc __fill (a:W64.t Ap1.t, x:W64.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- x;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _fill_ (a:W64.t Ap1.t, x:W64.t) : W64.t Ap1.t = {
    
    
    
    a <- a;
    x <- x;
    a <@ __fill (a, x);
    a <- a;
    return (a);
  }
  
  proc _set0_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int 0);
    a <@ _fill_ (a, t);
    return (a);
  }
  
  proc __cfill (a:W64.t Ap1.t, b:bool, x:W64.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- a.[i];
      t <- (b ? x : t);
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __or_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- (a.[i] `|` mask);
      i <- i + 1;
    }
    return (a);
  }
  
  proc _or_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    
    
    
    a <@ __or_mask (a, mask);
    return (a);
  }
  
  proc _or_mask_ (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    
    
    
    a <- a;
    mask <- mask;
    a <@ _or_mask (a, mask);
    a <- a;
    return (a);
  }
  
  proc _set_err_ (a:W64.t Ap1.t, _err:W64.t) : W64.t Ap1.t = {
    
    var err:W64.t;
    
    err <- _err;
    a <@ _or_mask_ (a, err);
    return (a);
  }
  
  proc __and_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- (a.[i] `&` mask);
      i <- i + 1;
    }
    return (a);
  }
  
  proc _and_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    
    
    
    a <@ __and_mask (a, mask);
    return (a);
  }
  
  proc _and_mask_ (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    
    
    
    a <- a;
    mask <- mask;
    a <@ _and_mask (a, mask);
    a <- a;
    return (a);
  }
  
  proc __carrypropU (a:W64.t Ap1.t, cf:bool, k:int) : bool *
                                                            W64.t Ap1.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var i:int;
    
    i <- k;
    while (i < nlimbs) {
      (aux_0, aux_1) <- adc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux_0;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __addc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < nlimbs) {
      t <- b.[i];
      (aux_0, aux_1) <- adc_64 a.[i] t cf;
      cf <- aux_0;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _addc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    
    
    
    (cf, a) <@ __addc1U (a, b, cf);
    return (cf, a);
  }
  
  proc _addc1U_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    
    
    
    a <- a;
    b <- b;
    (cf, a) <@ _addc1U (a, b, cf);
    a <- a;
    return (cf, a);
  }
  
  proc _addcU_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var t:W64.t;
    
    t <- b.[0];
    (aux, aux_0) <- adc_64 a.[0] t cf;
    cf <- aux;
    a.[0] <- aux_0;
    (cf, a) <@ _addc1U_ (a, b, cf);
    return (cf, a);
  }
  
  proc _addU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                         W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    t <- b.[0];
    (aux, aux_0) <- adc_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    (cf, a) <@ _addc1U_ (a, b, cf);
    return (cf, a);
  }
  
  proc __addc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- adc_64 t b.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _addc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    
    
    
    (cf, r) <@ __addc1 (r, a, b, cf);
    return (cf, r);
  }
  
  proc _addc1_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    
    
    
    r <- r;
    a <- a;
    b <- b;
    (cf, r) <@ _addc1 (r, a, b, cf);
    r <- r;
    return (cf, r);
  }
  
  proc _add_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- adc_64 t b.[0] false;
    r.[0] <- t;
    (cf, r) <@ _addc1_ (r, a, b, cf);
    return (cf, a);
  }
  
  proc _addc_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- adc_64 t b.[0] cf;
    r.[0] <- t;
    (cf, r) <@ _addc1_ (r, a, b, cf);
    return (cf, a);
  }
  
  proc __subc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < nlimbs) {
      t <- b.[i];
      (aux_0, aux_1) <- sbb_64 a.[i] t cf;
      cf <- aux_0;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _subc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    
    
    
    (cf, a) <@ __subc1U (a, b, cf);
    return (cf, a);
  }
  
  proc _subc1U_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    
    
    
    a <- a;
    b <- b;
    (cf, a) <@ _subc1U (a, b, cf);
    a <- a;
    return (cf, a);
  }
  
  proc _subU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                         W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    t <- b.[0];
    (aux, aux_0) <- sbb_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    (cf, a) <@ _subc1U_ (a, b, cf);
    return (cf, a);
  }
  
  proc _subcU_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var t:W64.t;
    
    t <- b.[0];
    (aux, aux_0) <- sbb_64 a.[0] t cf;
    cf <- aux;
    a.[0] <- aux_0;
    (cf, a) <@ _subc1U_ (a, b, cf);
    return (cf, a);
  }
  
  proc __subc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _subc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    
    
    
    (cf, r) <@ __subc1 (r, a, b, cf);
    return (cf, r);
  }
  
  proc _subc1_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    
    
    
    r <- r;
    a <- a;
    b <- b;
    (cf, r) <@ _subc1 (r, a, b, cf);
    r <- r;
    return (cf, r);
  }
  
  proc _sub_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    r.[0] <- t;
    (cf, r) <@ _subc1_ (r, a, b, cf);
    return (cf, r);
  }
  
  proc _subc_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] cf;
    r.[0] <- t;
    (cf, r) <@ _subc1_ (r, a, b, cf);
    return (cf, r);
  }
  
  proc __ltc1_cf (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : 
  bool = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc _ltc1_cf (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool = {
    
    
    
    cf <@ __ltc1_cf (a, b, cf);
    return (cf);
  }
  
  proc _ltc1_cf_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : 
  bool = {
    
    
    
    a <- a;
    b <- b;
    cf <@ _ltc1_cf (a, b, cf);
    return (cf);
  }
  
  proc _lt_cf_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    cf <@ _ltc1_cf_ (a, b, cf);
    return (cf);
  }
  
  proc _ltc_cf_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool = {
    
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] cf;
    cf <@ _ltc1_cf_ (a, b, cf);
    return (cf);
  }
  
  proc __negc1U (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    var aux: int;
    
    var t:W64.t;
    var i:int;
    
    i <- 1;
    while (i < nlimbs) {
      t <- (W64.of_int 0);
      (cf, t) <- sbb_64 t a.[i] cf;
      a.[i] <- t;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _negc1U (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    
    
    
    (cf, a) <@ __negc1U (a, cf);
    return (cf, a);
  }
  
  proc _negc1U_ (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    
    
    
    a <- a;
    (cf, a) <@ _negc1U (a, cf);
    a <- a;
    return (cf, a);
  }
  
  proc _negU_ (a:W64.t Ap1.t) : bool * W64.t Ap1.t = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t a.[0] false;
    a.[0] <- t;
    (cf, a) <@ _negc1U_ (a, cf);
    return (cf, a);
  }
  
  proc _negcU_ (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t a.[0] cf;
    a.[0] <- t;
    (cf, a) <@ _negc1U_ (a, cf);
    return (cf, a);
  }
  
  proc __negc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux: int;
    
    var t:W64.t;
    var i:int;
    
    i <- 1;
    while (i < nlimbs) {
      t <- (W64.of_int 0);
      (cf, t) <- sbb_64 t a.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _negc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                  W64.t Ap1.t = {
    
    
    
    (cf, r) <@ __negc1 (r, a, cf);
    return (cf, r);
  }
  
  proc _negc1_ (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    
    
    
    r <- r;
    a <- a;
    (cf, r) <@ _negc1 (r, a, cf);
    r <- r;
    return (cf, r);
  }
  
  proc _neg_ (r:W64.t Ap1.t, a:W64.t Ap1.t) : bool *
                                                        W64.t Ap1.t = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t a.[0] false;
    r.[0] <- t;
    (cf, r) <@ _negc1_ (r, a, cf);
    return (cf, a);
  }
  
  proc _negc_ (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                  W64.t Ap1.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t a.[0] cf;
    r.[0] <- t;
    (cf, r) <@ _negc1_ (r, a, cf);
    return (cf, a);
  }
  
  proc _cnegU_ (a:W64.t Ap1.t, cond:W64.t) : W64.t Ap1.t = {
    
    var _x:W64.t Ap1.t;
    var x:W64.t Ap1.t;
    var cf:bool;
    var  _0:bool;
    _x <- witness;
    x <- witness;
    x <- _x;
    ( _0, x) <@ _neg_ (x, a);
    cf <@ BNUTIL_M.__mask_cf (cond);
    a <@ _cmov_ (a, cf, x);
    return (a);
  }
  
  proc _caddU_ (x:W64.t Ap1.t, cf:bool, y:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var _tmp:W64.t Ap1.t;
    var tmp:W64.t Ap1.t;
    var mask:W64.t;
    var  _0:bool;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ _mov_ (tmp, y);
    mask <@ BNUTIL_M.__cf_mask (cf);
    tmp <@ _and_mask_ (tmp, mask);
    ( _0, x) <@ _addU_ (x, tmp);
    return (x);
  }
  
  proc __muln_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Array3.t = {
    var aux: int;
    
    var i:int;
    var j:int;
    var t0:W64.t;
    var t1:W64.t;
    
    aux <- iend;
    i <- istart;
    while (i < aux) {
      j <- (k - i);
      t0 <- a.[i];
      (t1, t0) <- mulu_64 t0 b.[j];
      x <@ BNUTIL_M.__addacc3 (x, t1, t0, k);
      i <- i + 1;
    }
    return (x);
  }
  
  proc __muln (r:W64.t Ap2.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux: int;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    x <- witness;
    t0 <- a.[0];
    (t1, t0) <- mulu_64 t0 b.[0];
    r.[0] <- t0;
    x.[1] <- t1;
    x.[2] <- (W64.of_int 0);
    x.[0] <- (W64.of_int 0);
    k <- 1;
    while (k < nlimbs) {
      x <@ __muln_innerloop (x, k, 0, (k + 1), a, b);
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    aux <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux) {
      x <@ __muln_innerloop (x, k, ((k - nlimbs) + 1), nlimbs, a, b);
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    r.[((2 * nlimbs) - 1)] <- x.[(((2 * nlimbs) - 1) %% 3)];
    return (r);
  }
  
  proc _muln (r:W64.t Ap2.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    
    
    
    r <@ __muln (r, a, b);
    return (r);
  }
  
  proc _muln_ (r:W64.t Ap2.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    
    
    
    r <- r;
    a <- a;
    b <- b;
    r <@ _muln (r, a, b);
    r <- r;
    return (r);
  }
  
  proc __sqrn_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Ap1.t) : W64.t Array3.t = {
    var aux: int;
    
    var i:int;
    var j:int;
    var ti:W64.t;
    var tj:W64.t;
    
    aux <- iend;
    i <- istart;
    while (i < aux) {
      j <- (k - i);
      ti <- a.[i];
      tj <- a.[j];
      x <@ BNUTIL_M.__addacc3x2 (x, ti, tj, k);
      i <- i + 1;
    }
    return (x);
  }
  
  proc __sqrn (r:W64.t Ap2.t, a:W64.t Ap1.t) : W64.t Ap2.t = {
    var aux: int;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    x <- witness;
    t0 <- a.[0];
    (t1, t0) <- mulu_64 t0 t0;
    r.[0] <- t0;
    x.[1] <- t1;
    x.[2] <- (W64.of_int 0);
    x.[0] <- (W64.of_int 0);
    k <- 1;
    while (k < nlimbs) {
      x <@ __sqrn_innerloop (x, k, 0, ((k + 1) %/ 2), a);
      if (((k %% 2) = 0)) {
        t0 <- a.[(k %/ 2)];
        (t1, t0) <- mulu_64 t0 t0;
        x <@ BNUTIL_M.__addacc3 (x, t1, t0, k);
      } else {
        
      }
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    aux <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux) {
      x <@ __sqrn_innerloop (x, k, ((k - nlimbs) + 1), ((k + 1) %/ 2), a);
      if (((k %% 2) = 0)) {
        t0 <- a.[(k %/ 2)];
        (t1, t0) <- mulu_64 t0 t0;
        x <@ BNUTIL_M.__addacc3 (x, t1, t0, k);
      } else {
        
      }
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    r.[((2 * nlimbs) - 1)] <- x.[(((2 * nlimbs) - 1) %% 3)];
    return (r);
  }
  
  proc _sqrn (r:W64.t Ap2.t, a:W64.t Ap1.t) : W64.t Ap2.t = {
    
    
    
    r <@ __sqrn (r, a);
    return (r);
  }
  
  proc _sqrn_ (r:W64.t Ap2.t, a:W64.t Ap1.t) : W64.t Ap2.t = {
    
    
    
    r <- r;
    a <- a;
    r <@ _sqrn (r, a);
    r <- r;
    return (r);
  }
  
  proc _cminusP_ (x:W64.t Ap1.t, mP:W64.t Ap1.t, lastbit:W64.t) : 
  W64.t Ap1.t = {
    
    var _tmp:W64.t Ap1.t;
    var tmp:W64.t Ap1.t;
    var _cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:W64.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ _mov_ (tmp, x);
    (_cf, tmp) <@ _addU_ (tmp, mP);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) _cf;
    ( _1, _cf,  _2,  _3,  _4,  _5) <- NEG_64 lastbit;
    x <@ _cmov_ (x, _cf, tmp);
    return (x);
  }
  
  proc __mont_redM (r:W64.t Ap1.t, a:W64.t Ap2.t,
                      _P:W64.t Ap1.t, _mP:W64.t Ap1.t, _U0:W64.t) : 
  W64.t Ap1.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var x:W64.t Array3.t;
    var p:W64.t Ap1.t;
    var k:int;
    var zero:W64.t;
    var t0:W64.t;
    var t1:W64.t;
    var lastbit:W64.t;
    var cf:bool;
    var mP:W64.t Ap1.t;
    var  _0:W64.t;
    var  _1:bool;
    p <- witness;
    mP <- witness;
    x <- witness;
    x.[0] <- (W64.of_int 0);
    x.[1] <- (W64.of_int 0);
    x.[2] <- (W64.of_int 0);
    k <- 0;
    while (k < nlimbs) {
      p <- _P;
      x <@ __muln_innerloop (x, k, 0, k, r, p);
      zero <- (W64.of_int 0);
      t0 <- a.[k];
      x <@ BNUTIL_M.__addacc3 (x, zero, t0, k);
      t0 <- x.[(k %% 3)];
      ( _0, t0) <- mulu_64 t0 _U0;
      r.[k] <- t0;
      (t1, t0) <- mulu_64 t0 _P.[0];
      x <@ BNUTIL_M.__addacc3 (x, t1, t0, k);
      k <- k + 1;
    }
    aux <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux) {
      p <- _P;
      x <@ __muln_innerloop (x, k, ((k - nlimbs) + 1), nlimbs, r, p);
      zero <- (W64.of_int 0);
      t0 <- a.[k];
      x <@ BNUTIL_M.__addacc3 (x, zero, t0, k);
      t0 <- x.[(k %% 3)];
      r.[(k - nlimbs)] <- t0;
      x.[(k %% 3)] <- (W64.of_int 0);
      k <- k + 1;
    }
    lastbit <- (W64.of_int 0);
    (aux_0, aux_1) <- adc_64 x.[(((2 * nlimbs) - 1) %% 3)] a.[((2 * nlimbs) - 1)]
    false;
    cf <- aux_0;
    x.[(((2 * nlimbs) - 1) %% 3)] <- aux_1;
    ( _1, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    r.[(nlimbs - 1)] <- x.[(((2 * nlimbs) - 1) %% 3)];
    mP <- _mP;
    r <@ _cminusP_ (r, mP, lastbit);
    return (r);
  }
  
  proc __pack2 (r:W64.t Ap2.t, lo:W64.t Ap1.t, hi:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < nlimbs) {
      t <- lo.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    i <- 0;
    while (i < nlimbs) {
      t <- hi.[i];
      r.[(nlimbs + i)] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc _pack2_ (r:W64.t Ap2.t, lo:W64.t Ap1.t, hi:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    
    
    
    r <- r;
    lo <- lo;
    hi <- hi;
    r <@ __pack2 (r, lo, hi);
    r <- r;
    return (r);
  }
}.



module MLeak = {
  proc __load (a:W64.t Ap1.t, ap:W64.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int (8 * i))))]) :: LEAK.leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _load (a:W64.t Ap1.t, ap:W64.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __load (a, ap);
    a <- aux;
    return (a);
  }
  
  proc _load_ (a:W64.t Ap1.t, ap:W64.t) : W64.t Ap1.t = {
    var aux_0: W64.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- ap;
    ap <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _load (a, ap);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc __store (ap:W64.t, a:W64.t Ap1.t) : unit = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int (8 * i))))]) :: LEAK.leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
  
  proc _store_ (ap:W64.t, a:W64.t Ap1.t) : unit = {
    var aux: W64.t;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- ap;
    ap <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- a;
    a <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    __store (ap, a);
    return ();
  }
  
  proc __eq_zf (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    acc <- aux;
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux <- a.[i];
      t <- aux;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux <- (t `^` b.[i]);
      t <- aux;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux <- (acc `|` t);
      acc <- aux;
      i <- i + 1;
    }
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    return (zf);
  }
  
  proc _eq_zf (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    var aux: bool;
    
    var zf:bool;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __eq_zf (a, b);
    zf <- aux;
    return (zf);
  }
  
  proc _eq_zf_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    var zf:bool;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _eq_zf (a, b);
    zf <- aux_0;
    return (zf);
  }
  
  proc _eq_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _eq_zf_ (a, b);
    zf <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (W64.of_int 0);
    res_0 <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (W64.of_int 1);
    are_equal <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (zf ? are_equal : res_0);
    res_0 <- aux_0;
    return (res_0);
  }
  
  proc __test0_zf (a:W64.t Ap1.t) : bool = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: int;
    var aux: W64.t;
    
    var zf:bool;
    var acc:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    acc <- aux;
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux <- (acc `|` a.[i]);
      acc <- aux;
      i <- i + 1;
    }
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    return (zf);
  }
  
  proc _test0_zf_ (a:W64.t Ap1.t) : bool = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    var zf:bool;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ __test0_zf (a);
    zf <- aux_0;
    return (zf);
  }
  
  proc _test0_ (a:W64.t Ap1.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var zf:bool;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    res_0 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 1);
    is_zero <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _test0_zf_ (a);
    zf <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (zf ? is_zero : res_0);
    res_0 <- aux;
    return (res_0);
  }
  
  proc __copy (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Ap1.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc __mov (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc _mov (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __mov (r, a);
    r <- aux;
    return (r);
  }
  
  proc _mov_ (r:W64.t Ap1.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _mov (r, a);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc __cmov (a:W64.t Ap1.t, cond:bool, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- (cond ? b.[i] : t);
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _cmov (a:W64.t Ap1.t, cond:bool, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __cmov (a, cond, b);
    a <- aux;
    return (a);
  }
  
  proc _cmov_ (a:W64.t Ap1.t, cond:bool, b:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _cmov (a, cond, b);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc __cswap_mask (x:W64.t Ap1.t, y:W64.t Ap1.t, mask:W64.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var tmp1:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- x.[i];
      tmp1 <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- (tmp1 `^` y.[i]);
      tmp1 <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (tmp1 `&` mask);
      tmp1 <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- (x.[i] `^` tmp1);
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      x.[i] <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- (y.[i] `^` tmp1);
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      y.[i] <- aux_0;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc _cswap_mask (x:W64.t Ap1.t, y:W64.t Ap1.t, mask:W64.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ __cswap_mask (x, y, mask);
    x <- aux_0;
    y <- aux;
    return (x, y);
  }
  
  proc _cswap_mask_ (x:W64.t Ap1.t, y:W64.t Ap1.t, mask:W64.t) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- x;
    x <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- y;
    y <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _cswap_mask (x, y, mask);
    x <- aux_0;
    y <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- x;
    x <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- y;
    y <- aux_0;
    return (x, y);
  }
  
  proc _cswap_cf_ (x:W64.t Ap1.t, y:W64.t Ap1.t, cf:bool) : 
  W64.t Ap1.t * W64.t Ap1.t = {
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    var aux_0: W64.t Ap1.t;
    
    var mask:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ BNUTIL_MLeak.__cf_mask (cf);
    mask <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_1, aux_0) <@ _cswap_mask_ (x, y, mask);
    x <- aux_1;
    y <- aux_0;
    return (x, y);
  }
  
  proc __fill (a:W64.t Ap1.t, x:W64.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- x;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _fill_ (a:W64.t Ap1.t, x:W64.t) : W64.t Ap1.t = {
    var aux_0: W64.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- x;
    x <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __fill (a, x);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc _set0_ (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: W64.t;
    var aux_0: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _fill_ (a, t);
    a <- aux_0;
    return (a);
  }
  
  proc __cfill (a:W64.t Ap1.t, b:bool, x:W64.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (b ? x : t);
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __or_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- (a.[i] `|` mask);
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _or_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __or_mask (a, mask);
    a <- aux;
    return (a);
  }
  
  proc _or_mask_ (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux_0: W64.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- mask;
    mask <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _or_mask (a, mask);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc _set_err_ (a:W64.t Ap1.t, _err:W64.t) : W64.t Ap1.t = {
    var aux: W64.t;
    var aux_0: W64.t Ap1.t;
    
    var err:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _err;
    err <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _or_mask_ (a, err);
    a <- aux_0;
    return (a);
  }
  
  proc __and_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- (a.[i] `&` mask);
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc _and_mask (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __and_mask (a, mask);
    a <- aux;
    return (a);
  }
  
  proc _and_mask_ (a:W64.t Ap1.t, mask:W64.t) : W64.t Ap1.t = {
    var aux_0: W64.t;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- mask;
    mask <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _and_mask (a, mask);
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc __carrypropU (a:W64.t Ap1.t, cf:bool, k:int) : bool *
                                                            W64.t Ap1.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var i:int;
    
    LEAK.leakages <- LeakFor(k,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- k;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_0, aux_1) <- adc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __addc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- b.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- adc_64 a.[i] t cf;
      cf <- aux_1;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _addc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ __addc1U (a, b, cf);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc _addc1U_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _addc1U (a, b, cf);
    cf <- aux_0;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (cf, a);
  }
  
  proc _addcU_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- b.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- adc_64 a.[0] t cf;
    cf <- aux_0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    a.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _addc1U_ (a, b, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc _addU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                         W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- b.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- adc_64 a.[0] t false;
    cf <- aux_0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    a.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _addc1U_ (a, b, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc __addc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- adc_64 t b.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _addc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ __addc1 (r, a, b, cf);
    cf <- aux;
    r <- aux_0;
    return (cf, r);
  }
  
  proc _addc1_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _addc1 (r, a, b, cf);
    cf <- aux_0;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (cf, r);
  }
  
  proc _add_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- adc_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _addc1_ (r, a, b, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, a);
  }
  
  proc _addc_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- adc_64 t b.[0] cf;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _addc1_ (r, a, b, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, a);
  }
  
  proc __subc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var cf_0:bool;
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- b.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- sbb_64 a.[i] t cf_0;
      cf_0 <- aux_1;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf_0, a);
  }
  
  proc _subc1U (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ __subc1U (a, b, cf);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc _subc1U_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                    W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _subc1U (a, b, cf);
    cf <- aux_0;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (cf, a);
  }
  
  proc _subU_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                         W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- b.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 a.[0] t false;
    cf <- aux_0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    a.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _subc1U_ (a, b, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc _subcU_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- b.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 a.[0] t cf;
    cf <- aux_0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    a.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _subc1U_ (a, b, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc __subc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- sbb_64 t b.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _subc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ __subc1 (r, a, b, cf);
    cf <- aux;
    r <- aux_0;
    return (cf, r);
  }
  
  proc _subc1_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                  cf:bool) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _subc1 (r, a, b, cf);
    cf <- aux_0;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (cf, r);
  }
  
  proc _sub_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _subc1_ (r, a, b, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, r);
  }
  
  proc _subc_ (r:W64.t Ap1.t, a:W64.t Ap1.t, b:W64.t Ap1.t,
                 cf:bool) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t b.[0] cf;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _subc1_ (r, a, b, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, r);
  }
  
  proc __ltc1_cf (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : 
  bool = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- sbb_64 t b.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc _ltc1_cf (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool = {
    var aux: bool;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __ltc1_cf (a, b, cf);
    cf <- aux;
    return (cf);
  }
  
  proc _ltc1_cf_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : 
  bool = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- b;
    b <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _ltc1_cf (a, b, cf);
    cf <- aux_0;
    return (cf);
  }
  
  proc _lt_cf_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    var aux_0: bool;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _ltc1_cf_ (a, b, cf);
    cf <- aux_0;
    return (cf);
  }
  
  proc _ltc_cf_ (a:W64.t Ap1.t, b:W64.t Ap1.t, cf:bool) : bool = {
    var aux_0: bool;
    var aux: W64.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux <- a.[0];
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t b.[0] cf;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ _ltc1_cf_ (a, b, cf);
    cf <- aux_0;
    return (cf);
  }
  
  proc __negc1U (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var t:W64.t;
    var i:int;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (W64.of_int 0);
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- sbb_64 t a.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc _negc1U (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ __negc1U (a, cf);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc _negc1U_ (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _negc1U (a, cf);
    cf <- aux_0;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    return (cf, a);
  }
  
  proc _negU_ (a:W64.t Ap1.t) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t a.[0] false;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    a.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _negc1U_ (a, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc _negcU_ (a:W64.t Ap1.t, cf:bool) : bool * W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t a.[0] cf;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    a.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _negc1U_ (a, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc __negc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var t:W64.t;
    var i:int;
    
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 1;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (W64.of_int 0);
      t <- aux_0;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      (aux_1, aux_0) <- sbb_64 t a.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _negc1 (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                  W64.t Ap1.t = {
    var aux: bool;
    var aux_0: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux, aux_0) <@ __negc1 (r, a, cf);
    cf <- aux;
    r <- aux_0;
    return (cf, r);
  }
  
  proc _negc1_ (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                   W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- a;
    a <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _negc1 (r, a, cf);
    cf <- aux_0;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (cf, r);
  }
  
  proc _neg_ (r:W64.t Ap1.t, a:W64.t Ap1.t) : bool *
                                                        W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var cf:bool;
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t a.[0] false;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _negc1_ (r, a, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, a);
  }
  
  proc _negc_ (r:W64.t Ap1.t, a:W64.t Ap1.t, cf:bool) : bool *
                                                                  W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Ap1.t;
    
    var t:W64.t;
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- sbb_64 t a.[0] cf;
    cf <- aux_0;
    t <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- t;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux_1) <@ _negc1_ (r, a, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, a);
  }
  
  proc _cnegU_ (a:W64.t Ap1.t, cond:W64.t) : W64.t Ap1.t = {
    var aux_0: bool;
    var aux: W64.t Ap1.t;
    
    var _x:W64.t Ap1.t;
    var x:W64.t Ap1.t;
    var cf:bool;
    var  _0:bool;
    _x <- witness;
    x <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _x;
    x <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <@ _neg_ (x, a);
     _0 <- aux_0;
    x <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BNUTIL_MLeak.__mask_cf (cond);
    cf <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _cmov_ (a, cf, x);
    a <- aux;
    return (a);
  }
  
  proc _caddU_ (x:W64.t Ap1.t, cf:bool, y:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W64.t Ap1.t;
    
    var _tmp:W64.t Ap1.t;
    var tmp:W64.t Ap1.t;
    var mask:W64.t;
    var  _0:bool;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _mov_ (tmp, y);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <@ BNUTIL_MLeak.__cf_mask (cf);
    mask <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _and_mask_ (tmp, mask);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_1, aux) <@ _addU_ (x, tmp);
     _0 <- aux_1;
    x <- aux;
    return (x);
  }
  
  proc __muln_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Array3.t = {
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux_2: W64.t Array3.t;
    
    var i:int;
    var j:int;
    var t0:W64.t;
    var t1:W64.t;
    
    LEAK.leakages <- LeakFor(istart,iend) :: LeakAddr([]) :: LEAK.leakages;
    aux <- iend;
    i <- istart;
    while (i < aux) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux <- (k - i);
      j <- aux;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_1 <- a.[i];
      t0 <- aux_1;
      LEAK.leakages <- LeakAddr([j]) :: LEAK.leakages;
      (aux_1, aux_0) <- mulu_64 t0 b.[j];
      t1 <- aux_1;
      t0 <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ BNUTIL_MLeak.__addacc3 (x, t1, t0, k);
      x <- aux_2;
      i <- i + 1;
    }
    return (x);
  }
  
  proc __muln (r:W64.t Ap2.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_2: W64.t Array3.t;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    x <- witness;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux_0 <- a.[0];
    t0 <- aux_0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    (aux_0, aux) <- mulu_64 t0 b.[0];
    t1 <- aux_0;
    t0 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- t0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- t1;
    LEAK.leakages <- LeakAddr([1]) :: LEAK.leakages;
    x.[1] <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([2]) :: LEAK.leakages;
    x.[2] <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    x.[0] <- aux_0;
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    k <- 1;
    while (k < nlimbs) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ __muln_innerloop (x, k, 0, (k + 1), a, b);
      x <- aux_2;
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (W64.of_int 0);
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      x.[(k %% 3)] <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t0;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    LEAK.leakages <- LeakFor(nlimbs,((2 * nlimbs) - 1)) :: LeakAddr([]) :: LEAK.leakages;
    aux_1 <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux_1) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ __muln_innerloop (x, k, ((k - nlimbs) + 1), nlimbs, a, b);
      x <- aux_2;
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (W64.of_int 0);
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      x.[(k %% 3)] <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t0;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    LEAK.leakages <- LeakAddr([(((2 * nlimbs) - 1) %% 3)]) :: LEAK.leakages;
    aux_0 <- x.[(((2 * nlimbs) - 1) %% 3)];
    LEAK.leakages <- LeakAddr([((2 * nlimbs) - 1)]) :: LEAK.leakages;
    r.[((2 * nlimbs) - 1)] <- aux_0;
    return (r);
  }
  
  proc _muln (r:W64.t Ap2.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux: W64.t Ap2.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __muln (r, a, b);
    r <- aux;
    return (r);
  }
  
  proc _muln_ (r:W64.t Ap2.t, a:W64.t Ap1.t, b:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- a;
    a <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- b;
    b <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _muln (r, a, b);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc __sqrn_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Ap1.t) : W64.t Array3.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array3.t;
    
    var i:int;
    var j:int;
    var ti:W64.t;
    var tj:W64.t;
    
    LEAK.leakages <- LeakFor(istart,iend) :: LeakAddr([]) :: LEAK.leakages;
    aux <- iend;
    i <- istart;
    while (i < aux) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux <- (k - i);
      j <- aux;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- a.[i];
      ti <- aux_0;
      LEAK.leakages <- LeakAddr([j]) :: LEAK.leakages;
      aux_0 <- a.[j];
      tj <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <@ BNUTIL_MLeak.__addacc3x2 (x, ti, tj, k);
      x <- aux_1;
      i <- i + 1;
    }
    return (x);
  }
  
  proc __sqrn (r:W64.t Ap2.t, a:W64.t Ap1.t) : W64.t Ap2.t = {
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_2: W64.t Array3.t;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    x <- witness;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    aux_0 <- a.[0];
    t0 <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_0, aux) <- mulu_64 t0 t0;
    t1 <- aux_0;
    t0 <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- t0;
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    r.[0] <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- t1;
    LEAK.leakages <- LeakAddr([1]) :: LEAK.leakages;
    x.[1] <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([2]) :: LEAK.leakages;
    x.[2] <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    x.[0] <- aux_0;
    LEAK.leakages <- LeakFor(1,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    k <- 1;
    while (k < nlimbs) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ __sqrn_innerloop (x, k, 0, ((k + 1) %/ 2), a);
      x <- aux_2;
      LEAK.leakages <- LeakCond(((k %% 2) = 0)) :: LeakAddr([]) :: LEAK.leakages;
      if (((k %% 2) = 0)) {
        LEAK.leakages <- LeakAddr([(k %/ 2)]) :: LEAK.leakages;
        aux_0 <- a.[(k %/ 2)];
        t0 <- aux_0;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_0, aux) <- mulu_64 t0 t0;
        t1 <- aux_0;
        t0 <- aux;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_2 <@ BNUTIL_MLeak.__addacc3 (x, t1, t0, k);
        x <- aux_2;
      } else {
        
      }
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (W64.of_int 0);
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      x.[(k %% 3)] <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t0;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    LEAK.leakages <- LeakFor(nlimbs,((2 * nlimbs) - 1)) :: LeakAddr([]) :: LEAK.leakages;
    aux_1 <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux_1) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ __sqrn_innerloop (x, k, ((k - nlimbs) + 1), ((k + 1) %/ 2), a);
      x <- aux_2;
      LEAK.leakages <- LeakCond(((k %% 2) = 0)) :: LeakAddr([]) :: LEAK.leakages;
      if (((k %% 2) = 0)) {
        LEAK.leakages <- LeakAddr([(k %/ 2)]) :: LEAK.leakages;
        aux_0 <- a.[(k %/ 2)];
        t0 <- aux_0;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        (aux_0, aux) <- mulu_64 t0 t0;
        t1 <- aux_0;
        t0 <- aux;
        LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
        aux_2 <@ BNUTIL_MLeak.__addacc3 (x, t1, t0, k);
        x <- aux_2;
      } else {
        
      }
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- (W64.of_int 0);
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      x.[(k %% 3)] <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t0;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    LEAK.leakages <- LeakAddr([(((2 * nlimbs) - 1) %% 3)]) :: LEAK.leakages;
    aux_0 <- x.[(((2 * nlimbs) - 1) %% 3)];
    LEAK.leakages <- LeakAddr([((2 * nlimbs) - 1)]) :: LEAK.leakages;
    r.[((2 * nlimbs) - 1)] <- aux_0;
    return (r);
  }
  
  proc _sqrn (r:W64.t Ap2.t, a:W64.t Ap1.t) : W64.t Ap2.t = {
    var aux: W64.t Ap2.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __sqrn (r, a);
    r <- aux;
    return (r);
  }
  
  proc _sqrn_ (r:W64.t Ap2.t, a:W64.t Ap1.t) : W64.t Ap2.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- a;
    a <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _sqrn (r, a);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc _cminusP_ (x:W64.t Ap1.t, mP:W64.t Ap1.t, lastbit:W64.t) : 
  W64.t Ap1.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_0: bool;
    var aux_1: W64.t;
    var aux: W64.t Ap1.t;
    
    var _tmp:W64.t Ap1.t;
    var tmp:W64.t Ap1.t;
    var _cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:W64.t;
    _tmp <- witness;
    tmp <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- _tmp;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _mov_ (tmp, x);
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux) <@ _addU_ (tmp, mP);
    _cf <- aux_5;
    tmp <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux_1) <- adc_64 lastbit (W64.of_int 0) _cf;
     _0 <- aux_5;
    lastbit <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_0, aux_1) <- NEG_64 lastbit;
     _1 <- aux_5;
    _cf <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
     _4 <- aux_0;
     _5 <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ _cmov_ (x, _cf, tmp);
    x <- aux;
    return (x);
  }
  
  proc __mont_redM (r:W64.t Ap1.t, a:W64.t Ap2.t,
                      _P:W64.t Ap1.t, _mP:W64.t Ap1.t, _U0:W64.t) : 
  W64.t Ap1.t = {
    var aux_4: bool;
    var aux_0: int;
    var aux_3: W64.t;
    var aux: W64.t;
    var aux_2: W64.t Array3.t;
    var aux_1: W64.t Ap1.t;
    
    var x:W64.t Array3.t;
    var p:W64.t Ap1.t;
    var k:int;
    var zero:W64.t;
    var t0:W64.t;
    var t1:W64.t;
    var lastbit:W64.t;
    var cf:bool;
    var mP:W64.t Ap1.t;
    var  _0:W64.t;
    var  _1:bool;
    p <- witness;
    mP <- witness;
    x <- witness;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_3 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
    x.[0] <- aux_3;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_3 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([1]) :: LEAK.leakages;
    x.[1] <- aux_3;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_3 <- (W64.of_int 0);
    LEAK.leakages <- LeakAddr([2]) :: LEAK.leakages;
    x.[2] <- aux_3;
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    k <- 0;
    while (k < nlimbs) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- _P;
      p <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ __muln_innerloop (x, k, 0, k, r, p);
      x <- aux_2;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_3 <- (W64.of_int 0);
      zero <- aux_3;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      aux_3 <- a.[k];
      t0 <- aux_3;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ BNUTIL_MLeak.__addacc3 (x, zero, t0, k);
      x <- aux_2;
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      aux_3 <- x.[(k %% 3)];
      t0 <- aux_3;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      (aux_3, aux) <- mulu_64 t0 _U0;
       _0 <- aux_3;
      t0 <- aux;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_3 <- t0;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      r.[k] <- aux_3;
      LEAK.leakages <- LeakAddr([0]) :: LEAK.leakages;
      (aux_3, aux) <- mulu_64 t0 _P.[0];
      t1 <- aux_3;
      t0 <- aux;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ BNUTIL_MLeak.__addacc3 (x, t1, t0, k);
      x <- aux_2;
      k <- k + 1;
    }
    LEAK.leakages <- LeakFor(nlimbs,((2 * nlimbs) - 1)) :: LeakAddr([]) :: LEAK.leakages;
    aux_0 <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux_0) {
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_1 <- _P;
      p <- aux_1;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ __muln_innerloop (x, k, ((k - nlimbs) + 1), nlimbs, r, p);
      x <- aux_2;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_3 <- (W64.of_int 0);
      zero <- aux_3;
      LEAK.leakages <- LeakAddr([k]) :: LEAK.leakages;
      aux_3 <- a.[k];
      t0 <- aux_3;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_2 <@ BNUTIL_MLeak.__addacc3 (x, zero, t0, k);
      x <- aux_2;
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      aux_3 <- x.[(k %% 3)];
      t0 <- aux_3;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_3 <- t0;
      LEAK.leakages <- LeakAddr([(k - nlimbs)]) :: LEAK.leakages;
      r.[(k - nlimbs)] <- aux_3;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_3 <- (W64.of_int 0);
      LEAK.leakages <- LeakAddr([(k %% 3)]) :: LEAK.leakages;
      x.[(k %% 3)] <- aux_3;
      k <- k + 1;
    }
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_3 <- (W64.of_int 0);
    lastbit <- aux_3;
    LEAK.leakages <- LeakAddr([((2 * nlimbs) - 1); (((2 * nlimbs) - 1) %% 3)]) :: LEAK.leakages;
    (aux_4, aux_3) <- adc_64 x.[(((2 * nlimbs) - 1) %% 3)] a.[((2 * nlimbs) - 1)]
    false;
    cf <- aux_4;
    LEAK.leakages <- LeakAddr([(((2 * nlimbs) - 1) %% 3)]) :: LEAK.leakages;
    x.[(((2 * nlimbs) - 1) %% 3)] <- aux_3;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    (aux_4, aux_3) <- adc_64 lastbit (W64.of_int 0) cf;
     _1 <- aux_4;
    lastbit <- aux_3;
    LEAK.leakages <- LeakAddr([(((2 * nlimbs) - 1) %% 3)]) :: LEAK.leakages;
    aux_3 <- x.[(((2 * nlimbs) - 1) %% 3)];
    LEAK.leakages <- LeakAddr([(nlimbs - 1)]) :: LEAK.leakages;
    r.[(nlimbs - 1)] <- aux_3;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <- _mP;
    mP <- aux_1;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_1 <@ _cminusP_ (r, mP, lastbit);
    r <- aux_1;
    return (r);
  }
  
  proc __pack2 (r:W64.t Ap2.t, lo:W64.t Ap1.t, hi:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- lo.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    LEAK.leakages <- LeakFor(0,nlimbs) :: LeakAddr([]) :: LEAK.leakages;
    i <- 0;
    while (i < nlimbs) {
      LEAK.leakages <- LeakAddr([i]) :: LEAK.leakages;
      aux_0 <- hi.[i];
      t <- aux_0;
      LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
      aux_0 <- t;
      LEAK.leakages <- LeakAddr([(nlimbs + i)]) :: LEAK.leakages;
      r.[(nlimbs + i)] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc _pack2_ (r:W64.t Ap2.t, lo:W64.t Ap1.t, hi:W64.t Ap1.t) : 
  W64.t Ap2.t = {
    var aux_0: W64.t Ap1.t;
    var aux: W64.t Ap2.t;
    
    
    
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- lo;
    lo <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux_0 <- hi;
    hi <- aux_0;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <@ __pack2 (r, lo, hi);
    r <- aux;
    LEAK.leakages <- LeakAddr([]) :: LEAK.leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
}.

