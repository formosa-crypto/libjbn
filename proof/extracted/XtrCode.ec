require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array3 Array11 Array22 Array88.
require import WArray24 WArray88 WArray176.

abbrev glob_rMP = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].


abbrev glob_exp0 = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].


abbrev glob_Pm2 = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].


abbrev glob_P0i = W64.of_int 0.


abbrev glob_mP = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].


abbrev glob_P = Array11.of_list witness [W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0;
W64.of_int 0; W64.of_int 0; W64.of_int 0; W64.of_int 0].


module type Syscall_t = {
  proc randombytes_88(_:W8.t Array88.t) : W8.t Array88.t
}.

module Syscall : Syscall_t = {
  proc randombytes_88(a:W8.t Array88.t) : W8.t Array88.t = {
    a <$ dmap WArray88.darray
         (fun a => Array88.init (fun i => WArray88.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc bN__cf_mask (cf:bool) : W64.t = {
    
    var mask:W64.t;
    
    mask <- (W64.of_int 0);
    (cf, mask) <- adc_64 mask (W64.of_int 0) cf;
    mask <- (- mask);
    return (mask);
  }
  
  proc bN__addacc3 (a:W64.t Array3.t, b1:W64.t, b0:W64.t, k:int) : W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    
    (aux, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux;
    a.[(k %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux;
    a.[((k + 1) %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 2) %% 3)] (W64.of_int 0) cf;
    cf <- aux;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
  
  proc bN__addacc3x2 (a:W64.t Array3.t, x:W64.t, y:W64.t, k:int) : W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var b1:W64.t;
    var b0:W64.t;
    var t:W64.t;
    var cf:bool;
    var b2:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    (b1, b0) <- mulu_64 x y;
    t <- b0;
    b0 <- (b0 `<<` (W8.of_int 1));
    ( _0, cf,  _1,  _2,  _3, b1) <- SHLD_64 b1 t (W8.of_int 1);
    b2 <- MOV_64 (W64.of_int 0);
    (cf, b2) <- adc_64 b2 b2 cf;
    (aux, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux;
    a.[(k %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux;
    a.[((k + 1) %% 3)] <- aux_0;
    (aux, aux_0) <- adc_64 a.[((k + 2) %% 3)] b2 cf;
    cf <- aux;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
  
  proc bN__load (a:W64.t Array11.t, ap:W64.t) : W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < 11) {
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_load (a:W64.t Array11.t, ap:W64.t) : W64.t Array11.t = {
    
    
    
    a <@ bN__load (a, ap);
    return (a);
  }
  
  proc bN_load_ (a:W64.t Array11.t, ap:W64.t) : W64.t Array11.t = {
    
    
    
    a <- a;
    ap <- ap;
    a <@ bN_load (a, ap);
    a <- a;
    return (a);
  }
  
  proc bN__store (ap:W64.t, a:W64.t Array11.t) : unit = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < 11) {
      t <- a.[i];
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))) (t);
      i <- i + 1;
    }
    return ();
  }
  
  proc bN_store_ (ap:W64.t, a:W64.t Array11.t) : unit = {
    
    
    
    ap <- ap;
    a <- a;
    bN__store (ap, a);
    return ();
  }
  
  proc bN__eq_zf (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
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
    while (i < 11) {
      t <- a.[i];
      t <- (t `^` b.[i]);
      acc <- (acc `|` t);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    return (zf);
  }
  
  proc bN_eq_zf (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
    
    var zf:bool;
    
    zf <@ bN__eq_zf (a, b);
    return (zf);
  }
  
  proc bN_eq_zf_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
    
    var zf:bool;
    
    a <- a;
    b <- b;
    zf <@ bN_eq_zf (a, b);
    return (zf);
  }
  
  proc bN_eq_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t = {
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    zf <@ bN_eq_zf_ (a, b);
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc bN__mov (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < 11) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bN_mov (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    
    
    
    r <@ bN__mov (r, a);
    return (r);
  }
  
  proc bN_mov_ (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    
    
    
    r <- r;
    a <- a;
    r <@ bN_mov (r, a);
    r <- r;
    return (r);
  }
  
  proc bN__cmov (a:W64.t Array11.t, cond:bool, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < 11) {
      t <- a.[i];
      t <- (cond ? b.[i] : t);
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_cmov (a:W64.t Array11.t, cond:bool, b:W64.t Array11.t) : W64.t Array11.t = {
    
    
    
    a <@ bN__cmov (a, cond, b);
    return (a);
  }
  
  proc bN_cmov_ (a:W64.t Array11.t, cond:bool, b:W64.t Array11.t) : W64.t Array11.t = {
    
    
    
    a <- a;
    b <- b;
    a <@ bN_cmov (a, cond, b);
    a <- a;
    return (a);
  }
  
  proc bN__cswap_mask (x:W64.t Array11.t, y:W64.t Array11.t, mask:W64.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    var tmp1:W64.t;
    
    i <- 0;
    while (i < 11) {
      tmp1 <- x.[i];
      tmp1 <- (tmp1 `^` y.[i]);
      tmp1 <- (tmp1 `&` mask);
      x.[i] <- (x.[i] `^` tmp1);
      y.[i] <- (y.[i] `^` tmp1);
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc bN_cswap_mask (x:W64.t Array11.t, y:W64.t Array11.t, mask:W64.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    
    
    
    (x, y) <@ bN__cswap_mask (x, y, mask);
    return (x, y);
  }
  
  proc bN_cswap_mask_ (x:W64.t Array11.t, y:W64.t Array11.t, mask:W64.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    
    
    
    x <- x;
    y <- y;
    (x, y) <@ bN_cswap_mask (x, y, mask);
    x <- x;
    y <- y;
    return (x, y);
  }
  
  proc bN__fill (a:W64.t Array11.t, x:W64.t) : W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 11) {
      a.[i] <- x;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_fill_ (a:W64.t Array11.t, x:W64.t) : W64.t Array11.t = {
    
    
    
    a <- a;
    x <- x;
    a <@ bN__fill (a, x);
    a <- a;
    return (a);
  }
  
  proc bN_set0_ (a:W64.t Array11.t) : W64.t Array11.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int 0);
    a <@ bN_fill_ (a, t);
    return (a);
  }
  
  proc bN__and_mask (a:W64.t Array11.t, mask:W64.t) : W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 11) {
      a.[i] <- (a.[i] `&` mask);
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_and_mask (a:W64.t Array11.t, mask:W64.t) : W64.t Array11.t = {
    
    
    
    a <@ bN__and_mask (a, mask);
    return (a);
  }
  
  proc bN_and_mask_ (a:W64.t Array11.t, mask:W64.t) : W64.t Array11.t = {
    
    
    
    a <- a;
    mask <- mask;
    a <@ bN_and_mask (a, mask);
    a <- a;
    return (a);
  }
  
  proc bN__addc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < 11) {
      t <- b.[i];
      (aux_0, aux_1) <- adc_64 a.[i] t cf;
      cf <- aux_0;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bN_addc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                   W64.t Array11.t = {
    
    
    
    (cf, a) <@ bN__addc1U (a, b, cf);
    return (cf, a);
  }
  
  proc bN_addc1U_ (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    
    
    
    a <- a;
    b <- b;
    (cf, a) <@ bN_addc1U (a, b, cf);
    a <- a;
    return (cf, a);
  }
  
  proc bN_addU_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool *
                                                         W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    t <- b.[0];
    (aux, aux_0) <- adc_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    (cf, a) <@ bN_addc1U_ (a, b, cf);
    return (cf, a);
  }
  
  proc bN__addc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < 11) {
      t <- a.[i];
      (cf, t) <- adc_64 t b.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc bN_addc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                 cf:bool) : bool * W64.t Array11.t = {
    
    
    
    (cf, r) <@ bN__addc1 (r, a, b, cf);
    return (cf, r);
  }
  
  proc bN_addc1_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    
    
    
    r <- r;
    a <- a;
    b <- b;
    (cf, r) <@ bN_addc1 (r, a, b, cf);
    r <- r;
    return (cf, r);
  }
  
  proc bN_add_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  bool * W64.t Array11.t = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- adc_64 t b.[0] false;
    r.[0] <- t;
    (cf, r) <@ bN_addc1_ (r, a, b, cf);
    return (cf, a);
  }
  
  proc bN__subc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < 11) {
      t <- b.[i];
      (aux_0, aux_1) <- sbb_64 a.[i] t cf;
      cf <- aux_0;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bN_subc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                   W64.t Array11.t = {
    
    
    
    (cf, a) <@ bN__subc1U (a, b, cf);
    return (cf, a);
  }
  
  proc bN_subc1U_ (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    
    
    
    a <- a;
    b <- b;
    (cf, a) <@ bN_subc1U (a, b, cf);
    a <- a;
    return (cf, a);
  }
  
  proc bN_subU_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool *
                                                         W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    t <- b.[0];
    (aux, aux_0) <- sbb_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    (cf, a) <@ bN_subc1U_ (a, b, cf);
    return (cf, a);
  }
  
  proc bN__subc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < 11) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc bN_subc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                 cf:bool) : bool * W64.t Array11.t = {
    
    
    
    (cf, r) <@ bN__subc1 (r, a, b, cf);
    return (cf, r);
  }
  
  proc bN_subc1_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    
    
    
    r <- r;
    a <- a;
    b <- b;
    (cf, r) <@ bN_subc1 (r, a, b, cf);
    r <- r;
    return (cf, r);
  }
  
  proc bN_sub_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  bool * W64.t Array11.t = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    r.[0] <- t;
    (cf, r) <@ bN_subc1_ (r, a, b, cf);
    return (cf, r);
  }
  
  proc bN__ltc1_cf (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : 
  bool = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 1;
    while (i < 11) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc bN_ltc1_cf (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool = {
    
    
    
    cf <@ bN__ltc1_cf (a, b, cf);
    return (cf);
  }
  
  proc bN_ltc1_cf_ (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : 
  bool = {
    
    
    
    a <- a;
    b <- b;
    cf <@ bN_ltc1_cf (a, b, cf);
    return (cf);
  }
  
  proc bN_lt_cf_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    cf <@ bN_ltc1_cf_ (a, b, cf);
    return (cf);
  }
  
  proc bN_caddU_ (x:W64.t Array11.t, cf:bool, y:W64.t Array11.t) : W64.t Array11.t = {
    
    var _tmp:W64.t Array11.t;
    var tmp:W64.t Array11.t;
    var mask:W64.t;
    var  _0:bool;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ bN_mov_ (tmp, y);
    mask <@ bN__cf_mask (cf);
    tmp <@ bN_and_mask_ (tmp, mask);
    ( _0, x) <@ bN_addU_ (x, tmp);
    return (x);
  }
  
  proc bN__muln_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array3.t = {
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
      x <@ bN__addacc3 (x, t1, t0, k);
      i <- i + 1;
    }
    return (x);
  }
  
  proc bN__muln (r:W64.t Array22.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array22.t = {
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
    while (k < 11) {
      x <@ bN__muln_innerloop (x, k, 0, (k + 1), a, b);
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    aux <- ((2 * 11) - 1);
    k <- 11;
    while (k < aux) {
      x <@ bN__muln_innerloop (x, k, ((k - 11) + 1), 11, a, b);
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    r.[((2 * 11) - 1)] <- x.[(((2 * 11) - 1) %% 3)];
    return (r);
  }
  
  proc bN_muln (r:W64.t Array22.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array22.t = {
    
    
    
    r <@ bN__muln (r, a, b);
    return (r);
  }
  
  proc bN_muln_ (r:W64.t Array22.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array22.t = {
    
    
    
    r <- r;
    a <- a;
    b <- b;
    r <@ bN_muln (r, a, b);
    r <- r;
    return (r);
  }
  
  proc bN__sqrn_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Array11.t) : W64.t Array3.t = {
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
      x <@ bN__addacc3x2 (x, ti, tj, k);
      i <- i + 1;
    }
    return (x);
  }
  
  proc bN__sqrn (r:W64.t Array22.t, a:W64.t Array11.t) : W64.t Array22.t = {
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
    while (k < 11) {
      x <@ bN__sqrn_innerloop (x, k, 0, ((k + 1) %/ 2), a);
      if (((k %% 2) = 0)) {
        t0 <- a.[(k %/ 2)];
        (t1, t0) <- mulu_64 t0 t0;
        x <@ bN__addacc3 (x, t1, t0, k);
      } else {
        
      }
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    aux <- ((2 * 11) - 1);
    k <- 11;
    while (k < aux) {
      x <@ bN__sqrn_innerloop (x, k, ((k - 11) + 1), ((k + 1) %/ 2), a);
      if (((k %% 2) = 0)) {
        t0 <- a.[(k %/ 2)];
        (t1, t0) <- mulu_64 t0 t0;
        x <@ bN__addacc3 (x, t1, t0, k);
      } else {
        
      }
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    r.[((2 * 11) - 1)] <- x.[(((2 * 11) - 1) %% 3)];
    return (r);
  }
  
  proc bN_sqrn (r:W64.t Array22.t, a:W64.t Array11.t) : W64.t Array22.t = {
    
    
    
    r <@ bN__sqrn (r, a);
    return (r);
  }
  
  proc bN_sqrn_ (r:W64.t Array22.t, a:W64.t Array11.t) : W64.t Array22.t = {
    
    
    
    r <- r;
    a <- a;
    r <@ bN_sqrn (r, a);
    r <- r;
    return (r);
  }
  
  proc bN_cminusP_ (x:W64.t Array11.t, mP:W64.t Array11.t, lastbit:W64.t) : 
  W64.t Array11.t = {
    
    var _tmp:W64.t Array11.t;
    var tmp:W64.t Array11.t;
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
    tmp <@ bN_mov_ (tmp, x);
    (_cf, tmp) <@ bN_addU_ (tmp, mP);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) _cf;
    ( _1, _cf,  _2,  _3,  _4,  _5) <- NEG_64 lastbit;
    x <@ bN_cmov_ (x, _cf, tmp);
    return (x);
  }
  
  proc bN__mont_redM (r:W64.t Array11.t, a:W64.t Array22.t,
                      _P:W64.t Array11.t, _mP:W64.t Array11.t, _U0:W64.t) : 
  W64.t Array11.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var x:W64.t Array3.t;
    var p:W64.t Array11.t;
    var k:int;
    var zero:W64.t;
    var t0:W64.t;
    var t1:W64.t;
    var lastbit:W64.t;
    var cf:bool;
    var mP:W64.t Array11.t;
    var  _0:W64.t;
    var  _1:bool;
    p <- witness;
    mP <- witness;
    x <- witness;
    x.[0] <- (W64.of_int 0);
    x.[1] <- (W64.of_int 0);
    x.[2] <- (W64.of_int 0);
    k <- 0;
    while (k < 11) {
      p <- _P;
      x <@ bN__muln_innerloop (x, k, 0, k, r, p);
      zero <- (W64.of_int 0);
      t0 <- a.[k];
      x <@ bN__addacc3 (x, zero, t0, k);
      t0 <- x.[(k %% 3)];
      ( _0, t0) <- mulu_64 t0 _U0;
      r.[k] <- t0;
      (t1, t0) <- mulu_64 t0 _P.[0];
      x <@ bN__addacc3 (x, t1, t0, k);
      k <- k + 1;
    }
    aux <- ((2 * 11) - 1);
    k <- 11;
    while (k < aux) {
      p <- _P;
      x <@ bN__muln_innerloop (x, k, ((k - 11) + 1), 11, r, p);
      zero <- (W64.of_int 0);
      t0 <- a.[k];
      x <@ bN__addacc3 (x, zero, t0, k);
      t0 <- x.[(k %% 3)];
      r.[(k - 11)] <- t0;
      x.[(k %% 3)] <- (W64.of_int 0);
      k <- k + 1;
    }
    lastbit <- (W64.of_int 0);
    (aux_0, aux_1) <- adc_64 x.[(((2 * 11) - 1) %% 3)] a.[((2 * 11) - 1)]
    false;
    cf <- aux_0;
    x.[(((2 * 11) - 1) %% 3)] <- aux_1;
    ( _1, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    r.[(11 - 1)] <- x.[(((2 * 11) - 1) %% 3)];
    mP <- _mP;
    r <@ bN_cminusP_ (r, mP, lastbit);
    return (r);
  }
  
  proc bN__pack2 (r:W64.t Array22.t, lo:W64.t Array11.t, hi:W64.t Array11.t) : 
  W64.t Array22.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t;
    
    i <- 0;
    while (i < 11) {
      t <- lo.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    i <- 0;
    while (i < 11) {
      t <- hi.[i];
      r.[(11 + i)] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bN_pack2_ (r:W64.t Array22.t, lo:W64.t Array11.t, hi:W64.t Array11.t) : 
  W64.t Array22.t = {
    
    
    
    r <- r;
    lo <- lo;
    hi <- hi;
    r <@ bN__pack2 (r, lo, hi);
    r <- r;
    return (r);
  }
  
  proc fPM_redM (r:W64.t Array11.t, a:W64.t Array22.t) : W64.t Array11.t = {
    
    var _P0i:W64.t;
    
    _P0i <- glob_P0i;
    r <@ bN__mont_redM (r, a, glob_P, glob_mP, _P0i);
    return (r);
  }
  
  proc fPM_redM_ (r:W64.t Array11.t, a:W64.t Array22.t) : W64.t Array11.t = {
    
    
    
    r <- r;
    a <- a;
    r <@ fPM_redM (r, a);
    r <- r;
    return (r);
  }
  
  proc fPM_fromM_ (a:W64.t Array11.t) : W64.t Array11.t = {
    
    var _tmp:W64.t Array22.t;
    var tmp2:W64.t Array11.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    tmp2 <- witness;
    tmp2 <- (Array11.init (fun i => _tmp.[0 + i]));
    tmp2 <@ bN_mov_ (tmp2, a);
    _tmp <- Array22.init
            (fun i => if 0 <= i < 0 + 11 then tmp2.[i-0] else _tmp.[i]);
    tmp2 <- (Array11.init (fun i => _tmp.[11 + i]));
    tmp2 <@ bN_set0_ (tmp2);
    _tmp <- Array22.init
            (fun i => if 11 <= i < 11 + 11 then tmp2.[i-11] else _tmp.[i]);
    tmp <- _tmp;
    a <@ fPM_redM_ (a, tmp);
    return (a);
  }
  
  proc bN_rnd_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W8.t Array88.t;
    
    
    
    a <- a;
    aux <@ SC.randombytes_88 ((Array88.init (fun i => get8
                              (WArray88.init64 (fun i => (a).[i])) i)));
    a <-
    (Array11.init (fun i => get64 (WArray88.init8 (fun i => (aux).[i])) i));
    a <- a;
    return (a);
  }
  
  proc bN_rsample_ (a:W64.t Array11.t, bnd:W64.t Array11.t) : W64.t Array11.t = {
    
    var cf:bool;
    
    a <@ bN_rnd_ (a);
    cf <@ bN_lt_cf_ (a, bnd);
    while ((! cf)) {
      a <@ bN_rnd_ (a);
      cf <@ bN_lt_cf_ (a, bnd);
    }
    return (a);
  }
  
  proc fPM_chk_bnds_ (err:W64.t, a:W64.t Array11.t) : W64.t = {
    
    var p:W64.t Array11.t;
    var cf:bool;
    var t:W64.t;
    p <- witness;
    p <- glob_P;
    cf <@ bN_lt_cf_ (a, p);
    t <@ bN__cf_mask (cf);
    t <- NOT_64 t;
    err <- (err `|` t);
    return (err);
  }
  
  proc fPM_rnd_ (a:W64.t Array11.t) : W64.t Array11.t = {
    
    var p:W64.t Array11.t;
    p <- witness;
    p <- glob_P;
    a <@ bN_rsample_ (a, p);
    return (a);
  }
  
  proc fPM_addm_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Array11.t;
    var  _0:bool;
    tmp <- witness;
    (cf, r) <@ bN_add_ (r, a, b);
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    tmp <- glob_mP;
    r <@ bN_cminusP_ (r, tmp, lastbit);
    return (r);
  }
  
  proc fPM_addmU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Array11.t;
    var  _0:bool;
    tmp <- witness;
    (cf, a) <@ bN_addU_ (a, b);
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    tmp <- glob_mP;
    a <@ bN_cminusP_ (a, tmp, lastbit);
    return (a);
  }
  
  proc fPM_subm_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    
    var cf:bool;
    var tmp:W64.t Array11.t;
    tmp <- witness;
    (cf, r) <@ bN_sub_ (r, a, b);
    tmp <- glob_P;
    r <@ bN_caddU_ (r, cf, tmp);
    return (r);
  }
  
  proc fPM_submU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    
    var cf:bool;
    var tmp:W64.t Array11.t;
    tmp <- witness;
    (cf, a) <@ bN_subU_ (a, b);
    tmp <- glob_P;
    a <@ bN_caddU_ (a, cf, tmp);
    return (a);
  }
  
  proc fPM_mulm_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ bN_muln_ (tmp, a, b);
    r <@ fPM_redM_ (r, tmp);
    return (r);
  }
  
  proc fPM_mulmU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ bN_muln_ (tmp, a, b);
    a <@ fPM_redM_ (a, tmp);
    return (a);
  }
  
  proc fPM_sqrm_ (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ bN_sqrn_ (tmp, a);
    r <@ fPM_redM_ (r, tmp);
    return (r);
  }
  
  proc fPM_sqrmU_ (a:W64.t Array11.t) : W64.t Array11.t = {
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ bN_sqrn_ (tmp, a);
    a <@ fPM_redM_ (a, tmp);
    return (a);
  }
  
  proc fPM_expm_noct (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    var aux: int;
    
    var _b:W64.t Array11.t;
    var _x:W64.t Array11.t;
    var x:W64.t Array11.t;
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
    x <@ bN_mov_ (x, a);
    _x <- x;
    j <- 0;
    while (j < 11) {
      b <- _b;
      t <- b.[j];
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- SHR_64 t (W8.of_int 1);
      x <- _x;
      if (cf) {
        r <@ fPM_mulmU_ (r, x);
      } else {
        
      }
      x <@ fPM_sqrmU_ (x);
      _x <- x;
      ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- SHR_64 t (W8.of_int 1);
        x <- _x;
        if (cf) {
          r <@ fPM_mulmU_ (r, x);
        } else {
          
        }
        x <@ fPM_sqrmU_ (x);
        _x <- x;
        ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      }
      j <- j + 1;
    }
    return (r);
  }
  
  proc fPM_expm_noct_ (r:W64.t Array11.t, a:W64.t Array11.t,
                       b:W64.t Array11.t) : W64.t Array11.t = {
    
    
    
    r <@ bN_mov_ (r, glob_exp0);
    a <- a;
    b <- b;
    r <@ fPM_expm_noct (r, a, b);
    r <- r;
    return (r);
  }
  
  proc fPM_expmU_noct_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    
    var _tmp:W64.t Array11.t;
    var tmp:W64.t Array11.t;
    _tmp <- witness;
    tmp <- witness;
    tmp <- _tmp;
    tmp <@ bN_mov_ (tmp, a);
    a <@ bN_mov_ (a, glob_exp0);
    a <@ fPM_expm_noct_ (a, tmp, b);
    return (a);
  }
  
  proc fPM_expm (x0:W64.t Array11.t, x1:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    var aux: int;
    
    var _b:W64.t Array11.t;
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
    j <- (11 - 1);
    while (aux < j) {
      b <- _b;
      t <- b.[j];
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- SHL_64 t (W8.of_int 1);
      _t <- t;
      mask <@ bN__cf_mask (cf);
      (x0, x1) <@ bN_cswap_mask_ (x0, x1, mask);
      _mask <- mask;
      x1 <@ fPM_mulmU_ (x1, x0);
      x0 <@ fPM_sqrmU_ (x0);
      mask <- _mask;
      (x0, x1) <@ bN_cswap_mask_ (x0, x1, mask);
      t <- _t;
      ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- SHL_64 t (W8.of_int 1);
        _t <- t;
        mask <@ bN__cf_mask (cf);
        (x0, x1) <@ bN_cswap_mask_ (x0, x1, mask);
        _mask <- mask;
        x1 <@ fPM_mulmU_ (x1, x0);
        x0 <@ fPM_sqrmU_ (x0);
        mask <- _mask;
        (x0, x1) <@ bN_cswap_mask_ (x0, x1, mask);
        t <- _t;
        ( _4,  _5,  _6, zf, _k) <- DEC_64 _k;
      }
      j <- j - 1;
    }
    return (x0, x1);
  }
  
  proc fPM_expm_ (x0:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    
    var _x1:W64.t Array11.t;
    var x1:W64.t Array11.t;
    var exp0:W64.t Array11.t;
    var  _0:W64.t Array11.t;
     _0 <- witness;
    _x1 <- witness;
    exp0 <- witness;
    x1 <- witness;
    x1 <- _x1;
    x1 <@ bN_mov_ (x1, a);
    exp0 <- glob_exp0;
    x0 <@ bN_mov_ (x0, exp0);
    b <- b;
    (x0,  _0) <@ fPM_expm (x0, x1, b);
    x0 <- x0;
    return (x0);
  }
  
  proc fPM_expmU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    
    var _x1:W64.t Array11.t;
    var x1:W64.t Array11.t;
    var exp0:W64.t Array11.t;
    var  _0:W64.t Array11.t;
     _0 <- witness;
    _x1 <- witness;
    exp0 <- witness;
    x1 <- witness;
    x1 <- _x1;
    x1 <@ bN_mov_ (x1, a);
    exp0 <- glob_exp0;
    a <@ bN_mov_ (a, exp0);
    b <- b;
    (a,  _0) <@ fPM_expm (a, x1, b);
    a <- a;
    return (a);
  }
  
  proc fPM_invmU_ (a:W64.t Array11.t) : W64.t Array11.t = {
    
    var pm2:W64.t Array11.t;
    pm2 <- witness;
    pm2 <- glob_Pm2;
    a <@ fPM_expmU_noct_ (a, pm2);
    return (a);
  }
  
  proc fPM_toM_ (a:W64.t Array11.t) : W64.t Array11.t = {
    
    var rMP:W64.t Array11.t;
    rMP <- witness;
    rMP <- glob_rMP;
    a <@ fPM_mulmU_ (a, rMP);
    a <- a;
    return (a);
  }
}.

