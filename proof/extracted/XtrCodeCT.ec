require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
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
  var leakages : leakages_t
  
  proc bN__cf_mask (cf:bool) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var mask:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    mask <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 mask (W64.of_int 0) cf;
    cf <- aux_0;
    mask <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (- mask);
    mask <- aux;
    return (mask);
  }
  
  proc bN__addacc3 (a:W64.t Array3.t, b1:W64.t, b0:W64.t, k:int) : W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([(k %% 3)]) :: leakages;
    (aux, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux;
    leakages <- LeakAddr([(k %% 3)]) :: leakages;
    a.[(k %% 3)] <- aux_0;
    leakages <- LeakAddr([((k + 1) %% 3)]) :: leakages;
    (aux, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux;
    leakages <- LeakAddr([((k + 1) %% 3)]) :: leakages;
    a.[((k + 1) %% 3)] <- aux_0;
    leakages <- LeakAddr([((k + 2) %% 3)]) :: leakages;
    (aux, aux_0) <- adc_64 a.[((k + 2) %% 3)] (W64.of_int 0) cf;
    cf <- aux;
    leakages <- LeakAddr([((k + 2) %% 3)]) :: leakages;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
  
  proc bN__addacc3x2 (a:W64.t Array3.t, x:W64.t, y:W64.t, k:int) : W64.t Array3.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W64.t;
    
    var b1:W64.t;
    var b0:W64.t;
    var t:W64.t;
    var cf:bool;
    var b2:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- mulu_64 x y;
    b1 <- aux_0;
    b0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b0;
    t <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (b0 `<<` (W8.of_int 1));
    b0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHLD_64 b1 t (W8.of_int 1);
     _0 <- aux_5;
    cf <- aux_4;
     _1 <- aux_3;
     _2 <- aux_2;
     _3 <- aux_1;
    b1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOV_64 (W64.of_int 0);
    b2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_0) <- adc_64 b2 b2 cf;
    cf <- aux_5;
    b2 <- aux_0;
    leakages <- LeakAddr([(k %% 3)]) :: leakages;
    (aux_5, aux_0) <- adc_64 a.[(k %% 3)] b0 false;
    cf <- aux_5;
    leakages <- LeakAddr([(k %% 3)]) :: leakages;
    a.[(k %% 3)] <- aux_0;
    leakages <- LeakAddr([((k + 1) %% 3)]) :: leakages;
    (aux_5, aux_0) <- adc_64 a.[((k + 1) %% 3)] b1 cf;
    cf <- aux_5;
    leakages <- LeakAddr([((k + 1) %% 3)]) :: leakages;
    a.[((k + 1) %% 3)] <- aux_0;
    leakages <- LeakAddr([((k + 2) %% 3)]) :: leakages;
    (aux_5, aux_0) <- adc_64 a.[((k + 2) %% 3)] b2 cf;
    cf <- aux_5;
    leakages <- LeakAddr([((k + 2) %% 3)]) :: leakages;
    a.[((k + 2) %% 3)] <- aux_0;
    return (a);
  }
  
  proc bN__load (a:W64.t Array11.t, ap:W64.t) : W64.t Array11.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_load (a:W64.t Array11.t, ap:W64.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__load (a, ap);
    a <- aux;
    return (a);
  }
  
  proc bN_load_ (a:W64.t Array11.t, ap:W64.t) : W64.t Array11.t = {
    var aux_0: W64.t;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ap;
    ap <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_load (a, ap);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc bN__store (ap:W64.t, a:W64.t Array11.t) : unit = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int (8 * i))))]) :: leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
  
  proc bN_store_ (ap:W64.t, a:W64.t Array11.t) : unit = {
    var aux: W64.t;
    var aux_0: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ap;
    ap <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- a;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    bN__store (ap, a);
    return ();
  }
  
  proc bN__eq_zf (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
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
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    acc <- aux;
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (t `^` b.[i]);
      t <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (acc `|` t);
      acc <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux) <- AND_64 acc acc;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
     _4 <- aux;
    return (zf);
  }
  
  proc bN_eq_zf (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
    var aux: bool;
    
    var zf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__eq_zf (a, b);
    zf <- aux;
    return (zf);
  }
  
  proc bN_eq_zf_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    var zf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_eq_zf (a, b);
    zf <- aux_0;
    return (zf);
  }
  
  proc bN_eq_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_eq_zf_ (a, b);
    zf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    res_0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    are_equal <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zf ? are_equal : res_0);
    res_0 <- aux_0;
    return (res_0);
  }
  
  proc bN__mov (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bN_mov (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__mov (r, a);
    r <- aux;
    return (r);
  }
  
  proc bN_mov_ (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov (r, a);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc bN__cmov (a:W64.t Array11.t, cond:bool, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (cond ? b.[i] : t);
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_cmov (a:W64.t Array11.t, cond:bool, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__cmov (a, cond, b);
    a <- aux;
    return (a);
  }
  
  proc bN_cmov_ (a:W64.t Array11.t, cond:bool, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_cmov (a, cond, b);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc bN__cswap_mask (x:W64.t Array11.t, y:W64.t Array11.t, mask:W64.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var tmp1:W64.t;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- x.[i];
      tmp1 <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (tmp1 `^` y.[i]);
      tmp1 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (tmp1 `&` mask);
      tmp1 <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (x.[i] `^` tmp1);
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (y.[i] `^` tmp1);
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux_0;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc bN_cswap_mask (x:W64.t Array11.t, y:W64.t Array11.t, mask:W64.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bN__cswap_mask (x, y, mask);
    x <- aux_0;
    y <- aux;
    return (x, y);
  }
  
  proc bN_cswap_mask_ (x:W64.t Array11.t, y:W64.t Array11.t, mask:W64.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bN_cswap_mask (x, y, mask);
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    y <- aux_0;
    return (x, y);
  }
  
  proc bN__fill (a:W64.t Array11.t, x:W64.t) : W64.t Array11.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- x;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_fill_ (a:W64.t Array11.t, x:W64.t) : W64.t Array11.t = {
    var aux_0: W64.t;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__fill (a, x);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc bN_set0_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t;
    var aux_0: W64.t Array11.t;
    
    var t:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_fill_ (a, t);
    a <- aux_0;
    return (a);
  }
  
  proc bN__and_mask (a:W64.t Array11.t, mask:W64.t) : W64.t Array11.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (a.[i] `&` mask);
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN_and_mask (a:W64.t Array11.t, mask:W64.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__and_mask (a, mask);
    a <- aux;
    return (a);
  }
  
  proc bN_and_mask_ (a:W64.t Array11.t, mask:W64.t) : W64.t Array11.t = {
    var aux_0: W64.t;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- mask;
    mask <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_and_mask (a, mask);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc bN__addc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- b.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_1, aux_0) <- adc_64 a.[i] t cf;
      cf <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bN_addc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                   W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN__addc1U (a, b, cf);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc bN_addc1U_ (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bN_addc1U (a, b, cf);
    cf <- aux_0;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (cf, a);
  }
  
  proc bN_addU_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool *
                                                         W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Array11.t;
    
    var cf:bool;
    var t:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- adc_64 a.[0] t false;
    cf <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ bN_addc1U_ (a, b, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc bN__addc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_1, aux_0) <- adc_64 t b.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc bN_addc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                 cf:bool) : bool * W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN__addc1 (r, a, b, cf);
    cf <- aux;
    r <- aux_0;
    return (cf, r);
  }
  
  proc bN_addc1_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bN_addc1 (r, a, b, cf);
    cf <- aux_0;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (cf, r);
  }
  
  proc bN_add_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  bool * W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Array11.t;
    
    var cf:bool;
    var t:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- adc_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ bN_addc1_ (r, a, b, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, a);
  }
  
  proc bN__subc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- b.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_1, aux_0) <- sbb_64 a.[i] t cf;
      cf <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bN_subc1U (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                   W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN__subc1U (a, b, cf);
    cf <- aux;
    a <- aux_0;
    return (cf, a);
  }
  
  proc bN_subc1U_ (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool *
                                                                    W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bN_subc1U (a, b, cf);
    cf <- aux_0;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (cf, a);
  }
  
  proc bN_subU_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool *
                                                         W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Array11.t;
    
    var cf:bool;
    var t:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- sbb_64 a.[0] t false;
    cf <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ bN_subc1U_ (a, b, cf);
    cf <- aux_0;
    a <- aux_1;
    return (cf, a);
  }
  
  proc bN__subc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_1, aux_0) <- sbb_64 t b.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc bN_subc1 (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                 cf:bool) : bool * W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN__subc1 (r, a, b, cf);
    cf <- aux;
    r <- aux_0;
    return (cf, r);
  }
  
  proc bN_subc1_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t,
                  cf:bool) : bool * W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ bN_subc1 (r, a, b, cf);
    cf <- aux_0;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (cf, r);
  }
  
  proc bN_sub_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  bool * W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t;
    var aux_1: W64.t Array11.t;
    
    var cf:bool;
    var t:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- sbb_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ bN_subc1_ (r, a, b, cf);
    cf <- aux_0;
    r <- aux_1;
    return (cf, r);
  }
  
  proc bN__ltc1_cf (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : 
  bool = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_1, aux_0) <- sbb_64 t b.[i] cf;
      cf <- aux_1;
      t <- aux_0;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc bN_ltc1_cf (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : bool = {
    var aux: bool;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__ltc1_cf (a, b, cf);
    cf <- aux;
    return (cf);
  }
  
  proc bN_ltc1_cf_ (a:W64.t Array11.t, b:W64.t Array11.t, cf:bool) : 
  bool = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_ltc1_cf (a, b, cf);
    cf <- aux_0;
    return (cf);
  }
  
  proc bN_lt_cf_ (a:W64.t Array11.t, b:W64.t Array11.t) : bool = {
    var aux_0: bool;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- sbb_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_ltc1_cf_ (a, b, cf);
    cf <- aux_0;
    return (cf);
  }
  
  proc bN_caddU_ (x:W64.t Array11.t, cf:bool, y:W64.t Array11.t) : W64.t Array11.t = {
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W64.t Array11.t;
    
    var _tmp:W64.t Array11.t;
    var tmp:W64.t Array11.t;
    var mask:W64.t;
    var  _0:bool;
    _tmp <- witness;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (tmp, y);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN__cf_mask (cf);
    mask <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_and_mask_ (tmp, mask);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux) <@ bN_addU_ (x, tmp);
     _0 <- aux_1;
    x <- aux;
    return (x);
  }
  
  proc bN__muln_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array3.t = {
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux_2: W64.t Array3.t;
    
    var i:int;
    var j:int;
    var t0:W64.t;
    var t1:W64.t;
    
    leakages <- LeakFor(istart,iend) :: LeakAddr([]) :: leakages;
    aux <- iend;
    i <- istart;
    while (i < aux) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (k - i);
      j <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- a.[i];
      t0 <- aux_1;
      leakages <- LeakAddr([j]) :: leakages;
      (aux_1, aux_0) <- mulu_64 t0 b.[j];
      t1 <- aux_1;
      t0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__addacc3 (x, t1, t0, k);
      x <- aux_2;
      i <- i + 1;
    }
    return (x);
  }
  
  proc bN__muln (r:W64.t Array22.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array22.t = {
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_2: W64.t Array3.t;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    x <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- a.[0];
    t0 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- mulu_64 t0 b.[0];
    t1 <- aux_0;
    t0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t0;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t1;
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux_0;
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    k <- 1;
    while (k < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__muln_innerloop (x, k, 0, (k + 1), a, b);
      x <- aux_2;
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      x.[(k %% 3)] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t0;
      leakages <- LeakAddr([k]) :: leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    leakages <- LeakFor(11,((2 * 11) - 1)) :: LeakAddr([]) :: leakages;
    aux_1 <- ((2 * 11) - 1);
    k <- 11;
    while (k < aux_1) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__muln_innerloop (x, k, ((k - 11) + 1), 11, a, b);
      x <- aux_2;
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      x.[(k %% 3)] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t0;
      leakages <- LeakAddr([k]) :: leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    leakages <- LeakAddr([(((2 * 11) - 1) %% 3)]) :: leakages;
    aux_0 <- x.[(((2 * 11) - 1) %% 3)];
    leakages <- LeakAddr([((2 * 11) - 1)]) :: leakages;
    r.[((2 * 11) - 1)] <- aux_0;
    return (r);
  }
  
  proc bN_muln (r:W64.t Array22.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array22.t = {
    var aux: W64.t Array22.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__muln (r, a, b);
    r <- aux;
    return (r);
  }
  
  proc bN_muln_ (r:W64.t Array22.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array22.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- a;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_muln (r, a, b);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc bN__sqrn_innerloop (x:W64.t Array3.t, k:int, istart:int, iend:int,
                           a:W64.t Array11.t) : W64.t Array3.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array3.t;
    
    var i:int;
    var j:int;
    var ti:W64.t;
    var tj:W64.t;
    
    leakages <- LeakFor(istart,iend) :: LeakAddr([]) :: leakages;
    aux <- iend;
    i <- istart;
    while (i < aux) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (k - i);
      j <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      ti <- aux_0;
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- a.[j];
      tj <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ bN__addacc3x2 (x, ti, tj, k);
      x <- aux_1;
      i <- i + 1;
    }
    return (x);
  }
  
  proc bN__sqrn (r:W64.t Array22.t, a:W64.t Array11.t) : W64.t Array22.t = {
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_2: W64.t Array3.t;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    x <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- a.[0];
    t0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- mulu_64 t0 t0;
    t1 <- aux_0;
    t0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t0;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t1;
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux_0;
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    k <- 1;
    while (k < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__sqrn_innerloop (x, k, 0, ((k + 1) %/ 2), a);
      x <- aux_2;
      leakages <- LeakCond(((k %% 2) = 0)) :: LeakAddr([]) :: leakages;
      if (((k %% 2) = 0)) {
        leakages <- LeakAddr([(k %/ 2)]) :: leakages;
        aux_0 <- a.[(k %/ 2)];
        t0 <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        (aux_0, aux) <- mulu_64 t0 t0;
        t1 <- aux_0;
        t0 <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux_2 <@ bN__addacc3 (x, t1, t0, k);
        x <- aux_2;
      } else {
        
      }
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      x.[(k %% 3)] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t0;
      leakages <- LeakAddr([k]) :: leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    leakages <- LeakFor(11,((2 * 11) - 1)) :: LeakAddr([]) :: leakages;
    aux_1 <- ((2 * 11) - 1);
    k <- 11;
    while (k < aux_1) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__sqrn_innerloop (x, k, ((k - 11) + 1), ((k + 1) %/ 2), a);
      x <- aux_2;
      leakages <- LeakCond(((k %% 2) = 0)) :: LeakAddr([]) :: leakages;
      if (((k %% 2) = 0)) {
        leakages <- LeakAddr([(k %/ 2)]) :: leakages;
        aux_0 <- a.[(k %/ 2)];
        t0 <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        (aux_0, aux) <- mulu_64 t0 t0;
        t1 <- aux_0;
        t0 <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux_2 <@ bN__addacc3 (x, t1, t0, k);
        x <- aux_2;
      } else {
        
      }
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      aux_0 <- x.[(k %% 3)];
      t0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      x.[(k %% 3)] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t0;
      leakages <- LeakAddr([k]) :: leakages;
      r.[k] <- aux_0;
      k <- k + 1;
    }
    leakages <- LeakAddr([(((2 * 11) - 1) %% 3)]) :: leakages;
    aux_0 <- x.[(((2 * 11) - 1) %% 3)];
    leakages <- LeakAddr([((2 * 11) - 1)]) :: leakages;
    r.[((2 * 11) - 1)] <- aux_0;
    return (r);
  }
  
  proc bN_sqrn (r:W64.t Array22.t, a:W64.t Array11.t) : W64.t Array22.t = {
    var aux: W64.t Array22.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__sqrn (r, a);
    r <- aux;
    return (r);
  }
  
  proc bN_sqrn_ (r:W64.t Array22.t, a:W64.t Array11.t) : W64.t Array22.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- a;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_sqrn (r, a);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc bN_cminusP_ (x:W64.t Array11.t, mP:W64.t Array11.t, lastbit:W64.t) : 
  W64.t Array11.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_0: bool;
    var aux_1: W64.t;
    var aux: W64.t Array11.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (tmp, x);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux) <@ bN_addU_ (tmp, mP);
    _cf <- aux_5;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_1) <- adc_64 lastbit (W64.of_int 0) _cf;
     _0 <- aux_5;
    lastbit <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_0, aux_1) <- NEG_64 lastbit;
     _1 <- aux_5;
    _cf <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
     _4 <- aux_0;
     _5 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_cmov_ (x, _cf, tmp);
    x <- aux;
    return (x);
  }
  
  proc bN__mont_redM (r:W64.t Array11.t, a:W64.t Array22.t,
                      _P:W64.t Array11.t, _mP:W64.t Array11.t, _U0:W64.t) : 
  W64.t Array11.t = {
    var aux_4: bool;
    var aux_0: int;
    var aux_3: W64.t;
    var aux: W64.t;
    var aux_2: W64.t Array3.t;
    var aux_1: W64.t Array11.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux_3;
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    k <- 0;
    while (k < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- _P;
      p <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__muln_innerloop (x, k, 0, k, r, p);
      x <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <- (W64.of_int 0);
      zero <- aux_3;
      leakages <- LeakAddr([k]) :: leakages;
      aux_3 <- a.[k];
      t0 <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__addacc3 (x, zero, t0, k);
      x <- aux_2;
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      aux_3 <- x.[(k %% 3)];
      t0 <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      (aux_3, aux) <- mulu_64 t0 _U0;
       _0 <- aux_3;
      t0 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <- t0;
      leakages <- LeakAddr([k]) :: leakages;
      r.[k] <- aux_3;
      leakages <- LeakAddr([0]) :: leakages;
      (aux_3, aux) <- mulu_64 t0 _P.[0];
      t1 <- aux_3;
      t0 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__addacc3 (x, t1, t0, k);
      x <- aux_2;
      k <- k + 1;
    }
    leakages <- LeakFor(11,((2 * 11) - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- ((2 * 11) - 1);
    k <- 11;
    while (k < aux_0) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- _P;
      p <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__muln_innerloop (x, k, ((k - 11) + 1), 11, r, p);
      x <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <- (W64.of_int 0);
      zero <- aux_3;
      leakages <- LeakAddr([k]) :: leakages;
      aux_3 <- a.[k];
      t0 <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ bN__addacc3 (x, zero, t0, k);
      x <- aux_2;
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      aux_3 <- x.[(k %% 3)];
      t0 <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <- t0;
      leakages <- LeakAddr([(k - 11)]) :: leakages;
      r.[(k - 11)] <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <- (W64.of_int 0);
      leakages <- LeakAddr([(k %% 3)]) :: leakages;
      x.[(k %% 3)] <- aux_3;
      k <- k + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (W64.of_int 0);
    lastbit <- aux_3;
    leakages <- LeakAddr([((2 * 11) - 1); (((2 * 11) - 1) %% 3)]) :: leakages;
    (aux_4, aux_3) <- adc_64 x.[(((2 * 11) - 1) %% 3)] a.[((2 * 11) - 1)]
    false;
    cf <- aux_4;
    leakages <- LeakAddr([(((2 * 11) - 1) %% 3)]) :: leakages;
    x.[(((2 * 11) - 1) %% 3)] <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3) <- adc_64 lastbit (W64.of_int 0) cf;
     _1 <- aux_4;
    lastbit <- aux_3;
    leakages <- LeakAddr([(((2 * 11) - 1) %% 3)]) :: leakages;
    aux_3 <- x.[(((2 * 11) - 1) %% 3)];
    leakages <- LeakAddr([(11 - 1)]) :: leakages;
    r.[(11 - 1)] <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- _mP;
    mP <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bN_cminusP_ (r, mP, lastbit);
    r <- aux_1;
    return (r);
  }
  
  proc bN__pack2 (r:W64.t Array22.t, lo:W64.t Array11.t, hi:W64.t Array11.t) : 
  W64.t Array22.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- lo.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 11) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- hi.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([(11 + i)]) :: leakages;
      r.[(11 + i)] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bN_pack2_ (r:W64.t Array22.t, lo:W64.t Array11.t, hi:W64.t Array11.t) : 
  W64.t Array22.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- lo;
    lo <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- hi;
    hi <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN__pack2 (r, lo, hi);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc fPM_redM (r:W64.t Array11.t, a:W64.t Array22.t) : W64.t Array11.t = {
    var aux: W64.t;
    var aux_0: W64.t Array11.t;
    
    var _P0i:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- glob_P0i;
    _P0i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN__mont_redM (r, a, glob_P, glob_mP, _P0i);
    r <- aux_0;
    return (r);
  }
  
  proc fPM_redM_ (r:W64.t Array11.t, a:W64.t Array22.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    var aux_0: W64.t Array22.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- a;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ fPM_redM (r, a);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc fPM_fromM_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    var aux_0: W64.t Array22.t;
    
    var _tmp:W64.t Array22.t;
    var tmp2:W64.t Array11.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    tmp2 <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (Array11.init (fun i => _tmp.[0 + i]));
    tmp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (tmp2, a);
    tmp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- tmp2;
    leakages <- LeakAddr([0]) :: leakages;
    _tmp <- Array22.init
            (fun i => if 0 <= i < 0 + 11 then aux.[i-0] else _tmp.[i]);
    leakages <- LeakAddr([11]) :: leakages;
    aux <- (Array11.init (fun i => _tmp.[11 + i]));
    tmp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_set0_ (tmp2);
    tmp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- tmp2;
    leakages <- LeakAddr([11]) :: leakages;
    _tmp <- Array22.init
            (fun i => if 11 <= i < 11 + 11 then aux.[i-11] else _tmp.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- _tmp;
    tmp <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ fPM_redM_ (a, tmp);
    a <- aux;
    return (a);
  }
  
  proc bN_rnd_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux_0: W8.t Array88.t;
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ SC.randombytes_88 ((Array88.init (fun i => get8
                                (WArray88.init64 (fun i => (a).[i])) i)));
    a <-
    (Array11.init (fun i => get64 (WArray88.init8 (fun i => (aux_0).[i])) i));
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
  
  proc bN_rsample_ (a:W64.t Array11.t, bnd:W64.t Array11.t) : W64.t Array11.t = {
    var aux_0: bool;
    var aux: W64.t Array11.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_rnd_ (a);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_lt_cf_ (a, bnd);
    cf <- aux_0;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    while ((! cf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ bN_rnd_ (a);
      a <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ bN_lt_cf_ (a, bnd);
      cf <- aux_0;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    }
    return (a);
  }
  
  proc fPM_chk_bnds_ (err:W64.t, a:W64.t Array11.t) : W64.t = {
    var aux_0: bool;
    var aux_1: W64.t;
    var aux: W64.t Array11.t;
    
    var p:W64.t Array11.t;
    var cf:bool;
    var t:W64.t;
    p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- glob_P;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_lt_cf_ (a, p);
    cf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ bN__cf_mask (cf);
    t <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- NOT_64 t;
    t <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (err `|` t);
    err <- aux_1;
    return (err);
  }
  
  proc fPM_rnd_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    var p:W64.t Array11.t;
    p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- glob_P;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_rsample_ (a, p);
    a <- aux;
    return (a);
  }
  
  proc fPM_addm_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    var aux: bool;
    var aux_1: W64.t;
    var aux_0: W64.t Array11.t;
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Array11.t;
    var  _0:bool;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN_add_ (r, a, b);
    cf <- aux;
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 0);
    lastbit <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1) <- adc_64 lastbit (W64.of_int 0) cf;
     _0 <- aux;
    lastbit <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_mP;
    tmp <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_cminusP_ (r, tmp, lastbit);
    r <- aux_0;
    return (r);
  }
  
  proc fPM_addmU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: bool;
    var aux_1: W64.t;
    var aux_0: W64.t Array11.t;
    
    var cf:bool;
    var lastbit:W64.t;
    var tmp:W64.t Array11.t;
    var  _0:bool;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN_addU_ (a, b);
    cf <- aux;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 0);
    lastbit <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_1) <- adc_64 lastbit (W64.of_int 0) cf;
     _0 <- aux;
    lastbit <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_mP;
    tmp <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_cminusP_ (a, tmp, lastbit);
    a <- aux_0;
    return (a);
  }
  
  proc fPM_subm_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t Array11.t;
    
    var cf:bool;
    var tmp:W64.t Array11.t;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN_sub_ (r, a, b);
    cf <- aux;
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_P;
    tmp <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_caddU_ (r, cf, tmp);
    r <- aux_0;
    return (r);
  }
  
  proc fPM_submU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: bool;
    var aux_0: W64.t Array11.t;
    
    var cf:bool;
    var tmp:W64.t Array11.t;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ bN_subU_ (a, b);
    cf <- aux;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_P;
    tmp <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_caddU_ (a, cf, tmp);
    a <- aux_0;
    return (a);
  }
  
  proc fPM_mulm_ (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_muln_ (tmp, a, b);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ fPM_redM_ (r, tmp);
    r <- aux_0;
    return (r);
  }
  
  proc fPM_mulmU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_muln_ (tmp, a, b);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ fPM_redM_ (a, tmp);
    a <- aux_0;
    return (a);
  }
  
  proc fPM_sqrm_ (r:W64.t Array11.t, a:W64.t Array11.t) : W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_sqrn_ (tmp, a);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ fPM_redM_ (r, tmp);
    r <- aux_0;
    return (r);
  }
  
  proc fPM_sqrmU_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array22.t;
    
    var _tmp:W64.t Array22.t;
    var tmp:W64.t Array22.t;
    _tmp <- witness;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_sqrn_ (tmp, a);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ fPM_redM_ (a, tmp);
    a <- aux_0;
    return (a);
  }
  
  proc fPM_expm_noct (r:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_0: int;
    var aux_1: W64.t;
    var aux: W64.t Array11.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    _b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (x, a);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    _x <- aux;
    leakages <- LeakFor(0,11) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- _b;
      b <- aux;
      leakages <- LeakAddr([j]) :: leakages;
      aux_1 <- b.[j];
      t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W64.of_int 64);
      _k <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_6, aux_5, aux_4, aux_3, aux_2, aux_1) <- SHR_64 t (W8.of_int 1);
       _0 <- aux_6;
      cf <- aux_5;
       _1 <- aux_4;
       _2 <- aux_3;
       _3 <- aux_2;
      t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux <- _x;
      x <- aux;
      leakages <- LeakCond(cf) :: LeakAddr([]) :: leakages;
      if (cf) {
        leakages <- LeakAddr([]) :: leakages;
        aux <@ fPM_mulmU_ (r, x);
        r <- aux;
      } else {
        
      }
      leakages <- LeakAddr([]) :: leakages;
      aux <@ fPM_sqrmU_ (x);
      x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      _x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_6, aux_5, aux_4, aux_3, aux_1) <- DEC_64 _k;
       _4 <- aux_6;
       _5 <- aux_5;
       _6 <- aux_4;
      zf <- aux_3;
      _k <- aux_1;
      leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
      
      while ((! zf)) {
        leakages <- LeakAddr([]) :: leakages;
        (aux_6, aux_5, aux_4, aux_3, aux_2, aux_1) <- SHR_64 t (W8.of_int 1);
         _0 <- aux_6;
        cf <- aux_5;
         _1 <- aux_4;
         _2 <- aux_3;
         _3 <- aux_2;
        t <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux <- _x;
        x <- aux;
        leakages <- LeakCond(cf) :: LeakAddr([]) :: leakages;
        if (cf) {
          leakages <- LeakAddr([]) :: leakages;
          aux <@ fPM_mulmU_ (r, x);
          r <- aux;
        } else {
          
        }
        leakages <- LeakAddr([]) :: leakages;
        aux <@ fPM_sqrmU_ (x);
        x <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- x;
        _x <- aux;
        leakages <- LeakAddr([]) :: leakages;
        (aux_6, aux_5, aux_4, aux_3, aux_1) <- DEC_64 _k;
         _4 <- aux_6;
         _5 <- aux_5;
         _6 <- aux_4;
        zf <- aux_3;
        _k <- aux_1;
      leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
      
      }
      j <- j + 1;
    }
    return (r);
  }
  
  proc fPM_expm_noct_ (r:W64.t Array11.t, a:W64.t Array11.t,
                       b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (r, glob_exp0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ fPM_expm_noct (r, a, b);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
  
  proc fPM_expmU_noct_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    var _tmp:W64.t Array11.t;
    var tmp:W64.t Array11.t;
    _tmp <- witness;
    tmp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- _tmp;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (tmp, a);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bN_mov_ (a, glob_exp0);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ fPM_expm_noct_ (a, tmp, b);
    a <- aux;
    return (a);
  }
  
  proc fPM_expm (x0:W64.t Array11.t, x1:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t * W64.t Array11.t = {
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_0: int;
    var aux_1: W64.t;
    var aux_7: W64.t Array11.t;
    var aux: W64.t Array11.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux_7 <- b;
    _b <- aux_7;
    leakages <- LeakFor((- 1),(11 - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (11 - 1);
    j <- (- 1);
    while (aux_0 < j) {
      leakages <- LeakAddr([]) :: leakages;
      aux_7 <- _b;
      b <- aux_7;
      leakages <- LeakAddr([j]) :: leakages;
      aux_1 <- b.[j];
      t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W64.of_int 64);
      _k <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_6, aux_5, aux_4, aux_3, aux_2, aux_1) <- SHL_64 t (W8.of_int 1);
       _0 <- aux_6;
      cf <- aux_5;
       _1 <- aux_4;
       _2 <- aux_3;
       _3 <- aux_2;
      t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- t;
      _t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ bN__cf_mask (cf);
      mask <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_7, aux) <@ bN_cswap_mask_ (x0, x1, mask);
      x0 <- aux_7;
      x1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- mask;
      _mask <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_7 <@ fPM_mulmU_ (x1, x0);
      x1 <- aux_7;
      leakages <- LeakAddr([]) :: leakages;
      aux_7 <@ fPM_sqrmU_ (x0);
      x0 <- aux_7;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- _mask;
      mask <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_7, aux) <@ bN_cswap_mask_ (x0, x1, mask);
      x0 <- aux_7;
      x1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- _t;
      t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      (aux_6, aux_5, aux_4, aux_3, aux_1) <- DEC_64 _k;
       _4 <- aux_6;
       _5 <- aux_5;
       _6 <- aux_4;
      zf <- aux_3;
      _k <- aux_1;
      leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
      
      while ((! zf)) {
        leakages <- LeakAddr([]) :: leakages;
        (aux_6, aux_5, aux_4, aux_3, aux_2, aux_1) <- SHL_64 t (W8.of_int 1);
         _0 <- aux_6;
        cf <- aux_5;
         _1 <- aux_4;
         _2 <- aux_3;
         _3 <- aux_2;
        t <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- t;
        _t <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ bN__cf_mask (cf);
        mask <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        (aux_7, aux) <@ bN_cswap_mask_ (x0, x1, mask);
        x0 <- aux_7;
        x1 <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- mask;
        _mask <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_7 <@ fPM_mulmU_ (x1, x0);
        x1 <- aux_7;
        leakages <- LeakAddr([]) :: leakages;
        aux_7 <@ fPM_sqrmU_ (x0);
        x0 <- aux_7;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- _mask;
        mask <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        (aux_7, aux) <@ bN_cswap_mask_ (x0, x1, mask);
        x0 <- aux_7;
        x1 <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- _t;
        t <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        (aux_6, aux_5, aux_4, aux_3, aux_1) <- DEC_64 _k;
         _4 <- aux_6;
         _5 <- aux_5;
         _6 <- aux_4;
        zf <- aux_3;
        _k <- aux_1;
      leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
      
      }
      j <- j - 1;
    }
    return (x0, x1);
  }
  
  proc fPM_expm_ (x0:W64.t Array11.t, a:W64.t Array11.t, b:W64.t Array11.t) : 
  W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array11.t;
    
    var _x1:W64.t Array11.t;
    var x1:W64.t Array11.t;
    var exp0:W64.t Array11.t;
    var  _0:W64.t Array11.t;
     _0 <- witness;
    _x1 <- witness;
    exp0 <- witness;
    x1 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- _x1;
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_mov_ (x1, a);
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_exp0;
    exp0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_mov_ (x0, exp0);
    x0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ fPM_expm (x0, x1, b);
    x0 <- aux_0;
     _0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x0;
    x0 <- aux_0;
    return (x0);
  }
  
  proc fPM_expmU_ (a:W64.t Array11.t, b:W64.t Array11.t) : W64.t Array11.t = {
    var aux_0: W64.t Array11.t;
    var aux: W64.t Array11.t;
    
    var _x1:W64.t Array11.t;
    var x1:W64.t Array11.t;
    var exp0:W64.t Array11.t;
    var  _0:W64.t Array11.t;
     _0 <- witness;
    _x1 <- witness;
    exp0 <- witness;
    x1 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- _x1;
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_mov_ (x1, a);
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_exp0;
    exp0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bN_mov_ (a, exp0);
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ fPM_expm (a, x1, b);
    a <- aux_0;
     _0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- a;
    a <- aux_0;
    return (a);
  }
  
  proc fPM_invmU_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    var pm2:W64.t Array11.t;
    pm2 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- glob_Pm2;
    pm2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ fPM_expmU_noct_ (a, pm2);
    a <- aux;
    return (a);
  }
  
  proc fPM_toM_ (a:W64.t Array11.t) : W64.t Array11.t = {
    var aux: W64.t Array11.t;
    
    var rMP:W64.t Array11.t;
    rMP <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- glob_rMP;
    rMP <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ fPM_mulmU_ (a, rMP);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    return (a);
  }
}.

