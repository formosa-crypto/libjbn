require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


from JExtract require export Array3.

(* Theory Parameters *)
op nlimbs: int.
clone export PolyArray as Ap1
 with op size <- nlimbs.
(*type bignum = W64.t Ap1.t.*)
clone export PolyArray as Ap2
 with op size <- 2*nlimbs.
(*abbrev bignum2 = W64.t Ap2.t.*)

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

(* Avoided for now! 
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
*)

(* Rewritings:
  "W64.t Array11.t" -> "W64.t Ap1.t"
  "Array11" -> "Ap1"
  "W64.t Array22.t" -> "W64.t Ap2.t"
  "Array22" -> "Ap2"
  "11" -> "nlimbs"
*)

module M(*SC:Syscall_t*) = {
  proc bNUTIL__cf_mask (cf:bool) : W64.t = {
    
    var mask:W64.t;
    
    mask <- (W64.of_int 0);
    (cf, mask) <- adc_64 mask (W64.of_int 0) cf;
    mask <- (- mask);
    return (mask);
  }
  proc bNUTIL__mask_cf (mask:W64.t) : bool = {
    
    var cf:bool;
    var t:W64.t;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t mask false;
    return (cf);
  }
  
  proc bNUTIL__addacc3 (b1:W64.t, b0:W64.t, a:W64.t Array3.t, k:int) : 
  W64.t Array3.t = {
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
  
  proc bNUTIL__addacc3x2 (x:W64.t, y:W64.t, a:W64.t Array3.t, k:int) : 
  W64.t Array3.t = {
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
  
  proc __load (ap:W64.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
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
  
  proc __eq (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t = {
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    zf <@ __eq_zf (a, b);
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc _eq (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ __eq (a, b);
    return (r);
  }
  
  proc _eq_ (a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t = {
    
    var r:W64.t;
    
    a <- a;
    b <- b;
    r <@ _eq (a, b);
    r <- r;
    return (r);
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
  
  proc __test0 (a:W64.t Ap1.t) : W64.t = {
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var zf:bool;
    
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    zf <@ __test0_zf (a);
    res_0 <- (zf ? is_zero : res_0);
    return (res_0);
  }
  
  proc _test0 (a:W64.t Ap1.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ __test0 (a);
    return (r);
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
  
  proc __copy2 (a:W64.t Ap1.t, r:W64.t Ap1.t) : W64.t Ap1.t = {
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
  
  proc __cmov (cond:bool, a:W64.t Ap1.t, b:W64.t Ap1.t) : W64.t Ap1.t = {
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

  proc __cswap_mask (mask:W64.t, x:W64.t Ap1.t, y:W64.t Ap1.t) : 
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
    
  proc __fill (x:W64.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- x;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __set0 (a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int 0);
    a <@ __fill (t, a);
    return (a);
  }
  
  proc __cfill (b:bool, x:W64.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- x;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __set_err (_err:W64.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var err:W64.t;
    var i:int;
    
    err <- _err;
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- (a.[i] `|` err);
      i <- i + 1;
    }
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
  
  proc __addU (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                         W64.t Ap1.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- b.[0];
    (aux, aux_0) <- adc_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < nlimbs) {
      t <- b.[i];
      (aux, aux_0) <- adc_64 a.[i] t cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __add (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    var aux: int;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- a.[0];
    (cf, t) <- adc_64 t b.[0] false;
    r.[0] <- t;
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- adc_64 t b.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc _addU (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                        W64.t Ap1.t = {
    
    var cf:bool;
    
    (cf, a) <@ __addU (a, b);
    return (cf, a);
  }
  
  proc _add (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    
    var cf:bool;
    
    (cf, r) <@ __add (a, b, r);
    return (cf, r);
  }
  
  proc __subU (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                         W64.t Ap1.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- b.[0];
    (aux, aux_0) <- sbb_64 a.[0] t false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < nlimbs) {
      t <- b.[i];
      (aux, aux_0) <- sbb_64 a.[i] t cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc __sub (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    var aux: int;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    r.[0] <- t;
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- sbb_64 t a.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (cf, r);
  }
  
  proc __lt_cf (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool = {
    var aux: int;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    i <- 1;
    while (i < nlimbs) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc __negU (a:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var t:W64.t;
    var cf:bool;
    var i:int;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t a.[0] false;
    a.[0] <- t;
    i <- 1;
    while (i < nlimbs) {
      t <- (W64.of_int 0);
      (cf, t) <- sbb_64 t a.[i] cf;
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc __neg (a:W64.t Ap1.t, r:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var t:W64.t;
    var cf:bool;
    var i:int;
    
    t <- (W64.of_int 0);
    (cf, t) <- sbb_64 t a.[0] false;
    r.[0] <- t;
    i <- 1;
    while (i < nlimbs) {
      t <- (W64.of_int 0);
      (cf, t) <- sbb_64 t a.[i] cf;
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc _subU (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                        W64.t Ap1.t = {
    
    var cf:bool;
    
    (cf, a) <@ __subU (a, b);
    return (cf, a);
  }
  
  proc _sub (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap1.t) : 
  bool * W64.t Ap1.t = {
    
    var cf:bool;
    
    (cf, r) <@ __sub (a, b, r);
    return (cf, r);
  }
  
  proc __rnd (a:W64.t Ap1.t) : W64.t Ap1.t = {
(* (for now...)
    var aux: W8.t Array88.t;
    a <- a;
    aux <@ SC.randombytes_88 ((Array88.init (fun i => get8
                              (WArray88.init64 (fun i => (a).[i])) i)));
    a <-
    (A.init (fun i => get64 (WArray88.init8 (fun i => (aux).[i])) i));
    a <- a;
*)
    return (a);
  }
  
  proc __rsample (a:W64.t Ap1.t, bnd:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var cf:bool;
    
    a <@ __rnd (a);
    cf <@ __lt_cf (a, bnd);
    while ((! cf)) {
      a <@ __rnd (a);
      cf <@ __lt_cf (a, bnd);
    }
    return (a);
  }
  
  proc __subU_signabs (a:W64.t Ap1.t, b:W64.t Ap1.t) : bool *
                                                                 W64.t Ap1.t = {
    
    var cf:bool;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    tmp <- witness;
    ( _0, tmp) <@ __sub (b, a, tmp);
    (cf, a) <@ __subU (a, b);
    a <@ __cmov (cf, a, tmp);
    return (cf, a);
  }
  
  proc __cnegU (cond:W64.t, a:W64.t Ap1.t) : W64.t Ap1.t = {
    
    var x:W64.t Ap1.t;
    var cf:bool;
    x <- witness;
    x <@ __neg (a, x);
    cf <@ bNUTIL__mask_cf (cond);
    a <@ __cmov (cf, a, x);
    return (a);
  }
  
  proc __caddU (cf:bool, x:W64.t Ap1.t, y:W64.t Ap1.t) : W64.t Ap1.t = {
    var aux: int;
    
    var _tmp:W64.t Ap1.t;
    var t0:W64.t;
    var i:int;
    var t:W64.t;
    var tmp:W64.t Ap1.t;
    var  _0:bool;
    _tmp <- witness;
    tmp <- witness;
    _tmp <@ __copy (y);
    t0 <- (W64.of_int 0);
    i <- 0;
    while (i < nlimbs) {
      t <- _tmp.[i];
      t <- ((! cf) ? t0 : t);
      _tmp.[i] <- t;
      i <- i + 1;
    }
    tmp <- _tmp;
    ( _0, x) <@ __addU (x, tmp);
    return (x);
  }
  
  proc __muln_innerloop (k:int, istart:int, iend:int, a:W64.t Ap1.t,
                           b:W64.t Ap1.t, x:W64.t Array3.t) : W64.t Array3.t = {
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
      x <@ bNUTIL__addacc3 (t1, t0, x, k);
      i <- i + 1;
    }
    return (x);
  }
  
  proc __muln (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap2.t) : 
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
      x <@ __muln_innerloop (k, 0, (k + 1), a, b, x);
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    aux <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux) {
      x <@ __muln_innerloop (k, ((k - nlimbs) + 1), nlimbs, a, b, x);
      t0 <- x.[(k %% 3)];
      x.[(k %% 3)] <- (W64.of_int 0);
      r.[k] <- t0;
      k <- k + 1;
    }
    r.[((2 * nlimbs) - 1)] <- x.[(((2 * nlimbs) - 1) %% 3)];
    return (r);
  }
  
  proc _muln (a:W64.t Ap1.t, b:W64.t Ap1.t, r:W64.t Ap2.t) : 
  W64.t Ap2.t = {
    
    
    
    r <@ __muln (a, b, r);
    return (r);
  }
  
  proc __sqrn_innerloop (k:int, istart:int, iend:int, a:W64.t Ap1.t,
                           x:W64.t Array3.t) : W64.t Array3.t = {
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
      x <@ bNUTIL__addacc3x2 (ti, tj, x, k);
      i <- i + 1;
    }
    return (x);
  }
  
  proc __sqrn (a:W64.t Ap1.t, r:W64.t Ap2.t) : W64.t Ap2.t = {
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
      x <@ __sqrn_innerloop (k, 0, ((k + 1) %/ 2), a, x);
      if (((k %% 2) = 0)) {
        t0 <- a.[(k %/ 2)];
        (t1, t0) <- mulu_64 t0 t0;
        x <@ bNUTIL__addacc3 (t1, t0, x, k);
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
      x <@ __sqrn_innerloop (k, ((k - nlimbs) + 1), ((k + 1) %/ 2), a, x);
      if (((k %% 2) = 0)) {
        t0 <- a.[(k %/ 2)];
        (t1, t0) <- mulu_64 t0 t0;
        x <@ bNUTIL__addacc3 (t1, t0, x, k);
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
  
  proc _sqrn (a:W64.t Ap1.t, r:W64.t Ap2.t) : W64.t Ap2.t = {
    
    
    
    r <@ __sqrn (a, r);
    return (r);
  }
  
  proc __cminusP (lastbit:W64.t, x:W64.t Ap1.t, mP:W64.t Ap1.t) : 
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
    _tmp <@ __copy (x);
    tmp <- _tmp;
    (_cf, tmp) <@ __addU (tmp, mP);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) _cf;
    ( _1, _cf,  _2,  _3,  _4,  _5) <- NEG_64 lastbit;
    x <@ __cmov (_cf, x, tmp);
    return (x);
  }
  
  proc __mont_redM (a:W64.t Ap2.t, r:W64.t Ap1.t,
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
      x <@ __muln_innerloop (k, 0, k, r, p, x);
      zero <- (W64.of_int 0);
      t0 <- a.[k];
      x <@ bNUTIL__addacc3 (zero, t0, x, k);
      t0 <- x.[(k %% 3)];
      ( _0, t0) <- mulu_64 t0 _U0;
      r.[k] <- t0;
      (t1, t0) <- mulu_64 t0 _P.[0];
      x <@ bNUTIL__addacc3 (t1, t0, x, k);
      k <- k + 1;
    }
    aux <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux) {
      p <- _P;
      x <@ __muln_innerloop (k, ((k - nlimbs) + 1), nlimbs, r, p, x);
      zero <- (W64.of_int 0);
      t0 <- a.[k];
      x <@ bNUTIL__addacc3 (zero, t0, x, k);
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
    r <@ __cminusP (lastbit, r, mP);
    return (r);
  }
  
  proc __pack2 (lo:W64.t Ap1.t, hi:W64.t Ap1.t, r:W64.t Ap2.t) : 
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
}.

