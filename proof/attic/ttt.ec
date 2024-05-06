require import AllCore Int IntDiv List StdOrder Bool.


from Jasmin require import JModel_x86.
import SLH64.


require import Array3.
require import JBigNum.


abstract theory BigN.

op nlimbs: int.
axiom gt0_nlimbs: 0 < nlimbs.

clone BN as BN2
 with op nlimbs <- 2*nlimbs
      proof gt0_nlimbs by smt(gt0_nlimbs).

clone export BN
 with op nlimbs <- nlimbs
      proof gt0_nlimbs by exact gt0_nlimbs.

end BigN.



abstract theory Bn_base.

clone include BigN.
import BN2.

print BN.t.

module BNbase = {
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
  
  proc bN__load (ap:W64.t, a:BN.t) : BN.t = {
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
  
  proc bN__store (ap:W64.t, a:BN.t) : unit = {
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
  
  proc bN__eq_zf (a:BN.t, b:BN.t) : bool = {
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
  
  proc bN__eq (a:BN.t, b:BN.t) : W64.t = {
    
    var res_0:W64.t;
    var zf:bool;
    var are_equal:W64.t;
    
    zf <@ bN__eq_zf (a, b);
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc bN_eq (a:BN.t, b:BN.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ bN__eq (a, b);
    return (r);
  }
  
  proc bN_eq_ (a:BN.t, b:BN.t) : W64.t = {
    
    var r:W64.t;
    
    a <- a;
    b <- b;
    r <@ bN_eq (a, b);
    r <- r;
    return (r);
  }
  
  proc bN__test0_zf (a:BN.t) : bool = {
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
  
  proc bN__test0 (a:BN.t) : W64.t = {
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var zf:bool;
    
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    zf <@ bN__test0_zf (a);
    res_0 <- (zf ? is_zero : res_0);
    return (res_0);
  }
  
  proc bN_test0 (a:BN.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ bN__test0 (a);
    return (r);
  }
  
  proc bN__copy (a:BN.t) : BN.t = {
    var aux: int;
    
    var r:BN.t;
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
  
  proc bN__copy2 (a:BN.t, r:BN.t) : BN.t = {
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
  
  proc bN__cmov (cond:bool, a:BN.t, b:BN.t) : BN.t = {
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
  
  proc bN__fill (x:W64.t, a:BN.t) : BN.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- x;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN__set0 (a:BN.t) : BN.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int 0);
    a <@ bN__fill (t, a);
    return (a);
  }
  
  proc bN__cfill (b:bool, x:W64.t, a:BN.t) : BN.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < nlimbs) {
      a.[i] <- x;
      i <- i + 1;
    }
    return (a);
  }
  
  proc bN__seterr (b:bool, a:BN.t) : BN.t = {
    
    var t:W64.t;
    
    t <- (W64.of_int (- 1));
    a <@ bN__cfill (b, t, a);
    return (a);
  }
  
  proc bN__add1U (a:BN.t, b:W64.t) : bool * BN.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- adc_64 a.[0] b false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < nlimbs) {
      (aux, aux_0) <- adc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bN__addU (a:BN.t, b:BN.t) : bool * BN.t = {
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
  
  proc bN_addU (a:BN.t, b:BN.t) : bool * BN.t = {
    
    var cf:bool;
    
    (cf, a) <@ bN__addU (a, b);
    return (cf, a);
  }
  
  proc bN__subU (a:BN.t, b:BN.t) : bool * BN.t = {
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
  
  proc bN__lt_cf (a:BN.t, b:BN.t) : bool = {
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
  
  proc bN_subU (a:BN.t, b:BN.t) : bool * BN.t = {
    
    var cf:bool;
    
    (cf, a) <@ bN__subU (a, b);
    return (cf, a);
  }
  
(*
  proc bN__rnd (a:BN.t) : BN.t = {
    var aux: W8.t Array64.t;
    
    
    
    aux <@ SC.randombytes_64 ((Array64.init (fun i => get8
                              (WArray64.init64 (fun i => (a).[i])) i)));
    a <-
    (Array8.init (fun i => get64 (WArray64.init8 (fun i => (aux).[i])) i));
    return (a);
  }
*)
  proc bN__rnd (a:BN.t) : BN.t = {
    return witness;
  }
  proc bN__rsample (a:BN.t, bnd:BN.t) : BN.t = {
    
    var cf:bool;
    
    a <@ bN__rnd (a);
    cf <@ bN__lt_cf (a, bnd);
    while ((! cf)) {
      a <@ bN__rnd (a);
      cf <@ bN__lt_cf (a, bnd);
    }
    return (a);
  }
  
  proc bN__caddU (cf:bool, x:BN.t, y:BN.t) : BN.t = {
    var aux: int;
    
    var _tmp:BN.t;
    var t0:W64.t;
    var i:int;
    var t:W64.t;
    var tmp:BN.t;
    var  _0:bool;
    _tmp <- witness;
    tmp <- witness;
    _tmp <@ bN__copy (y);
    t0 <- (W64.of_int 0);
    i <- 0;
    while (i < nlimbs) {
      t <- _tmp.[i];
      t <- ((! cf) ? t0 : t);
      _tmp.[i] <- t;
      i <- i + 1;
    }
    tmp <- _tmp;
    ( _0, x) <@ bN__addU (x, tmp);
    return (x);
  }
  
  proc bN__muln_innerloop (k:int, istart:int, iend:int, a:BN.t,
                           b:BN.t, x:W64.t Array3.t) : W64.t Array3.t = {
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
  
  proc bN__muln (a:BN.t, b:BN.t, r:BN2.t) : 
  BN2.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_5: int;
    var aux_4: W64.t;
    
    var t0:W64.t;
    var t1:W64.t;
    var x:W64.t Array3.t;
    var k:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    x <- witness;
    t0 <- a.[0];
    (t1, t0) <- mulu_64 t0 b.[0];
    r.[0] <- t0;
    x.[1] <- t1;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    x.[2] <- aux_4;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _5 <- aux_3;
     _6 <- aux_2;
     _7 <- aux_1;
     _8 <- aux_0;
     _9 <- aux;
    x.[0] <- aux_4;
    k <- 1;
    while (k < nlimbs) {
      x <@ bN__muln_innerloop (k, 0, (k + 1), a, b, x);
      t0 <- x.[(k %% 3)];
      (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
       _10 <- aux_3;
       _11 <- aux_2;
       _12 <- aux_1;
       _13 <- aux_0;
       _14 <- aux;
      x.[(k %% 3)] <- aux_4;
      r.[k] <- t0;
      k <- k + 1;
    }
    aux_5 <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux_5) {
      x <@ bN__muln_innerloop (k, ((k - nlimbs) + 1), nlimbs, a, b, x);
      t0 <- x.[(k %% 3)];
      (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
       _15 <- aux_3;
       _16 <- aux_2;
       _17 <- aux_1;
       _18 <- aux_0;
       _19 <- aux;
      x.[(k %% 3)] <- aux_4;
      r.[k] <- t0;
      k <- k + 1;
    }
    r.[((2 * nlimbs) - 1)] <- x.[(((2 * nlimbs) - 1) %% 3)];
    return (r);
  }
  
  proc bN_muln (a:BN.t, b:BN.t, r:BN2.t) : 
  BN2.t = {
    
    
    
    r <@ bN__muln (a, b, r);
    return (r);
  }
  
  proc bN__cminusP (lastbit:W64.t, x:BN.t, mP:BN.t) : 
  BN.t = {
    
    var _tmp:BN.t;
    var tmp:BN.t;
    var _cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:W64.t;
    _tmp <- witness;
    tmp <- witness;
    _tmp <@ bN__copy (x);
    tmp <- _tmp;
    (_cf, tmp) <@ bN__addU (tmp, mP);
    ( _0, lastbit) <- adc_64 lastbit (W64.of_int 0) _cf;
    ( _1, _cf,  _2,  _3,  _4,  _5) <- NEG_64 lastbit;
    x <@ bN__cmov (_cf, x, tmp);
    return (x);
  }
  
  proc bN__mont_redM (a:BN2.t, r:BN.t, _P:BN.t,
                      _mP:BN.t, _U0:W64.t) : BN.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_5: int;
    var aux_4: W64.t;
    
    var x:W64.t Array3.t;
    var p:BN.t;
    var k:int;
    var zero:W64.t;
    var t0:W64.t;
    var t1:W64.t;
    var lastbit:W64.t;
    var cf:bool;
    var mP:BN.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    var  _20:W64.t;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    var  _24:bool;
    var  _25:bool;
    var  _26:bool;
    var  _27:bool;
    var  _28:bool;
    var  _29:bool;
    var  _30:bool;
    var  _31:bool;
    p <- witness;
    mP <- witness;
    x <- witness;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    x.[0] <- aux_4;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _5 <- aux_3;
     _6 <- aux_2;
     _7 <- aux_1;
     _8 <- aux_0;
     _9 <- aux;
    x.[1] <- aux_4;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _10 <- aux_3;
     _11 <- aux_2;
     _12 <- aux_1;
     _13 <- aux_0;
     _14 <- aux;
    x.[2] <- aux_4;
    k <- 0;
    while (k < nlimbs) {
      p <- _P;
      x <@ bN__muln_innerloop (k, 0, k, r, p, x);
      ( _15,  _16,  _17,  _18,  _19, zero) <- set0_64 ;
      t0 <- a.[k];
      x <@ bNUTIL__addacc3 (zero, t0, x, k);
      t0 <- x.[(k %% 3)];
      ( _20, t0) <- mulu_64 t0 _U0;
      r.[k] <- t0;
      (t1, t0) <- mulu_64 t0 _P.[0];
      x <@ bNUTIL__addacc3 (t1, t0, x, k);
      k <- k + 1;
    }
    aux_5 <- ((2 * nlimbs) - 1);
    k <- nlimbs;
    while (k < aux_5) {
      p <- _P;
      x <@ bN__muln_innerloop (k, ((k - nlimbs) + 1), nlimbs, r, p, x);
      ( _21,  _22,  _23,  _24,  _25, zero) <- set0_64 ;
      t0 <- a.[k];
      x <@ bNUTIL__addacc3 (zero, t0, x, k);
      t0 <- x.[(k %% 3)];
      r.[(k - nlimbs)] <- t0;
      (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
       _26 <- aux_3;
       _27 <- aux_2;
       _28 <- aux_1;
       _29 <- aux_0;
       _30 <- aux;
      x.[(k %% 3)] <- aux_4;
      k <- k + 1;
    }
    lastbit <- (W64.of_int 0);
    (aux_3, aux_4) <- adc_64 x.[(((2 * nlimbs) - 1) %% 3)] a.[((2 * nlimbs) - 1)]
    false;
    cf <- aux_3;
    x.[(((2 * nlimbs) - 1) %% 3)] <- aux_4;
    ( _31, lastbit) <- adc_64 lastbit (W64.of_int 0) cf;
    r.[(nlimbs - 1)] <- x.[(((2 * nlimbs) - 1) %% 3)];
    mP <- _mP;
    r <@ bN__cminusP (lastbit, r, mP);
    return (r);
  }
  
  proc bNBASE_toec (ap:W64.t) : unit = {
    
    var a:BN.t;
    var b:BN.t;
    var x:W64.t;
    var _x:W64.t;
    var cf:bool;
    var c:BN2.t;
    a <- witness;
    b <- witness;
    c <- witness;
    a <@ bN__load (ap, a);
    b <@ bN__load (ap, a);
    bN__store (ap, a);
    x <@ bN_eq_ (a, b);
    _x <- x;
    x <@ bN_test0 (a);
    b <@ bN__copy (a);
    b <@ bN__copy2 (a, b);
    (cf, a) <@ bN__add1U (a, x);
    a <@ bN__cmov (cf, a, b);
    a <@ bN__seterr (cf, a);
    a <@ bN__set0 (a);
    (cf, a) <@ bN_addU (a, b);
    (cf, a) <@ bN_subU (a, b);
    cf <@ bN__lt_cf (a, b);
    a <@ bN__caddU (cf, a, b);
    a <@ bN__rsample (a, b);
    c <@ bN_muln (a, b, c);
    a <@ bN__mont_redM (c, a, b, b, _x);
    return ();
  }
}.

hoare set_h: BNbase.bN__set0 : true ==> bn res = 0.
admitted.

(*
hoare muln_h _x _y: BNbase.bN_muln : x=_x /\  y=_y ==> BN2.bn res = bn _x * bn _y.
admitted.
*)

end Bn_base.


abstract theory Bn_mont.

clone import Bn_base as BNB.

op glob_P: BN.t.

module BNmont = {
 proc redM(x: BN2.t): BN.t = {
  var z;
  z <@ BNbase.set0(z);
  return z;
 }
}.

hoare redM_h _x: BNmont.redM : x=_x ==> bn res = BN2.bn _x %% bn glob_P.
admitted.

end Bn_mont.

abstract theory Fp_base.

clone export Bn_base as BNB.

op bn_red: int -> int.

module type FPbaseP = {
 proc red(x: BN2.t): BN.t
}.

module FPbase (P: FPbaseP) = {
 proc mulm(x y: BN.t): BN.t = {
  var z;
  z <@ BNbase.muln(x, y);
  y <@ P.red(z);
  return y;
 }
}.

lemma mulm_h (P <: FPbaseP) _x _y:
 (forall _x, hoare [ P.red : x=_x ==> bn res = bn_red (BN2.bn _x) ]) =>
 hoare [FPbase(P).mulm : x=_x /\ y=_y ==> bn res = bn_red (bn _x * bn _y) ].
admitted.

end Fp_base.

abstract theory Fp.

clone export Bn_base as BNB.

op glob_P: BN.t.
clone Bn_mont as BNM
 with theory BNB <- BNB,
      op glob_P <- glob_P.
clone Fp_base as FPB
 with theory BNB <- BNB.


module P = { proc red = BNM.BNmont.redM }.

module FP = {
 proc mulm(x y: BN.t): BN.t = {
  var z;
  z <@ FPB.FPbase(P).mulm(x, y);
  return z;
 }
}.

hoare mulm_h _x _y:
 FP.mulm : x=_x /\ y=_y ==> bn res = (bn _x * bn _y) %% bn glob_P.
admitted.

end Fp.

theory FP1.

(*
clone import BigN as BigN32
 with op nlimbs <- 32
      proof gt0_nlimbs by smt().
*)

clone export Bn_base as BNB
 with op nlimbs <= 32
      proof gt0_nlimbs by smt().

op cst: BN.t.

clone export Fp as FP
 with theory BNB <- BNB,
      op glob_P <- cst.

print FP.

end FP1.

