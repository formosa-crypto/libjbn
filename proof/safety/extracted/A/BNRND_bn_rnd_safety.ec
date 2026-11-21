require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import Array11 Array88 BArray88.

module type Syscall_t = {
  proc randombytes_88 (_:BArray88.t) : BArray88.t
}.

module Syscall : Syscall_t = {
  proc randombytes_88 (a:BArray88.t) : BArray88.t = {
    
    a <$ BArray88.darray;
    return a;
  }
}.

module M(SC:Syscall_t) = {
  var tmp__trace : trace
  proc h__BN____ltc1_cf (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                         b_b:BArray88.t, cf:bool) : bool * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____ltc1_cf:trace;
    trace_h__BN____ltc1_cf <- [];
    trace_h__BN____ltc1_cf <-
    (trace_h__BN____ltc1_cf ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN____ltc1_cf <-
    (trace_h__BN____ltc1_cf ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    i <- 1;
    while ((i < 11)) {
      trace_h__BN____ltc1_cf <-
      (trace_h__BN____ltc1_cf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__BN____ltc1_cf <-
      (trace_h__BN____ltc1_cf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (cf, t) <- (sbb_64 t (BArray88.get64 b i) cf);
      i <- (i + 1);
    }
    return (cf, trace_h__BN____ltc1_cf);
  }
  proc h__BN___ltc1_cf (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, cf:bool) : bool * trace = {
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___ltc1_cf:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___ltc1_cf <- [];
    trace_h__BN___ltc1_cf <-
    (trace_h__BN___ltc1_cf ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___ltc1_cf <-
    (trace_h__BN___ltc1_cf ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN____ltc1_cf (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___ltc1_cf <- (trace_h__BN___ltc1_cf ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___ltc1_cf);
  }
  proc h__BN___ltc1_cf_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                         b_b:BArray88.t, cf:bool) : bool * trace = {
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___ltc1_cf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___ltc1_cf_ <- [];
    trace_h__BN___ltc1_cf_ <-
    (trace_h__BN___ltc1_cf_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___ltc1_cf_ <-
    (trace_h__BN___ltc1_cf_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN___ltc1_cf (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___ltc1_cf_ <- (trace_h__BN___ltc1_cf_ ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___ltc1_cf_);
  }
  proc h__BN___lt_cf_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                       b_b:BArray88.t) : bool * trace = {
    var t:W64.t;
    var cf:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___lt_cf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___lt_cf_ <- [];
    trace_h__BN___lt_cf_ <-
    (trace_h__BN___lt_cf_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___lt_cf_ <-
    (trace_h__BN___lt_cf_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    t <- (BArray88.get64 a 0);
    (cf, t) <- (sbb_64 t (BArray88.get64 b 0) false);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN___ltc1_cf_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___lt_cf_ <- (trace_h__BN___lt_cf_ ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___lt_cf_);
  }
  proc h__RND___rnd_ (a:BArray88.t, b_a:BArray88.t) : BArray88.t *
                                                      BArray88.t * trace = {
    var trace_h__RND___rnd_:trace;
    trace_h__RND___rnd_ <- [];
    a <- a;
    a <@ SC.randombytes_88 (a);
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__RND___rnd_);
  }
  proc h__RND____bnd_mask (mask:BArray88.t, b_mask:BArray88.t,
                           bnd:BArray88.t, b_bnd:BArray88.t) : BArray88.t *
                                                               BArray88.t *
                                                               trace = {
    var hi:W64.t;
    var i:int;
    var w:W64.t;
    var t:W64.t;
    var trace_h__RND____bnd_mask:trace;
    trace_h__RND____bnd_mask <- [];
    trace_h__RND____bnd_mask <-
    (trace_h__RND____bnd_mask ++ [(Assert, (BArray88.is_init b_bnd 0 88))]);
    hi <- (W64.of_int 0);
    i <- (11 - 1);
    while (((-1) < i)) {
      trace_h__RND____bnd_mask <-
      (trace_h__RND____bnd_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      w <- (BArray88.get64 bnd i);
      t <- w;
      t <- (t `>>` (W8.of_int 1));
      w <- (w `|` t);
      t <- w;
      t <- (t `>>` (W8.of_int 2));
      w <- (w `|` t);
      t <- w;
      t <- (t `>>` (W8.of_int 4));
      w <- (w `|` t);
      t <- w;
      t <- (t `>>` (W8.of_int 8));
      w <- (w `|` t);
      t <- w;
      t <- (t `>>` (W8.of_int 16));
      w <- (w `|` t);
      t <- w;
      t <- (t `>>` (W8.of_int 32));
      w <- (w `|` t);
      w <- (w `|` hi);
      trace_h__RND____bnd_mask <-
      (trace_h__RND____bnd_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_mask <-
      (BArray88.set64d b_mask (i * 8) (W64.of_int 18446744073709551615));
      mask <- (BArray88.set64 mask i w);
      t <- w;
      t <- (- t);
      t <- (t `|` w);
      t <- (t `|>>` (W8.of_int 63));
      hi <- (hi `|` t);
      i <- (i - 1);
    }
    return (mask, b_mask, trace_h__RND____bnd_mask);
  }
  proc h__RND___rsample_ (a:BArray88.t, b_a:BArray88.t, bnd:BArray88.t,
                          b_bnd:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__mask:BArray88.t;
    var b_mask:BArray88.t;
    var mask:BArray88.t;
    var _mask:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var i:int;
    var t:W64.t;
    var param_2:BArray88.t;
    var param_3:BArray88.t;
    var result_1:bool;
    var cf:bool;
    var trace_h__RND___rsample_:trace;
    _mask <- witness;
    b__mask <- witness;
    b_mask <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    mask <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__RND___rsample_ <- [];
    trace_h__RND___rsample_ <-
    (trace_h__RND___rsample_ ++ [(Assert, (BArray88.is_init b_bnd 0 88))]);
    b__mask <- (BArray88.init_arr (W8.of_int 0));
    b_mask <- b__mask;
    mask <- _mask;
    b_param <- b_mask;
    param <- mask;
    param_0 <- bnd;
    (aux, aux_0, tmp__trace) <@ h__RND____bnd_mask (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__RND___rsample_ <- (trace_h__RND___rsample_ ++ tmp__trace);
    trace_h__RND___rsample_ <-
    (trace_h__RND___rsample_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    mask <- result;
    _mask <- mask;
    b_param_0 <- b_a;
    param_1 <- a;
    (aux_3, aux_4, tmp__trace) <@ h__RND___rnd_ (param_1, b_param_0);
    result_0 <- aux_3;
    b_result_0 <- aux_4;
    trace_h__RND___rsample_ <- (trace_h__RND___rsample_ ++ tmp__trace);
    trace_h__RND___rsample_ <-
    (trace_h__RND___rsample_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b_a <- (BArray88.init_arr (W8.of_int 255));
    a <- result_0;
    i <- 0;
    while ((i < 11)) {
      trace_h__RND___rsample_ <-
      (trace_h__RND___rsample_ ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 _mask i);
      trace_h__RND___rsample_ <-
      (trace_h__RND___rsample_ ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__RND___rsample_ <-
      (trace_h__RND___rsample_ ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_a <- (BArray88.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray88.set64 a i ((BArray88.get64 a i) `&` t));
      i <- (i + 1);
    }
    param_2 <- a;
    param_3 <- bnd;
    (result_1, tmp__trace) <@ h__BN___lt_cf_ (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__RND___rsample_ <- (trace_h__RND___rsample_ ++ tmp__trace);
    cf <- result_1;
    while ((! cf)) {
      b_param_0 <- b_a;
      param_1 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__RND___rnd_ (param_1, b_param_0);
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__RND___rsample_ <- (trace_h__RND___rsample_ ++ tmp__trace);
      trace_h__RND___rsample_ <-
      (trace_h__RND___rsample_ ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      b_a <- (BArray88.init_arr (W8.of_int 255));
      a <- result_0;
      i <- 0;
      while ((i < 11)) {
        trace_h__RND___rsample_ <-
        (trace_h__RND___rsample_ ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
        t <- (BArray88.get64 _mask i);
        trace_h__RND___rsample_ <-
        (trace_h__RND___rsample_ ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
        trace_h__RND___rsample_ <-
        (trace_h__RND___rsample_ ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
        b_a <-
        (BArray88.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
        a <- (BArray88.set64 a i ((BArray88.get64 a i) `&` t));
        i <- (i + 1);
      }
      param_2 <- a;
      param_3 <- bnd;
      (result_1, tmp__trace) <@ h__BN___lt_cf_ (param_2,
      (BArray88.init_arr (W8.of_int 255)), param_3,
      (BArray88.init_arr (W8.of_int 255)));
      trace_h__RND___rsample_ <- (trace_h__RND___rsample_ ++ tmp__trace);
      cf <- result_1;
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__RND___rsample_);
  }
}.

(* The post and trace are valid. *)

op h__BN____ltc1_cf_spec _a _b_a _b _b_b _cf =
   hoare [M(Syscall).h__BN____ltc1_cf :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN___ltc1_cf_spec _a _b_a _b _b_b _cf =
   hoare [M(Syscall).h__BN___ltc1_cf :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN___ltc1_cf__spec _a _b_a _b _b_b _cf =
   hoare [M(Syscall).h__BN___ltc1_cf_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN___lt_cf__spec _a _b_a _b _b_b =
   hoare [M(Syscall).h__BN___lt_cf_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__RND___rnd__spec _a _b_a =
   hoare [M(Syscall).h__RND___rnd_ :
   (((_b_a = b_a) /\ (_a = a)) /\ true) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__RND____bnd_mask_spec _mask _b_mask _bnd _b_bnd =
   hoare [M(Syscall).h__RND____bnd_mask :
   (((_b_bnd = b_bnd) /\
    ((_bnd = bnd) /\ ((_b_mask = b_mask) /\ (_mask = mask)))) /\
   (BArray88.is_init _b_bnd 0 (8 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__RND___rsample__spec _a _b_a _bnd _b_bnd =
   hoare [M(Syscall).h__RND___rsample_ :
   (((_b_bnd = b_bnd) /\ ((_bnd = bnd) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   (BArray88.is_init _b_bnd 0 (8 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].
