require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array3 Array11 Array22 Array24 Array44 Array88 Array176 Array352 BArray24
BArray88 BArray176 BArray352 SBArray176_88 SBArray352_88 SBArray352_176.

module M = {
  var tmp__trace : trace
  proc uTIL____mask_cf (mask:W64.t) : bool * trace = {
    var t:W64.t;
    var cf:bool;
    var trace_uTIL____mask_cf:trace;
    trace_uTIL____mask_cf <- [];
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t mask false);
    return (cf, trace_uTIL____mask_cf);
  }
  proc uTIL____cf_mask (cf:bool) : W64.t * trace = {
    var mask:W64.t;
    var  _0:bool;
    var trace_uTIL____cf_mask:trace;
    trace_uTIL____cf_mask <- [];
    mask <- (W64.of_int 0);
    ( _0, mask) <- (sbb_64 mask (W64.of_int 0) cf);
    return (mask, trace_uTIL____cf_mask);
  }
  proc uTIL____addacc3 (a:BArray24.t, b_a:BArray24.t, b1:W64.t, b0:W64.t,
                        k:int) : BArray24.t * BArray24.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var cf:bool;
    var trace_uTIL____addacc3:trace;
    trace_uTIL____addacc3 <- [];
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++ [(Assert, (BArray24.is_init b_a 0 24))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    (aux, aux_0) <- (adc_64 (BArray24.get64 a (k %% 3)) b0 false);
    cf <- aux;
    a <- (BArray24.set64 a (k %% 3) aux_0);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    (aux_1, aux_2) <- (adc_64 (BArray24.get64 a ((k + 1) %% 3)) b1 cf);
    cf <- aux_1;
    a <- (BArray24.set64 a ((k + 1) %% 3) aux_2);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3 <-
    (trace_uTIL____addacc3 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    (aux_3, aux_4) <-
    (adc_64 (BArray24.get64 a ((k + 2) %% 3)) (W64.of_int 0) cf);
    cf <- aux_3;
    a <- (BArray24.set64 a ((k + 2) %% 3) aux_4);
    b_a <- (BArray24.init_arr (W8.of_int 255));
    return (a, b_a, trace_uTIL____addacc3);
  }
  proc h__H__BN____cmov (a:BArray88.t, b_a:BArray88.t, cond:bool,
                         b:BArray88.t, b_b:BArray88.t) : BArray88.t *
                                                         BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____cmov:trace;
    trace_h__H__BN____cmov <- [];
    trace_h__H__BN____cmov <-
    (trace_h__H__BN____cmov ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__H__BN____cmov <-
    (trace_h__H__BN____cmov ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__H__BN____cmov <-
      (trace_h__H__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__H__BN____cmov <-
      (trace_h__H__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (cond ? (BArray88.get64 b i) : t);
      trace_h__H__BN____cmov <-
      (trace_h__H__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      a <- (BArray88.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN____cmov);
  }
  proc h__H__BN___cmov (a:BArray88.t, b_a:BArray88.t, cond:bool,
                        b:BArray88.t, b_b:BArray88.t) : BArray88.t *
                                                        BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var param:BArray88.t;
    var param_0:bool;
    var param_1:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__BN___cmov <- [];
    trace_h__H__BN___cmov <-
    (trace_h__H__BN___cmov ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__H__BN___cmov <-
    (trace_h__H__BN___cmov ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__BN____cmov (param,
    (BArray88.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___cmov <- (trace_h__H__BN___cmov ++ tmp__trace);
    trace_h__H__BN___cmov <-
    (trace_h__H__BN___cmov ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___cmov);
  }
  proc h__H__BN___cmov_ (a:BArray88.t, b_a:BArray88.t, cond:bool,
                         b:BArray88.t, b_b:BArray88.t) : BArray88.t *
                                                         BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var param:BArray88.t;
    var param_0:bool;
    var param_1:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__BN___cmov_ <- [];
    trace_h__H__BN___cmov_ <-
    (trace_h__H__BN___cmov_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__H__BN___cmov_ <-
    (trace_h__H__BN___cmov_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__BN___cmov (param,
    (BArray88.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__BN___cmov_ <- (trace_h__H__BN___cmov_ ++ tmp__trace);
    trace_h__H__BN___cmov_ <-
    (trace_h__H__BN___cmov_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___cmov_);
  }
  proc h__H__BN____carrypropU (a:BArray88.t, b_a:BArray88.t, cf:bool, k:int) : 
  bool * BArray88.t * BArray88.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var trace_h__H__BN____carrypropU:trace;
    trace_h__H__BN____carrypropU <- [];
    trace_h__H__BN____carrypropU <-
    (trace_h__H__BN____carrypropU ++
    [(Assert, ((0 <= k) /\ (BArray88.is_init b_a 0 88)))]);
    i <- k;
    while ((i < 11)) {
      trace_h__H__BN____carrypropU <-
      (trace_h__H__BN____carrypropU ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__H__BN____carrypropU <-
      (trace_h__H__BN____carrypropU ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (aux, aux_0) <- (adc_64 (BArray88.get64 a i) (W64.of_int 0) cf);
      cf <- aux;
      a <- (BArray88.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__H__BN____carrypropU);
  }
  proc h__H__BN____subc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                          b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                          cf:bool) : bool * BArray88.t * BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____subc1:trace;
    trace_h__H__BN____subc1 <- [];
    trace_h__H__BN____subc1 <-
    (trace_h__H__BN____subc1 ++
    [(Assert,
     (((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)) /\
     (BArray88.is_init b_b 0 88)))]);
    i <- 1;
    while ((i < 11)) {
      trace_h__H__BN____subc1 <-
      (trace_h__H__BN____subc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__H__BN____subc1 <-
      (trace_h__H__BN____subc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (cf, t) <- (sbb_64 t (BArray88.get64 b i) cf);
      trace_h__H__BN____subc1 <-
      (trace_h__H__BN____subc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__H__BN____subc1);
  }
  proc h__H__BN___subc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                         b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                         cf:bool) : bool * BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___subc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__H__BN___subc1 <- [];
    trace_h__H__BN___subc1 <-
    (trace_h__H__BN___subc1 ++
    [(Assert,
     (((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)) /\
     (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN____subc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___subc1 <- (trace_h__H__BN___subc1 ++ tmp__trace);
    trace_h__H__BN___subc1 <-
    (trace_h__H__BN___subc1 ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___subc1);
  }
  proc h__H__BN___subc1_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                          b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                          cf:bool) : bool * BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___subc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__H__BN___subc1_ <- [];
    trace_h__H__BN___subc1_ <-
    (trace_h__H__BN___subc1_ ++
    [(Assert,
     (((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)) /\
     (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___subc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___subc1_ <- (trace_h__H__BN___subc1_ ++ tmp__trace);
    trace_h__H__BN___subc1_ <-
    (trace_h__H__BN___subc1_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___subc1_);
  }
  proc h__H__BN___sub_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                        b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  bool * BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___sub_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__H__BN___sub_ <- [];
    trace_h__H__BN___sub_ <-
    (trace_h__H__BN___sub_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    t <- (BArray88.get64 a 0);
    (cf, t) <- (sbb_64 t (BArray88.get64 b 0) false);
    b_r <- (BArray88.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray88.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___subc1_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___sub_ <- (trace_h__H__BN___sub_ ++ tmp__trace);
    trace_h__H__BN___sub_ <-
    (trace_h__H__BN___sub_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___sub_);
  }
  proc h__H__BN____negc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                          b_a:BArray88.t, cf:bool) : bool * BArray88.t *
                                                     BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__H__BN____negc1:trace;
    trace_h__H__BN____negc1 <- [];
    trace_h__H__BN____negc1 <-
    (trace_h__H__BN____negc1 ++
    [(Assert, ((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)))]);
    i <- 1;
    while ((i < 11)) {
      t <- (W64.of_int 0);
      trace_h__H__BN____negc1 <-
      (trace_h__H__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (cf, t) <- (sbb_64 t (BArray88.get64 a i) cf);
      trace_h__H__BN____negc1 <-
      (trace_h__H__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__H__BN____negc1);
  }
  proc h__H__BN___negc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                         b_a:BArray88.t, cf:bool) : bool * BArray88.t *
                                                    BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___negc1 <- [];
    trace_h__H__BN___negc1 <-
    (trace_h__H__BN___negc1 ++
    [(Assert, ((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN____negc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___negc1 <- (trace_h__H__BN___negc1 ++ tmp__trace);
    trace_h__H__BN___negc1 <-
    (trace_h__H__BN___negc1 ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___negc1);
  }
  proc h__H__BN___negc1_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                          b_a:BArray88.t, cf:bool) : bool * BArray88.t *
                                                     BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___negc1_ <- [];
    trace_h__H__BN___negc1_ <-
    (trace_h__H__BN___negc1_ ++
    [(Assert, ((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___negc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___negc1_ <- (trace_h__H__BN___negc1_ ++ tmp__trace);
    trace_h__H__BN___negc1_ <-
    (trace_h__H__BN___negc1_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___negc1_);
  }
  proc h__H__BN___neg_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                        b_a:BArray88.t) : bool * BArray88.t * BArray88.t *
                                          trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__H__BN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__H__BN___neg_ <- [];
    trace_h__H__BN___neg_ <-
    (trace_h__H__BN___neg_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray88.get64 a 0) false);
    b_r <- (BArray88.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray88.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___negc1_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___neg_ <- (trace_h__H__BN___neg_ ++ tmp__trace);
    trace_h__H__BN___neg_ <-
    (trace_h__H__BN___neg_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__H__BN___neg_);
  }
  proc h__H__BN___cnegU_ (a:BArray88.t, b_a:BArray88.t, cond:W64.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux:bool;
    var b__x:BArray88.t;
    var b_x:BArray88.t;
    var x:BArray88.t;
    var _x:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var param_1:W64.t;
    var result_1:bool;
    var cf:bool;
    var param_2:BArray88.t;
    var param_3:bool;
    var param_4:BArray88.t;
    var result_2:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__H__BN___cnegU_:trace;
    _x <- witness;
    b__x <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_x <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    x <- witness;
    trace_h__H__BN___cnegU_ <- [];
    trace_h__H__BN___cnegU_ <-
    (trace_h__H__BN___cnegU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b__x <- (BArray88.init_arr (W8.of_int 0));
    b_x <- b__x;
    x <- _x;
    b_param <- b_x;
    param <- x;
    param_0 <- a;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___neg_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__H__BN___cnegU_ <- (trace_h__H__BN___cnegU_ ++ tmp__trace);
    trace_h__H__BN___cnegU_ <-
    (trace_h__H__BN___cnegU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    x <- result_0;
    param_1 <- cond;
    (result_1, tmp__trace) <@ uTIL____mask_cf (param_1);
    trace_h__H__BN___cnegU_ <- (trace_h__H__BN___cnegU_ ++ tmp__trace);
    cf <- result_1;
    param_2 <- a;
    param_3 <- cf;
    param_4 <- x;
    (aux_2, aux_3, tmp__trace) <@ h__H__BN___cmov_ (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray88.init_arr (W8.of_int 255)));
    result_2 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__H__BN___cnegU_ <- (trace_h__H__BN___cnegU_ ++ tmp__trace);
    trace_h__H__BN___cnegU_ <-
    (trace_h__H__BN___cnegU_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_2;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__H__BN___cnegU_);
  }
  proc h__H__MUL____muln_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                    istart:int, iend:int, a:BArray88.t,
                                    b_a:BArray88.t, b:BArray88.t,
                                    b_b:BArray88.t) : BArray24.t *
                                                      BArray24.t * trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var inc:int;
    var i:int;
    var j:int;
    var t0:W64.t;
    var t1:W64.t;
    var param:BArray24.t;
    var param_0:W64.t;
    var param_1:W64.t;
    var param_2:int;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var trace_h__H__MUL____muln_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__H__MUL____muln_innerloop <- [];
    trace_h__H__MUL____muln_innerloop <-
    (trace_h__H__MUL____muln_innerloop ++
    [(Assert,
     (((((((0 <= istart) /\ (iend <= 11)) /\ (0 <= (k - (iend - 1)))) /\
        ((k - istart) < 11)) /\
       (BArray24.is_init b_x 0 24)) /\
      (BArray88.is_init b_a (8 * istart) (8 * (iend - istart)))) /\
     (BArray88.is_init b_b 0 88)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__H__MUL____muln_innerloop <-
      (trace_h__H__MUL____muln_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__H__MUL____muln_innerloop <-
      (trace_h__H__MUL____muln_innerloop ++
      [(Assert, (BArray88.is_init b_a (i * 8) 8))]);
      t0 <- (BArray88.get64 a i);
      trace_h__H__MUL____muln_innerloop <-
      (trace_h__H__MUL____muln_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      (t1, t0) <- (mulu_64 t0 (BArray88.get64 b j));
      param <- x;
      param_0 <- t1;
      param_1 <- t0;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL____muln_innerloop <-
      (trace_h__H__MUL____muln_innerloop ++ tmp__trace);
      trace_h__H__MUL____muln_innerloop <-
      (trace_h__H__MUL____muln_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__H__MUL____muln_innerloop);
  }
  proc h__H__MUL____ps_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                             b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var inc:int;
    var b_x:BArray24.t;
    var t0:W64.t;
    var t1:W64.t;
    var x:BArray24.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var b_param_0:BArray24.t;
    var param_5:BArray24.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:BArray88.t;
    var param_10:BArray88.t;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var trace_h__H__MUL____ps_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_x <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_10 <- witness;
    result <- witness;
    result_0 <- witness;
    x <- witness;
    trace_h__H__MUL____ps_muln <- [];
    trace_h__H__MUL____ps_muln <-
    (trace_h__H__MUL____ps_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray88.get64 a 0);
    (t1, t0) <- (mulu_64 t0 (BArray88.get64 b 0));
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 11)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- (k + 1);
      param_3 <- a;
      param_4 <- b;
      (aux, aux_0, tmp__trace) <@ h__H__MUL____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray88.init_arr (W8.of_int 255)), param_4,
      (BArray88.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++ tmp__trace);
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 11) - 1);
    k <- 11;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_5 <- x;
      param_6 <- k;
      param_7 <- ((k - 11) + 1);
      param_8 <- 11;
      param_9 <- a;
      param_10 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__H__MUL____muln_innerloop (param_5,
      b_param_0, param_6, param_7, param_8, param_9,
      (BArray88.init_arr (W8.of_int 255)), param_10,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++ tmp__trace);
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_0;
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__H__MUL____ps_muln <-
      (trace_h__H__MUL____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__H__MUL____ps_muln <-
    (trace_h__H__MUL____ps_muln ++
    [(Assert,
     ((0 <= (((2 * 11) - 1) * 8)) /\ (((((2 * 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__H__MUL____ps_muln <-
    (trace_h__H__MUL____ps_muln ++
    [(Assert,
     ((0 <= ((((2 * 11) - 1) %% 3) * 8)) /\
     ((((((2 * 11) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__H__MUL____ps_muln <-
    (trace_h__H__MUL____ps_muln ++
    [(Assert, (BArray24.is_init b_x ((((2 * 11) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray176.set64 r ((2 * 11) - 1)
    (BArray24.get64 x (((2 * 11) - 1) %% 3)));
    return (r, b_r, trace_h__H__MUL____ps_muln);
  }
  proc h__H__MUL___ps_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                            b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__H__MUL___ps_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL___ps_muln <- [];
    trace_h__H__MUL___ps_muln <-
    (trace_h__H__MUL___ps_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL____ps_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL___ps_muln <- (trace_h__H__MUL___ps_muln ++ tmp__trace);
    trace_h__H__MUL___ps_muln <-
    (trace_h__H__MUL___ps_muln ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL___ps_muln);
  }
  proc h__H__MUL___ps_muln_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                             b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__H__MUL___ps_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__H__MUL___ps_muln_ <- [];
    trace_h__H__MUL___ps_muln_ <-
    (trace_h__H__MUL___ps_muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL___ps_muln (param, b_param, 
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__H__MUL___ps_muln_ <- (trace_h__H__MUL___ps_muln_ ++ tmp__trace);
    trace_h__H__MUL___ps_muln_ <-
    (trace_h__H__MUL___ps_muln_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__H__MUL___ps_muln_);
  }
  proc h__BN____load (a:BArray176.t, b_a:BArray176.t, ap:W64.t) : BArray176.t *
                                                                  BArray176.t *
                                                                  trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____load:trace;
    trace_h__BN____load <- [];
    trace_h__BN____load <-
    (trace_h__BN____load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 22)))]);
    i <- 0;
    while ((i < 22)) {
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      b_a <-
      (BArray176.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray176.set64 a i t);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____load);
  }
  proc h__BN___load (a:BArray176.t, b_a:BArray176.t, ap:W64.t) : BArray176.t *
                                                                 BArray176.t *
                                                                 trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___load:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load <- [];
    trace_h__BN___load <-
    (trace_h__BN___load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 22)))]);
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN____load (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___load <- (trace_h__BN___load ++ tmp__trace);
    trace_h__BN___load <-
    (trace_h__BN___load ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    a <- result;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load);
  }
  proc h__BN___load_ (a:BArray176.t, b_a:BArray176.t, ap:W64.t) : BArray176.t *
                                                                  BArray176.t *
                                                                  trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___load_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load_ <- [];
    trace_h__BN___load_ <-
    (trace_h__BN___load_ ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 22)))]);
    b_a <- b_a;
    a <- a;
    ap <- ap;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___load_ <- (trace_h__BN___load_ ++ tmp__trace);
    trace_h__BN___load_ <-
    (trace_h__BN___load_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    a <- result;
    a <- a;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load_);
  }
  proc h__BN____cmov (a:BArray176.t, b_a:BArray176.t, cond:bool,
                      b:BArray176.t, b_b:BArray176.t) : BArray176.t *
                                                        BArray176.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____cmov:trace;
    trace_h__BN____cmov <- [];
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    i <- 0;
    while ((i < 22)) {
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      t <- (BArray176.get64 a i);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      t <- (cond ? (BArray176.get64 b i) : t);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      a <- (BArray176.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____cmov);
  }
  proc h__BN___cmov (a:BArray176.t, b_a:BArray176.t, cond:bool,
                     b:BArray176.t, b_b:BArray176.t) : BArray176.t *
                                                       BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var param:BArray176.t;
    var param_0:bool;
    var param_1:BArray176.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov <- [];
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN____cmov (param,
    (BArray176.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray176.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov <- (trace_h__BN___cmov ++ tmp__trace);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    a <- result;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov);
  }
  proc h__BN___cmov_ (a:BArray176.t, b_a:BArray176.t, cond:bool,
                      b:BArray176.t, b_b:BArray176.t) : BArray176.t *
                                                        BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var param:BArray176.t;
    var param_0:bool;
    var param_1:BArray176.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov_ <- [];
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN___cmov (param,
    (BArray176.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray176.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov_ <- (trace_h__BN___cmov_ ++ tmp__trace);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    a <- result;
    a <- a;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov_);
  }
  proc h__BN____addc1U (a:BArray176.t, b_a:BArray176.t, b:BArray176.t,
                        b_b:BArray176.t, cf:bool) : bool * BArray176.t *
                                                    BArray176.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1U:trace;
    trace_h__BN____addc1U <- [];
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    i <- 1;
    while ((i < 22)) {
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      t <- (BArray176.get64 b i);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      (aux, aux_0) <- (adc_64 (BArray176.get64 a i) t cf);
      cf <- aux;
      a <- (BArray176.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____addc1U);
  }
  proc h__BN___addc1U (a:BArray176.t, b_a:BArray176.t, b:BArray176.t,
                       b_b:BArray176.t, cf:bool) : bool * BArray176.t *
                                                   BArray176.t * trace = {
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux:bool;
    var param:BArray176.t;
    var param_0:BArray176.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___addc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U <- [];
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1U (param,
    (BArray176.init_arr (W8.of_int 255)), param_0,
    (BArray176.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U <- (trace_h__BN___addc1U ++ tmp__trace);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U);
  }
  proc h__BN___addc1U_ (a:BArray176.t, b_a:BArray176.t, b:BArray176.t,
                        b_b:BArray176.t, cf:bool) : bool * BArray176.t *
                                                    BArray176.t * trace = {
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux:bool;
    var param:BArray176.t;
    var param_0:BArray176.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___addc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U_ <- [];
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1U (param,
    (BArray176.init_arr (W8.of_int 255)), param_0,
    (BArray176.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U_ <- (trace_h__BN___addc1U_ ++ tmp__trace);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U_);
  }
  proc h__BN___addU_ (a:BArray176.t, b_a:BArray176.t, b:BArray176.t,
                      b_b:BArray176.t) : bool * BArray176.t * BArray176.t *
                                         trace = {
    var aux_2:BArray176.t;
    var aux_3:BArray176.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray176.t;
    var param_0:BArray176.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___addU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addU_ <- [];
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray176.is_init b_b 0 176))]);
    t <- (BArray176.get64 b 0);
    (aux, aux_0) <- (adc_64 (BArray176.get64 a 0) t false);
    cf <- aux;
    a <- (BArray176.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___addc1U_ (param,
    (BArray176.init_arr (W8.of_int 255)), param_0,
    (BArray176.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___addU_ <- (trace_h__BN___addU_ ++ tmp__trace);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray176.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addU_);
  }
  proc h__BN____negc1 (r:BArray176.t, b_r:BArray176.t, a:BArray176.t,
                       b_a:BArray176.t, cf:bool) : bool * BArray176.t *
                                                   BArray176.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____negc1:trace;
    trace_h__BN____negc1 <- [];
    trace_h__BN____negc1 <-
    (trace_h__BN____negc1 ++
    [(Assert, ((BArray176.is_init b_r 0 8) /\ (BArray176.is_init b_a 0 176)))]);
    i <- 1;
    while ((i < 22)) {
      t <- (W64.of_int 0);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      (cf, t) <- (sbb_64 t (BArray176.get64 a i) cf);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____negc1);
  }
  proc h__BN___negc1 (r:BArray176.t, b_r:BArray176.t, a:BArray176.t,
                      b_a:BArray176.t, cf:bool) : bool * BArray176.t *
                                                  BArray176.t * trace = {
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux:bool;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray176.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1 <- [];
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++
    [(Assert, ((BArray176.is_init b_r 0 8) /\ (BArray176.is_init b_a 0 176)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____negc1 (param, b_param,
    param_0, (BArray176.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1 <- (trace_h__BN___negc1 ++ tmp__trace);
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1);
  }
  proc h__BN___negc1_ (r:BArray176.t, b_r:BArray176.t, a:BArray176.t,
                       b_a:BArray176.t, cf:bool) : bool * BArray176.t *
                                                   BArray176.t * trace = {
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux:bool;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray176.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1_ <- [];
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++
    [(Assert, ((BArray176.is_init b_r 0 8) /\ (BArray176.is_init b_a 0 176)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1 (param, b_param,
    param_0, (BArray176.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1_ <- (trace_h__BN___negc1_ ++ tmp__trace);
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1_);
  }
  proc h__BN___neg_ (r:BArray176.t, b_r:BArray176.t, a:BArray176.t,
                     b_a:BArray176.t) : bool * BArray176.t * BArray176.t *
                                        trace = {
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray176.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__BN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___neg_ <- [];
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray176.is_init b_a 0 176))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray176.get64 a 0) false);
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1_ (param, b_param,
    param_0, (BArray176.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___neg_ <- (trace_h__BN___neg_ ++ tmp__trace);
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___neg_);
  }
  proc h__fun_kmuln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                     b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__fun_kmuln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__fun_kmuln <- [];
    trace_h__fun_kmuln <-
    (trace_h__fun_kmuln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__H__MUL___ps_muln_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__fun_kmuln <- (trace_h__fun_kmuln ++ tmp__trace);
    trace_h__fun_kmuln <-
    (trace_h__fun_kmuln ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__fun_kmuln);
  }
  proc h__KAR____sub_signabs (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                              b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  W64.t * BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var cf:bool;
    var param_2:bool;
    var result_1:W64.t;
    var sign:W64.t;
    var param_3:BArray88.t;
    var param_4:W64.t;
    var result_2:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__KAR____sub_signabs:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    trace_h__KAR____sub_signabs <- [];
    trace_h__KAR____sub_signabs <-
    (trace_h__KAR____sub_signabs ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__H__BN___sub_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__KAR____sub_signabs <-
    (trace_h__KAR____sub_signabs ++ tmp__trace);
    trace_h__KAR____sub_signabs <-
    (trace_h__KAR____sub_signabs ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    param_2 <- cf;
    (result_1, tmp__trace) <@ uTIL____cf_mask (param_2);
    trace_h__KAR____sub_signabs <-
    (trace_h__KAR____sub_signabs ++ tmp__trace);
    sign <- result_1;
    param_3 <- r;
    param_4 <- sign;
    (aux_2, aux_3, tmp__trace) <@ h__H__BN___cnegU_ (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4);
    result_2 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__KAR____sub_signabs <-
    (trace_h__KAR____sub_signabs ++ tmp__trace);
    trace_h__KAR____sub_signabs <-
    (trace_h__KAR____sub_signabs ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_2;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (sign, r, b_r, trace_h__KAR____sub_signabs);
  }
  proc h__KAR___kar_muln (r:BArray352.t, b_r:BArray352.t, a:BArray176.t,
                          b_a:BArray176.t, b:BArray176.t, b_b:BArray176.t) : 
  BArray352.t * BArray352.t * trace = {
    var aux_5:BArray176.t;
    var aux_6:BArray176.t;
    var aux_8:BArray176.t;
    var aux_9:BArray176.t;
    var aux_10:BArray176.t;
    var aux_11:BArray176.t;
    var aux_12:BArray176.t;
    var aux_13:BArray176.t;
    var aux_14:BArray176.t;
    var aux_15:BArray176.t;
    var aux_17:BArray176.t;
    var aux_18:BArray176.t;
    var aux_20:BArray176.t;
    var aux_21:BArray176.t;
    var aux_23:BArray176.t;
    var aux_24:BArray176.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_28:BArray88.t;
    var aux_29:BArray88.t;
    var aux:W64.t;
    var aux_2:W64.t;
    var aux_26:W64.t;
    var aux_7:bool;
    var aux_16:bool;
    var aux_19:bool;
    var aux_22:bool;
    var aux_25:bool;
    var aux_27:bool;
    var b__tmp:BArray176.t;
    var b__x:BArray176.t;
    var b__r:BArray352.t;
    var _r:BArray352.t;
    var b_rlo:BArray176.t;
    var rlo:BArray176.t;
    var b_rlolo:BArray88.t;
    var rlolo:BArray88.t;
    var b_alo:BArray88.t;
    var alo:BArray88.t;
    var b_ahi:BArray88.t;
    var ahi:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var b_param_0:BArray88.t;
    var param_0:BArray88.t;
    var b_param_1:BArray88.t;
    var param_1:BArray88.t;
    var result:W64.t;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var sa:W64.t;
    var b_rlohi:BArray88.t;
    var rlohi:BArray88.t;
    var b_blo:BArray88.t;
    var blo:BArray88.t;
    var b_bhi:BArray88.t;
    var bhi:BArray88.t;
    var b_param_2:BArray88.t;
    var param_2:BArray88.t;
    var b_param_3:BArray88.t;
    var param_3:BArray88.t;
    var b_param_4:BArray88.t;
    var param_4:BArray88.t;
    var result_1:W64.t;
    var result_2:BArray88.t;
    var b_result_0:BArray88.t;
    var sb:W64.t;
    var _sa:W64.t;
    var _a:BArray176.t;
    var _b:BArray176.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param_5:BArray176.t;
    var param_5:BArray176.t;
    var b_param_6:BArray88.t;
    var param_6:BArray88.t;
    var b_param_7:BArray88.t;
    var param_7:BArray88.t;
    var result_3:BArray176.t;
    var b_result_1:BArray176.t;
    var b_x:BArray176.t;
    var x:BArray176.t;
    var _x:BArray176.t;
    var b_param_8:BArray176.t;
    var param_8:BArray176.t;
    var param_9:BArray176.t;
    var result_4:bool;
    var result_5:BArray176.t;
    var b_result_2:BArray176.t;
    var cf:bool;
    var param_10:bool;
    var result_6:W64.t;
    var m:W64.t;
    var param_11:W64.t;
    var result_7:bool;
    var param_12:BArray176.t;
    var param_13:bool;
    var param_14:BArray176.t;
    var result_8:BArray176.t;
    var b_result_3:BArray176.t;
    var b_param_9:BArray176.t;
    var param_15:BArray176.t;
    var b_param_10:BArray88.t;
    var param_16:BArray88.t;
    var b_param_11:BArray88.t;
    var param_17:BArray88.t;
    var result_9:BArray176.t;
    var b_result_4:BArray176.t;
    var b_rhi:BArray176.t;
    var rhi:BArray176.t;
    var b_param_12:BArray176.t;
    var param_18:BArray176.t;
    var b_param_13:BArray88.t;
    var param_19:BArray88.t;
    var b_param_14:BArray88.t;
    var param_20:BArray88.t;
    var result_10:BArray176.t;
    var b_result_5:BArray176.t;
    var param_21:BArray176.t;
    var b_param_15:BArray176.t;
    var param_22:BArray176.t;
    var result_11:bool;
    var result_12:BArray176.t;
    var b_result_6:BArray176.t;
    var param_23:BArray176.t;
    var b_param_16:BArray176.t;
    var param_24:BArray176.t;
    var result_13:bool;
    var result_14:BArray176.t;
    var b_result_7:BArray176.t;
    var b_rmid:BArray176.t;
    var rmid:BArray176.t;
    var b_param_17:BArray176.t;
    var param_25:BArray176.t;
    var param_26:BArray176.t;
    var result_15:bool;
    var result_16:BArray176.t;
    var b_result_8:BArray176.t;
    var b_rhihi:BArray88.t;
    var rhihi:BArray88.t;
    var b_param_18:BArray88.t;
    var param_27:BArray88.t;
    var param_28:bool;
    var param_29:int;
    var result_17:bool;
    var result_18:BArray88.t;
    var b_result_9:BArray88.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__KAR___kar_muln:trace;
    _a <- witness;
    _b <- witness;
    _r <- witness;
    _tmp <- witness;
    _x <- witness;
    ahi <- witness;
    alo <- witness;
    b__r <- witness;
    b__tmp <- witness;
    b__x <- witness;
    b_ahi <- witness;
    b_alo <- witness;
    b_bhi <- witness;
    b_blo <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_param_7 <- witness;
    b_param_8 <- witness;
    b_param_9 <- witness;
    b_param_10 <- witness;
    b_param_11 <- witness;
    b_param_12 <- witness;
    b_param_13 <- witness;
    b_param_14 <- witness;
    b_param_15 <- witness;
    b_param_16 <- witness;
    b_param_17 <- witness;
    b_param_18 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_result_8 <- witness;
    b_result_9 <- witness;
    b_rhi <- witness;
    b_rhihi <- witness;
    b_rlo <- witness;
    b_rlohi <- witness;
    b_rlolo <- witness;
    b_rmid <- witness;
    b_tmp <- witness;
    b_x <- witness;
    bhi <- witness;
    blo <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_12 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_20 <- witness;
    param_21 <- witness;
    param_22 <- witness;
    param_23 <- witness;
    param_24 <- witness;
    param_25 <- witness;
    param_26 <- witness;
    param_27 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_5 <- witness;
    result_8 <- witness;
    result_9 <- witness;
    result_10 <- witness;
    result_12 <- witness;
    result_14 <- witness;
    result_16 <- witness;
    result_18 <- witness;
    rhi <- witness;
    rhihi <- witness;
    rlo <- witness;
    rlohi <- witness;
    rlolo <- witness;
    rmid <- witness;
    tmp <- witness;
    x <- witness;
    trace_h__KAR___kar_muln <- [];
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b_b 0 176)))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    b__x <- (BArray176.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    b_rlo <- (SBArray352_176.get_sub64 b__r 0);
    rlo <- (SBArray352_176.get_sub64 _r 0);
    b_rlolo <- (SBArray352_88.get_sub64 b_r 0);
    rlolo <- (SBArray352_88.get_sub64 r 0);
    b_alo <- (SBArray176_88.get_sub64 b_a 0);
    alo <- (SBArray176_88.get_sub64 a 0);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_ahi <- (SBArray176_88.get_sub64 b_a 11);
    ahi <- (SBArray176_88.get_sub64 a 11);
    b_param <- b_rlolo;
    param <- rlolo;
    b_param_0 <- b_alo;
    param_0 <- alo;
    b_param_1 <- b_ahi;
    param_1 <- ahi;
    (aux, aux_0, aux_1, tmp__trace) <@ h__KAR____sub_signabs (param, 
    b_param, param_0, b_param_0, param_1, b_param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    sa <- result;
    rlolo <- result_0;
    b_rlo <-
    (SBArray176_88.set_sub64 b_rlo 0 (BArray88.init_arr (W8.of_int 255)));
    rlo <- (SBArray176_88.set_sub64 rlo 0 rlolo);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_rlohi <- (SBArray176_88.get_sub64 b_rlo 11);
    rlohi <- (SBArray176_88.get_sub64 rlo 11);
    b_blo <- (SBArray176_88.get_sub64 b_b 0);
    blo <- (SBArray176_88.get_sub64 b 0);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_bhi <- (SBArray176_88.get_sub64 b_b 11);
    bhi <- (SBArray176_88.get_sub64 b 11);
    b_param_2 <- b_rlohi;
    param_2 <- rlohi;
    b_param_3 <- b_bhi;
    param_3 <- bhi;
    b_param_4 <- b_blo;
    param_4 <- blo;
    (aux_2, aux_3, aux_4, tmp__trace) <@ h__KAR____sub_signabs (param_2,
    b_param_2, param_3, b_param_3, param_4, b_param_4);
    result_1 <- aux_2;
    result_2 <- aux_3;
    b_result_0 <- aux_4;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    sb <- result_1;
    rlohi <- result_2;
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_rlo <-
    (SBArray176_88.set_sub64 b_rlo 11 (BArray88.init_arr (W8.of_int 255)));
    rlo <- (SBArray176_88.set_sub64 rlo 11 rlohi);
    b__r <- (SBArray352_176.set_sub64 b__r 0 b_rlo);
    _r <- (SBArray352_176.set_sub64 _r 0 rlo);
    sa <- (sa `^` sb);
    _sa <- sa;
    _a <- a;
    _b <- b;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_rlo <- (SBArray352_176.get_sub64 b__r 0);
    rlo <- (SBArray352_176.get_sub64 _r 0);
    b_rlolo <- (SBArray176_88.get_sub64 b_rlo 0);
    rlolo <- (SBArray176_88.get_sub64 rlo 0);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_rlohi <- (SBArray176_88.get_sub64 b_rlo 11);
    rlohi <- (SBArray176_88.get_sub64 rlo 11);
    b_param_5 <- b_tmp;
    param_5 <- tmp;
    b_param_6 <- b_rlolo;
    param_6 <- rlolo;
    b_param_7 <- b_rlohi;
    param_7 <- rlohi;
    (aux_5, aux_6, tmp__trace) <@ h__fun_kmuln (param_5, b_param_5, param_6,
    b_param_6, param_7, b_param_7);
    result_3 <- aux_5;
    b_result_1 <- aux_6;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_1 0 176))]);
    tmp <- result_3;
    b_x <- b__x;
    x <- _x;
    b_param_8 <- b_x;
    param_8 <- x;
    param_9 <- tmp;
    (aux_7, aux_8, aux_9, tmp__trace) <@ h__BN___neg_ (param_8, b_param_8,
    param_9, (BArray176.init_arr (W8.of_int 255)));
    result_4 <- aux_7;
    result_5 <- aux_8;
    b_result_2 <- aux_9;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_2 0 176))]);
    cf <- result_4;
    x <- result_5;
    param_10 <- cf;
    (result_6, tmp__trace) <@ uTIL____cf_mask (param_10);
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    m <- result_6;
    sa <- _sa;
    sa <- (sa `&` m);
    _sa <- sa;
    param_11 <- sa;
    (result_7, tmp__trace) <@ uTIL____mask_cf (param_11);
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    cf <- result_7;
    param_12 <- tmp;
    param_13 <- cf;
    param_14 <- x;
    (aux_10, aux_11, tmp__trace) <@ h__BN___cmov_ (param_12,
    (BArray176.init_arr (W8.of_int 255)), param_13, param_14,
    (BArray176.init_arr (W8.of_int 255)));
    result_8 <- aux_10;
    b_result_3 <- aux_11;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_3 0 176))]);
    tmp <- result_8;
    _tmp <- tmp;
    b_rlo <- (SBArray352_176.get_sub64 b__r 0);
    rlo <- (SBArray352_176.get_sub64 _r 0);
    b_a <- (BArray176.init_arr (W8.of_int 255));
    a <- _a;
    b_alo <- (SBArray176_88.get_sub64 b_a 0);
    alo <- (SBArray176_88.get_sub64 a 0);
    b_b <- (BArray176.init_arr (W8.of_int 255));
    b <- _b;
    b_blo <- (SBArray176_88.get_sub64 b_b 0);
    blo <- (SBArray176_88.get_sub64 b 0);
    b_param_9 <- b_rlo;
    param_15 <- rlo;
    b_param_10 <- b_alo;
    param_16 <- alo;
    b_param_11 <- b_blo;
    param_17 <- blo;
    (aux_12, aux_13, tmp__trace) <@ h__fun_kmuln (param_15, b_param_9,
    param_16, b_param_10, param_17, b_param_11);
    result_9 <- aux_12;
    b_result_4 <- aux_13;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_4 0 176))]);
    rlo <- result_9;
    b__r <-
    (SBArray352_176.set_sub64 b__r 0 (BArray176.init_arr (W8.of_int 255)));
    _r <- (SBArray352_176.set_sub64 _r 0 rlo);
    b_a <- (BArray176.init_arr (W8.of_int 255));
    a <- _a;
    b_b <- (BArray176.init_arr (W8.of_int 255));
    b <- _b;
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_ahi <- (SBArray176_88.get_sub64 b_a 11);
    ahi <- (SBArray176_88.get_sub64 a 11);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_bhi <- (SBArray176_88.get_sub64 b_b 11);
    bhi <- (SBArray176_88.get_sub64 b 11);
    b_r <- b__r;
    r <- _r;
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 176) <= 352)))]);
    b_rhi <- (SBArray352_176.get_sub64 b_r 22);
    rhi <- (SBArray352_176.get_sub64 r 22);
    b_param_12 <- b_rhi;
    param_18 <- rhi;
    b_param_13 <- b_ahi;
    param_19 <- ahi;
    b_param_14 <- b_bhi;
    param_20 <- bhi;
    (aux_14, aux_15, tmp__trace) <@ h__fun_kmuln (param_18, b_param_12,
    param_19, b_param_13, param_20, b_param_14);
    result_10 <- aux_14;
    b_result_5 <- aux_15;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_5 0 176))]);
    rhi <- result_10;
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 176) <= 352)))]);
    b__r <-
    (SBArray352_176.set_sub64 b__r 22 (BArray176.init_arr (W8.of_int 255)));
    _r <- (SBArray352_176.set_sub64 _r 22 rhi);
    b_r <- b__r;
    r <- _r;
    tmp <- _tmp;
    b_rlo <- (SBArray352_176.get_sub64 b_r 0);
    rlo <- (SBArray352_176.get_sub64 r 0);
    param_21 <- tmp;
    b_param_15 <- b_rlo;
    param_22 <- rlo;
    (aux_16, aux_17, aux_18, tmp__trace) <@ h__BN___addU_ (param_21,
    (BArray176.init_arr (W8.of_int 255)), param_22, b_param_15);
    result_11 <- aux_16;
    result_12 <- aux_17;
    b_result_6 <- aux_18;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_6 0 176))]);
    cf <- result_11;
    tmp <- result_12;
    sa <- _sa;
    ( _0, sa) <- (adc_64 sa (W64.of_int 0) cf);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 176) <= 352)))]);
    b_rhi <- (SBArray352_176.get_sub64 b_r 22);
    rhi <- (SBArray352_176.get_sub64 r 22);
    param_23 <- tmp;
    b_param_16 <- b_rhi;
    param_24 <- rhi;
    (aux_19, aux_20, aux_21, tmp__trace) <@ h__BN___addU_ (param_23,
    (BArray176.init_arr (W8.of_int 255)), param_24, b_param_16);
    result_13 <- aux_19;
    result_14 <- aux_20;
    b_result_7 <- aux_21;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_7 0 176))]);
    cf <- result_13;
    tmp <- result_14;
    ( _1, sa) <- (adc_64 sa (W64.of_int 0) cf);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 176) <= 352)))]);
    b_rmid <- (SBArray352_176.get_sub64 b_r 11);
    rmid <- (SBArray352_176.get_sub64 r 11);
    b_param_17 <- b_rmid;
    param_25 <- rmid;
    param_26 <- tmp;
    (aux_22, aux_23, aux_24, tmp__trace) <@ h__BN___addU_ (param_25,
    b_param_17, param_26, (BArray176.init_arr (W8.of_int 255)));
    result_15 <- aux_22;
    result_16 <- aux_23;
    b_result_8 <- aux_24;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray176.is_init b_result_8 0 176))]);
    cf <- result_15;
    rmid <- result_16;
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 176) <= 352)))]);
    b_r <-
    (SBArray352_176.set_sub64 b_r 11 (BArray176.init_arr (W8.of_int 255)));
    r <- (SBArray352_176.set_sub64 r 11 rmid);
    ( _2, sa) <- (adc_64 sa (W64.of_int 0) cf);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 11) * 8)) /\ ((((3 * 11) * 8) + 8) <= 352)))]);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 11) * 8)) /\ ((((3 * 11) * 8) + 8) <= 352)))]);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray352.is_init b_r ((3 * 11) * 8) 8))]);
    b_r <-
    (BArray352.set64d b_r ((3 * 11) * 8) (W64.of_int 18446744073709551615));
    (aux_25, aux_26) <- (adc_64 (BArray352.get64 r (3 * 11)) sa false);
    cf <- aux_25;
    r <- (BArray352.set64 r (3 * 11) aux_26);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 11) * 8)) /\ ((((3 * 11) * 8) + 88) <= 352)))]);
    b_rhihi <- (SBArray352_88.get_sub64 b_r (3 * 11));
    rhihi <- (SBArray352_88.get_sub64 r (3 * 11));
    b_param_18 <- b_rhihi;
    param_27 <- rhihi;
    param_28 <- cf;
    param_29 <- 1;
    (aux_27, aux_28, aux_29, tmp__trace) <@ h__H__BN____carrypropU (param_27,
    b_param_18, param_28, param_29);
    result_17 <- aux_27;
    result_18 <- aux_28;
    b_result_9 <- aux_29;
    trace_h__KAR___kar_muln <- (trace_h__KAR___kar_muln ++ tmp__trace);
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, (BArray88.is_init b_result_9 0 88))]);
    rhihi <- result_18;
    trace_h__KAR___kar_muln <-
    (trace_h__KAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 11) * 8)) /\ ((((3 * 11) * 8) + 88) <= 352)))]);
    b_r <-
    (SBArray352_88.set_sub64 b_r (3 * 11) (BArray88.init_arr (W8.of_int 255))
    );
    r <- (SBArray352_88.set_sub64 r (3 * 11) rhihi);
    return (r, b_r, trace_h__KAR___kar_muln);
  }
  proc h__KAR___kar_muln_ (r:BArray352.t, b_r:BArray352.t, a:BArray176.t,
                           b_a:BArray176.t, b:BArray176.t, b_b:BArray176.t) : 
  BArray352.t * BArray352.t * trace = {
    var aux:BArray352.t;
    var aux_0:BArray352.t;
    var b_param:BArray352.t;
    var param:BArray352.t;
    var param_0:BArray176.t;
    var param_1:BArray176.t;
    var result:BArray352.t;
    var b_result:BArray352.t;
    var trace_h__KAR___kar_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__KAR___kar_muln_ <- [];
    trace_h__KAR___kar_muln_ <-
    (trace_h__KAR___kar_muln_ ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b_b 0 176)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__KAR___kar_muln (param, b_param, param_0,
    (BArray176.init_arr (W8.of_int 255)), param_1,
    (BArray176.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__KAR___kar_muln_ <- (trace_h__KAR___kar_muln_ ++ tmp__trace);
    trace_h__KAR___kar_muln_ <-
    (trace_h__KAR___kar_muln_ ++
    [(Assert, (BArray352.is_init b_result 0 352))]);
    r <- result;
    r <- r;
    b_r <- (BArray352.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__KAR___kar_muln_);
  }
  proc bN____store (ap:W64.t, a:BArray352.t, b_a:BArray352.t) : trace = {
    var i:int;
    var t:W64.t;
    var trace_bN____store:trace;
    trace_bN____store <- [];
    trace_bN____store <-
    (trace_bN____store ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 44)) /\
     (BArray352.is_init b_a 0 352)))]);
    i <- 0;
    while ((i < 44)) {
      trace_bN____store <-
      (trace_bN____store ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 352)))]);
      t <- (BArray352.get64 a i);
      trace_bN____store <-
      (trace_bN____store ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      Glob.mem <-
      (storeW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))) t);
      i <- (i + 1);
    }
    return (trace_bN____store);
  }
  proc bN___store_ (ap:W64.t, a:BArray352.t, b_a:BArray352.t) : trace = {
    var param:W64.t;
    var param_0:BArray352.t;
    var trace_bN___store_:trace;
    param_0 <- witness;
    trace_bN___store_ <- [];
    trace_bN___store_ <-
    (trace_bN___store_ ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 44)) /\
     (BArray352.is_init b_a 0 352)))]);
    ap <- ap;
    a <- a;
    param <- ap;
    param_0 <- a;
    tmp__trace <@ bN____store (param, param_0,
    (BArray352.init_arr (W8.of_int 255)));
    trace_bN___store_ <- (trace_bN___store_ ++ tmp__trace);
    return (trace_bN___store_);
  }
  proc bn_kar_muln (rp:W64.t, ap:W64.t, bp:W64.t) : trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var aux_3:BArray352.t;
    var aux_4:BArray352.t;
    var b__a:BArray176.t;
    var b__b:BArray176.t;
    var b__r:BArray352.t;
    var _rp:W64.t;
    var b_a:BArray176.t;
    var a:BArray176.t;
    var _a:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_b:BArray176.t;
    var b:BArray176.t;
    var _b:BArray176.t;
    var b_param_0:BArray176.t;
    var param_1:BArray176.t;
    var param_2:W64.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var b_r:BArray352.t;
    var r:BArray352.t;
    var _r:BArray352.t;
    var b_param_1:BArray352.t;
    var param_3:BArray352.t;
    var param_4:BArray176.t;
    var param_5:BArray176.t;
    var result_1:BArray352.t;
    var b_result_1:BArray352.t;
    var param_6:W64.t;
    var param_7:BArray352.t;
    var trace_bn_kar_muln:trace;
    _a <- witness;
    _b <- witness;
    _r <- witness;
    a <- witness;
    b <- witness;
    b__a <- witness;
    b__b <- witness;
    b__r <- witness;
    b_a <- witness;
    b_b <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_r <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_bn_kar_muln <- [];
    trace_bn_kar_muln <-
    (trace_bn_kar_muln ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 22)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 22))) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 44))))]);
    b__a <- (BArray176.init_arr (W8.of_int 0));
    b__b <- (BArray176.init_arr (W8.of_int 0));
    b__r <- (BArray352.init_arr (W8.of_int 0));
    _rp <- rp;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_kar_muln <- (trace_bn_kar_muln ++ tmp__trace);
    trace_bn_kar_muln <-
    (trace_bn_kar_muln ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    a <- result;
    b_b <- b__b;
    b <- _b;
    b_param_0 <- b_b;
    param_1 <- b;
    param_2 <- bp;
    (aux_1, aux_2, tmp__trace) <@ h__BN___load_ (param_1, b_param_0,
    param_2);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_bn_kar_muln <- (trace_bn_kar_muln ++ tmp__trace);
    trace_bn_kar_muln <-
    (trace_bn_kar_muln ++ [(Assert, (BArray176.is_init b_result_0 0 176))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    (aux_3, aux_4, tmp__trace) <@ h__KAR___kar_muln_ (param_3, b_param_1,
    param_4, (BArray176.init_arr (W8.of_int 255)), param_5,
    (BArray176.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_bn_kar_muln <- (trace_bn_kar_muln ++ tmp__trace);
    trace_bn_kar_muln <-
    (trace_bn_kar_muln ++ [(Assert, (BArray352.is_init b_result_1 0 352))]);
    r <- result_1;
    rp <- _rp;
    param_6 <- rp;
    param_7 <- r;
    tmp__trace <@ bN___store_ (param_6, param_7,
    (BArray352.init_arr (W8.of_int 255)));
    trace_bn_kar_muln <- (trace_bn_kar_muln ++ tmp__trace);
    return (trace_bn_kar_muln);
  }
}.

(* The post and trace are valid. *)

op uTIL____mask_cf_spec _mask =
   hoare [M.uTIL____mask_cf :
   ((_mask = mask) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____addacc3_spec _a _b_a _b1 _b0 _k =
   hoare [M.uTIL____addacc3 :
   (((_k = k) /\ ((_b0 = b0) /\ ((_b1 = b1) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   (BArray24.is_init _b_a 0 24)) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__H__BN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__H__BN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__H__BN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__H__BN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__H__BN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.h__H__BN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__H__BN____carrypropU_spec _a _b_a _cf _k =
   hoare [M.h__H__BN____carrypropU :
   (((_k = k) /\ ((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   (true /\ ((0 <= _k) /\ (BArray88.is_init _b_a 0 (8 * 11))))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN____subc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN____subc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11))) /\
   (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___subc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN___subc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11))) /\
   (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___subc1__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__H__BN___subc1_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11))) /\
   (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___sub__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__BN___sub_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__H__BN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__H__BN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.h__H__BN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___neg__spec _r _b_r _a _b_a =
   hoare [M.h__H__BN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__H__BN___cnegU__spec _a _b_a _cond =
   hoare [M.h__H__BN___cnegU_ :
   (((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray88.is_init _b_a 0 88)) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__H__MUL____muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b =
   hoare [M.h__H__MUL____muln_innerloop :
   (((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_a = b_a) /\
    ((_a = a) /\
    ((_iend = iend) /\
    ((_istart = istart) /\ ((_k = k) /\ ((_b_x = b_x) /\ (_x = x))))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (((((((0 <= _istart) /\ (_iend <= 11)) /\ (0 <= (_k - (_iend - 1)))) /\
      ((_k - _istart) < 11)) /\
     (BArray24.is_init _b_x 0 24)) /\
    (BArray88.is_init _b_a (8 * _istart) (8 * (_iend - _istart)))) /\
   (BArray88.is_init _b_b 0 (8 * 11))))))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__H__MUL____ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL____ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__H__MUL___ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL___ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__H__MUL___ps_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__H__MUL___ps_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__BN____load_spec _a _b_a _ap =
   hoare [M.h__BN____load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 22)))) ==>
   ((BArray176.is_init res.`2 0 (8 * 22)) /\ (valid res.`3))].

op h__BN___load_spec _a _b_a _ap =
   hoare [M.h__BN___load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 22)))) ==>
   ((BArray176.is_init res.`2 0 (8 * 22)) /\ (valid res.`3))].

op h__BN___load__spec _a _b_a _ap =
   hoare [M.h__BN___load_ :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 22)))) ==>
   ((BArray176.is_init res.`2 0 (8 * 22)) /\ (valid res.`3))].

op h__BN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`2 0 176) /\ (valid res.`3))].

op h__BN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`2 0 176) /\ (valid res.`3))].

op h__BN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`2 0 176) /\ (valid res.`3))].

op h__BN____addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`3 0 176) /\ (valid res.`4))].

op h__BN___addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`3 0 176) /\ (valid res.`4))].

op h__BN___addc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`3 0 176) /\ (valid res.`4))].

op h__BN___addU__spec _a _b_a _b _b_b =
   hoare [M.h__BN___addU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray176.is_init _b_b 0 176) /\ (BArray176.is_init _b_a 0 176))) ==>
   ((BArray176.is_init res.`3 0 176) /\ (valid res.`4))].

op h__BN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray176.is_init _b_r 0 8) /\ (BArray176.is_init _b_a 0 (8 * 22)))) ==>
   ((BArray176.is_init res.`3 0 (8 * 22)) /\ (valid res.`4))].

op h__BN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray176.is_init _b_r 0 8) /\ (BArray176.is_init _b_a 0 (8 * 22)))) ==>
   ((BArray176.is_init res.`3 0 (8 * 22)) /\ (valid res.`4))].

op h__BN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray176.is_init _b_r 0 8) /\ (BArray176.is_init _b_a 0 (8 * 22)))) ==>
   ((BArray176.is_init res.`3 0 (8 * 22)) /\ (valid res.`4))].

op h__BN___neg__spec _r _b_r _a _b_a =
   hoare [M.h__BN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray176.is_init _b_a 0 (8 * 22))) ==>
   ((BArray176.is_init res.`3 0 (8 * 22)) /\ (valid res.`4))].

op h__fun_kmuln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__fun_kmuln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (8 * 22)) /\ (valid res.`3))].

op h__KAR____sub_signabs_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__KAR____sub_signabs :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__KAR___kar_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__KAR___kar_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray176.is_init _b_a 0 (8 * 22)) /\
   (BArray176.is_init _b_b 0 (8 * 22)))) ==>
   ((BArray352.is_init res.`2 0 (16 * 22)) /\ (valid res.`3))].

op h__KAR___kar_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__KAR___kar_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray176.is_init _b_a 0 (8 * 22)) /\
   (BArray176.is_init _b_b 0 (8 * 22)))) ==>
   ((BArray352.is_init res.`2 0 (16 * 22)) /\ (valid res.`3))].

op bN____store_spec _ap _a _b_a =
   hoare [M.bN____store :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 44)) /\
   (BArray352.is_init _b_a 0 (8 * 44))))) ==> (true /\ (valid res))].

op bN___store__spec _ap _a _b_a =
   hoare [M.bN___store_ :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 44)) /\
   (BArray352.is_init _b_a 0 (8 * 44))))) ==> (true /\ (valid res))].

op bn_kar_muln_spec _rp _ap _bp =
   hoare [M.bn_kar_muln :
   (((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))) /\
   (true /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 22)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 22))) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 44))))))) ==>
   (true /\ (valid res))].
