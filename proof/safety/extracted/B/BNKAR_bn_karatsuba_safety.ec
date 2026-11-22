require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array7 Array14 Array28 Array56 Array112 Array224 BArray56 BArray112 BArray224
SBArray112_56 SBArray224_56 SBArray224_112.

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
  proc h__BN____cmov (a:BArray56.t, b_a:BArray56.t, cond:bool, b:BArray56.t,
                      b_b:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____cmov:trace;
    trace_h__BN____cmov <- [];
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (cond ? (BArray56.get64 b i) : t);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      a <- (BArray56.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____cmov);
  }
  proc h__BN___cmov (a:BArray56.t, b_a:BArray56.t, cond:bool, b:BArray56.t,
                     b_b:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:bool;
    var param_1:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov <- [];
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN____cmov (param,
    (BArray56.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov <- (trace_h__BN___cmov ++ tmp__trace);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov);
  }
  proc h__BN___cmov_ (a:BArray56.t, b_a:BArray56.t, cond:bool, b:BArray56.t,
                      b_b:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:bool;
    var param_1:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov_ <- [];
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN___cmov (param,
    (BArray56.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov_ <- (trace_h__BN___cmov_ ++ tmp__trace);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov_);
  }
  proc h__BN____carrypropU (a:BArray56.t, b_a:BArray56.t, cf:bool, k:int) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var trace_h__BN____carrypropU:trace;
    trace_h__BN____carrypropU <- [];
    trace_h__BN____carrypropU <-
    (trace_h__BN____carrypropU ++
    [(Assert, ((0 <= k) /\ (BArray56.is_init b_a 0 56)))]);
    i <- k;
    while ((i < 7)) {
      trace_h__BN____carrypropU <-
      (trace_h__BN____carrypropU ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____carrypropU <-
      (trace_h__BN____carrypropU ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (aux, aux_0) <- (adc_64 (BArray56.get64 a i) (W64.of_int 0) cf);
      cf <- aux;
      a <- (BArray56.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____carrypropU);
  }
  proc h__BN____subc1 (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                       b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t, cf:bool) : 
  bool * BArray56.t * BArray56.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____subc1:trace;
    trace_h__BN____subc1 <- [];
    trace_h__BN____subc1 <-
    (trace_h__BN____subc1 ++
    [(Assert,
     (((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)) /\
     (BArray56.is_init b_b 0 56)))]);
    i <- 1;
    while ((i < 7)) {
      trace_h__BN____subc1 <-
      (trace_h__BN____subc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____subc1 <-
      (trace_h__BN____subc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (cf, t) <- (sbb_64 t (BArray56.get64 b i) cf);
      trace_h__BN____subc1 <-
      (trace_h__BN____subc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____subc1);
  }
  proc h__BN___subc1 (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t, cf:bool) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___subc1 <- [];
    trace_h__BN___subc1 <-
    (trace_h__BN___subc1 ++
    [(Assert,
     (((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)) /\
     (BArray56.is_init b_b 0 56)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____subc1 (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___subc1 <- (trace_h__BN___subc1 ++ tmp__trace);
    trace_h__BN___subc1 <-
    (trace_h__BN___subc1 ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___subc1);
  }
  proc h__BN___subc1_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                       b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t, cf:bool) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___subc1_ <- [];
    trace_h__BN___subc1_ <-
    (trace_h__BN___subc1_ ++
    [(Assert,
     (((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)) /\
     (BArray56.is_init b_b 0 56)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___subc1 (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___subc1_ <- (trace_h__BN___subc1_ ++ tmp__trace);
    trace_h__BN___subc1_ <-
    (trace_h__BN___subc1_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___subc1_);
  }
  proc h__BN___sub_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                     b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___sub_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___sub_ <- [];
    trace_h__BN___sub_ <-
    (trace_h__BN___sub_ ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    t <- (BArray56.get64 a 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 b 0) false);
    b_r <- (BArray56.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___subc1_ (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___sub_ <- (trace_h__BN___sub_ ++ tmp__trace);
    trace_h__BN___sub_ <-
    (trace_h__BN___sub_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___sub_);
  }
  proc h__BN____negc1 (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                       b_a:BArray56.t, cf:bool) : bool * BArray56.t *
                                                  BArray56.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____negc1:trace;
    trace_h__BN____negc1 <- [];
    trace_h__BN____negc1 <-
    (trace_h__BN____negc1 ++
    [(Assert, ((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)))]);
    i <- 1;
    while ((i < 7)) {
      t <- (W64.of_int 0);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (cf, t) <- (sbb_64 t (BArray56.get64 a i) cf);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____negc1);
  }
  proc h__BN___negc1 (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, cf:bool) : bool * BArray56.t *
                                                 BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1 <- [];
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++
    [(Assert, ((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____negc1 (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1 <- (trace_h__BN___negc1 ++ tmp__trace);
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1);
  }
  proc h__BN___negc1_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                       b_a:BArray56.t, cf:bool) : bool * BArray56.t *
                                                  BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1_ <- [];
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++
    [(Assert, ((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1 (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1_ <- (trace_h__BN___negc1_ ++ tmp__trace);
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1_);
  }
  proc h__BN___neg_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                     b_a:BArray56.t) : bool * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___neg_ <- [];
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 a 0) false);
    b_r <- (BArray56.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1_ (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___neg_ <- (trace_h__BN___neg_ ++ tmp__trace);
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___neg_);
  }
  proc h__BN___cnegU_ (a:BArray56.t, b_a:BArray56.t, cond:W64.t) : BArray56.t *
                                                                   BArray56.t *
                                                                   trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux:bool;
    var b__x:BArray56.t;
    var b_x:BArray56.t;
    var x:BArray56.t;
    var _x:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var param_1:W64.t;
    var result_1:bool;
    var cf:bool;
    var param_2:BArray56.t;
    var param_3:bool;
    var param_4:BArray56.t;
    var result_2:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__BN___cnegU_:trace;
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
    trace_h__BN___cnegU_ <- [];
    trace_h__BN___cnegU_ <-
    (trace_h__BN___cnegU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b__x <- (BArray56.init_arr (W8.of_int 0));
    b_x <- b__x;
    x <- _x;
    b_param <- b_x;
    param <- x;
    param_0 <- a;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___neg_ (param, b_param, 
    param_0, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___cnegU_ <- (trace_h__BN___cnegU_ ++ tmp__trace);
    trace_h__BN___cnegU_ <-
    (trace_h__BN___cnegU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    x <- result_0;
    param_1 <- cond;
    (result_1, tmp__trace) <@ uTIL____mask_cf (param_1);
    trace_h__BN___cnegU_ <- (trace_h__BN___cnegU_ ++ tmp__trace);
    cf <- result_1;
    param_2 <- a;
    param_3 <- cf;
    param_4 <- x;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cmov_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray56.init_arr (W8.of_int 255)));
    result_2 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___cnegU_ <- (trace_h__BN___cnegU_ ++ tmp__trace);
    trace_h__BN___cnegU_ <-
    (trace_h__BN___cnegU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_2;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cnegU_);
  }
  proc bN____cmov (a:BArray112.t, b_a:BArray112.t, cond:bool, b:BArray112.t,
                   b_b:BArray112.t) : BArray112.t * BArray112.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_bN____cmov:trace;
    trace_bN____cmov <- [];
    trace_bN____cmov <-
    (trace_bN____cmov ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN____cmov <-
    (trace_bN____cmov ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    i <- 0;
    while ((i < 14)) {
      trace_bN____cmov <-
      (trace_bN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      t <- (BArray112.get64 a i);
      trace_bN____cmov <-
      (trace_bN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      t <- (cond ? (BArray112.get64 b i) : t);
      trace_bN____cmov <-
      (trace_bN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      a <- (BArray112.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (a, b_a, trace_bN____cmov);
  }
  proc bN___cmov (a:BArray112.t, b_a:BArray112.t, cond:bool, b:BArray112.t,
                  b_b:BArray112.t) : BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var param:BArray112.t;
    var param_0:bool;
    var param_1:BArray112.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_bN___cmov <- [];
    trace_bN___cmov <-
    (trace_bN___cmov ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN___cmov <-
    (trace_bN___cmov ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ bN____cmov (param,
    (BArray112.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray112.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_bN___cmov <- (trace_bN___cmov ++ tmp__trace);
    trace_bN___cmov <-
    (trace_bN___cmov ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    a <- result;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (a, b_a, trace_bN___cmov);
  }
  proc bN___cmov_ (a:BArray112.t, b_a:BArray112.t, cond:bool, b:BArray112.t,
                   b_b:BArray112.t) : BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var param:BArray112.t;
    var param_0:bool;
    var param_1:BArray112.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_bN___cmov_ <- [];
    trace_bN___cmov_ <-
    (trace_bN___cmov_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN___cmov_ <-
    (trace_bN___cmov_ ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ bN___cmov (param,
    (BArray112.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray112.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_bN___cmov_ <- (trace_bN___cmov_ ++ tmp__trace);
    trace_bN___cmov_ <-
    (trace_bN___cmov_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    a <- result;
    a <- a;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (a, b_a, trace_bN___cmov_);
  }
  proc bN____addc1U (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
                     b_b:BArray112.t, cf:bool) : bool * BArray112.t *
                                                 BArray112.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_bN____addc1U:trace;
    trace_bN____addc1U <- [];
    trace_bN____addc1U <-
    (trace_bN____addc1U ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN____addc1U <-
    (trace_bN____addc1U ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    i <- 1;
    while ((i < 14)) {
      trace_bN____addc1U <-
      (trace_bN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      t <- (BArray112.get64 b i);
      trace_bN____addc1U <-
      (trace_bN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_bN____addc1U <-
      (trace_bN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      (aux, aux_0) <- (adc_64 (BArray112.get64 a i) t cf);
      cf <- aux;
      a <- (BArray112.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_bN____addc1U);
  }
  proc bN___addc1U (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
                    b_b:BArray112.t, cf:bool) : bool * BArray112.t *
                                                BArray112.t * trace = {
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux:bool;
    var param:BArray112.t;
    var param_0:BArray112.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___addc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_bN___addc1U <- [];
    trace_bN___addc1U <-
    (trace_bN___addc1U ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN___addc1U <-
    (trace_bN___addc1U ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ bN____addc1U (param,
    (BArray112.init_arr (W8.of_int 255)), param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_bN___addc1U <- (trace_bN___addc1U ++ tmp__trace);
    trace_bN___addc1U <-
    (trace_bN___addc1U ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_bN___addc1U);
  }
  proc bN___addc1U_ (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
                     b_b:BArray112.t, cf:bool) : bool * BArray112.t *
                                                 BArray112.t * trace = {
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux:bool;
    var param:BArray112.t;
    var param_0:BArray112.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___addc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_bN___addc1U_ <- [];
    trace_bN___addc1U_ <-
    (trace_bN___addc1U_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN___addc1U_ <-
    (trace_bN___addc1U_ ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ bN___addc1U (param,
    (BArray112.init_arr (W8.of_int 255)), param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_bN___addc1U_ <- (trace_bN___addc1U_ ++ tmp__trace);
    trace_bN___addc1U_ <-
    (trace_bN___addc1U_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_bN___addc1U_);
  }
  proc bN___addU_ (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
                   b_b:BArray112.t) : bool * BArray112.t * BArray112.t *
                                      trace = {
    var aux_2:BArray112.t;
    var aux_3:BArray112.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray112.t;
    var param_0:BArray112.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___addU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_bN___addU_ <- [];
    trace_bN___addU_ <-
    (trace_bN___addU_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_bN___addU_ <-
    (trace_bN___addU_ ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    t <- (BArray112.get64 b 0);
    (aux, aux_0) <- (adc_64 (BArray112.get64 a 0) t false);
    cf <- aux;
    a <- (BArray112.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ bN___addc1U_ (param,
    (BArray112.init_arr (W8.of_int 255)), param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_bN___addU_ <- (trace_bN___addU_ ++ tmp__trace);
    trace_bN___addU_ <-
    (trace_bN___addU_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_bN___addU_);
  }
  proc bN____negc1 (r:BArray112.t, b_r:BArray112.t, a:BArray112.t,
                    b_a:BArray112.t, cf:bool) : bool * BArray112.t *
                                                BArray112.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_bN____negc1:trace;
    trace_bN____negc1 <- [];
    trace_bN____negc1 <-
    (trace_bN____negc1 ++
    [(Assert, ((BArray112.is_init b_r 0 8) /\ (BArray112.is_init b_a 0 112)))]);
    i <- 1;
    while ((i < 14)) {
      t <- (W64.of_int 0);
      trace_bN____negc1 <-
      (trace_bN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      (cf, t) <- (sbb_64 t (BArray112.get64 a i) cf);
      trace_bN____negc1 <-
      (trace_bN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_bN____negc1);
  }
  proc bN___negc1 (r:BArray112.t, b_r:BArray112.t, a:BArray112.t,
                   b_a:BArray112.t, cf:bool) : bool * BArray112.t *
                                               BArray112.t * trace = {
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux:bool;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray112.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_bN___negc1 <- [];
    trace_bN___negc1 <-
    (trace_bN___negc1 ++
    [(Assert, ((BArray112.is_init b_r 0 8) /\ (BArray112.is_init b_a 0 112)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ bN____negc1 (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_bN___negc1 <- (trace_bN___negc1 ++ tmp__trace);
    trace_bN___negc1 <-
    (trace_bN___negc1 ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_bN___negc1);
  }
  proc bN___negc1_ (r:BArray112.t, b_r:BArray112.t, a:BArray112.t,
                    b_a:BArray112.t, cf:bool) : bool * BArray112.t *
                                                BArray112.t * trace = {
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux:bool;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray112.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_bN___negc1_ <- [];
    trace_bN___negc1_ <-
    (trace_bN___negc1_ ++
    [(Assert, ((BArray112.is_init b_r 0 8) /\ (BArray112.is_init b_a 0 112)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ bN___negc1 (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_bN___negc1_ <- (trace_bN___negc1_ ++ tmp__trace);
    trace_bN___negc1_ <-
    (trace_bN___negc1_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_bN___negc1_);
  }
  proc bN___neg_ (r:BArray112.t, b_r:BArray112.t, a:BArray112.t,
                  b_a:BArray112.t) : bool * BArray112.t * BArray112.t * trace = {
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray112.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray112.t;
    var b_result:BArray112.t;
    var trace_bN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_bN___neg_ <- [];
    trace_bN___neg_ <-
    (trace_bN___neg_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray112.get64 a 0) false);
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ bN___negc1_ (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_bN___neg_ <- (trace_bN___neg_ ++ tmp__trace);
    trace_bN___neg_ <-
    (trace_bN___neg_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_bN___neg_);
  }
  proc kAR__fun_kmuln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                       b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var trace_kAR__fun_kmuln:trace;
    trace_kAR__fun_kmuln <- [];
    trace_kAR__fun_kmuln <-
    (trace_kAR__fun_kmuln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    return (r, b_r, trace_kAR__fun_kmuln);
  }
  proc kAR____sub_signabs (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                           b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  W64.t * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux:bool;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var cf:bool;
    var param_2:bool;
    var result_1:W64.t;
    var sign:W64.t;
    var param_3:BArray56.t;
    var param_4:W64.t;
    var result_2:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_kAR____sub_signabs:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    trace_kAR____sub_signabs <- [];
    trace_kAR____sub_signabs <-
    (trace_kAR____sub_signabs ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___sub_ (param, b_param, 
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_kAR____sub_signabs <- (trace_kAR____sub_signabs ++ tmp__trace);
    trace_kAR____sub_signabs <-
    (trace_kAR____sub_signabs ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    param_2 <- cf;
    (result_1, tmp__trace) <@ uTIL____cf_mask (param_2);
    trace_kAR____sub_signabs <- (trace_kAR____sub_signabs ++ tmp__trace);
    sign <- result_1;
    param_3 <- r;
    param_4 <- sign;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cnegU_ (param_3,
    (BArray56.init_arr (W8.of_int 255)), param_4);
    result_2 <- aux_2;
    b_result_0 <- aux_3;
    trace_kAR____sub_signabs <- (trace_kAR____sub_signabs ++ tmp__trace);
    trace_kAR____sub_signabs <-
    (trace_kAR____sub_signabs ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_2;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (sign, r, b_r, trace_kAR____sub_signabs);
  }
  proc kAR___kar_muln (r:BArray224.t, b_r:BArray224.t, a:BArray112.t,
                       b_a:BArray112.t, b:BArray112.t, b_b:BArray112.t) : 
  BArray224.t * BArray224.t * trace = {
    var aux_5:BArray112.t;
    var aux_6:BArray112.t;
    var aux_8:BArray112.t;
    var aux_9:BArray112.t;
    var aux_10:BArray112.t;
    var aux_11:BArray112.t;
    var aux_12:BArray112.t;
    var aux_13:BArray112.t;
    var aux_14:BArray112.t;
    var aux_15:BArray112.t;
    var aux_17:BArray112.t;
    var aux_18:BArray112.t;
    var aux_20:BArray112.t;
    var aux_21:BArray112.t;
    var aux_23:BArray112.t;
    var aux_24:BArray112.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_3:BArray56.t;
    var aux_4:BArray56.t;
    var aux_28:BArray56.t;
    var aux_29:BArray56.t;
    var aux:W64.t;
    var aux_2:W64.t;
    var aux_26:W64.t;
    var aux_7:bool;
    var aux_16:bool;
    var aux_19:bool;
    var aux_22:bool;
    var aux_25:bool;
    var aux_27:bool;
    var b__tmp:BArray112.t;
    var b__x:BArray112.t;
    var b__r:BArray224.t;
    var _r:BArray224.t;
    var b_rlo:BArray112.t;
    var rlo:BArray112.t;
    var b_rlolo:BArray56.t;
    var rlolo:BArray56.t;
    var b_alo:BArray56.t;
    var alo:BArray56.t;
    var b_ahi:BArray56.t;
    var ahi:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var b_param_0:BArray56.t;
    var param_0:BArray56.t;
    var b_param_1:BArray56.t;
    var param_1:BArray56.t;
    var result:W64.t;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var sa:W64.t;
    var b_rlohi:BArray56.t;
    var rlohi:BArray56.t;
    var b_blo:BArray56.t;
    var blo:BArray56.t;
    var b_bhi:BArray56.t;
    var bhi:BArray56.t;
    var b_param_2:BArray56.t;
    var param_2:BArray56.t;
    var b_param_3:BArray56.t;
    var param_3:BArray56.t;
    var b_param_4:BArray56.t;
    var param_4:BArray56.t;
    var result_1:W64.t;
    var result_2:BArray56.t;
    var b_result_0:BArray56.t;
    var sb:W64.t;
    var _sa:W64.t;
    var _a:BArray112.t;
    var _b:BArray112.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var _tmp:BArray112.t;
    var b_param_5:BArray112.t;
    var param_5:BArray112.t;
    var b_param_6:BArray56.t;
    var param_6:BArray56.t;
    var b_param_7:BArray56.t;
    var param_7:BArray56.t;
    var result_3:BArray112.t;
    var b_result_1:BArray112.t;
    var b_x:BArray112.t;
    var x:BArray112.t;
    var _x:BArray112.t;
    var b_param_8:BArray112.t;
    var param_8:BArray112.t;
    var param_9:BArray112.t;
    var result_4:bool;
    var result_5:BArray112.t;
    var b_result_2:BArray112.t;
    var cf:bool;
    var param_10:bool;
    var result_6:W64.t;
    var m:W64.t;
    var param_11:W64.t;
    var result_7:bool;
    var param_12:BArray112.t;
    var param_13:bool;
    var param_14:BArray112.t;
    var result_8:BArray112.t;
    var b_result_3:BArray112.t;
    var b_param_9:BArray112.t;
    var param_15:BArray112.t;
    var b_param_10:BArray56.t;
    var param_16:BArray56.t;
    var b_param_11:BArray56.t;
    var param_17:BArray56.t;
    var result_9:BArray112.t;
    var b_result_4:BArray112.t;
    var b_rhi:BArray112.t;
    var rhi:BArray112.t;
    var b_param_12:BArray112.t;
    var param_18:BArray112.t;
    var b_param_13:BArray56.t;
    var param_19:BArray56.t;
    var b_param_14:BArray56.t;
    var param_20:BArray56.t;
    var result_10:BArray112.t;
    var b_result_5:BArray112.t;
    var param_21:BArray112.t;
    var b_param_15:BArray112.t;
    var param_22:BArray112.t;
    var result_11:bool;
    var result_12:BArray112.t;
    var b_result_6:BArray112.t;
    var param_23:BArray112.t;
    var b_param_16:BArray112.t;
    var param_24:BArray112.t;
    var result_13:bool;
    var result_14:BArray112.t;
    var b_result_7:BArray112.t;
    var b_rmid:BArray112.t;
    var rmid:BArray112.t;
    var b_param_17:BArray112.t;
    var param_25:BArray112.t;
    var param_26:BArray112.t;
    var result_15:bool;
    var result_16:BArray112.t;
    var b_result_8:BArray112.t;
    var b_rhihi:BArray56.t;
    var rhihi:BArray56.t;
    var b_param_18:BArray56.t;
    var param_27:BArray56.t;
    var param_28:bool;
    var param_29:int;
    var result_17:bool;
    var result_18:BArray56.t;
    var b_result_9:BArray56.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_kAR___kar_muln:trace;
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
    trace_kAR___kar_muln <- [];
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert,
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b_b 0 112)))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    b__x <- (BArray112.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    b_rlo <- (SBArray224_112.get_sub64 b__r 0);
    rlo <- (SBArray224_112.get_sub64 _r 0);
    b_rlolo <- (SBArray224_56.get_sub64 b_r 0);
    rlolo <- (SBArray224_56.get_sub64 r 0);
    b_alo <- (SBArray112_56.get_sub64 b_a 0);
    alo <- (SBArray112_56.get_sub64 a 0);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_ahi <- (SBArray112_56.get_sub64 b_a 7);
    ahi <- (SBArray112_56.get_sub64 a 7);
    b_param <- b_rlolo;
    param <- rlolo;
    b_param_0 <- b_alo;
    param_0 <- alo;
    b_param_1 <- b_ahi;
    param_1 <- ahi;
    (aux, aux_0, aux_1, tmp__trace) <@ kAR____sub_signabs (param, b_param,
    param_0, b_param_0, param_1, b_param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    sa <- result;
    rlolo <- result_0;
    b_rlo <-
    (SBArray112_56.set_sub64 b_rlo 0 (BArray56.init_arr (W8.of_int 255)));
    rlo <- (SBArray112_56.set_sub64 rlo 0 rlolo);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_rlohi <- (SBArray112_56.get_sub64 b_rlo 7);
    rlohi <- (SBArray112_56.get_sub64 rlo 7);
    b_blo <- (SBArray112_56.get_sub64 b_b 0);
    blo <- (SBArray112_56.get_sub64 b 0);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_bhi <- (SBArray112_56.get_sub64 b_b 7);
    bhi <- (SBArray112_56.get_sub64 b 7);
    b_param_2 <- b_rlohi;
    param_2 <- rlohi;
    b_param_3 <- b_bhi;
    param_3 <- bhi;
    b_param_4 <- b_blo;
    param_4 <- blo;
    (aux_2, aux_3, aux_4, tmp__trace) <@ kAR____sub_signabs (param_2,
    b_param_2, param_3, b_param_3, param_4, b_param_4);
    result_1 <- aux_2;
    result_2 <- aux_3;
    b_result_0 <- aux_4;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    sb <- result_1;
    rlohi <- result_2;
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_rlo <-
    (SBArray112_56.set_sub64 b_rlo 7 (BArray56.init_arr (W8.of_int 255)));
    rlo <- (SBArray112_56.set_sub64 rlo 7 rlohi);
    b__r <- (SBArray224_112.set_sub64 b__r 0 b_rlo);
    _r <- (SBArray224_112.set_sub64 _r 0 rlo);
    sa <- (sa `^` sb);
    _sa <- sa;
    _a <- a;
    _b <- b;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_rlo <- (SBArray224_112.get_sub64 b__r 0);
    rlo <- (SBArray224_112.get_sub64 _r 0);
    b_rlolo <- (SBArray112_56.get_sub64 b_rlo 0);
    rlolo <- (SBArray112_56.get_sub64 rlo 0);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_rlohi <- (SBArray112_56.get_sub64 b_rlo 7);
    rlohi <- (SBArray112_56.get_sub64 rlo 7);
    b_param_5 <- b_tmp;
    param_5 <- tmp;
    b_param_6 <- b_rlolo;
    param_6 <- rlolo;
    b_param_7 <- b_rlohi;
    param_7 <- rlohi;
    (aux_5, aux_6, tmp__trace) <@ kAR__fun_kmuln (param_5, b_param_5,
    param_6, b_param_6, param_7, b_param_7);
    result_3 <- aux_5;
    b_result_1 <- aux_6;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_1 0 112))]);
    tmp <- result_3;
    b_x <- b__x;
    x <- _x;
    b_param_8 <- b_x;
    param_8 <- x;
    param_9 <- tmp;
    (aux_7, aux_8, aux_9, tmp__trace) <@ bN___neg_ (param_8, b_param_8,
    param_9, (BArray112.init_arr (W8.of_int 255)));
    result_4 <- aux_7;
    result_5 <- aux_8;
    b_result_2 <- aux_9;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_2 0 112))]);
    cf <- result_4;
    x <- result_5;
    param_10 <- cf;
    (result_6, tmp__trace) <@ uTIL____cf_mask (param_10);
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    m <- result_6;
    sa <- _sa;
    sa <- (sa `&` m);
    _sa <- sa;
    param_11 <- sa;
    (result_7, tmp__trace) <@ uTIL____mask_cf (param_11);
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    cf <- result_7;
    param_12 <- tmp;
    param_13 <- cf;
    param_14 <- x;
    (aux_10, aux_11, tmp__trace) <@ bN___cmov_ (param_12,
    (BArray112.init_arr (W8.of_int 255)), param_13, param_14,
    (BArray112.init_arr (W8.of_int 255)));
    result_8 <- aux_10;
    b_result_3 <- aux_11;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_3 0 112))]);
    tmp <- result_8;
    _tmp <- tmp;
    b_rlo <- (SBArray224_112.get_sub64 b__r 0);
    rlo <- (SBArray224_112.get_sub64 _r 0);
    b_a <- (BArray112.init_arr (W8.of_int 255));
    a <- _a;
    b_alo <- (SBArray112_56.get_sub64 b_a 0);
    alo <- (SBArray112_56.get_sub64 a 0);
    b_b <- (BArray112.init_arr (W8.of_int 255));
    b <- _b;
    b_blo <- (SBArray112_56.get_sub64 b_b 0);
    blo <- (SBArray112_56.get_sub64 b 0);
    b_param_9 <- b_rlo;
    param_15 <- rlo;
    b_param_10 <- b_alo;
    param_16 <- alo;
    b_param_11 <- b_blo;
    param_17 <- blo;
    (aux_12, aux_13, tmp__trace) <@ kAR__fun_kmuln (param_15, b_param_9,
    param_16, b_param_10, param_17, b_param_11);
    result_9 <- aux_12;
    b_result_4 <- aux_13;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_4 0 112))]);
    rlo <- result_9;
    b__r <-
    (SBArray224_112.set_sub64 b__r 0 (BArray112.init_arr (W8.of_int 255)));
    _r <- (SBArray224_112.set_sub64 _r 0 rlo);
    b_a <- (BArray112.init_arr (W8.of_int 255));
    a <- _a;
    b_b <- (BArray112.init_arr (W8.of_int 255));
    b <- _b;
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_ahi <- (SBArray112_56.get_sub64 b_a 7);
    ahi <- (SBArray112_56.get_sub64 a 7);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_bhi <- (SBArray112_56.get_sub64 b_b 7);
    bhi <- (SBArray112_56.get_sub64 b 7);
    b_r <- b__r;
    r <- _r;
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 112) <= 224)))]);
    b_rhi <- (SBArray224_112.get_sub64 b_r 14);
    rhi <- (SBArray224_112.get_sub64 r 14);
    b_param_12 <- b_rhi;
    param_18 <- rhi;
    b_param_13 <- b_ahi;
    param_19 <- ahi;
    b_param_14 <- b_bhi;
    param_20 <- bhi;
    (aux_14, aux_15, tmp__trace) <@ kAR__fun_kmuln (param_18, b_param_12,
    param_19, b_param_13, param_20, b_param_14);
    result_10 <- aux_14;
    b_result_5 <- aux_15;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_5 0 112))]);
    rhi <- result_10;
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 112) <= 224)))]);
    b__r <-
    (SBArray224_112.set_sub64 b__r 14 (BArray112.init_arr (W8.of_int 255)));
    _r <- (SBArray224_112.set_sub64 _r 14 rhi);
    b_r <- b__r;
    r <- _r;
    tmp <- _tmp;
    b_rlo <- (SBArray224_112.get_sub64 b_r 0);
    rlo <- (SBArray224_112.get_sub64 r 0);
    param_21 <- tmp;
    b_param_15 <- b_rlo;
    param_22 <- rlo;
    (aux_16, aux_17, aux_18, tmp__trace) <@ bN___addU_ (param_21,
    (BArray112.init_arr (W8.of_int 255)), param_22, b_param_15);
    result_11 <- aux_16;
    result_12 <- aux_17;
    b_result_6 <- aux_18;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_6 0 112))]);
    cf <- result_11;
    tmp <- result_12;
    sa <- _sa;
    ( _0, sa) <- (adc_64 sa (W64.of_int 0) cf);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 112) <= 224)))]);
    b_rhi <- (SBArray224_112.get_sub64 b_r 14);
    rhi <- (SBArray224_112.get_sub64 r 14);
    param_23 <- tmp;
    b_param_16 <- b_rhi;
    param_24 <- rhi;
    (aux_19, aux_20, aux_21, tmp__trace) <@ bN___addU_ (param_23,
    (BArray112.init_arr (W8.of_int 255)), param_24, b_param_16);
    result_13 <- aux_19;
    result_14 <- aux_20;
    b_result_7 <- aux_21;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_7 0 112))]);
    cf <- result_13;
    tmp <- result_14;
    ( _1, sa) <- (adc_64 sa (W64.of_int 0) cf);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 112) <= 224)))]);
    b_rmid <- (SBArray224_112.get_sub64 b_r 7);
    rmid <- (SBArray224_112.get_sub64 r 7);
    b_param_17 <- b_rmid;
    param_25 <- rmid;
    param_26 <- tmp;
    (aux_22, aux_23, aux_24, tmp__trace) <@ bN___addU_ (param_25, b_param_17,
    param_26, (BArray112.init_arr (W8.of_int 255)));
    result_15 <- aux_22;
    result_16 <- aux_23;
    b_result_8 <- aux_24;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray112.is_init b_result_8 0 112))]);
    cf <- result_15;
    rmid <- result_16;
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 112) <= 224)))]);
    b_r <-
    (SBArray224_112.set_sub64 b_r 7 (BArray112.init_arr (W8.of_int 255)));
    r <- (SBArray224_112.set_sub64 r 7 rmid);
    ( _2, sa) <- (adc_64 sa (W64.of_int 0) cf);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 8) <= 224)))]);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 8) <= 224)))]);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, (BArray224.is_init b_r ((3 * 7) * 8) 8))]);
    b_r <-
    (BArray224.set64d b_r ((3 * 7) * 8) (W64.of_int 18446744073709551615));
    (aux_25, aux_26) <- (adc_64 (BArray224.get64 r (3 * 7)) sa false);
    cf <- aux_25;
    r <- (BArray224.set64 r (3 * 7) aux_26);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 56) <= 224)))]);
    b_rhihi <- (SBArray224_56.get_sub64 b_r (3 * 7));
    rhihi <- (SBArray224_56.get_sub64 r (3 * 7));
    b_param_18 <- b_rhihi;
    param_27 <- rhihi;
    param_28 <- cf;
    param_29 <- 1;
    (aux_27, aux_28, aux_29, tmp__trace) <@ h__BN____carrypropU (param_27,
    b_param_18, param_28, param_29);
    result_17 <- aux_27;
    result_18 <- aux_28;
    b_result_9 <- aux_29;
    trace_kAR___kar_muln <- (trace_kAR___kar_muln ++ tmp__trace);
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++ [(Assert, (BArray56.is_init b_result_9 0 56))]);
    rhihi <- result_18;
    trace_kAR___kar_muln <-
    (trace_kAR___kar_muln ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 56) <= 224)))]);
    b_r <-
    (SBArray224_56.set_sub64 b_r (3 * 7) (BArray56.init_arr (W8.of_int 255)));
    r <- (SBArray224_56.set_sub64 r (3 * 7) rhihi);
    return (r, b_r, trace_kAR___kar_muln);
  }
  proc kAR___kar_muln_ (r:BArray224.t, b_r:BArray224.t, a:BArray112.t,
                        b_a:BArray112.t, b:BArray112.t, b_b:BArray112.t) : 
  BArray224.t * BArray224.t * trace = {
    var aux:BArray224.t;
    var aux_0:BArray224.t;
    var b_param:BArray224.t;
    var param:BArray224.t;
    var param_0:BArray112.t;
    var param_1:BArray112.t;
    var result:BArray224.t;
    var b_result:BArray224.t;
    var trace_kAR___kar_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_kAR___kar_muln_ <- [];
    trace_kAR___kar_muln_ <-
    (trace_kAR___kar_muln_ ++
    [(Assert,
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b_b 0 112)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ kAR___kar_muln (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1,
    (BArray112.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_kAR___kar_muln_ <- (trace_kAR___kar_muln_ ++ tmp__trace);
    trace_kAR___kar_muln_ <-
    (trace_kAR___kar_muln_ ++ [(Assert, (BArray224.is_init b_result 0 224))]);
    r <- result;
    r <- r;
    b_r <- (BArray224.init_arr (W8.of_int 255));
    return (r, b_r, trace_kAR___kar_muln_);
  }
}.

(* The post and trace are valid. *)

op uTIL____mask_cf_spec _mask =
   hoare [M.uTIL____mask_cf :
   ((_mask = mask) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

op h__BN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN____carrypropU_spec _a _b_a _cf _k =
   hoare [M.h__BN____carrypropU :
   (((_k = k) /\ ((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   (true /\ ((0 <= _k) /\ (BArray56.is_init _b_a 0 (8 * 7))))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN____subc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN____subc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7))) /\
   (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___subc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7))) /\
   (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___subc1__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc1_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7))) /\
   (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___sub__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__BN___sub_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___neg__spec _r _b_r _a _b_a =
   hoare [M.h__BN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___cnegU__spec _a _b_a _cond =
   hoare [M.h__BN___cnegU_ :
   (((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op bN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.bN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`2 0 112) /\ (valid res.`3))].

op bN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.bN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`2 0 112) /\ (valid res.`3))].

op bN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.bN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`2 0 112) /\ (valid res.`3))].

op bN____addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.bN____addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op bN___addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.bN___addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op bN___addc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.bN___addc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op bN___addU__spec _a _b_a _b _b_b =
   hoare [M.bN___addU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op bN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.bN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray112.is_init _b_r 0 8) /\ (BArray112.is_init _b_a 0 (8 * 14)))) ==>
   ((BArray112.is_init res.`3 0 (8 * 14)) /\ (valid res.`4))].

op bN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.bN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray112.is_init _b_r 0 8) /\ (BArray112.is_init _b_a 0 (8 * 14)))) ==>
   ((BArray112.is_init res.`3 0 (8 * 14)) /\ (valid res.`4))].

op bN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.bN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray112.is_init _b_r 0 8) /\ (BArray112.is_init _b_a 0 (8 * 14)))) ==>
   ((BArray112.is_init res.`3 0 (8 * 14)) /\ (valid res.`4))].

op bN___neg__spec _r _b_r _a _b_a =
   hoare [M.bN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray112.is_init _b_a 0 (8 * 14))) ==>
   ((BArray112.is_init res.`3 0 (8 * 14)) /\ (valid res.`4))].

op kAR__fun_kmuln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.kAR__fun_kmuln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (8 * 14)) /\ (valid res.`3))].

op kAR____sub_signabs_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.kAR____sub_signabs :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op kAR___kar_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.kAR___kar_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (8 * 14)) /\
   (BArray112.is_init _b_b 0 (8 * 14)))) ==>
   ((BArray224.is_init res.`2 0 (16 * 14)) /\ (valid res.`3))].

op kAR___kar_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.kAR___kar_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (8 * 14)) /\
   (BArray112.is_init _b_b 0 (8 * 14)))) ==>
   ((BArray224.is_init res.`2 0 (16 * 14)) /\ (valid res.`3))].
