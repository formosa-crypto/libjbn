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
  proc kSQR__BN____subc1U (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
                           b_b:BArray112.t, cf:bool) : bool * BArray112.t *
                                                       BArray112.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_kSQR__BN____subc1U:trace;
    trace_kSQR__BN____subc1U <- [];
    trace_kSQR__BN____subc1U <-
    (trace_kSQR__BN____subc1U ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_kSQR__BN____subc1U <-
    (trace_kSQR__BN____subc1U ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    i <- 1;
    while ((i < 14)) {
      trace_kSQR__BN____subc1U <-
      (trace_kSQR__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      t <- (BArray112.get64 b i);
      trace_kSQR__BN____subc1U <-
      (trace_kSQR__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_kSQR__BN____subc1U <-
      (trace_kSQR__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      (aux, aux_0) <- (sbb_64 (BArray112.get64 a i) t cf);
      cf <- aux;
      a <- (BArray112.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_kSQR__BN____subc1U);
  }
  proc kSQR__BN___subc1U (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
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
    var trace_kSQR__BN___subc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_kSQR__BN___subc1U <- [];
    trace_kSQR__BN___subc1U <-
    (trace_kSQR__BN___subc1U ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_kSQR__BN___subc1U <-
    (trace_kSQR__BN___subc1U ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ kSQR__BN____subc1U (param,
    (BArray112.init_arr (W8.of_int 255)), param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_kSQR__BN___subc1U <- (trace_kSQR__BN___subc1U ++ tmp__trace);
    trace_kSQR__BN___subc1U <-
    (trace_kSQR__BN___subc1U ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_kSQR__BN___subc1U);
  }
  proc kSQR__BN___subc1U_ (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
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
    var trace_kSQR__BN___subc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_kSQR__BN___subc1U_ <- [];
    trace_kSQR__BN___subc1U_ <-
    (trace_kSQR__BN___subc1U_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_kSQR__BN___subc1U_ <-
    (trace_kSQR__BN___subc1U_ ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ kSQR__BN___subc1U (param,
    (BArray112.init_arr (W8.of_int 255)), param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_kSQR__BN___subc1U_ <- (trace_kSQR__BN___subc1U_ ++ tmp__trace);
    trace_kSQR__BN___subc1U_ <-
    (trace_kSQR__BN___subc1U_ ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_kSQR__BN___subc1U_);
  }
  proc kSQR__BN___subU_ (a:BArray112.t, b_a:BArray112.t, b:BArray112.t,
                         b_b:BArray112.t) : bool * BArray112.t *
                                            BArray112.t * trace = {
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
    var trace_kSQR__BN___subU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_kSQR__BN___subU_ <- [];
    trace_kSQR__BN___subU_ <-
    (trace_kSQR__BN___subU_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    trace_kSQR__BN___subU_ <-
    (trace_kSQR__BN___subU_ ++ [(Assert, (BArray112.is_init b_b 0 112))]);
    t <- (BArray112.get64 b 0);
    (aux, aux_0) <- (sbb_64 (BArray112.get64 a 0) t false);
    cf <- aux;
    a <- (BArray112.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ kSQR__BN___subc1U_ (param,
    (BArray112.init_arr (W8.of_int 255)), param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_kSQR__BN___subU_ <- (trace_kSQR__BN___subU_ ++ tmp__trace);
    trace_kSQR__BN___subU_ <-
    (trace_kSQR__BN___subU_ ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_kSQR__BN___subU_);
  }
  proc kSQR__fun_ksqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                        b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var trace_kSQR__fun_ksqrn:trace;
    trace_kSQR__fun_ksqrn <- [];
    trace_kSQR__fun_ksqrn <-
    (trace_kSQR__fun_ksqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    return (r, b_r, trace_kSQR__fun_ksqrn);
  }
  proc kSQR____sub_abs (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                        b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray56.t * BArray56.t * trace = {
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
    var trace_kSQR____sub_abs:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    trace_kSQR____sub_abs <- [];
    trace_kSQR____sub_abs <-
    (trace_kSQR____sub_abs ++
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
    trace_kSQR____sub_abs <- (trace_kSQR____sub_abs ++ tmp__trace);
    trace_kSQR____sub_abs <-
    (trace_kSQR____sub_abs ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    param_2 <- cf;
    (result_1, tmp__trace) <@ uTIL____cf_mask (param_2);
    trace_kSQR____sub_abs <- (trace_kSQR____sub_abs ++ tmp__trace);
    sign <- result_1;
    param_3 <- r;
    param_4 <- sign;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cnegU_ (param_3,
    (BArray56.init_arr (W8.of_int 255)), param_4);
    result_2 <- aux_2;
    b_result_0 <- aux_3;
    trace_kSQR____sub_abs <- (trace_kSQR____sub_abs ++ tmp__trace);
    trace_kSQR____sub_abs <-
    (trace_kSQR____sub_abs ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_2;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_kSQR____sub_abs);
  }
  proc kSQR___kar_sqrn (r:BArray224.t, b_r:BArray224.t, a:BArray112.t,
                        b_a:BArray112.t) : BArray224.t * BArray224.t * trace = {
    var aux_1:BArray112.t;
    var aux_2:BArray112.t;
    var aux_3:BArray112.t;
    var aux_4:BArray112.t;
    var aux_5:BArray112.t;
    var aux_6:BArray112.t;
    var aux_8:BArray112.t;
    var aux_9:BArray112.t;
    var aux_11:BArray112.t;
    var aux_12:BArray112.t;
    var aux_14:BArray112.t;
    var aux_15:BArray112.t;
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_19:BArray56.t;
    var aux_20:BArray56.t;
    var aux_17:W64.t;
    var aux_7:bool;
    var aux_10:bool;
    var aux_13:bool;
    var aux_16:bool;
    var aux_18:bool;
    var b__tmp:BArray112.t;
    var b_d:BArray56.t;
    var d:BArray56.t;
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
    var result:BArray56.t;
    var b_result:BArray56.t;
    var _a:BArray112.t;
    var b__r:BArray224.t;
    var _r:BArray224.t;
    var b_rlo:BArray112.t;
    var rlo:BArray112.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var _tmp:BArray112.t;
    var b_param_2:BArray112.t;
    var param_2:BArray112.t;
    var b_param_3:BArray56.t;
    var param_3:BArray56.t;
    var result_0:BArray112.t;
    var b_result_0:BArray112.t;
    var b_param_4:BArray112.t;
    var param_4:BArray112.t;
    var b_param_5:BArray56.t;
    var param_5:BArray56.t;
    var result_1:BArray112.t;
    var b_result_1:BArray112.t;
    var b_rhi:BArray112.t;
    var rhi:BArray112.t;
    var b_param_6:BArray112.t;
    var param_6:BArray112.t;
    var b_param_7:BArray56.t;
    var param_7:BArray56.t;
    var result_2:BArray112.t;
    var b_result_2:BArray112.t;
    var c:W64.t;
    var param_8:BArray112.t;
    var b_param_8:BArray112.t;
    var param_9:BArray112.t;
    var result_3:bool;
    var result_4:BArray112.t;
    var b_result_3:BArray112.t;
    var cf:bool;
    var param_10:BArray112.t;
    var b_param_9:BArray112.t;
    var param_11:BArray112.t;
    var result_5:bool;
    var result_6:BArray112.t;
    var b_result_4:BArray112.t;
    var b_rmid:BArray112.t;
    var rmid:BArray112.t;
    var b_param_10:BArray112.t;
    var param_12:BArray112.t;
    var param_13:BArray112.t;
    var result_7:bool;
    var result_8:BArray112.t;
    var b_result_5:BArray112.t;
    var b_rhihi:BArray56.t;
    var rhihi:BArray56.t;
    var b_param_11:BArray56.t;
    var param_14:BArray56.t;
    var param_15:bool;
    var param_16:int;
    var result_9:bool;
    var result_10:BArray56.t;
    var b_result_6:BArray56.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_kSQR___kar_sqrn:trace;
    _a <- witness;
    _r <- witness;
    _tmp <- witness;
    ahi <- witness;
    alo <- witness;
    b__r <- witness;
    b__tmp <- witness;
    b_ahi <- witness;
    b_alo <- witness;
    b_d <- witness;
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
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_rhi <- witness;
    b_rhihi <- witness;
    b_rlo <- witness;
    b_rmid <- witness;
    b_tmp <- witness;
    d <- witness;
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
    param_10 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_14 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_4 <- witness;
    result_6 <- witness;
    result_8 <- witness;
    result_10 <- witness;
    rhi <- witness;
    rhihi <- witness;
    rlo <- witness;
    rmid <- witness;
    tmp <- witness;
    trace_kSQR___kar_sqrn <- [];
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    b_d <- (SBArray224_56.get_sub64 b_r 0);
    d <- (SBArray224_56.get_sub64 r 0);
    b_alo <- (SBArray112_56.get_sub64 b_a 0);
    alo <- (SBArray112_56.get_sub64 a 0);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_ahi <- (SBArray112_56.get_sub64 b_a 7);
    ahi <- (SBArray112_56.get_sub64 a 7);
    b_param <- b_d;
    param <- d;
    b_param_0 <- b_alo;
    param_0 <- alo;
    b_param_1 <- b_ahi;
    param_1 <- ahi;
    (aux, aux_0, tmp__trace) <@ kSQR____sub_abs (param, b_param, param_0,
    b_param_0, param_1, b_param_1);
    result <- aux;
    b_result <- aux_0;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    d <- result;
    b_r <-
    (SBArray224_56.set_sub64 b_r 0 (BArray56.init_arr (W8.of_int 255)));
    r <- (SBArray224_56.set_sub64 r 0 d);
    _a <- a;
    b__r <- b_r;
    _r <- r;
    b_rlo <- (SBArray224_112.get_sub64 b__r 0);
    rlo <- (SBArray224_112.get_sub64 _r 0);
    b_d <- (SBArray112_56.get_sub64 b_rlo 0);
    d <- (SBArray112_56.get_sub64 rlo 0);
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param_2 <- b_tmp;
    param_2 <- tmp;
    b_param_3 <- b_d;
    param_3 <- d;
    (aux_1, aux_2, tmp__trace) <@ kSQR__fun_ksqrn (param_2, b_param_2,
    param_3, b_param_3);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray112.is_init b_result_0 0 112))]);
    tmp <- result_0;
    _tmp <- tmp;
    b_a <- (BArray112.init_arr (W8.of_int 255));
    a <- _a;
    b_alo <- (SBArray112_56.get_sub64 b_a 0);
    alo <- (SBArray112_56.get_sub64 a 0);
    b_rlo <- (SBArray224_112.get_sub64 b__r 0);
    rlo <- (SBArray224_112.get_sub64 _r 0);
    b_param_4 <- b_rlo;
    param_4 <- rlo;
    b_param_5 <- b_alo;
    param_5 <- alo;
    (aux_3, aux_4, tmp__trace) <@ kSQR__fun_ksqrn (param_4, b_param_4,
    param_5, b_param_5);
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray112.is_init b_result_1 0 112))]);
    rlo <- result_1;
    b__r <-
    (SBArray224_112.set_sub64 b__r 0 (BArray112.init_arr (W8.of_int 255)));
    _r <- (SBArray224_112.set_sub64 _r 0 rlo);
    b_a <- (BArray112.init_arr (W8.of_int 255));
    a <- _a;
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_ahi <- (SBArray112_56.get_sub64 b_a 7);
    ahi <- (SBArray112_56.get_sub64 a 7);
    b_r <- b__r;
    r <- _r;
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 112) <= 224)))]);
    b_rhi <- (SBArray224_112.get_sub64 b_r 14);
    rhi <- (SBArray224_112.get_sub64 r 14);
    b_param_6 <- b_rhi;
    param_6 <- rhi;
    b_param_7 <- b_ahi;
    param_7 <- ahi;
    (aux_5, aux_6, tmp__trace) <@ kSQR__fun_ksqrn (param_6, b_param_6,
    param_7, b_param_7);
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray112.is_init b_result_2 0 112))]);
    rhi <- result_2;
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 112) <= 224)))]);
    b__r <-
    (SBArray224_112.set_sub64 b__r 14 (BArray112.init_arr (W8.of_int 255)));
    _r <- (SBArray224_112.set_sub64 _r 14 rhi);
    b_r <- b__r;
    r <- _r;
    tmp <- _tmp;
    c <- (W64.of_int 0);
    b_rlo <- (SBArray224_112.get_sub64 b_r 0);
    rlo <- (SBArray224_112.get_sub64 r 0);
    param_8 <- tmp;
    b_param_8 <- b_rlo;
    param_9 <- rlo;
    (aux_7, aux_8, aux_9, tmp__trace) <@ kSQR__BN___subU_ (param_8,
    (BArray112.init_arr (W8.of_int 255)), param_9, b_param_8);
    result_3 <- aux_7;
    result_4 <- aux_8;
    b_result_3 <- aux_9;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray112.is_init b_result_3 0 112))]);
    cf <- result_3;
    tmp <- result_4;
    ( _0, c) <- (adc_64 c (W64.of_int 0) cf);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 112) <= 224)))]);
    b_rhi <- (SBArray224_112.get_sub64 b_r 14);
    rhi <- (SBArray224_112.get_sub64 r 14);
    param_10 <- tmp;
    b_param_9 <- b_rhi;
    param_11 <- rhi;
    (aux_10, aux_11, aux_12, tmp__trace) <@ kSQR__BN___subU_ (param_10,
    (BArray112.init_arr (W8.of_int 255)), param_11, b_param_9);
    result_5 <- aux_10;
    result_6 <- aux_11;
    b_result_4 <- aux_12;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray112.is_init b_result_4 0 112))]);
    cf <- result_5;
    tmp <- result_6;
    ( _1, c) <- (adc_64 c (W64.of_int 0) cf);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 112) <= 224)))]);
    b_rmid <- (SBArray224_112.get_sub64 b_r 7);
    rmid <- (SBArray224_112.get_sub64 r 7);
    b_param_10 <- b_rmid;
    param_12 <- rmid;
    param_13 <- tmp;
    (aux_13, aux_14, aux_15, tmp__trace) <@ kSQR__BN___subU_ (param_12,
    b_param_10, param_13, (BArray112.init_arr (W8.of_int 255)));
    result_7 <- aux_13;
    result_8 <- aux_14;
    b_result_5 <- aux_15;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray112.is_init b_result_5 0 112))]);
    cf <- result_7;
    rmid <- result_8;
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 112) <= 224)))]);
    b_r <-
    (SBArray224_112.set_sub64 b_r 7 (BArray112.init_arr (W8.of_int 255)));
    r <- (SBArray224_112.set_sub64 r 7 rmid);
    ( _2, c) <- (sbb_64 c (W64.of_int 0) cf);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 8) <= 224)))]);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 8) <= 224)))]);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, (BArray224.is_init b_r ((3 * 7) * 8) 8))]);
    b_r <-
    (BArray224.set64d b_r ((3 * 7) * 8) (W64.of_int 18446744073709551615));
    (aux_16, aux_17) <- (adc_64 (BArray224.get64 r (3 * 7)) c false);
    cf <- aux_16;
    r <- (BArray224.set64 r (3 * 7) aux_17);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 56) <= 224)))]);
    b_rhihi <- (SBArray224_56.get_sub64 b_r (3 * 7));
    rhihi <- (SBArray224_56.get_sub64 r (3 * 7));
    b_param_11 <- b_rhihi;
    param_14 <- rhihi;
    param_15 <- cf;
    param_16 <- 1;
    (aux_18, aux_19, aux_20, tmp__trace) <@ h__BN____carrypropU (param_14,
    b_param_11, param_15, param_16);
    result_9 <- aux_18;
    result_10 <- aux_19;
    b_result_6 <- aux_20;
    trace_kSQR___kar_sqrn <- (trace_kSQR___kar_sqrn ++ tmp__trace);
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++ [(Assert, (BArray56.is_init b_result_6 0 56))]);
    rhihi <- result_10;
    trace_kSQR___kar_sqrn <-
    (trace_kSQR___kar_sqrn ++
    [(Assert, ((0 <= ((3 * 7) * 8)) /\ ((((3 * 7) * 8) + 56) <= 224)))]);
    b_r <-
    (SBArray224_56.set_sub64 b_r (3 * 7) (BArray56.init_arr (W8.of_int 255)));
    r <- (SBArray224_56.set_sub64 r (3 * 7) rhihi);
    return (r, b_r, trace_kSQR___kar_sqrn);
  }
  proc kSQR___kar_sqrn_ (r:BArray224.t, b_r:BArray224.t, a:BArray112.t,
                         b_a:BArray112.t) : BArray224.t * BArray224.t * trace = {
    var aux:BArray224.t;
    var aux_0:BArray224.t;
    var b_param:BArray224.t;
    var param:BArray224.t;
    var param_0:BArray112.t;
    var result:BArray224.t;
    var b_result:BArray224.t;
    var trace_kSQR___kar_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_kSQR___kar_sqrn_ <- [];
    trace_kSQR___kar_sqrn_ <-
    (trace_kSQR___kar_sqrn_ ++ [(Assert, (BArray112.is_init b_a 0 112))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ kSQR___kar_sqrn (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_kSQR___kar_sqrn_ <- (trace_kSQR___kar_sqrn_ ++ tmp__trace);
    trace_kSQR___kar_sqrn_ <-
    (trace_kSQR___kar_sqrn_ ++
    [(Assert, (BArray224.is_init b_result 0 224))]);
    r <- result;
    r <- r;
    b_r <- (BArray224.init_arr (W8.of_int 255));
    return (r, b_r, trace_kSQR___kar_sqrn_);
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

op kSQR__BN____subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.kSQR__BN____subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op kSQR__BN___subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.kSQR__BN___subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op kSQR__BN___subc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.kSQR__BN___subc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op kSQR__BN___subU__spec _a _b_a _b _b_b =
   hoare [M.kSQR__BN___subU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray112.is_init _b_b 0 112) /\ (BArray112.is_init _b_a 0 112))) ==>
   ((BArray112.is_init res.`3 0 112) /\ (valid res.`4))].

op kSQR__fun_ksqrn_spec _r _b_r _a _b_a =
   hoare [M.kSQR__fun_ksqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (8 * 14)) /\ (valid res.`3))].

op kSQR____sub_abs_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.kSQR____sub_abs :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op kSQR___kar_sqrn_spec _r _b_r _a _b_a =
   hoare [M.kSQR___kar_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray112.is_init _b_a 0 (8 * 14))) ==>
   ((BArray224.is_init res.`2 0 (16 * 14)) /\ (valid res.`3))].

op kSQR___kar_sqrn__spec _r _b_r _a _b_a =
   hoare [M.kSQR___kar_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray112.is_init _b_a 0 (8 * 14))) ==>
   ((BArray224.is_init res.`2 0 (16 * 14)) /\ (valid res.`3))].
