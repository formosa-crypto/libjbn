require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array7 Array14 Array29 Array56 Array112 Array232 BArray56 BArray112 BArray232
SBArray232_56.

module M = {
  var tmp__trace : trace
  proc uTIL____cf_mask (cf:bool) : W64.t * trace = {
    var mask:W64.t;
    var  _0:bool;
    var trace_uTIL____cf_mask:trace;
    trace_uTIL____cf_mask <- [];
    mask <- (W64.of_int 0);
    ( _0, mask) <- (sbb_64 mask (W64.of_int 0) cf);
    return (mask, trace_uTIL____cf_mask);
  }
  proc uTIL____ncf_mask (cf:bool) : W64.t * trace = {
    var param:bool;
    var result:W64.t;
    var mask:W64.t;
    var trace_uTIL____ncf_mask:trace;
    trace_uTIL____ncf_mask <- [];
    param <- cf;
    (result, tmp__trace) <@ uTIL____cf_mask (param);
    trace_uTIL____ncf_mask <- (trace_uTIL____ncf_mask ++ tmp__trace);
    mask <- result;
    mask <- (NOT_64 mask);
    return (mask, trace_uTIL____ncf_mask);
  }
  proc h__BN____mov (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                     b_a:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____mov:trace;
    trace_h__BN____mov <- [];
    trace_h__BN____mov <-
    (trace_h__BN____mov ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__BN____mov);
  }
  proc h__BN___mov (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                    b_a:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___mov:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov <- [];
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN____mov (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov <- (trace_h__BN___mov ++ tmp__trace);
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov);
  }
  proc h__BN___mov_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                     b_a:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___mov_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov_ <- [];
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov_ <- (trace_h__BN___mov_ ++ tmp__trace);
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov_);
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
  proc h__BN____and_mask (a:BArray56.t, b_a:BArray56.t, mask:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var i:int;
    var trace_h__BN____and_mask:trace;
    trace_h__BN____and_mask <- [];
    trace_h__BN____and_mask <-
    (trace_h__BN____and_mask ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____and_mask <-
      (trace_h__BN____and_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____and_mask <-
      (trace_h__BN____and_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      a <- (BArray56.set64 a i ((BArray56.get64 a i) `&` mask));
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____and_mask);
  }
  proc h__BN___and_mask (a:BArray56.t, b_a:BArray56.t, mask:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___and_mask:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___and_mask <- [];
    trace_h__BN___and_mask <-
    (trace_h__BN___and_mask ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    param <- a;
    param_0 <- mask;
    (aux, aux_0, tmp__trace) <@ h__BN____and_mask (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___and_mask <- (trace_h__BN___and_mask ++ tmp__trace);
    trace_h__BN___and_mask <-
    (trace_h__BN___and_mask ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___and_mask);
  }
  proc h__BN___and_mask_ (a:BArray56.t, b_a:BArray56.t, mask:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___and_mask_:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___and_mask_ <- [];
    trace_h__BN___and_mask_ <-
    (trace_h__BN___and_mask_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    a <- a;
    mask <- mask;
    param <- a;
    param_0 <- mask;
    (aux, aux_0, tmp__trace) <@ h__BN___and_mask (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___and_mask_ <- (trace_h__BN___and_mask_ ++ tmp__trace);
    trace_h__BN___and_mask_ <-
    (trace_h__BN___and_mask_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___and_mask_);
  }
  proc h__BN____addc1U (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                   BArray56.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1U:trace;
    trace_h__BN____addc1U <- [];
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    i <- 1;
    while ((i < 7)) {
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 b i);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (aux, aux_0) <- (adc_64 (BArray56.get64 a i) t cf);
      cf <- aux;
      a <- (BArray56.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____addc1U);
  }
  proc h__BN___addc1U (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                  BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___addc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U <- [];
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1U (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U <- (trace_h__BN___addc1U ++ tmp__trace);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U);
  }
  proc h__BN___addc1U_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                   BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___addc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U_ <- [];
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1U (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U_ <- (trace_h__BN___addc1U_ ++ tmp__trace);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U_);
  }
  proc h__BN___addU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                      b_b:BArray56.t) : bool * BArray56.t * BArray56.t *
                                        trace = {
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___addU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addU_ <- [];
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    t <- (BArray56.get64 b 0);
    (aux, aux_0) <- (adc_64 (BArray56.get64 a 0) t false);
    cf <- aux;
    a <- (BArray56.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___addc1U_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___addU_ <- (trace_h__BN___addU_ ++ tmp__trace);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addU_);
  }
  proc h__BN____addc1 (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                       b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t, cf:bool) : 
  bool * BArray56.t * BArray56.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1:trace;
    trace_h__BN____addc1 <- [];
    trace_h__BN____addc1 <-
    (trace_h__BN____addc1 ++
    [(Assert,
     (((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)) /\
     (BArray56.is_init b_b 0 56)))]);
    i <- 1;
    while ((i < 7)) {
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (cf, t) <- (adc_64 t (BArray56.get64 b i) cf);
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____addc1);
  }
  proc h__BN___addc1 (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
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
    var trace_h__BN___addc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1 <- [];
    trace_h__BN___addc1 <-
    (trace_h__BN___addc1 ++
    [(Assert,
     (((BArray56.is_init b_r 0 8) /\ (BArray56.is_init b_a 0 56)) /\
     (BArray56.is_init b_b 0 56)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1 (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1 <- (trace_h__BN___addc1 ++ tmp__trace);
    trace_h__BN___addc1 <-
    (trace_h__BN___addc1 ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc1);
  }
  proc h__BN___addc1_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
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
    var trace_h__BN___addc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1_ <- [];
    trace_h__BN___addc1_ <-
    (trace_h__BN___addc1_ ++
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
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1 (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1_ <- (trace_h__BN___addc1_ ++ tmp__trace);
    trace_h__BN___addc1_ <-
    (trace_h__BN___addc1_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc1_);
  }
  proc h__BN___add_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
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
    var trace_h__BN___add_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___add_ <- [];
    trace_h__BN___add_ <-
    (trace_h__BN___add_ ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    t <- (BArray56.get64 a 0);
    (cf, t) <- (adc_64 t (BArray56.get64 b 0) false);
    b_r <- (BArray56.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1_ (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___add_ <- (trace_h__BN___add_ ++ tmp__trace);
    trace_h__BN___add_ <-
    (trace_h__BN___add_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___add_);
  }
  proc h__BN____subc1U (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                   BArray56.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____subc1U:trace;
    trace_h__BN____subc1U <- [];
    trace_h__BN____subc1U <-
    (trace_h__BN____subc1U ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN____subc1U <-
    (trace_h__BN____subc1U ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    i <- 1;
    while ((i < 7)) {
      trace_h__BN____subc1U <-
      (trace_h__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 b i);
      trace_h__BN____subc1U <-
      (trace_h__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____subc1U <-
      (trace_h__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (aux, aux_0) <- (sbb_64 (BArray56.get64 a i) t cf);
      cf <- aux;
      a <- (BArray56.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____subc1U);
  }
  proc h__BN___subc1U (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                  BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subc1U <- [];
    trace_h__BN___subc1U <-
    (trace_h__BN___subc1U ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___subc1U <-
    (trace_h__BN___subc1U ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____subc1U (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___subc1U <- (trace_h__BN___subc1U ++ tmp__trace);
    trace_h__BN___subc1U <-
    (trace_h__BN___subc1U ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subc1U);
  }
  proc h__BN___subc1U_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                   BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subc1U_ <- [];
    trace_h__BN___subc1U_ <-
    (trace_h__BN___subc1U_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___subc1U_ <-
    (trace_h__BN___subc1U_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___subc1U (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___subc1U_ <- (trace_h__BN___subc1U_ ++ tmp__trace);
    trace_h__BN___subc1U_ <-
    (trace_h__BN___subc1U_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subc1U_);
  }
  proc h__BN___subU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                      b_b:BArray56.t) : bool * BArray56.t * BArray56.t *
                                        trace = {
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subU_ <- [];
    trace_h__BN___subU_ <-
    (trace_h__BN___subU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___subU_ <-
    (trace_h__BN___subU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    t <- (BArray56.get64 b 0);
    (aux, aux_0) <- (sbb_64 (BArray56.get64 a 0) t false);
    cf <- aux;
    a <- (BArray56.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___subc1U_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___subU_ <- (trace_h__BN___subU_ ++ tmp__trace);
    trace_h__BN___subU_ <-
    (trace_h__BN___subU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subU_);
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
  proc h__BN____ltc1_cf (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                         b_b:BArray56.t, cf:bool) : bool * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____ltc1_cf:trace;
    trace_h__BN____ltc1_cf <- [];
    trace_h__BN____ltc1_cf <-
    (trace_h__BN____ltc1_cf ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN____ltc1_cf <-
    (trace_h__BN____ltc1_cf ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    i <- 1;
    while ((i < 7)) {
      trace_h__BN____ltc1_cf <-
      (trace_h__BN____ltc1_cf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____ltc1_cf <-
      (trace_h__BN____ltc1_cf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (cf, t) <- (sbb_64 t (BArray56.get64 b i) cf);
      i <- (i + 1);
    }
    return (cf, trace_h__BN____ltc1_cf);
  }
  proc h__BN___ltc1_cf (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, cf:bool) : bool * trace = {
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___ltc1_cf:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___ltc1_cf <- [];
    trace_h__BN___ltc1_cf <-
    (trace_h__BN___ltc1_cf ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___ltc1_cf <-
    (trace_h__BN___ltc1_cf ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN____ltc1_cf (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___ltc1_cf <- (trace_h__BN___ltc1_cf ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___ltc1_cf);
  }
  proc h__BN___ltc1_cf_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                         b_b:BArray56.t, cf:bool) : bool * trace = {
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___ltc1_cf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___ltc1_cf_ <- [];
    trace_h__BN___ltc1_cf_ <-
    (trace_h__BN___ltc1_cf_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___ltc1_cf_ <-
    (trace_h__BN___ltc1_cf_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN___ltc1_cf (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___ltc1_cf_ <- (trace_h__BN___ltc1_cf_ ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___ltc1_cf_);
  }
  proc h__BN___lt_cf_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t) : bool * trace = {
    var t:W64.t;
    var cf:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___lt_cf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___lt_cf_ <- [];
    trace_h__BN___lt_cf_ <-
    (trace_h__BN___lt_cf_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___lt_cf_ <-
    (trace_h__BN___lt_cf_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    t <- (BArray56.get64 a 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 b 0) false);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN___ltc1_cf_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___lt_cf_ <- (trace_h__BN___lt_cf_ ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___lt_cf_);
  }
  proc h__BN___caddU_ (x:BArray56.t, b_x:BArray56.t, cf:bool, y:BArray56.t,
                       b_y:BArray56.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_4:BArray56.t;
    var aux_5:BArray56.t;
    var aux_3:bool;
    var b__tmp:BArray56.t;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var _tmp:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var param_1:bool;
    var result_0:W64.t;
    var mask:W64.t;
    var param_2:BArray56.t;
    var param_3:W64.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var param_4:BArray56.t;
    var param_5:BArray56.t;
    var result_2:bool;
    var result_3:BArray56.t;
    var b_result_1:BArray56.t;
    var trace_h__BN___caddU_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_1 <- witness;
    result_3 <- witness;
    tmp <- witness;
    trace_h__BN___caddU_ <- [];
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray56.is_init b_y 0 56))]);
    b__tmp <- (BArray56.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- y;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    tmp <- result;
    param_1 <- cf;
    (result_0, tmp__trace) <@ uTIL____cf_mask (param_1);
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    mask <- result_0;
    param_2 <- tmp;
    param_3 <- mask;
    (aux_1, aux_2, tmp__trace) <@ h__BN___and_mask_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3);
    result_1 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    tmp <- result_1;
    param_4 <- x;
    param_5 <- tmp;
    (aux_3, aux_4, aux_5, tmp__trace) <@ h__BN___addU_ (param_4,
    (BArray56.init_arr (W8.of_int 255)), param_5,
    (BArray56.init_arr (W8.of_int 255)));
    result_2 <- aux_3;
    result_3 <- aux_4;
    b_result_1 <- aux_5;
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray56.is_init b_result_1 0 56))]);
    x <- result_3;
    b_x <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__BN___caddU_);
  }
  proc h__BN___cminusP_ (x:BArray56.t, b_x:BArray56.t, mP:BArray56.t,
                         b_mP:BArray56.t, lastbit:W64.t) : BArray56.t *
                                                           BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_4:BArray56.t;
    var aux_5:BArray56.t;
    var aux_1:bool;
    var b__tmp:BArray56.t;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var _tmp:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var result_0:bool;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var _cf:bool;
    var param_3:BArray56.t;
    var param_4:bool;
    var param_5:BArray56.t;
    var result_2:BArray56.t;
    var b_result_1:BArray56.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:W64.t;
    var trace_h__BN___cminusP_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    tmp <- witness;
    trace_h__BN___cminusP_ <- [];
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray56.is_init b_mP 0 56))]);
    b__tmp <- (BArray56.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    tmp <- result;
    param_1 <- tmp;
    param_2 <- mP;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___addU_ (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2,
    (BArray56.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    _cf <- result_0;
    tmp <- result_1;
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) _cf);
    ( _1, _cf,  _2,  _3,  _4,  _5) <- (NEG_64 lastbit);
    param_3 <- x;
    param_4 <- _cf;
    param_5 <- tmp;
    (aux_4, aux_5, tmp__trace) <@ h__BN___cmov_ (param_3,
    (BArray56.init_arr (W8.of_int 255)), param_4, param_5,
    (BArray56.init_arr (W8.of_int 255)));
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++
    [(Assert, (BArray56.is_init b_result_1 0 56))]);
    x <- result_2;
    b_x <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__BN___cminusP_);
  }
  proc h__FP__fun_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                        b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var trace_h__FP__fun_muln:trace;
    trace_h__FP__fun_muln <- [];
    trace_h__FP__fun_muln <-
    (trace_h__FP__fun_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    return (r, b_r, trace_h__FP__fun_muln);
  }
  proc h__FP__fun_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                        b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var trace_h__FP__fun_sqrn:trace;
    trace_h__FP__fun_sqrn <- [];
    trace_h__FP__fun_sqrn <-
    (trace_h__FP__fun_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    return (r, b_r, trace_h__FP__fun_sqrn);
  }
  proc h__FP__fun_red (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                       b_a:BArray112.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var trace_h__FP__fun_red:trace;
    trace_h__FP__fun_red <- [];
    trace_h__FP__fun_red <-
    (trace_h__FP__fun_red ++
    [(Assert,
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    return (r, b_r, trace_h__FP__fun_red);
  }
  proc h__FP___chk_bnds_ (err:W64.t, a:BArray56.t, b_a:BArray56.t,
                          ctx:BArray232.t, b_ctx:BArray232.t) : W64.t * trace = {
    var b_P:BArray56.t;
    var p:BArray56.t;
    var param:BArray56.t;
    var b_param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var cf:bool;
    var param_1:bool;
    var result_0:W64.t;
    var t:W64.t;
    var trace_h__FP___chk_bnds_:trace;
    p <- witness;
    b_P <- witness;
    b_param <- witness;
    param <- witness;
    param_0 <- witness;
    trace_h__FP___chk_bnds_ <- [];
    trace_h__FP___chk_bnds_ <-
    (trace_h__FP___chk_bnds_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___chk_bnds_ <-
    (trace_h__FP___chk_bnds_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    trace_h__FP___chk_bnds_ <-
    (trace_h__FP___chk_bnds_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 56) <= 232)))]);
    b_P <- (SBArray232_56.get_sub64 b_ctx 0);
    p <- (SBArray232_56.get_sub64 ctx 0);
    param <- a;
    b_param <- b_P;
    param_0 <- p;
    (result, tmp__trace) <@ h__BN___lt_cf_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0, b_param);
    trace_h__FP___chk_bnds_ <- (trace_h__FP___chk_bnds_ ++ tmp__trace);
    cf <- result;
    param_1 <- cf;
    (result_0, tmp__trace) <@ uTIL____ncf_mask (param_1);
    trace_h__FP___chk_bnds_ <- (trace_h__FP___chk_bnds_ ++ tmp__trace);
    t <- result_0;
    err <- (err `|` t);
    return (err, trace_h__FP___chk_bnds_);
  }
  proc h__FP___addm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t,
                      ctx:BArray232.t, b_ctx:BArray232.t) : BArray56.t *
                                                            BArray56.t *
                                                            trace = {
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
    var lastbit:W64.t;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var param_2:BArray56.t;
    var b_param_0:BArray56.t;
    var param_3:BArray56.t;
    var param_4:W64.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var  _0:bool;
    var trace_h__FP___addm_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__FP___addm_ <- [];
    trace_h__FP___addm_ <-
    (trace_h__FP___addm_ ++
    [(Assert,
     (((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)) /\
     (BArray232.is_init b_ctx 56 56)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param, b_param, 
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FP___addm_ <- (trace_h__FP___addm_ ++ tmp__trace);
    trace_h__FP___addm_ <-
    (trace_h__FP___addm_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__FP___addm_ <-
    (trace_h__FP___addm_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_tmp <- (SBArray232_56.get_sub64 b_ctx 7);
    tmp <- (SBArray232_56.get_sub64 ctx 7);
    param_2 <- r;
    b_param_0 <- b_tmp;
    param_3 <- tmp;
    param_4 <- lastbit;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cminusP_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3, b_param_0, param_4);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FP___addm_ <- (trace_h__FP___addm_ ++ tmp__trace);
    trace_h__FP___addm_ <-
    (trace_h__FP___addm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_1;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___addm_);
  }
  proc h__FP___addmU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var cf:bool;
    var lastbit:W64.t;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var param_1:BArray56.t;
    var b_param:BArray56.t;
    var param_2:BArray56.t;
    var param_3:W64.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var  _0:bool;
    var trace_h__FP___addmU_:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__FP___addmU_ <- [];
    trace_h__FP___addmU_ <-
    (trace_h__FP___addmU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___addmU_ <-
    (trace_h__FP___addmU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP___addmU_ <-
    (trace_h__FP___addmU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    param <- a;
    param_0 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addU_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FP___addmU_ <- (trace_h__FP___addmU_ ++ tmp__trace);
    trace_h__FP___addmU_ <-
    (trace_h__FP___addmU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__FP___addmU_ <-
    (trace_h__FP___addmU_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_tmp <- (SBArray232_56.get_sub64 b_ctx 7);
    tmp <- (SBArray232_56.get_sub64 ctx 7);
    param_1 <- a;
    b_param <- b_tmp;
    param_2 <- tmp;
    param_3 <- lastbit;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cminusP_ (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2, b_param, param_3);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FP___addmU_ <- (trace_h__FP___addmU_ ++ tmp__trace);
    trace_h__FP___addmU_ <-
    (trace_h__FP___addmU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_1;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___addmU_);
  }
  proc h__FP___subm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t,
                      ctx:BArray232.t, b_ctx:BArray232.t) : BArray56.t *
                                                            BArray56.t *
                                                            trace = {
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
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var param_2:BArray56.t;
    var param_3:bool;
    var b_param_0:BArray56.t;
    var param_4:BArray56.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___subm_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__FP___subm_ <- [];
    trace_h__FP___subm_ <-
    (trace_h__FP___subm_ ++
    [(Assert,
     (((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)) /\
     (BArray232.is_init b_ctx 0 232)))]);
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
    trace_h__FP___subm_ <- (trace_h__FP___subm_ ++ tmp__trace);
    trace_h__FP___subm_ <-
    (trace_h__FP___subm_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    trace_h__FP___subm_ <-
    (trace_h__FP___subm_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 56) <= 232)))]);
    b_tmp <- (SBArray232_56.get_sub64 b_ctx 0);
    tmp <- (SBArray232_56.get_sub64 ctx 0);
    param_2 <- r;
    param_3 <- cf;
    b_param_0 <- b_tmp;
    param_4 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___caddU_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3, param_4, b_param_0);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FP___subm_ <- (trace_h__FP___subm_ ++ tmp__trace);
    trace_h__FP___subm_ <-
    (trace_h__FP___subm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_1;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___subm_);
  }
  proc h__FP___submU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var cf:bool;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var param_1:BArray56.t;
    var param_2:bool;
    var b_param:BArray56.t;
    var param_3:BArray56.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___submU_:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__FP___submU_ <- [];
    trace_h__FP___submU_ <-
    (trace_h__FP___submU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___submU_ <-
    (trace_h__FP___submU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP___submU_ <-
    (trace_h__FP___submU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    param <- a;
    param_0 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___subU_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FP___submU_ <- (trace_h__FP___submU_ ++ tmp__trace);
    trace_h__FP___submU_ <-
    (trace_h__FP___submU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    trace_h__FP___submU_ <-
    (trace_h__FP___submU_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 56) <= 232)))]);
    b_tmp <- (SBArray232_56.get_sub64 b_ctx 0);
    tmp <- (SBArray232_56.get_sub64 ctx 0);
    param_1 <- a;
    param_2 <- cf;
    b_param <- b_tmp;
    param_3 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___caddU_ (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2, param_3, b_param);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FP___submU_ <- (trace_h__FP___submU_ ++ tmp__trace);
    trace_h__FP___submU_ <-
    (trace_h__FP___submU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_1;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___submU_);
  }
  proc h__FP___mulm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t,
                      ctx:BArray232.t, b_ctx:BArray232.t) : BArray56.t *
                                                            BArray56.t *
                                                            trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__tmp:BArray112.t;
    var b__r:BArray56.t;
    var _r:BArray56.t;
    var _ctx:BArray232.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var _tmp:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var b_param_0:BArray56.t;
    var param_2:BArray56.t;
    var param_3:BArray112.t;
    var param_4:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___mulm_:trace;
    _ctx <- witness;
    _r <- witness;
    _tmp <- witness;
    b__r <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FP___mulm_ <- [];
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++
    [(Assert,
     (((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)) /\
     (BArray232.is_init b_ctx 0 232)))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_2 <- r;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_2, b_param_0,
    param_3, (BArray112.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___mulm_);
  }
  proc h__FP___mulmU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__tmp:BArray112.t;
    var _a:BArray56.t;
    var _ctx:BArray232.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var _tmp:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var param_2:BArray56.t;
    var param_3:BArray112.t;
    var param_4:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___mulmU_:trace;
    _a <- witness;
    _ctx <- witness;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FP___mulmU_ <- [];
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray112.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___mulmU_);
  }
  proc h__FP___sqrm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__tmp:BArray112.t;
    var b__r:BArray56.t;
    var _r:BArray56.t;
    var _ctx:BArray232.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var _tmp:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var b_param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray112.t;
    var param_3:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___sqrm_:trace;
    _ctx <- witness;
    _r <- witness;
    _tmp <- witness;
    b__r <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FP___sqrm_ <- [];
    trace_h__FP___sqrm_ <-
    (trace_h__FP___sqrm_ ++
    [(Assert,
     ((BArray56.is_init b_a 0 56) /\ (BArray232.is_init b_ctx 0 232)))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_sqrn (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___sqrm_ <- (trace_h__FP___sqrm_ ++ tmp__trace);
    trace_h__FP___sqrm_ <-
    (trace_h__FP___sqrm_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- tmp;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_1, b_param_0,
    param_2, (BArray112.init_arr (W8.of_int 255)), param_3,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___sqrm_ <- (trace_h__FP___sqrm_ ++ tmp__trace);
    trace_h__FP___sqrm_ <-
    (trace_h__FP___sqrm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___sqrm_);
  }
  proc h__FP___sqrmU_ (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                       b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__tmp:BArray112.t;
    var _a:BArray56.t;
    var _ctx:BArray232.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var _tmp:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var param_1:BArray56.t;
    var param_2:BArray112.t;
    var param_3:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___sqrmU_:trace;
    _a <- witness;
    _ctx <- witness;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FP___sqrmU_ <- [];
    trace_h__FP___sqrmU_ <-
    (trace_h__FP___sqrmU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___sqrmU_ <-
    (trace_h__FP___sqrmU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_sqrn (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___sqrmU_ <- (trace_h__FP___sqrmU_ ++ tmp__trace);
    trace_h__FP___sqrmU_ <-
    (trace_h__FP___sqrmU_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2,
    (BArray112.init_arr (W8.of_int 255)), param_3,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___sqrmU_ <- (trace_h__FP___sqrmU_ ++ tmp__trace);
    trace_h__FP___sqrmU_ <-
    (trace_h__FP___sqrmU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___sqrmU_);
  }
  proc h__FP__fun_mulU (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__FP__fun_mulU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FP__fun_mulU <- [];
    trace_h__FP__fun_mulU <-
    (trace_h__FP__fun_mulU ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP__fun_mulU <-
    (trace_h__FP__fun_mulU ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP__fun_mulU <-
    (trace_h__FP__fun_mulU ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    param <- a;
    param_0 <- b;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FP___mulmU_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP__fun_mulU <- (trace_h__FP__fun_mulU ++ tmp__trace);
    trace_h__FP__fun_mulU <-
    (trace_h__FP__fun_mulU ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP__fun_mulU);
  }
  proc h__FP__fun_sqrU (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                        b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__FP__fun_sqrU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__FP__fun_sqrU <- [];
    trace_h__FP__fun_sqrU <-
    (trace_h__FP__fun_sqrU ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP__fun_sqrU <-
    (trace_h__FP__fun_sqrU ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    param <- a;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FP___sqrmU_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP__fun_sqrU <- (trace_h__FP__fun_sqrU ++ tmp__trace);
    trace_h__FP__fun_sqrU <-
    (trace_h__FP__fun_sqrU ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP__fun_sqrU);
  }
  proc h__FP__EXP___expm_noct (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                               b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t,
                               ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_4:BArray56.t;
    var aux_5:BArray56.t;
    var aux_6:BArray56.t;
    var aux_7:BArray56.t;
    var aux_8:BArray56.t;
    var b__x:BArray56.t;
    var _b:BArray56.t;
    var _ctx:BArray232.t;
    var b_x:BArray56.t;
    var x:BArray56.t;
    var _x:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var j:int;
    var t:W64.t;
    var _k:W64.t;
    var cf:bool;
    var _t:W64.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var param_3:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var _r:BArray56.t;
    var param_4:BArray56.t;
    var param_5:BArray232.t;
    var result_1:BArray56.t;
    var b_result_1:BArray56.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var trace_h__FP__EXP___expm_noct:trace;
    _b <- witness;
    _ctx <- witness;
    _r <- witness;
    _x <- witness;
    b__x <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_x <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    x <- witness;
    trace_h__FP__EXP___expm_noct <- [];
    trace_h__FP__EXP___expm_noct <-
    (trace_h__FP__EXP___expm_noct ++ [(Assert, (BArray56.is_init b_r 0 56))]);
    trace_h__FP__EXP___expm_noct <-
    (trace_h__FP__EXP___expm_noct ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP__EXP___expm_noct <-
    (trace_h__FP__EXP___expm_noct ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP__EXP___expm_noct <-
    (trace_h__FP__EXP___expm_noct ++
    [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__x <- (BArray56.init_arr (W8.of_int 0));
    _b <- b;
    _ctx <- ctx;
    b_x <- b__x;
    x <- _x;
    b_param <- b_x;
    param <- x;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP__EXP___expm_noct <-
    (trace_h__FP__EXP___expm_noct ++ tmp__trace);
    trace_h__FP__EXP___expm_noct <-
    (trace_h__FP__EXP___expm_noct ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    x <- result;
    _x <- x;
    j <- 0;
    while ((j < 7)) {
      b <- _b;
      trace_h__FP__EXP___expm_noct <-
      (trace_h__FP__EXP___expm_noct ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 b j);
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- (SHR_64 t (W8.of_int 1));
      _t <- t;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_1 <- r;
        param_2 <- x;
        param_3 <- ctx;
        (aux_5, aux_6, tmp__trace) <@ h__FP__fun_mulU (param_1,
        (BArray56.init_arr (W8.of_int 255)), param_2,
        (BArray56.init_arr (W8.of_int 255)), param_3,
        (BArray232.init_arr (W8.of_int 255)));
        result_0 <- aux_5;
        b_result_0 <- aux_6;
        trace_h__FP__EXP___expm_noct <-
        (trace_h__FP__EXP___expm_noct ++ tmp__trace);
        trace_h__FP__EXP___expm_noct <-
        (trace_h__FP__EXP___expm_noct ++
        [(Assert, (BArray56.is_init b_result_0 0 56))]);
        r <- result_0;
      } else {
        
      }
      _r <- r;
      x <- _x;
      ctx <- _ctx;
      param_4 <- x;
      param_5 <- ctx;
      (aux_7, aux_8, tmp__trace) <@ h__FP__fun_sqrU (param_4,
      (BArray56.init_arr (W8.of_int 255)), param_5,
      (BArray232.init_arr (W8.of_int 255)));
      result_1 <- aux_7;
      b_result_1 <- aux_8;
      trace_h__FP__EXP___expm_noct <-
      (trace_h__FP__EXP___expm_noct ++ tmp__trace);
      trace_h__FP__EXP___expm_noct <-
      (trace_h__FP__EXP___expm_noct ++
      [(Assert, (BArray56.is_init b_result_1 0 56))]);
      x <- result_1;
      _x <- x;
      r <- _r;
      t <- _t;
      ( _4,  _5,  _6, zf, _k) <- (DEC_64 _k);
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- (SHR_64 t (W8.of_int 1));
        _t <- t;
        if (cf) {
          x <- _x;
          ctx <- _ctx;
          param_1 <- r;
          param_2 <- x;
          param_3 <- ctx;
          (aux_1, aux_2, tmp__trace) <@ h__FP__fun_mulU (param_1,
          (BArray56.init_arr (W8.of_int 255)), param_2,
          (BArray56.init_arr (W8.of_int 255)), param_3,
          (BArray232.init_arr (W8.of_int 255)));
          result_0 <- aux_1;
          b_result_0 <- aux_2;
          trace_h__FP__EXP___expm_noct <-
          (trace_h__FP__EXP___expm_noct ++ tmp__trace);
          trace_h__FP__EXP___expm_noct <-
          (trace_h__FP__EXP___expm_noct ++
          [(Assert, (BArray56.is_init b_result_0 0 56))]);
          r <- result_0;
        } else {
          
        }
        _r <- r;
        x <- _x;
        ctx <- _ctx;
        param_4 <- x;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__FP__fun_sqrU (param_4,
        (BArray56.init_arr (W8.of_int 255)), param_5,
        (BArray232.init_arr (W8.of_int 255)));
        result_1 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__FP__EXP___expm_noct <-
        (trace_h__FP__EXP___expm_noct ++ tmp__trace);
        trace_h__FP__EXP___expm_noct <-
        (trace_h__FP__EXP___expm_noct ++
        [(Assert, (BArray56.is_init b_result_1 0 56))]);
        x <- result_1;
        _x <- x;
        r <- _r;
        t <- _t;
        ( _4,  _5,  _6, zf, _k) <- (DEC_64 _k);
      }
      j <- (j + 1);
    }
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP__EXP___expm_noct);
  }
  proc h__FP__EXP___expm_noct_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                                b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t,
                                ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b_exp0:BArray56.t;
    var exp0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var b_param_0:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var param_3:BArray56.t;
    var param_4:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP__EXP___expm_noct_:trace;
    b_exp0 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    exp0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__FP__EXP___expm_noct_ <- [];
    trace_h__FP__EXP___expm_noct_ <-
    (trace_h__FP__EXP___expm_noct_ ++
    [(Assert,
     (((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)) /\
     (BArray232.is_init b_ctx 0 232)))]);
    trace_h__FP__EXP___expm_noct_ <-
    (trace_h__FP__EXP___expm_noct_ ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 56) <= 232)))]);
    b_exp0 <- (SBArray232_56.get_sub64 b_ctx 14);
    exp0 <- (SBArray232_56.get_sub64 ctx 14);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_exp0;
    param_0 <- exp0;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__FP__EXP___expm_noct_ <-
    (trace_h__FP__EXP___expm_noct_ ++ tmp__trace);
    trace_h__FP__EXP___expm_noct_ <-
    (trace_h__FP__EXP___expm_noct_ ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    a <- a;
    b <- b;
    param_1 <- r;
    param_2 <- a;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__EXP___expm_noct (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray56.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP__EXP___expm_noct_ <-
    (trace_h__FP__EXP___expm_noct_ ++ tmp__trace);
    trace_h__FP__EXP___expm_noct_ <-
    (trace_h__FP__EXP___expm_noct_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_0;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP__EXP___expm_noct_);
  }
  proc h__FP__EXP___expmU_noct_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                                 b_b:BArray56.t, ctx:BArray232.t,
                                 b_ctx:BArray232.t) : BArray56.t *
                                                      BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__tmp:BArray56.t;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var _tmp:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var param_3:BArray56.t;
    var param_4:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP__EXP___expmU_noct_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    tmp <- witness;
    trace_h__FP__EXP___expmU_noct_ <- [];
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++
    [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++
    [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++
    [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__tmp <- (BArray56.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++ tmp__trace);
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    tmp <- result;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__EXP___expm_noct_ (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray56.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++ tmp__trace);
    trace_h__FP__EXP___expmU_noct_ <-
    (trace_h__FP__EXP___expmU_noct_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP__EXP___expmU_noct_);
  }
  proc h__FP____Pm2 (r:BArray56.t, b_r:BArray56.t, ctx:BArray232.t,
                     b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var t:W64.t;
    var cf:bool;
    var i:int;
    var trace_h__FP____Pm2:trace;
    trace_h__FP____Pm2 <- [];
    trace_h__FP____Pm2 <-
    (trace_h__FP____Pm2 ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    trace_h__FP____Pm2 <-
    (trace_h__FP____Pm2 ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 232)))]);
    t <- (BArray232.get64 ctx 0);
    (cf, t) <- (sbb_64 t (W64.of_int 2) false);
    b_r <- (BArray56.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r 0 t);
    i <- 1;
    while ((i < 7)) {
      trace_h__FP____Pm2 <-
      (trace_h__FP____Pm2 ++
      [(Assert, ((0 <= ((0 + i) * 8)) /\ ((((0 + i) * 8) + 8) <= 232)))]);
      t <- (BArray232.get64 ctx (0 + i));
      (cf, t) <- (sbb_64 t (W64.of_int 0) cf);
      trace_h__FP____Pm2 <-
      (trace_h__FP____Pm2 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__FP____Pm2);
  }
  proc h__FP___invmU_ (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                       b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__Pm2:BArray56.t;
    var b_Pm2:BArray56.t;
    var pm2:BArray56.t;
    var _Pm2:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var param_3:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___invmU_:trace;
    pm2 <- witness;
    _Pm2 <- witness;
    b_Pm2 <- witness;
    b__Pm2 <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__FP___invmU_ <- [];
    trace_h__FP___invmU_ <-
    (trace_h__FP___invmU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___invmU_ <-
    (trace_h__FP___invmU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__Pm2 <- (BArray56.init_arr (W8.of_int 0));
    b_Pm2 <- b__Pm2;
    pm2 <- _Pm2;
    b_param <- b_Pm2;
    param <- pm2;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FP____Pm2 (param, b_param, param_0,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___invmU_ <- (trace_h__FP___invmU_ ++ tmp__trace);
    trace_h__FP___invmU_ <-
    (trace_h__FP___invmU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    pm2 <- result;
    param_1 <- a;
    param_2 <- pm2;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__EXP___expmU_noct_ (param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___invmU_ <- (trace_h__FP___invmU_ ++ tmp__trace);
    trace_h__FP___invmU_ <-
    (trace_h__FP___invmU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___invmU_);
  }
  proc h__FP___invm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__Pm2:BArray56.t;
    var b_Pm2:BArray56.t;
    var pm2:BArray56.t;
    var _Pm2:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var b_param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var param_3:BArray56.t;
    var param_4:BArray232.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__FP___invm_:trace;
    pm2 <- witness;
    _Pm2 <- witness;
    b_Pm2 <- witness;
    b__Pm2 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__FP___invm_ <- [];
    trace_h__FP___invm_ <-
    (trace_h__FP___invm_ ++
    [(Assert,
     ((BArray56.is_init b_a 0 56) /\ (BArray232.is_init b_ctx 0 232)))]);
    b__Pm2 <- (BArray56.init_arr (W8.of_int 0));
    b_Pm2 <- b__Pm2;
    pm2 <- _Pm2;
    b_param <- b_Pm2;
    param <- pm2;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FP____Pm2 (param, b_param, param_0,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___invm_ <- (trace_h__FP___invm_ ++ tmp__trace);
    trace_h__FP___invm_ <-
    (trace_h__FP___invm_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    pm2 <- result;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- a;
    param_3 <- pm2;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__EXP___expm_noct_ (param_1,
    b_param_0, param_2, (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray56.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___invm_ <- (trace_h__FP___invm_ ++ tmp__trace);
    trace_h__FP___invm_ <-
    (trace_h__FP___invm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___invm_);
  }
}.

(* The post and trace are valid. *)

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____ncf_mask_spec _cf =
   hoare [M.uTIL____ncf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

op h__BN____mov_spec _r _b_r _a _b_a =
   hoare [M.h__BN____mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__BN___mov_spec _r _b_r _a _b_a =
   hoare [M.h__BN___mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__BN___mov__spec _r _b_r _a _b_a =
   hoare [M.h__BN___mov_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

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

op h__BN____and_mask_spec _a _b_a _mask =
   hoare [M.h__BN____and_mask :
   (((_mask = mask) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___and_mask_spec _a _b_a _mask =
   hoare [M.h__BN___and_mask :
   (((_mask = mask) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___and_mask__spec _a _b_a _mask =
   hoare [M.h__BN___and_mask_ :
   (((_mask = mask) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN____addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___addc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___addU__spec _a _b_a _b _b_b =
   hoare [M.h__BN___addU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN____addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7))) /\
   (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7))) /\
   (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___addc1__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray56.is_init _b_r 0 8) /\ (BArray56.is_init _b_a 0 (8 * 7))) /\
   (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___add__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__BN___add_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN____subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___subc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___subU__spec _a _b_a _b _b_b =
   hoare [M.h__BN___subU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

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

op h__BN____ltc1_cf_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____ltc1_cf :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___ltc1_cf_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___ltc1_cf :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___ltc1_cf__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___ltc1_cf_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___lt_cf__spec _a _b_a _b _b_b =
   hoare [M.h__BN___lt_cf_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___caddU__spec _x _b_x _cf _y _b_y =
   hoare [M.h__BN___caddU_ :
   (((_b_y = b_y) /\
    ((_y = y) /\ ((_cf = cf) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_y 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit =
   hoare [M.h__BN___cminusP_ :
   (((_lastbit = lastbit) /\
    ((_b_mP = b_mP) /\ ((_mP = mP) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_mP 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FP__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FP__fun_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__FP__fun_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FP__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FP__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___chk_bnds__spec _err _a _b_a _ctx _b_ctx =
   hoare [M.h__FP___chk_bnds_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_b_a = b_a) /\ ((_a = a) /\ (_err = err))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__FP___addm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___addm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx (8 * 7) (8 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___addmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___addmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP___subm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___subm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___submU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___submU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP___mulm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___mulm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP___sqrm__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FP___sqrm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___sqrmU__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FP___sqrmU_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP__fun_mulU_spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP__fun_mulU :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP__fun_sqrU_spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FP__fun_sqrU :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP__EXP___expm_noct_spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP__EXP___expm_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\
   ((BArray56.is_init _b_a 0 56) /\ (BArray56.is_init _b_r 0 56))))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP__EXP___expm_noct__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP__EXP___expm_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP__EXP___expmU_noct__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP__EXP___expmU_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP____Pm2_spec _r _b_r _ctx _b_ctx =
   hoare [M.h__FP____Pm2 :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray232.is_init _b_ctx 0 (8 * 29))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___invmU__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FP___invmU_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FP___invm__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FP___invm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].
