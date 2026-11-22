require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array3 Array11 Array22 Array24 Array45 Array88 Array176 Array360 Array1408
BArray24 BArray88 BArray176 BArray360 BArray1408 SBArray176_88 SBArray360_88
SBArray1408_88 SBArray360_176.

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
  proc uTIL____addacc3x2 (a:BArray24.t, b_a:BArray24.t, x:W64.t, y:W64.t,
                          k:int) : BArray24.t * BArray24.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var b1:W64.t;
    var b0:W64.t;
    var t:W64.t;
    var cf:bool;
    var b2:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_uTIL____addacc3x2:trace;
    trace_uTIL____addacc3x2 <- [];
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++ [(Assert, (BArray24.is_init b_a 0 24))]);
    (b1, b0) <- (mulu_64 x y);
    t <- b0;
    b0 <- (b0 `<<` (W8.of_int 1));
    ( _0, cf,  _1,  _2,  _3, b1) <- (SHLD_64 b1 t (W8.of_int 1));
    b2 <- (MOV_64 (W64.of_int 0));
    (cf, b2) <- (adc_64 b2 b2 cf);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
    (aux, aux_0) <- (adc_64 (BArray24.get64 a (k %% 3)) b0 false);
    cf <- aux;
    a <- (BArray24.set64 a (k %% 3) aux_0);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 1) %% 3) * 8)) /\ (((((k + 1) %% 3) * 8) + 8) <= 24)))]);
    (aux_1, aux_2) <- (adc_64 (BArray24.get64 a ((k + 1) %% 3)) b1 cf);
    cf <- aux_1;
    a <- (BArray24.set64 a ((k + 1) %% 3) aux_2);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    trace_uTIL____addacc3x2 <-
    (trace_uTIL____addacc3x2 ++
    [(Assert,
     ((0 <= (((k + 2) %% 3) * 8)) /\ (((((k + 2) %% 3) * 8) + 8) <= 24)))]);
    (aux_3, aux_4) <- (adc_64 (BArray24.get64 a ((k + 2) %% 3)) b2 cf);
    cf <- aux_3;
    a <- (BArray24.set64 a ((k + 2) %% 3) aux_4);
    b_a <- (BArray24.init_arr (W8.of_int 255));
    return (a, b_a, trace_uTIL____addacc3x2);
  }
  proc h__BN____load (a:BArray88.t, b_a:BArray88.t, ap:W64.t) : BArray88.t *
                                                                BArray88.t *
                                                                trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____load:trace;
    trace_h__BN____load <- [];
    trace_h__BN____load <-
    (trace_h__BN____load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_a <- (BArray88.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray88.set64 a i t);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____load);
  }
  proc h__BN___load (a:BArray88.t, b_a:BArray88.t, ap:W64.t) : BArray88.t *
                                                               BArray88.t *
                                                               trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___load:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load <- [];
    trace_h__BN___load <-
    (trace_h__BN___load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)))]);
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN____load (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___load <- (trace_h__BN___load ++ tmp__trace);
    trace_h__BN___load <-
    (trace_h__BN___load ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load);
  }
  proc h__BN___load_ (a:BArray88.t, b_a:BArray88.t, ap:W64.t) : BArray88.t *
                                                                BArray88.t *
                                                                trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___load_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load_ <- [];
    trace_h__BN___load_ <-
    (trace_h__BN___load_ ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)))]);
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
    (trace_h__BN___load_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load_);
  }
  proc h__BN____store (ap:W64.t, a:BArray88.t, b_a:BArray88.t) : trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____store:trace;
    trace_h__BN____store <- [];
    trace_h__BN____store <-
    (trace_h__BN____store ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
     (BArray88.is_init b_a 0 88)))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____store <-
      (trace_h__BN____store ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__BN____store <-
      (trace_h__BN____store ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      Glob.mem <-
      (storeW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))) t);
      i <- (i + 1);
    }
    return (trace_h__BN____store);
  }
  proc h__BN___store_ (ap:W64.t, a:BArray88.t, b_a:BArray88.t) : trace = {
    var param:W64.t;
    var param_0:BArray88.t;
    var trace_h__BN___store_:trace;
    param_0 <- witness;
    trace_h__BN___store_ <- [];
    trace_h__BN___store_ <-
    (trace_h__BN___store_ ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
     (BArray88.is_init b_a 0 88)))]);
    ap <- ap;
    a <- a;
    param <- ap;
    param_0 <- a;
    tmp__trace <@ h__BN____store (param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___store_ <- (trace_h__BN___store_ ++ tmp__trace);
    return (trace_h__BN___store_);
  }
  proc h__BN____mov (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                     b_a:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____mov:trace;
    trace_h__BN____mov <- [];
    trace_h__BN____mov <-
    (trace_h__BN____mov ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__BN____mov);
  }
  proc h__BN___mov (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                    b_a:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___mov:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov <- [];
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN____mov (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov <- (trace_h__BN___mov ++ tmp__trace);
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov);
  }
  proc h__BN___mov_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                     b_a:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___mov_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov_ <- [];
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov_ <- (trace_h__BN___mov_ ++ tmp__trace);
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov_);
  }
  proc h__BN____cmov (a:BArray88.t, b_a:BArray88.t, cond:bool, b:BArray88.t,
                      b_b:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____cmov:trace;
    trace_h__BN____cmov <- [];
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN____cmov <-
    (trace_h__BN____cmov ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (cond ? (BArray88.get64 b i) : t);
      trace_h__BN____cmov <-
      (trace_h__BN____cmov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      a <- (BArray88.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____cmov);
  }
  proc h__BN___cmov (a:BArray88.t, b_a:BArray88.t, cond:bool, b:BArray88.t,
                     b_b:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var param:BArray88.t;
    var param_0:bool;
    var param_1:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___cmov:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov <- [];
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN____cmov (param,
    (BArray88.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov <- (trace_h__BN___cmov ++ tmp__trace);
    trace_h__BN___cmov <-
    (trace_h__BN___cmov ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov);
  }
  proc h__BN___cmov_ (a:BArray88.t, b_a:BArray88.t, cond:bool, b:BArray88.t,
                      b_b:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var param:BArray88.t;
    var param_0:bool;
    var param_1:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___cmov_:trace;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___cmov_ <- [];
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- cond;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__BN___cmov (param,
    (BArray88.init_arr (W8.of_int 255)), param_0, param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___cmov_ <- (trace_h__BN___cmov_ ++ tmp__trace);
    trace_h__BN___cmov_ <-
    (trace_h__BN___cmov_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cmov_);
  }
  proc h__BN____cswap_mask (x:BArray88.t, b_x:BArray88.t, y:BArray88.t,
                            b_y:BArray88.t, mask:W64.t) : BArray88.t *
                                                          BArray88.t *
                                                          BArray88.t *
                                                          BArray88.t * trace = {
    var i:int;
    var tmp:W64.t;
    var trace_h__BN____cswap_mask:trace;
    trace_h__BN____cswap_mask <- [];
    trace_h__BN____cswap_mask <-
    (trace_h__BN____cswap_mask ++ [(Assert, (BArray88.is_init b_x 0 88))]);
    trace_h__BN____cswap_mask <-
    (trace_h__BN____cswap_mask ++ [(Assert, (BArray88.is_init b_y 0 88))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      tmp <- (BArray88.get64 x i);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      tmp <- (tmp `^` (BArray88.get64 y i));
      tmp <- (tmp `&` mask);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      x <- (BArray88.set64 x i ((BArray88.get64 x i) `^` tmp));
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      y <- (BArray88.set64 y i ((BArray88.get64 y i) `^` tmp));
      i <- (i + 1);
    }
    b_x <- (BArray88.init_arr (W8.of_int 255));
    b_y <- (BArray88.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN____cswap_mask);
  }
  proc h__BN___cswap_mask (x:BArray88.t, b_x:BArray88.t, y:BArray88.t,
                           b_y:BArray88.t, mask:W64.t) : BArray88.t *
                                                         BArray88.t *
                                                         BArray88.t *
                                                         BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__BN___cswap_mask:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__BN___cswap_mask <- [];
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++ [(Assert, (BArray88.is_init b_x 0 88))]);
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++ [(Assert, (BArray88.is_init b_y 0 88))]);
    param <- x;
    param_0 <- y;
    param_1 <- mask;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ h__BN____cswap_mask (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    b_result <- aux_0;
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__BN___cswap_mask <- (trace_h__BN___cswap_mask ++ tmp__trace);
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    x <- result;
    y <- result_0;
    b_x <- (BArray88.init_arr (W8.of_int 255));
    b_y <- (BArray88.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN___cswap_mask);
  }
  proc h__BN___cswap_mask_ (x:BArray88.t, b_x:BArray88.t, y:BArray88.t,
                            b_y:BArray88.t, mask:W64.t) : BArray88.t *
                                                          BArray88.t *
                                                          BArray88.t *
                                                          BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__BN___cswap_mask_:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__BN___cswap_mask_ <- [];
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++ [(Assert, (BArray88.is_init b_x 0 88))]);
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++ [(Assert, (BArray88.is_init b_y 0 88))]);
    x <- x;
    y <- y;
    param <- x;
    param_0 <- y;
    param_1 <- mask;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ h__BN___cswap_mask (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    b_result <- aux_0;
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__BN___cswap_mask_ <- (trace_h__BN___cswap_mask_ ++ tmp__trace);
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    x <- result;
    y <- result_0;
    x <- x;
    y <- y;
    b_x <- (BArray88.init_arr (W8.of_int 255));
    b_y <- (BArray88.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN___cswap_mask_);
  }
  proc h__BN____fill (a:BArray88.t, b_a:BArray88.t, x:W64.t) : BArray88.t *
                                                               BArray88.t *
                                                               trace = {
    var i:int;
    var trace_h__BN____fill:trace;
    trace_h__BN____fill <- [];
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____fill <-
      (trace_h__BN____fill ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_a <- (BArray88.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray88.set64 a i x);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____fill);
  }
  proc h__BN___fill_ (a:BArray88.t, b_a:BArray88.t, x:W64.t) : BArray88.t *
                                                               BArray88.t *
                                                               trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___fill_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___fill_ <- [];
    b_a <- b_a;
    a <- a;
    x <- x;
    b_param <- b_a;
    param <- a;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__BN____fill (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___fill_ <- (trace_h__BN___fill_ ++ tmp__trace);
    trace_h__BN___fill_ <-
    (trace_h__BN___fill_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___fill_);
  }
  proc h__BN___set0_ (a:BArray88.t, b_a:BArray88.t) : BArray88.t *
                                                      BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var t:W64.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___set0_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___set0_ <- [];
    t <- (W64.of_int 0);
    b_param <- b_a;
    param <- a;
    param_0 <- t;
    (aux, aux_0, tmp__trace) <@ h__BN___fill_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___set0_ <- (trace_h__BN___set0_ ++ tmp__trace);
    trace_h__BN___set0_ <-
    (trace_h__BN___set0_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___set0_);
  }
  proc h__BN____addc1U (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, cf:bool) : bool * BArray88.t *
                                                   BArray88.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1U:trace;
    trace_h__BN____addc1U <- [];
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    i <- 1;
    while ((i < 11)) {
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 b i);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (aux, aux_0) <- (adc_64 (BArray88.get64 a i) t cf);
      cf <- aux;
      a <- (BArray88.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____addc1U);
  }
  proc h__BN___addc1U (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                       b_b:BArray88.t, cf:bool) : bool * BArray88.t *
                                                  BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___addc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U <- [];
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1U (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U <- (trace_h__BN___addc1U ++ tmp__trace);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U);
  }
  proc h__BN___addc1U_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, cf:bool) : bool * BArray88.t *
                                                   BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___addc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U_ <- [];
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1U (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U_ <- (trace_h__BN___addc1U_ ++ tmp__trace);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U_);
  }
  proc h__BN___addU_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                      b_b:BArray88.t) : bool * BArray88.t * BArray88.t *
                                        trace = {
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___addU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addU_ <- [];
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    t <- (BArray88.get64 b 0);
    (aux, aux_0) <- (adc_64 (BArray88.get64 a 0) t false);
    cf <- aux;
    a <- (BArray88.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___addc1U_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___addU_ <- (trace_h__BN___addU_ ++ tmp__trace);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addU_);
  }
  proc h__BN____addc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t, cf:bool) : 
  bool * BArray88.t * BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1:trace;
    trace_h__BN____addc1 <- [];
    trace_h__BN____addc1 <-
    (trace_h__BN____addc1 ++
    [(Assert,
     (((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)) /\
     (BArray88.is_init b_b 0 88)))]);
    i <- 1;
    while ((i < 11)) {
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (cf, t) <- (adc_64 t (BArray88.get64 b i) cf);
      trace_h__BN____addc1 <-
      (trace_h__BN____addc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____addc1);
  }
  proc h__BN___addc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                      b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t, cf:bool) : 
  bool * BArray88.t * BArray88.t * trace = {
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
     (((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)) /\
     (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____addc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1 <- (trace_h__BN___addc1 ++ tmp__trace);
    trace_h__BN___addc1 <-
    (trace_h__BN___addc1 ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc1);
  }
  proc h__BN___addc1_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t, cf:bool) : 
  bool * BArray88.t * BArray88.t * trace = {
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
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1_ <- (trace_h__BN___addc1_ ++ tmp__trace);
    trace_h__BN___addc1_ <-
    (trace_h__BN___addc1_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc1_);
  }
  proc h__BN___add_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
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
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    t <- (BArray88.get64 a 0);
    (cf, t) <- (adc_64 t (BArray88.get64 b 0) false);
    b_r <- (BArray88.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray88.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addc1_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___add_ <- (trace_h__BN___add_ ++ tmp__trace);
    trace_h__BN___add_ <-
    (trace_h__BN___add_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___add_);
  }
  proc h__BN____subc1U (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, cf:bool) : bool * BArray88.t *
                                                   BArray88.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____subc1U:trace;
    trace_h__BN____subc1U <- [];
    trace_h__BN____subc1U <-
    (trace_h__BN____subc1U ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN____subc1U <-
    (trace_h__BN____subc1U ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    i <- 1;
    while ((i < 11)) {
      trace_h__BN____subc1U <-
      (trace_h__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 b i);
      trace_h__BN____subc1U <-
      (trace_h__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__BN____subc1U <-
      (trace_h__BN____subc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (aux, aux_0) <- (sbb_64 (BArray88.get64 a i) t cf);
      cf <- aux;
      a <- (BArray88.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____subc1U);
  }
  proc h__BN___subc1U (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                       b_b:BArray88.t, cf:bool) : bool * BArray88.t *
                                                  BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___subc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subc1U <- [];
    trace_h__BN___subc1U <-
    (trace_h__BN___subc1U ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___subc1U <-
    (trace_h__BN___subc1U ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____subc1U (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___subc1U <- (trace_h__BN___subc1U ++ tmp__trace);
    trace_h__BN___subc1U <-
    (trace_h__BN___subc1U ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subc1U);
  }
  proc h__BN___subc1U_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, cf:bool) : bool * BArray88.t *
                                                   BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___subc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subc1U_ <- [];
    trace_h__BN___subc1U_ <-
    (trace_h__BN___subc1U_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___subc1U_ <-
    (trace_h__BN___subc1U_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___subc1U (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___subc1U_ <- (trace_h__BN___subc1U_ ++ tmp__trace);
    trace_h__BN___subc1U_ <-
    (trace_h__BN___subc1U_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subc1U_);
  }
  proc h__BN___subU_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                      b_b:BArray88.t) : bool * BArray88.t * BArray88.t *
                                        trace = {
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__BN___subU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subU_ <- [];
    trace_h__BN___subU_ <-
    (trace_h__BN___subU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___subU_ <-
    (trace_h__BN___subU_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    t <- (BArray88.get64 b 0);
    (aux, aux_0) <- (sbb_64 (BArray88.get64 a 0) t false);
    cf <- aux;
    a <- (BArray88.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___subc1U_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___subU_ <- (trace_h__BN___subU_ ++ tmp__trace);
    trace_h__BN___subU_ <-
    (trace_h__BN___subU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subU_);
  }
  proc h__BN____negc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, cf:bool) : bool * BArray88.t *
                                                  BArray88.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____negc1:trace;
    trace_h__BN____negc1 <- [];
    trace_h__BN____negc1 <-
    (trace_h__BN____negc1 ++
    [(Assert, ((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)))]);
    i <- 1;
    while ((i < 11)) {
      t <- (W64.of_int 0);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (cf, t) <- (sbb_64 t (BArray88.get64 a i) cf);
      trace_h__BN____negc1 <-
      (trace_h__BN____negc1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    return (cf, r, b_r, trace_h__BN____negc1);
  }
  proc h__BN___negc1 (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
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
    var trace_h__BN___negc1:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1 <- [];
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++
    [(Assert, ((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____negc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1 <- (trace_h__BN___negc1 ++ tmp__trace);
    trace_h__BN___negc1 <-
    (trace_h__BN___negc1 ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1);
  }
  proc h__BN___negc1_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
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
    var trace_h__BN___negc1_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc1_ <- [];
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++
    [(Assert, ((BArray88.is_init b_r 0 8) /\ (BArray88.is_init b_a 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1 (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1_ <- (trace_h__BN___negc1_ ++ tmp__trace);
    trace_h__BN___negc1_ <-
    (trace_h__BN___negc1_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc1_);
  }
  proc h__BN___neg_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                     b_a:BArray88.t) : bool * BArray88.t * BArray88.t * trace = {
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
    var trace_h__BN___neg_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___neg_ <- [];
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray88.get64 a 0) false);
    b_r <- (BArray88.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray88.set64 r 0 t);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1_ (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___neg_ <- (trace_h__BN___neg_ ++ tmp__trace);
    trace_h__BN___neg_ <-
    (trace_h__BN___neg_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___neg_);
  }
  proc h__BN___caddU_ (x:BArray88.t, b_x:BArray88.t, cf:bool, y:BArray88.t,
                       b_y:BArray88.t) : BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux:bool;
    var b__tmp:BArray88.t;
    var param:bool;
    var result:W64.t;
    var mask:W64.t;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var _tmp:BArray88.t;
    var b_param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var result_0:bool;
    var result_1:BArray88.t;
    var b_result:BArray88.t;
    var param_3:W64.t;
    var result_2:bool;
    var param_4:BArray88.t;
    var param_5:bool;
    var param_6:BArray88.t;
    var result_3:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__BN___caddU_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_tmp <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    param_6 <- witness;
    result_1 <- witness;
    result_3 <- witness;
    tmp <- witness;
    trace_h__BN___caddU_ <- [];
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray88.is_init b_x 0 88))]);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray88.is_init b_y 0 88))]);
    b__tmp <- (BArray88.init_arr (W8.of_int 0));
    param <- cf;
    (result, tmp__trace) <@ uTIL____cf_mask (param);
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    mask <- result;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param_0 <- tmp;
    param_1 <- x;
    param_2 <- y;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param_0, b_param,
    param_1, (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray88.init_arr (W8.of_int 255)));
    result_0 <- aux;
    result_1 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    tmp <- result_1;
    param_3 <- mask;
    (result_2, tmp__trace) <@ uTIL____mask_cf (param_3);
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    cf <- result_2;
    param_4 <- x;
    param_5 <- cf;
    param_6 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cmov_ (param_4,
    (BArray88.init_arr (W8.of_int 255)), param_5, param_6,
    (BArray88.init_arr (W8.of_int 255)));
    result_3 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___caddU_ <- (trace_h__BN___caddU_ ++ tmp__trace);
    trace_h__BN___caddU_ <-
    (trace_h__BN___caddU_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    x <- result_3;
    b_x <- (BArray88.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__BN___caddU_);
  }
  proc h__BN___cminusP_ (x:BArray88.t, b_x:BArray88.t, mP:BArray88.t,
                         b_mP:BArray88.t, lastbit:W64.t) : BArray88.t *
                                                           BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux:bool;
    var b__tmp:BArray88.t;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var _tmp:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var _cf:bool;
    var param_2:BArray88.t;
    var param_3:bool;
    var param_4:BArray88.t;
    var result_1:BArray88.t;
    var b_result_0:BArray88.t;
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
    b_tmp <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    trace_h__BN___cminusP_ <- [];
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray88.is_init b_x 0 88))]);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray88.is_init b_mP 0 88))]);
    b__tmp <- (BArray88.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- x;
    param_1 <- mP;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param, b_param, 
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    _cf <- result;
    tmp <- result_0;
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) _cf);
    ( _1, _cf,  _2,  _3,  _4,  _5) <- (NEG_64 lastbit);
    param_2 <- x;
    param_3 <- _cf;
    param_4 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cmov_ (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray88.init_arr (W8.of_int 255)));
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    x <- result_1;
    b_x <- (BArray88.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__BN___cminusP_);
  }
  proc h__MUL__UNR____muln_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
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
    var trace_h__MUL__UNR____muln_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__MUL__UNR____muln_innerloop <- [];
    trace_h__MUL__UNR____muln_innerloop <-
    (trace_h__MUL__UNR____muln_innerloop ++
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
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray88.is_init b_a (i * 8) 8))]);
      t0 <- (BArray88.get64 a i);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
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
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++ tmp__trace);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__MUL__UNR____muln_innerloop);
  }
  proc h__MUL__UNR____ps_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__MUL__UNR____ps_muln:trace;
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
    trace_h__MUL__UNR____ps_muln <- [];
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
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
      (aux, aux_0, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray88.init_arr (W8.of_int 255)), param_4,
      (BArray88.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++ tmp__trace);
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
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
      (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param_5,
      b_param_0, param_6, param_7, param_8, param_9,
      (BArray88.init_arr (W8.of_int 255)), param_10,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++ tmp__trace);
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_0;
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_muln <-
      (trace_h__MUL__UNR____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert,
     ((0 <= (((2 * 11) - 1) * 8)) /\ (((((2 * 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert,
     ((0 <= ((((2 * 11) - 1) %% 3) * 8)) /\
     ((((((2 * 11) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____ps_muln <-
    (trace_h__MUL__UNR____ps_muln ++
    [(Assert, (BArray24.is_init b_x ((((2 * 11) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray176.set64 r ((2 * 11) - 1)
    (BArray24.get64 x (((2 * 11) - 1) %% 3)));
    return (r, b_r, trace_h__MUL__UNR____ps_muln);
  }
  proc h__MUL__UNR___ps_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__MUL__UNR___ps_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_muln <- [];
    trace_h__MUL__UNR___ps_muln <-
    (trace_h__MUL__UNR___ps_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR____ps_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_muln <-
    (trace_h__MUL__UNR___ps_muln ++ tmp__trace);
    trace_h__MUL__UNR___ps_muln <-
    (trace_h__MUL__UNR___ps_muln ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_muln);
  }
  proc h__MUL__UNR___ps_muln_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__MUL__UNR___ps_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_muln_ <- [];
    trace_h__MUL__UNR___ps_muln_ <-
    (trace_h__MUL__UNR___ps_muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR___ps_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_muln_ <-
    (trace_h__MUL__UNR___ps_muln_ ++ tmp__trace);
    trace_h__MUL__UNR___ps_muln_ <-
    (trace_h__MUL__UNR___ps_muln_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_muln_);
  }
  proc h__MUL__UNR____sqrn_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                      istart:int, iend:int, a:BArray88.t,
                                      b_a:BArray88.t) : BArray24.t *
                                                        BArray24.t * trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var inc:int;
    var i:int;
    var j:int;
    var ti:W64.t;
    var tj:W64.t;
    var param:BArray24.t;
    var param_0:W64.t;
    var param_1:W64.t;
    var param_2:int;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var trace_h__MUL__UNR____sqrn_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__MUL__UNR____sqrn_innerloop <- [];
    trace_h__MUL__UNR____sqrn_innerloop <-
    (trace_h__MUL__UNR____sqrn_innerloop ++
    [(Assert,
     ((((((0 <= istart) /\ (iend <= 11)) /\ (0 <= (k - (iend - 1)))) /\
       ((k - istart) < 11)) /\
      (BArray24.is_init b_x 0 24)) /\
     (BArray88.is_init b_a 0 88)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      ti <- (BArray88.get64 a i);
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      tj <- (BArray88.get64 a j);
      param <- x;
      param_0 <- ti;
      param_1 <- tj;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3x2 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++ tmp__trace);
      trace_h__MUL__UNR____sqrn_innerloop <-
      (trace_h__MUL__UNR____sqrn_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__MUL__UNR____sqrn_innerloop);
  }
  proc h__MUL__UNR____ps_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                 trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var aux_3:BArray24.t;
    var aux_4:BArray24.t;
    var aux_5:BArray24.t;
    var aux_6:BArray24.t;
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
    var result:BArray24.t;
    var b_result:BArray24.t;
    var param_4:BArray24.t;
    var param_5:W64.t;
    var param_6:W64.t;
    var param_7:int;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var b_param_0:BArray24.t;
    var param_8:BArray24.t;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:BArray88.t;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var param_13:BArray24.t;
    var param_14:W64.t;
    var param_15:W64.t;
    var param_16:int;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var trace_h__MUL__UNR____ps_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_x <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_8 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    x <- witness;
    trace_h__MUL__UNR____ps_sqrn <- [];
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray88.get64 a 0);
    (t1, t0) <- (mulu_64 t0 t0);
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
      param_2 <- ((k + 1) %/ 2);
      param_3 <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__UNR____sqrn_innerloop (param,
      b_param, param_0, param_1, param_2, param_3,
      (BArray88.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      if (((k %% 2) = 0)) {
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 88)))]);
        t0 <- (BArray88.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_4 <- x;
        param_5 <- t1;
        param_6 <- t0;
        param_7 <- k;
        (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_4,
        (BArray24.init_arr (W8.of_int 255)), param_5, param_6, param_7);
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_0 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_0;
      } else {
        
      }
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
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
      param_8 <- x;
      param_9 <- k;
      param_10 <- ((k - 11) + 1);
      param_11 <- ((k + 1) %/ 2);
      param_12 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__UNR____sqrn_innerloop (param_8,
      b_param_0, param_9, param_10, param_11, param_12,
      (BArray88.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      if (((k %% 2) = 0)) {
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 88)))]);
        t0 <- (BArray88.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_13 <- x;
        param_14 <- t1;
        param_15 <- t0;
        param_16 <- k;
        (aux_5, aux_6, tmp__trace) <@ uTIL____addacc3 (param_13,
        (BArray24.init_arr (W8.of_int 255)), param_14, param_15, param_16);
        result_2 <- aux_5;
        b_result_2 <- aux_6;
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++ tmp__trace);
        trace_h__MUL__UNR____ps_sqrn <-
        (trace_h__MUL__UNR____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_2 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_2;
      } else {
        
      }
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL__UNR____ps_sqrn <-
      (trace_h__MUL__UNR____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert,
     ((0 <= (((2 * 11) - 1) * 8)) /\ (((((2 * 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert,
     ((0 <= ((((2 * 11) - 1) %% 3) * 8)) /\
     ((((((2 * 11) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____ps_sqrn <-
    (trace_h__MUL__UNR____ps_sqrn ++
    [(Assert, (BArray24.is_init b_x ((((2 * 11) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray176.set64 r ((2 * 11) - 1)
    (BArray24.get64 x (((2 * 11) - 1) %% 3)));
    return (r, b_r, trace_h__MUL__UNR____ps_sqrn);
  }
  proc h__MUL__UNR___ps_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                              b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__UNR___ps_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_sqrn <- [];
    trace_h__MUL__UNR___ps_sqrn <-
    (trace_h__MUL__UNR___ps_sqrn ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR____ps_sqrn (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_sqrn <-
    (trace_h__MUL__UNR___ps_sqrn ++ tmp__trace);
    trace_h__MUL__UNR___ps_sqrn <-
    (trace_h__MUL__UNR___ps_sqrn ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_sqrn);
  }
  proc h__MUL__UNR___ps_sqrn_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                 trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__UNR___ps_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__UNR___ps_sqrn_ <- [];
    trace_h__MUL__UNR___ps_sqrn_ <-
    (trace_h__MUL__UNR___ps_sqrn_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__UNR___ps_sqrn (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__UNR___ps_sqrn_ <-
    (trace_h__MUL__UNR___ps_sqrn_ ++ tmp__trace);
    trace_h__MUL__UNR___ps_sqrn_ <-
    (trace_h__MUL__UNR___ps_sqrn_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR___ps_sqrn_);
  }
  proc h__MUL__UNR____mont_redM (r:BArray88.t, b_r:BArray88.t, a:BArray176.t,
                                 b_a:BArray176.t, _P_mP:BArray176.t,
                                 b__P_mP:BArray176.t, _U0:W64.t) : BArray88.t *
                                                                   BArray88.t *
                                                                   trace = {
    var aux:BArray24.t;
    var aux_0:BArray24.t;
    var aux_1:BArray24.t;
    var aux_2:BArray24.t;
    var aux_3:BArray24.t;
    var aux_4:BArray24.t;
    var aux_5:BArray24.t;
    var aux_6:BArray24.t;
    var aux_7:BArray24.t;
    var aux_8:BArray24.t;
    var aux_11:BArray88.t;
    var aux_12:BArray88.t;
    var aux_10:W64.t;
    var aux_9:bool;
    var inc:int;
    var b_x:BArray24.t;
    var x:BArray24.t;
    var b_P:BArray88.t;
    var p:BArray88.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var b_param_0:BArray88.t;
    var param_3:BArray88.t;
    var b_param_1:BArray88.t;
    var param_4:BArray88.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var zero:W64.t;
    var t0:W64.t;
    var param_5:BArray24.t;
    var param_6:W64.t;
    var param_7:W64.t;
    var param_8:int;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var t1:W64.t;
    var param_9:BArray24.t;
    var param_10:W64.t;
    var param_11:W64.t;
    var param_12:int;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var b_param_2:BArray24.t;
    var param_13:BArray24.t;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var b_param_3:BArray88.t;
    var param_17:BArray88.t;
    var b_param_4:BArray88.t;
    var param_18:BArray88.t;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var param_19:BArray24.t;
    var param_20:W64.t;
    var param_21:W64.t;
    var param_22:int;
    var result_3:BArray24.t;
    var b_result_3:BArray24.t;
    var lastbit:W64.t;
    var cf:bool;
    var b_mP:BArray88.t;
    var mP:BArray88.t;
    var b_param_5:BArray88.t;
    var param_23:BArray88.t;
    var b_param_6:BArray88.t;
    var param_24:BArray88.t;
    var param_25:W64.t;
    var result_4:BArray88.t;
    var b_result_4:BArray88.t;
    var  _0:W64.t;
    var  _1:bool;
    var trace_h__MUL__UNR____mont_redM:trace;
    p <- witness;
    b_P <- witness;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_param_6 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_x <- witness;
    mP <- witness;
    param <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    param_13 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_23 <- witness;
    param_24 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    x <- witness;
    trace_h__MUL__UNR____mont_redM <- [];
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b__P_mP 0 176)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_P <- (SBArray176_88.get_sub64 b__P_mP 0);
    p <- (SBArray176_88.get_sub64 _P_mP 0);
    k <- 0;
    while ((k < 11)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_P;
      param_4 <- p;
      (aux, aux_0, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param,
      b_param, param_0, param_1, param_2, param_3, b_param_0, param_4,
      b_param_1);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      zero <- (W64.of_int 0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      t0 <- (BArray176.get64 a k);
      param_5 <- x;
      param_6 <- zero;
      param_7 <- t0;
      param_8 <- k;
      (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_5,
      (BArray24.init_arr (W8.of_int 255)), param_6, param_7, param_8);
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      x <- result_0;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      ( _0, t0) <- (mulu_64 t0 _U0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r k t0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray88.is_init b_P 0 8))]);
      (t1, t0) <- (mulu_64 t0 (BArray88.get64 p 0));
      param_9 <- x;
      param_10 <- t1;
      param_11 <- t0;
      param_12 <- k;
      (aux_3, aux_4, tmp__trace) <@ uTIL____addacc3 (param_9,
      (BArray24.init_arr (W8.of_int 255)), param_10, param_11, param_12);
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      k <- (k + 1);
    }
    inc <- ((2 * 11) - 1);
    k <- 11;
    while ((k < inc)) {
      b_param_2 <- b_x;
      param_13 <- x;
      param_14 <- k;
      param_15 <- ((k - 11) + 1);
      param_16 <- 11;
      b_param_3 <- b_r;
      param_17 <- r;
      b_param_4 <- b_P;
      param_18 <- p;
      (aux_5, aux_6, tmp__trace) <@ h__MUL__UNR____muln_innerloop (param_13,
      b_param_2, param_14, param_15, param_16, param_17, b_param_3, param_18,
      b_param_4);
      result_2 <- aux_5;
      b_result_2 <- aux_6;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_2 0 24))]);
      x <- result_2;
      zero <- (W64.of_int 0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      t0 <- (BArray176.get64 a k);
      param_19 <- x;
      param_20 <- zero;
      param_21 <- t0;
      param_22 <- k;
      (aux_7, aux_8, tmp__trace) <@ uTIL____addacc3 (param_19,
      (BArray24.init_arr (W8.of_int 255)), param_20, param_21, param_22);
      result_3 <- aux_7;
      b_result_3 <- aux_8;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray24.is_init b_result_3 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_3;
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k - 11) * 8)) /\ ((((k - 11) * 8) + 8) <= 88)))]);
      b_r <-
      (BArray88.set64d b_r ((k - 11) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r (k - 11) t0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      k <- (k + 1);
    }
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 11) %% 3) * 8)) /\ (((((2 * 11) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x (((2 * 11) %% 3) * 8) 8))]);
    lastbit <- (BArray24.get64 x ((2 * 11) %% 3));
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 11) - 1) %% 3) * 8)) /\
     ((((((2 * 11) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 11) - 1) %% 3) * 8)) /\
     ((((((2 * 11) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 11) - 1) %% 3) * 8) 8))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 11) - 1) * 8)) /\ (((((2 * 11) - 1) * 8) + 8) <= 176)))]);
    b_x <-
    (BArray24.set64d b_x ((((2 * 11) - 1) %% 3) * 8)
    (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <-
    (adc_64 (BArray24.get64 x (((2 * 11) - 1) %% 3))
    (BArray176.get64 a ((2 * 11) - 1)) false);
    cf <- aux_9;
    x <- (BArray24.set64 x (((2 * 11) - 1) %% 3) aux_10);
    ( _1, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 11) - 1) %% 3) * 8)) /\
     ((((((2 * 11) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 11) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray88.set64d b_r ((11 - 1) * 8) (W64.of_int 18446744073709551615));
    r <-
    (BArray88.set64 r (11 - 1) (BArray24.get64 x (((2 * 11) - 1) %% 3)));
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_mP <- (SBArray176_88.get_sub64 b__P_mP 11);
    mP <- (SBArray176_88.get_sub64 _P_mP 11);
    b_param_5 <- b_r;
    param_23 <- r;
    b_param_6 <- b_mP;
    param_24 <- mP;
    param_25 <- lastbit;
    (aux_11, aux_12, tmp__trace) <@ h__BN___cminusP_ (param_23, b_param_5,
    param_24, b_param_6, param_25);
    result_4 <- aux_11;
    b_result_4 <- aux_12;
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++ tmp__trace);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray88.is_init b_result_4 0 88))]);
    r <- result_4;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR____mont_redM);
  }
  proc h__MUL__LOOP____mul1 (r:BArray176.t, b_r:BArray176.t, a:W64.t,
                             b:BArray88.t, b_b:BArray88.t) : BArray176.t *
                                                             BArray176.t *
                                                             trace = {
    var lo:W64.t;
    var hi:W64.t;
    var c:W64.t;
    var i:int;
    var cf:bool;
    var  _0:bool;
    var trace_h__MUL__LOOP____mul1:trace;
    trace_h__MUL__LOOP____mul1 <- [];
    trace_h__MUL__LOOP____mul1 <-
    (trace_h__MUL__LOOP____mul1 ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    lo <- (BArray88.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 lo);
    c <- hi;
    i <- 1;
    while ((i < 11)) {
      trace_h__MUL__LOOP____mul1 <-
      (trace_h__MUL__LOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      lo <- (BArray88.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      (cf, lo) <- (adc_64 lo c false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__MUL__LOOP____mul1 <-
      (trace_h__MUL__LOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r i lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__MUL__LOOP____mul1 <-
    (trace_h__MUL__LOOP____mul1 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    b_r <- (BArray176.set64d b_r (11 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 11 c);
    return (r, b_r, trace_h__MUL__LOOP____mul1);
  }
  proc h__MUL__LOOP____mul1acc (k:W64.t, r:BArray176.t, b_r:BArray176.t,
                                a:W64.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var lo:W64.t;
    var hi:W64.t;
    var cf:bool;
    var c:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__LOOP____mul1acc:trace;
    trace_h__MUL__LOOP____mul1acc <- [];
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 11)) /\
      (BArray176.is_init b_r 0 (8 * ((W64.to_uint k) + 11)))) /\
     (BArray88.is_init b_b 0 88)))]);
    lo <- (BArray88.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 176)))]);
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 176)))]);
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert, (BArray176.is_init b_r ((W64.to_uint k) * 8) 8))]);
    b_r <-
    (BArray176.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (adc_64 (BArray176.get64 r (W64.to_uint k)) lo false);
    cf <- aux;
    r <- (BArray176.set64 r (W64.to_uint k) aux_0);
    ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
    c <- hi;
    i <- 1;
    while ((i < 11)) {
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      lo <- (BArray88.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 176)))]);
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert,
       (BArray176.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      (cf, lo) <-
      (adc_64 lo (BArray176.get64 r (W64.to_uint (k + (W64.of_int i)))) false
      );
      ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
      (cf, lo) <- (adc_64 lo c false);
      ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__MUL__LOOP____mul1acc <-
      (trace_h__MUL__LOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r (W64.to_uint (k + (W64.of_int i))) lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__MUL__LOOP____mul1acc <-
    (trace_h__MUL__LOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 11))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 11))) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r ((W64.to_uint (k + (W64.of_int 11))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r (W64.to_uint (k + (W64.of_int 11))) c);
    return (r, b_r, trace_h__MUL__LOOP____mul1acc);
  }
  proc h__MUL__LOOP___os_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var ai:W64.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray176.t;
    var param_3:BArray176.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var trace_h__MUL__LOOP___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__LOOP___os_muln <- [];
    trace_h__MUL__LOOP___os_muln <-
    (trace_h__MUL__LOOP___os_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    ai <- (BArray88.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mul1 (param, b_param,
    param_0, param_1, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_muln <-
    (trace_h__MUL__LOOP___os_muln ++ tmp__trace);
    trace_h__MUL__LOOP___os_muln <-
    (trace_h__MUL__LOOP___os_muln ++
    [(Assert, (BArray176.is_init b_result 0 96))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 11))) {
      trace_h__MUL__LOOP___os_muln <-
      (trace_h__MUL__LOOP___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__LOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__LOOP___os_muln <-
      (trace_h__MUL__LOOP___os_muln ++ tmp__trace);
      trace_h__MUL__LOOP___os_muln <-
      (trace_h__MUL__LOOP___os_muln ++
      [(Assert,
       (BArray176.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 11) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__LOOP___os_muln);
  }
  proc h__MUL__LOOP___os_muln_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__MUL__LOOP___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__LOOP___os_muln_ <- [];
    trace_h__MUL__LOOP___os_muln_ <-
    (trace_h__MUL__LOOP___os_muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_muln_ <-
    (trace_h__MUL__LOOP___os_muln_ ++ tmp__trace);
    trace_h__MUL__LOOP___os_muln_ <-
    (trace_h__MUL__LOOP___os_muln_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP___os_muln_);
  }
  proc h__MUL__LOOP___os_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                 trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var ai:W64.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray176.t;
    var param_3:BArray176.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var trace_h__MUL__LOOP___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__LOOP___os_sqrn <- [];
    trace_h__MUL__LOOP___os_sqrn <-
    (trace_h__MUL__LOOP___os_sqrn ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    ai <- (BArray88.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mul1 (param, b_param,
    param_0, param_1, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_sqrn <-
    (trace_h__MUL__LOOP___os_sqrn ++ tmp__trace);
    trace_h__MUL__LOOP___os_sqrn <-
    (trace_h__MUL__LOOP___os_sqrn ++
    [(Assert, (BArray176.is_init b_result 0 96))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 11))) {
      trace_h__MUL__LOOP___os_sqrn <-
      (trace_h__MUL__LOOP___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__LOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__LOOP___os_sqrn <-
      (trace_h__MUL__LOOP___os_sqrn ++ tmp__trace);
      trace_h__MUL__LOOP___os_sqrn <-
      (trace_h__MUL__LOOP___os_sqrn ++
      [(Assert,
       (BArray176.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 11) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__LOOP___os_sqrn);
  }
  proc h__MUL__LOOP___os_sqrn_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                                b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                  trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__LOOP___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__LOOP___os_sqrn_ <- [];
    trace_h__MUL__LOOP___os_sqrn_ <-
    (trace_h__MUL__LOOP___os_sqrn_ ++
    [(Assert, (BArray88.is_init b_a 0 88))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_sqrn (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP___os_sqrn_ <-
    (trace_h__MUL__LOOP___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__LOOP___os_sqrn_ <-
    (trace_h__MUL__LOOP___os_sqrn_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP___os_sqrn_);
  }
  proc h__MUL__LOOP____mont_redM (r:BArray88.t, b_r:BArray88.t,
                                  a:BArray176.t, b_a:BArray176.t,
                                  _P_mP:BArray176.t, b__P_mP:BArray176.t,
                                  _U0:W64.t) : BArray88.t * BArray88.t *
                                               trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var i:int;
    var lo:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var hi:W64.t;
    var cf:bool;
    var w:W64.t;
    var b_mP:BArray88.t;
    var mP:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var b_param_0:BArray88.t;
    var param_0:BArray88.t;
    var param_1:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__MUL__LOOP____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__LOOP____mont_redM <- [];
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b__P_mP 0 176)))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      lo <- (BArray176.get64 a i);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i lo);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 11))) {
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, (BArray88.is_init b_r 0 8))]);
      m <- (BArray88.get64 r 0);
      m <- (m * _U0);
      lo <- (BArray176.get64 _P_mP 0);
      (hi, lo) <- (mulu_64 lo m);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, (BArray88.is_init b_r 0 8))]);
      (cf, lo) <- (adc_64 lo (BArray88.get64 r 0) false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      w <- hi;
      i <- 1;
      while ((i < 11)) {
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
        lo <- (BArray176.get64 _P_mP i);
        (hi, lo) <- (mulu_64 lo m);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, (BArray88.is_init b_r (i * 8) 8))]);
        (cf, lo) <- (adc_64 lo (BArray88.get64 r i) false);
        ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
        (cf, lo) <- (adc_64 lo w false);
        ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 88)))]);
        b_r <-
        (BArray88.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615));
        r <- (BArray88.set64 r (i - 1) lo);
        w <- hi;
        i <- (i + 1);
      }
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 11))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 11))) * 8) + 8) <= 176)))]);
      (cf, w) <-
      (adc_64 w (BArray176.get64 a (W64.to_uint (k + (W64.of_int 11)))) cf);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
      b_r <-
      (BArray88.set64d b_r ((11 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r (11 - 1) w);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_mP <- (SBArray176_88.get_sub64 b__P_mP 11);
    mP <- (SBArray176_88.get_sub64 _P_mP 11);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___cminusP_ (param, b_param, param_0,
    b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++ tmp__trace);
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP____mont_redM);
  }
  proc h__MUL__XUNR____mul1 (r:BArray176.t, b_r:BArray176.t, a:W64.t,
                             b:BArray88.t, b_b:BArray88.t) : BArray176.t *
                                                             BArray176.t *
                                                             trace = {
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XUNR____mul1:trace;
    trace_h__MUL__XUNR____mul1 <- [];
    trace_h__MUL__XUNR____mul1 <-
    (trace_h__MUL__XUNR____mul1 ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray88.get64 b 0));
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 lo);
    i <- 1;
    while ((i < 11)) {
      t <- hi;
      trace_h__MUL__XUNR____mul1 <-
      (trace_h__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 a (BArray88.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XUNR____mul1 <-
      (trace_h__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XUNR____mul1 <-
    (trace_h__MUL__XUNR____mul1 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    b_r <- (BArray176.set64d b_r (11 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 11 hi);
    return (r, b_r, trace_h__MUL__XUNR____mul1);
  }
  proc h__MUL__XUNR____mul1acc (k:int, r:BArray176.t, b_r:BArray176.t,
                                a:W64.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XUNR____mul1acc:trace;
    trace_h__MUL__XUNR____mul1acc <- [];
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert,
     ((((1 <= k) /\ (k < 11)) /\ (BArray176.is_init b_r 0 (8 * (k + 11)))) /\
     (BArray88.is_init b_b 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray88.get64 b 0));
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, (BArray176.is_init b_r (k * 8) 8))]);
    t <- (BArray176.get64 r k);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
    b_r <- (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r k t);
    i <- 1;
    while ((i < 11)) {
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, (BArray176.is_init b_r ((k + i) * 8) 8))]);
      t <- (BArray176.get64 r (k + i));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 a (BArray88.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r ((k + i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r (k + i) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r ((k + 11) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r (k + 11) hi);
    return (r, b_r, trace_h__MUL__XUNR____mul1acc);
  }
  proc h__MUL__XUNR___os_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var ai:W64.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var k:int;
    var param_2:int;
    var b_param_0:BArray176.t;
    var param_3:BArray176.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var trace_h__MUL__XUNR___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__XUNR___os_muln <- [];
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    ai <- (BArray88.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR____mul1 (param, b_param,
    param_0, param_1, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++ tmp__trace);
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++
    [(Assert, (BArray176.is_init b_result 0 96))]);
    b_r <- b_result;
    r <- result;
    k <- 1;
    while ((k < 11)) {
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a k);
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XUNR____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++ tmp__trace);
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++
      [(Assert, (BArray176.is_init b_result_0 0 (8 * ((param_2 + 11) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + 1);
    }
    return (r, b_r, trace_h__MUL__XUNR___os_muln);
  }
  proc h__MUL__XUNR___os_muln_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__MUL__XUNR___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__XUNR___os_muln_ <- [];
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR___os_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++ tmp__trace);
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR___os_muln_);
  }
  proc h__MUL__XUNR____sqr_row0 (r:BArray176.t, b_r:BArray176.t,
                                 a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                 BArray176.t *
                                                                 trace = {
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var j:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XUNR____sqr_row0:trace;
    trace_h__MUL__XUNR____sqr_row0 <- [];
    trace_h__MUL__XUNR____sqr_row0 <-
    (trace_h__MUL__XUNR____sqr_row0 ++
    [(Assert, ((2 <= 11) /\ (BArray88.is_init b_a 0 88)))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray88.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray88.get64 a 1));
    b_r <- (BArray176.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 1 lo);
    j <- 2;
    while ((j < 11)) {
      t <- hi;
      trace_h__MUL__XUNR____sqr_row0 <-
      (trace_h__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a j));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XUNR____sqr_row0 <-
      (trace_h__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (j * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r j t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XUNR____sqr_row0 <-
    (trace_h__MUL__XUNR____sqr_row0 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    b_r <- (BArray176.set64d b_r (11 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 11 hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_row0);
  }
  proc h__MUL__XUNR____sqr_rowacc (i:int, r:BArray176.t, b_r:BArray176.t,
                                   a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                   BArray176.t *
                                                                   trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var j:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XUNR____sqr_rowacc:trace;
    trace_h__MUL__XUNR____sqr_rowacc <- [];
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((((1 <= i) /\ (i < (11 - 1))) /\
      (BArray176.is_init b_r 8 (8 * ((i + 11) - 1)))) /\
     (BArray88.is_init b_a 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
    ai <- (BArray88.get64 a i);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 88)))]);
    (hi, lo) <- (MULX_64 ai (BArray88.get64 a (i + 1)));
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, (BArray176.is_init b_r (((2 * i) + 1) * 8) 8))]);
    t <- (BArray176.get64 r ((2 * i) + 1));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r (((2 * i) + 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r ((2 * i) + 1) t);
    j <- (i + 2);
    while ((j < 11)) {
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 176)))]);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, (BArray176.is_init b_r ((i + j) * 8) 8))]);
      t <- (BArray176.get64 r (i + j));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a j));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r ((i + j) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r (i + j) t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 11) * 8)) /\ ((((i + 11) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r ((i + 11) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r (i + 11) hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_rowacc);
  }
  proc h__MUL__XUNR____sqr_diag (r:BArray176.t, b_r:BArray176.t,
                                 a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                 BArray176.t *
                                                                 trace = {
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XUNR____sqr_diag:trace;
    trace_h__MUL__XUNR____sqr_diag <- [];
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     (((2 <= 11) /\ (BArray176.is_init b_r 8 160)) /\
     (BArray88.is_init b_a 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray88.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray88.get64 a 0));
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 lo);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray176.is_init b_r 8 8))]);
    t <- (BArray176.get64 r 1);
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t hi of_0);
    b_r <- (BArray176.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 1 t);
    inc <- (11 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a i);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a i));
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 176)))]);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray176.is_init b_r ((2 * i) * 8) 8))]);
      t <- (BArray176.get64 r (2 * i));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r (2 * i) t);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray176.is_init b_r (((2 * i) + 1) * 8) 8))]);
      t <- (BArray176.get64 r ((2 * i) + 1));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t hi of_0);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r ((2 * i) + 1) t);
      i <- (i + 1);
    }
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    ai <- (BArray88.get64 a (11 - 1));
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    (hi, lo) <- (MULX_64 ai (BArray88.get64 a (11 - 1)));
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 11) - 2) * 8)) /\ (((((2 * 11) - 2) * 8) + 8) <= 176)))]);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray176.is_init b_r (((2 * 11) - 2) * 8) 8))]);
    t <- (BArray176.get64 r ((2 * 11) - 2));
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 11) - 2) * 8)) /\ (((((2 * 11) - 2) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r ((2 * 11) - 2) t);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 11) - 1) * 8)) /\ (((((2 * 11) - 1) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r ((2 * 11) - 1) hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_diag);
  }
  proc h__MUL__XUNR___os_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                 trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var aux_3:BArray176.t;
    var aux_4:BArray176.t;
    var inc:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var i:int;
    var param_1:int;
    var b_param_0:BArray176.t;
    var param_2:BArray176.t;
    var param_3:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var b_param_1:BArray176.t;
    var param_4:BArray176.t;
    var param_5:BArray88.t;
    var result_1:BArray176.t;
    var b_result_1:BArray176.t;
    var trace_h__MUL__XUNR___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__MUL__XUNR___os_sqrn <- [];
    trace_h__MUL__XUNR___os_sqrn <-
    (trace_h__MUL__XUNR___os_sqrn ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    if ((11 = 1)) {
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a 0);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a 0));
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r 0 lo);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r 1 hi);
    } else {
      b_param <- b_r;
      param <- r;
      param_0 <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__XUNR____sqr_row0 (param, b_param,
      param_0, (BArray88.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray176.is_init b_result 8 88))]);
      b_r <- b_result;
      r <- result;
      inc <- (11 - 1);
      i <- 1;
      while ((i < inc)) {
        param_1 <- i;
        b_param_0 <- b_r;
        param_2 <- r;
        param_3 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__XUNR____sqr_rowacc (param_1,
        param_2, b_param_0, param_3, (BArray88.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__XUNR___os_sqrn <-
        (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
        trace_h__MUL__XUNR___os_sqrn <-
        (trace_h__MUL__XUNR___os_sqrn ++
        [(Assert, (BArray176.is_init b_result_0 8 (8 * (param_1 + 11))))]);
        b_r <- b_result_0;
        r <- result_0;
        i <- (i + 1);
      }
      b_param_1 <- b_r;
      param_4 <- r;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__XUNR____sqr_diag (param_4,
      b_param_1, param_5, (BArray88.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray176.is_init b_result_1 0 176))]);
      b_r <- (BArray176.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__MUL__XUNR___os_sqrn);
  }
  proc h__MUL__XUNR___os_sqrn_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                                b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                  trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__XUNR___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XUNR___os_sqrn_ <- [];
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray88.is_init b_a 0 88))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR___os_sqrn (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR___os_sqrn_);
  }
  proc h__MUL__XUNR____mont_redM (r:BArray88.t, b_r:BArray88.t,
                                  a:BArray176.t, b_a:BArray176.t,
                                  _P_mP:BArray176.t, b__P_mP:BArray176.t,
                                  _U0:W64.t) : BArray88.t * BArray88.t *
                                               trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var c:W64.t;
    var w0:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var b_mP:BArray88.t;
    var mP:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var b_param_0:BArray88.t;
    var param_0:BArray88.t;
    var param_1:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__MUL__XUNR____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XUNR____mont_redM <- [];
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b__P_mP 0 176)))]);
    c <- (W64.of_int 0);
    w0 <- (BArray176.get64 a 0);
    k <- 0;
    while ((k < 11)) {
      m <- w0;
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray176.get64 _P_mP 0));
      (of_0, w0) <- (ADOX_64 w0 lo of_0);
      i <- 1;
      while ((i < 11)) {
        if ((k = 0)) {
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
          t <- (BArray176.get64 a i);
        } else {
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, (BArray88.is_init b_r (i * 8) 8))]);
          t <- (BArray88.get64 r i);
        }
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
        (hi, lo) <- (MULX_64 m (BArray176.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 88)))]);
        b_r <-
        (BArray88.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615));
        r <- (BArray88.set64 r (i - 1) t);
        if ((i = 1)) {
          w0 <- t;
        } else {
          
        }
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
        (cf, hi) <- (adc_64 hi (BArray176.get64 a 11) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
        (cf, hi) <- (adc_64 hi (BArray176.get64 a (k + 11)) cf);
      }
      trace_h__MUL__XUNR____mont_redM <-
      (trace_h__MUL__XUNR____mont_redM ++
      [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
      b_r <-
      (BArray88.set64d b_r ((11 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r (11 - 1) hi);
      if ((11 = 1)) {
        w0 <- hi;
      } else {
        
      }
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_mP <- (SBArray176_88.get_sub64 b__P_mP 11);
    mP <- (SBArray176_88.get_sub64 _P_mP 11);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___cminusP_ (param, b_param, param_0,
    b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++ tmp__trace);
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR____mont_redM);
  }
  proc h__MUL__XLOOP____mul1 (r:BArray176.t, b_r:BArray176.t, a:W64.t,
                              b:BArray88.t, b_b:BArray88.t) : BArray176.t *
                                                              BArray176.t *
                                                              trace = {
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var i:int;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XLOOP____mul1:trace;
    trace_h__MUL__XLOOP____mul1 <- [];
    trace_h__MUL__XLOOP____mul1 <-
    (trace_h__MUL__XLOOP____mul1 ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray88.get64 b 0));
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 lo);
    i <- 1;
    while ((i < 11)) {
      t <- hi;
      trace_h__MUL__XLOOP____mul1 <-
      (trace_h__MUL__XLOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 a (BArray88.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XLOOP____mul1 <-
      (trace_h__MUL__XLOOP____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XLOOP____mul1 <-
    (trace_h__MUL__XLOOP____mul1 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    b_r <- (BArray176.set64d b_r (11 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 11 hi);
    return (r, b_r, trace_h__MUL__XLOOP____mul1);
  }
  proc h__MUL__XLOOP____mul1acc (k:W64.t, r:BArray176.t, b_r:BArray176.t,
                                 a:W64.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XLOOP____mul1acc:trace;
    trace_h__MUL__XLOOP____mul1acc <- [];
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 11)) /\
      (BArray176.is_init b_r 0 (8 * ((W64.to_uint k) + 11)))) /\
     (BArray88.is_init b_b 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray88.get64 b 0));
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 176)))]);
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert, (BArray176.is_init b_r ((W64.to_uint k) * 8) 8))]);
    t <- (BArray176.get64 r (W64.to_uint k));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r (W64.to_uint k) t);
    i <- 1;
    while ((i < 11)) {
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 176)))]);
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert,
       (BArray176.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      t <- (BArray176.get64 r (W64.to_uint (k + (W64.of_int i))));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 a (BArray88.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XLOOP____mul1acc <-
      (trace_h__MUL__XLOOP____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r (W64.to_uint (k + (W64.of_int i))) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XLOOP____mul1acc <-
    (trace_h__MUL__XLOOP____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 11))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 11))) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r ((W64.to_uint (k + (W64.of_int 11))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r (W64.to_uint (k + (W64.of_int 11))) hi);
    return (r, b_r, trace_h__MUL__XLOOP____mul1acc);
  }
  proc h__MUL__XLOOP___os_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                                b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var ai:W64.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray176.t;
    var param_3:BArray176.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var trace_h__MUL__XLOOP___os_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__XLOOP___os_muln <- [];
    trace_h__MUL__XLOOP___os_muln <-
    (trace_h__MUL__XLOOP___os_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    ai <- (BArray88.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP____mul1 (param, b_param,
    param_0, param_1, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_muln <-
    (trace_h__MUL__XLOOP___os_muln ++ tmp__trace);
    trace_h__MUL__XLOOP___os_muln <-
    (trace_h__MUL__XLOOP___os_muln ++
    [(Assert, (BArray176.is_init b_result 0 96))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 11))) {
      trace_h__MUL__XLOOP___os_muln <-
      (trace_h__MUL__XLOOP___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XLOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XLOOP___os_muln <-
      (trace_h__MUL__XLOOP___os_muln ++ tmp__trace);
      trace_h__MUL__XLOOP___os_muln <-
      (trace_h__MUL__XLOOP___os_muln ++
      [(Assert,
       (BArray176.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 11) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__XLOOP___os_muln);
  }
  proc h__MUL__XLOOP___os_muln_ (r:BArray176.t, b_r:BArray176.t,
                                 a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                                 b_b:BArray88.t) : BArray176.t *
                                                   BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__XLOOP___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__XLOOP___os_muln_ <- [];
    trace_h__MUL__XLOOP___os_muln_ <-
    (trace_h__MUL__XLOOP___os_muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP___os_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_muln_ <-
    (trace_h__MUL__XLOOP___os_muln_ ++ tmp__trace);
    trace_h__MUL__XLOOP___os_muln_ <-
    (trace_h__MUL__XLOOP___os_muln_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP___os_muln_);
  }
  proc h__MUL__XLOOP___os_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                                b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                  trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var ai:W64.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:W64.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray176.t;
    var param_3:BArray176.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var trace_h__MUL__XLOOP___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__MUL__XLOOP___os_sqrn <- [];
    trace_h__MUL__XLOOP___os_sqrn <-
    (trace_h__MUL__XLOOP___os_sqrn ++
    [(Assert, (BArray88.is_init b_a 0 88))]);
    ai <- (BArray88.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP____mul1 (param, b_param,
    param_0, param_1, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_sqrn <-
    (trace_h__MUL__XLOOP___os_sqrn ++ tmp__trace);
    trace_h__MUL__XLOOP___os_sqrn <-
    (trace_h__MUL__XLOOP___os_sqrn ++
    [(Assert, (BArray176.is_init b_result 0 96))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 11))) {
      trace_h__MUL__XLOOP___os_sqrn <-
      (trace_h__MUL__XLOOP___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XLOOP____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XLOOP___os_sqrn <-
      (trace_h__MUL__XLOOP___os_sqrn ++ tmp__trace);
      trace_h__MUL__XLOOP___os_sqrn <-
      (trace_h__MUL__XLOOP___os_sqrn ++
      [(Assert,
       (BArray176.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 11) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL__XLOOP___os_sqrn);
  }
  proc h__MUL__XLOOP___os_sqrn_ (r:BArray176.t, b_r:BArray176.t,
                                 a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                 BArray176.t *
                                                                 trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__XLOOP___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XLOOP___os_sqrn_ <- [];
    trace_h__MUL__XLOOP___os_sqrn_ <-
    (trace_h__MUL__XLOOP___os_sqrn_ ++
    [(Assert, (BArray88.is_init b_a 0 88))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XLOOP___os_sqrn (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP___os_sqrn_ <-
    (trace_h__MUL__XLOOP___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XLOOP___os_sqrn_ <-
    (trace_h__MUL__XLOOP___os_sqrn_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP___os_sqrn_);
  }
  proc h__MUL__XLOOP____mont_redM (r:BArray88.t, b_r:BArray88.t,
                                   a:BArray176.t, b_a:BArray176.t,
                                   _P_mP:BArray176.t, b__P_mP:BArray176.t,
                                   _U0:W64.t) : BArray88.t * BArray88.t *
                                                trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var i:int;
    var t:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_mP:BArray88.t;
    var mP:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var b_param_0:BArray88.t;
    var param_0:BArray88.t;
    var param_1:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var trace_h__MUL__XLOOP____mont_redM:trace;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    mP <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XLOOP____mont_redM <- [];
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b__P_mP 0 176)))]);
    i <- 0;
    while ((i < 11)) {
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      t <- (BArray176.get64 a i);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 11))) {
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray88.is_init b_r 0 8))]);
      m <- (BArray88.get64 r 0);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray176.get64 _P_mP 0));
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray88.is_init b_r 0 8))]);
      t <- (BArray88.get64 r 0);
      (of_0, t) <- (ADOX_64 t lo of_0);
      i <- 1;
      while ((i < 11)) {
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, (BArray88.is_init b_r (i * 8) 8))]);
        t <- (BArray88.get64 r i);
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
        (hi, lo) <- (MULX_64 m (BArray176.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 88)))]);
        b_r <-
        (BArray88.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615));
        r <- (BArray88.set64 r (i - 1) t);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 11))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 11))) * 8) + 8) <= 176)))]);
      (cf, hi) <-
      (adc_64 hi (BArray176.get64 a (W64.to_uint (k + (W64.of_int 11)))) cf);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
      b_r <-
      (BArray88.set64d b_r ((11 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r (11 - 1) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_mP <- (SBArray176_88.get_sub64 b__P_mP 11);
    mP <- (SBArray176_88.get_sub64 _P_mP 11);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_mP;
    param_0 <- mP;
    param_1 <- c;
    (aux, aux_0, tmp__trace) <@ h__BN___cminusP_ (param, b_param, param_0,
    b_param_0, param_1);
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++ tmp__trace);
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP____mont_redM);
  }
  proc h__MUL__XREG____mulr_row0 (a:W64.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_t:BArray176.t;
    var cf:bool;
    var _zero:W64.t;
    var t:BArray176.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XREG____mulr_row0:trace;
    b_t <- witness;
    t <- witness;
    trace_h__MUL__XREG____mulr_row0 <- [];
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, (BArray88.is_init b_b 0 88))]);
    b_t <- (BArray176.init_arr (W8.of_int 0));
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    b_t <- (BArray176.set64d b_t 8 (W64.of_int 18446744073709551615));
    b_t <- (BArray176.set64d b_t 0 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 a (BArray88.get64 b 0));
    t <- (BArray176.set64 t 1 aux);
    t <- (BArray176.set64 t 0 aux_0);
    i <- 1;
    while ((i < 11)) {
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_t <-
      (BArray176.set64d b_t ((i + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 a (BArray88.get64 b i));
      t <- (BArray176.set64 t (i + 1) aux_1);
      lo <- aux_2;
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_row0 <-
      (trace_h__MUL__XREG____mulr_row0 ++
      [(Assert, (BArray176.is_init b_t (i * 8) 8))]);
      b_t <-
      (BArray176.set64d b_t (i * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray176.get64 t i) lo cf);
      cf <- aux_3;
      t <- (BArray176.set64 t i aux_4);
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_row0 <-
    (trace_h__MUL__XREG____mulr_row0 ++
    [(Assert, (BArray176.is_init b_t (11 * 8) 8))]);
    b_t <- (BArray176.set64d b_t (11 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray176.get64 t 11) _zero cf);
    cf <- aux_5;
    t <- (BArray176.set64 t 11 aux_6);
    return (t, b_t, trace_h__MUL__XREG____mulr_row0);
  }
  proc h__MUL__XREG____mulr_rowk (k:int, t:BArray176.t, b_t:BArray176.t,
                                  a:W64.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_3:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux_10:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_7:bool;
    var aux_9:bool;
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XREG____mulr_rowk:trace;
    trace_h__MUL__XREG____mulr_rowk <- [];
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((((1 <= k) /\ (k < 11)) /\ (BArray176.is_init b_t 0 (8 * (k + 11)))) /\
     (BArray88.is_init b_b 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    inc <- (11 - 1);
    i <- 0;
    while ((i < inc)) {
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 a (BArray88.get64 b i));
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, (BArray176.is_init b_t ((k + i) * 8) 8))]);
      b_t <-
      (BArray176.set64d b_t ((k + i) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray176.get64 t (k + i)) lo of_0);
      of_0 <- aux;
      t <- (BArray176.set64 t (k + i) aux_0);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mulr_rowk <-
      (trace_h__MUL__XREG____mulr_rowk ++
      [(Assert, (BArray176.is_init b_t (((k + i) + 1) * 8) 8))]);
      b_t <-
      (BArray176.set64d b_t (((k + i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray176.get64 t ((k + i) + 1)) hi cf);
      cf <- aux_1;
      t <- (BArray176.set64 t ((k + i) + 1) aux_2);
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    b_t <-
    (BArray176.set64d b_t ((k + 11) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 a (BArray88.get64 b (11 - 1)));
    t <- (BArray176.set64 t (k + 11) aux_3);
    lo <- aux_4;
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((0 <= (((k + 11) - 1) * 8)) /\ (((((k + 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert,
     ((0 <= (((k + 11) - 1) * 8)) /\ (((((k + 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray176.is_init b_t (((k + 11) - 1) * 8) 8))]);
    b_t <-
    (BArray176.set64d b_t (((k + 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray176.get64 t ((k + 11) - 1)) lo of_0);
    of_0 <- aux_5;
    t <- (BArray176.set64 t ((k + 11) - 1) aux_6);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray176.is_init b_t ((k + 11) * 8) 8))]);
    b_t <-
    (BArray176.set64d b_t ((k + 11) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray176.get64 t (k + 11)) _zero cf);
    cf <- aux_7;
    t <- (BArray176.set64 t (k + 11) aux_8);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____mulr_rowk <-
    (trace_h__MUL__XREG____mulr_rowk ++
    [(Assert, (BArray176.is_init b_t ((k + 11) * 8) 8))]);
    b_t <-
    (BArray176.set64d b_t ((k + 11) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray176.get64 t (k + 11)) _zero of_0);
    of_0 <- aux_9;
    t <- (BArray176.set64 t (k + 11) aux_10);
    return (t, b_t, trace_h__MUL__XREG____mulr_rowk);
  }
  proc h__MUL__XREG___os_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var inc:int;
    var ak:W64.t;
    var param:W64.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_t:BArray176.t;
    var t:BArray176.t;
    var k:int;
    var param_1:int;
    var b_param:BArray176.t;
    var param_2:BArray176.t;
    var param_3:W64.t;
    var param_4:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var trace_h__MUL__XREG___os_muln:trace;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_t <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    t <- witness;
    trace_h__MUL__XREG___os_muln <- [];
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    ak <- (BArray88.get64 a 0);
    param <- ak;
    param_0 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XREG____mulr_row0 (param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++ tmp__trace);
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++
    [(Assert, (BArray176.is_init b_result 0 96))]);
    b_t <- b_result;
    t <- result;
    trace_h__MUL__XREG___os_muln <-
    (trace_h__MUL__XREG___os_muln ++ [(Assert, (BArray176.is_init b_t 0 8))]);
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 (BArray176.get64 t 0));
    k <- 1;
    while ((k < 11)) {
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 88)))]);
      ak <- (BArray88.get64 a k);
      param_1 <- k;
      b_param <- b_t;
      param_2 <- t;
      param_3 <- ak;
      param_4 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XREG____mulr_rowk (param_1,
      param_2, b_param, param_3, param_4,
      (BArray88.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++ tmp__trace);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, (BArray176.is_init b_result_0 0 (8 * ((param_1 + 11) + 1))))]);
      b_t <- b_result_0;
      t <- result_0;
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, (BArray176.is_init b_t (k * 8) 8))]);
      b_r <-
      (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r k (BArray176.get64 t k));
      k <- (k + 1);
    }
    inc <- (2 * 11);
    k <- 11;
    while ((k < inc)) {
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG___os_muln <-
      (trace_h__MUL__XREG___os_muln ++
      [(Assert, (BArray176.is_init b_t (k * 8) 8))]);
      b_r <-
      (BArray176.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r k (BArray176.get64 t k));
      k <- (k + 1);
    }
    return (r, b_r, trace_h__MUL__XREG___os_muln);
  }
  proc h__MUL__XREG___os_muln_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__MUL__XREG___os_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL__XREG___os_muln_ <- [];
    trace_h__MUL__XREG___os_muln_ <-
    (trace_h__MUL__XREG___os_muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XREG___os_muln (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XREG___os_muln_ <-
    (trace_h__MUL__XREG___os_muln_ ++ tmp__trace);
    trace_h__MUL__XREG___os_muln_ <-
    (trace_h__MUL__XREG___os_muln_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XREG___os_muln_);
  }
  proc h__MUL__XREG____sqrr_row0 (a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                  BArray176.t *
                                                                  trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_t:BArray176.t;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var t:BArray176.t;
    var j:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__MUL__XREG____sqrr_row0:trace;
    b_t <- witness;
    t <- witness;
    trace_h__MUL__XREG____sqrr_row0 <- [];
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, ((2 <= 11) /\ (BArray88.is_init b_a 0 88)))]);
    b_t <- (BArray176.init_arr (W8.of_int 0));
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray88.get64 a 0);
    b_t <- (BArray176.set64d b_t 16 (W64.of_int 18446744073709551615));
    b_t <- (BArray176.set64d b_t 8 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 ai (BArray88.get64 a 1));
    t <- (BArray176.set64 t 2 aux);
    t <- (BArray176.set64 t 1 aux_0);
    j <- 2;
    while ((j < 11)) {
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= ((j + 1) * 8)) /\ ((((j + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      b_t <-
      (BArray176.set64d b_t ((j + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 ai (BArray88.get64 a j));
      t <- (BArray176.set64 t (j + 1) aux_1);
      lo <- aux_2;
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_row0 <-
      (trace_h__MUL__XREG____sqrr_row0 ++
      [(Assert, (BArray176.is_init b_t (j * 8) 8))]);
      b_t <-
      (BArray176.set64d b_t (j * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray176.get64 t j) lo cf);
      cf <- aux_3;
      t <- (BArray176.set64 t j aux_4);
      j <- (j + 1);
    }
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_row0 <-
    (trace_h__MUL__XREG____sqrr_row0 ++
    [(Assert, (BArray176.is_init b_t (11 * 8) 8))]);
    b_t <- (BArray176.set64d b_t (11 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray176.get64 t 11) _zero cf);
    cf <- aux_5;
    t <- (BArray176.set64 t 11 aux_6);
    return (t, b_t, trace_h__MUL__XREG____sqrr_row0);
  }
  proc h__MUL__XREG____sqrr_rowi (i:int, t:BArray176.t, b_t:BArray176.t,
                                  a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                  BArray176.t *
                                                                  trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_3:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux_10:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_7:bool;
    var aux_9:bool;
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var j:int;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XREG____sqrr_rowi:trace;
    trace_h__MUL__XREG____sqrr_rowi <- [];
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((((1 <= i) /\ (i < (11 - 1))) /\
      (BArray176.is_init b_t 8 (8 * ((i + 11) - 1)))) /\
     (BArray88.is_init b_a 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
    ai <- (BArray88.get64 a i);
    inc <- (11 - 1);
    j <- (i + 1);
    while ((j < inc)) {
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a j));
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, (BArray176.is_init b_t ((i + j) * 8) 8))]);
      b_t <-
      (BArray176.set64d b_t ((i + j) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray176.get64 t (i + j)) lo of_0);
      of_0 <- aux;
      t <- (BArray176.set64 t (i + j) aux_0);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert,
       ((0 <= (((i + j) + 1) * 8)) /\ (((((i + j) + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert,
       ((0 <= (((i + j) + 1) * 8)) /\ (((((i + j) + 1) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_rowi <-
      (trace_h__MUL__XREG____sqrr_rowi ++
      [(Assert, (BArray176.is_init b_t (((i + j) + 1) * 8) 8))]);
      b_t <-
      (BArray176.set64d b_t (((i + j) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray176.get64 t ((i + j) + 1)) hi cf);
      cf <- aux_1;
      t <- (BArray176.set64 t ((i + j) + 1) aux_2);
      j <- (j + 1);
    }
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 11) * 8)) /\ ((((i + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    b_t <-
    (BArray176.set64d b_t ((i + 11) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 ai (BArray88.get64 a (11 - 1)));
    t <- (BArray176.set64 t (i + 11) aux_3);
    lo <- aux_4;
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((0 <= (((i + 11) - 1) * 8)) /\ (((((i + 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert,
     ((0 <= (((i + 11) - 1) * 8)) /\ (((((i + 11) - 1) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray176.is_init b_t (((i + 11) - 1) * 8) 8))]);
    b_t <-
    (BArray176.set64d b_t (((i + 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray176.get64 t ((i + 11) - 1)) lo of_0);
    of_0 <- aux_5;
    t <- (BArray176.set64 t ((i + 11) - 1) aux_6);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 11) * 8)) /\ ((((i + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 11) * 8)) /\ ((((i + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray176.is_init b_t ((i + 11) * 8) 8))]);
    b_t <-
    (BArray176.set64d b_t ((i + 11) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray176.get64 t (i + 11)) _zero cf);
    cf <- aux_7;
    t <- (BArray176.set64 t (i + 11) aux_8);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 11) * 8)) /\ ((((i + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, ((0 <= ((i + 11) * 8)) /\ ((((i + 11) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_rowi <-
    (trace_h__MUL__XREG____sqrr_rowi ++
    [(Assert, (BArray176.is_init b_t ((i + 11) * 8) 8))]);
    b_t <-
    (BArray176.set64d b_t ((i + 11) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray176.get64 t (i + 11)) _zero of_0);
    of_0 <- aux_9;
    t <- (BArray176.set64 t (i + 11) aux_10);
    return (t, b_t, trace_h__MUL__XREG____sqrr_rowi);
  }
  proc h__MUL__XREG____sqrr_diag (r:BArray176.t, b_r:BArray176.t,
                                  t:BArray176.t, b_t:BArray176.t,
                                  a:BArray88.t, b_a:BArray88.t) : BArray176.t *
                                                                  BArray176.t *
                                                                  trace = {
    var inc:int;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var w:int;
    var x:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL__XREG____sqrr_diag:trace;
    trace_h__MUL__XREG____sqrr_diag <- [];
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((((2 <= 11) /\ (BArray176.is_init b_r 8 96)) /\
      (BArray176.is_init b_t 8 160)) /\
     (BArray88.is_init b_a 0 88)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray88.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray88.get64 a 0));
    b_r <- (BArray176.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 0 lo);
    w <- 1;
    if (((w + 10) <= (2 * 11))) {
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, (BArray176.is_init b_r (w * 8) 8))]);
      x <- (BArray176.get64 r w);
    } else {
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, (BArray176.is_init b_t (w * 8) 8))]);
      x <- (BArray176.get64 t w);
    }
    (cf, x) <- (ADCX_64 x x cf);
    (of_0, x) <- (ADOX_64 x hi of_0);
    b_r <- (BArray176.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r 1 x);
    inc <- (11 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a i);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a i));
      w <- (2 * i);
      if (((w + 10) <= (2 * 11))) {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray176.is_init b_r (w * 8) 8))]);
        x <- (BArray176.get64 r w);
      } else {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray176.is_init b_t (w * 8) 8))]);
        x <- (BArray176.get64 t w);
      }
      (cf, x) <- (ADCX_64 x x cf);
      (of_0, x) <- (ADOX_64 x lo of_0);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r (2 * i) x);
      w <- ((2 * i) + 1);
      if (((w + 10) <= (2 * 11))) {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray176.is_init b_r (w * 8) 8))]);
        x <- (BArray176.get64 r w);
      } else {
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____sqrr_diag <-
        (trace_h__MUL__XREG____sqrr_diag ++
        [(Assert, (BArray176.is_init b_t (w * 8) 8))]);
        x <- (BArray176.get64 t w);
      }
      (cf, x) <- (ADCX_64 x x cf);
      (of_0, x) <- (ADOX_64 x hi of_0);
      trace_h__MUL__XREG____sqrr_diag <-
      (trace_h__MUL__XREG____sqrr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r ((2 * i) + 1) x);
      i <- (i + 1);
    }
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    ai <- (BArray88.get64 a (11 - 1));
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert, ((0 <= ((11 - 1) * 8)) /\ ((((11 - 1) * 8) + 8) <= 88)))]);
    (hi, lo) <- (MULX_64 ai (BArray88.get64 a (11 - 1)));
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 11) - 2) * 8)) /\ (((((2 * 11) - 2) * 8) + 8) <= 176)))]);
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert, (BArray176.is_init b_t (((2 * 11) - 2) * 8) 8))]);
    x <- (BArray176.get64 t ((2 * 11) - 2));
    (cf, x) <- (ADCX_64 x x cf);
    (of_0, x) <- (ADOX_64 x lo of_0);
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 11) - 2) * 8)) /\ (((((2 * 11) - 2) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r ((2 * 11) - 2) x);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XREG____sqrr_diag <-
    (trace_h__MUL__XREG____sqrr_diag ++
    [(Assert,
     ((0 <= (((2 * 11) - 1) * 8)) /\ (((((2 * 11) - 1) * 8) + 8) <= 176)))]);
    b_r <-
    (BArray176.set64d b_r (((2 * 11) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray176.set64 r ((2 * 11) - 1) hi);
    return (r, b_r, trace_h__MUL__XREG____sqrr_diag);
  }
  proc h__MUL__XREG___os_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                               b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                 trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var aux_3:BArray176.t;
    var aux_4:BArray176.t;
    var inc:int;
    var inc_0:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var param:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_t:BArray176.t;
    var t:BArray176.t;
    var w:int;
    var i:int;
    var param_0:int;
    var b_param:BArray176.t;
    var param_1:BArray176.t;
    var param_2:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var b_param_0:BArray176.t;
    var param_3:BArray176.t;
    var b_param_1:BArray176.t;
    var param_4:BArray176.t;
    var param_5:BArray88.t;
    var result_1:BArray176.t;
    var b_result_1:BArray176.t;
    var trace_h__MUL__XREG___os_sqrn:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_t <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    t <- witness;
    trace_h__MUL__XREG___os_sqrn <- [];
    trace_h__MUL__XREG___os_sqrn <-
    (trace_h__MUL__XREG___os_sqrn ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    if ((11 = 1)) {
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 88)))]);
      ai <- (BArray88.get64 a 0);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 88)))]);
      (hi, lo) <- (MULX_64 ai (BArray88.get64 a 0));
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r 0 lo);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 176)))]);
      b_r <-
      (BArray176.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray176.set64 r 1 hi);
    } else {
      param <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__XREG____sqrr_row0 (param,
      (BArray88.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++ tmp__trace);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, (BArray176.is_init b_result 8 88))]);
      b_t <- b_result;
      t <- result;
      w <- 1;
      while ((w < 3)) {
        if (((w + 10) <= (2 * 11))) {
          trace_h__MUL__XREG___os_sqrn <-
          (trace_h__MUL__XREG___os_sqrn ++
          [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
          trace_h__MUL__XREG___os_sqrn <-
          (trace_h__MUL__XREG___os_sqrn ++
          [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
          trace_h__MUL__XREG___os_sqrn <-
          (trace_h__MUL__XREG___os_sqrn ++
          [(Assert, (BArray176.is_init b_t (w * 8) 8))]);
          b_r <-
          (BArray176.set64d b_r (w * 8) (W64.of_int 18446744073709551615));
          r <- (BArray176.set64 r w (BArray176.get64 t w));
        } else {
          
        }
        w <- (w + 1);
      }
      inc <- (11 - 1);
      i <- 1;
      while ((i < inc)) {
        param_0 <- i;
        b_param <- b_t;
        param_1 <- t;
        param_2 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__XREG____sqrr_rowi (param_0,
        param_1, b_param, param_2, (BArray88.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__XREG___os_sqrn <-
        (trace_h__MUL__XREG___os_sqrn ++ tmp__trace);
        trace_h__MUL__XREG___os_sqrn <-
        (trace_h__MUL__XREG___os_sqrn ++
        [(Assert, (BArray176.is_init b_result_0 8 (8 * (param_0 + 11))))]);
        b_t <- b_result_0;
        t <- result_0;
        inc_0 <- ((2 * i) + 3);
        w <- ((2 * i) + 1);
        while ((w < inc_0)) {
          if (((w + 10) <= (2 * 11))) {
            trace_h__MUL__XREG___os_sqrn <-
            (trace_h__MUL__XREG___os_sqrn ++
            [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
            trace_h__MUL__XREG___os_sqrn <-
            (trace_h__MUL__XREG___os_sqrn ++
            [(Assert, ((0 <= (w * 8)) /\ (((w * 8) + 8) <= 176)))]);
            trace_h__MUL__XREG___os_sqrn <-
            (trace_h__MUL__XREG___os_sqrn ++
            [(Assert, (BArray176.is_init b_t (w * 8) 8))]);
            b_r <-
            (BArray176.set64d b_r (w * 8) (W64.of_int 18446744073709551615));
            r <- (BArray176.set64 r w (BArray176.get64 t w));
          } else {
            
          }
          w <- (w + 1);
        }
        i <- (i + 1);
      }
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_t;
      param_4 <- t;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__XREG____sqrr_diag (param_3,
      b_param_0, param_4, b_param_1, param_5,
      (BArray88.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++ tmp__trace);
      trace_h__MUL__XREG___os_sqrn <-
      (trace_h__MUL__XREG___os_sqrn ++
      [(Assert, (BArray176.is_init b_result_1 0 176))]);
      b_r <- (BArray176.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__MUL__XREG___os_sqrn);
  }
  proc h__MUL__XREG___os_sqrn_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                                b_a:BArray88.t) : BArray176.t * BArray176.t *
                                                  trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__MUL__XREG___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XREG___os_sqrn_ <- [];
    trace_h__MUL__XREG___os_sqrn_ <-
    (trace_h__MUL__XREG___os_sqrn_ ++
    [(Assert, (BArray88.is_init b_a 0 88))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XREG___os_sqrn (param, b_param,
    param_0, (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XREG___os_sqrn_ <-
    (trace_h__MUL__XREG___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XREG___os_sqrn_ <-
    (trace_h__MUL__XREG___os_sqrn_ ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    r <- r;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XREG___os_sqrn_);
  }
  proc h__MUL__XREG____mont_redM (r:BArray88.t, b_r:BArray88.t,
                                  a:BArray176.t, b_a:BArray176.t,
                                  _P_mP:BArray176.t, b__P_mP:BArray176.t,
                                  _U0:W64.t) : BArray88.t * BArray88.t *
                                               trace = {
    var aux_0:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_8:W64.t;
    var aux:bool;
    var aux_1:bool;
    var aux_3:bool;
    var aux_5:bool;
    var aux_7:bool;
    var b_w:BArray176.t;
    var b_s:BArray88.t;
    var i:int;
    var w:BArray176.t;
    var c:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var s:BArray88.t;
    var x:W64.t;
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
    var  _13:W64.t;
    var trace_h__MUL__XREG____mont_redM:trace;
    b_s <- witness;
    b_w <- witness;
    s <- witness;
    w <- witness;
    trace_h__MUL__XREG____mont_redM <- [];
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b__P_mP 0 176)))]);
    b_w <- (BArray176.init_arr (W8.of_int 0));
    b_s <- (BArray88.init_arr (W8.of_int 0));
    i <- 0;
    while ((i < 11)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
      b_w <-
      (BArray176.set64d b_w (i * 8) (W64.of_int 18446744073709551615));
      w <- (BArray176.set64 w i (BArray176.get64 a i));
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- 0;
    while ((k < 11)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray176.is_init b_w (k * 8) 8))]);
      m <- (BArray176.get64 w k);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray176.get64 _P_mP 0));
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray176.is_init b_w (k * 8) 8))]);
      b_w <-
      (BArray176.set64d b_w (k * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray176.get64 w k) lo of_0);
      of_0 <- aux;
      w <- (BArray176.set64 w k aux_0);
      i <- 1;
      while ((i < 11)) {
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, (BArray176.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray176.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_1, aux_2) <- (ADCX_64 (BArray176.get64 w (k + i)) hi cf);
        cf <- aux_1;
        w <- (BArray176.set64 w (k + i) aux_2);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 176)))]);
        (hi, lo) <- (MULX_64 m (BArray176.get64 _P_mP i));
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 176)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, (BArray176.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray176.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_3, aux_4) <- (ADOX_64 (BArray176.get64 w (k + i)) lo of_0);
        of_0 <- aux_3;
        w <- (BArray176.set64 w (k + i) aux_4);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
        (cf, hi) <- (adc_64 hi (BArray176.get64 a 11) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
        (cf, hi) <- (adc_64 hi (BArray176.get64 a (k + 11)) cf);
      }
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((k + 11) * 8)) /\ ((((k + 11) * 8) + 8) <= 176)))]);
      b_w <-
      (BArray176.set64d b_w ((k + 11) * 8) (W64.of_int 18446744073709551615));
      w <- (BArray176.set64 w (k + 11) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    i <- 0;
    while ((i < 11)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((11 + i) * 8)) /\ ((((11 + i) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray176.is_init b_w ((11 + i) * 8) 8))]);
      b_s <- (BArray88.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      s <- (BArray88.set64 s i (BArray176.get64 w (11 + i)));
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert, (BArray88.is_init b_s 0 8))]);
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 8) <= 176)))]);
    b_s <- (BArray88.set64d b_s 0 (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <-
    (adc_64 (BArray88.get64 s 0) (BArray176.get64 _P_mP 11) false);
    cf <- aux_5;
    s <- (BArray88.set64 s 0 aux_6);
    i <- 1;
    while ((i < 11)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray88.is_init b_s (i * 8) 8))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((11 + i) * 8)) /\ ((((11 + i) * 8) + 8) <= 176)))]);
      b_s <- (BArray88.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      (aux_7, aux_8) <-
      (adc_64 (BArray88.get64 s i) (BArray176.get64 _P_mP (11 + i)) cf);
      cf <- aux_7;
      s <- (BArray88.set64 s i aux_8);
      i <- (i + 1);
    }
    ( _8, c) <- (adc_64 c (W64.of_int 0) cf);
    ( _9, cf,  _10,  _11,  _12,  _13) <- (NEG_64 c);
    i <- 0;
    while ((i < 11)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((11 + i) * 8)) /\ ((((11 + i) * 8) + 8) <= 176)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray176.is_init b_w ((11 + i) * 8) 8))]);
      x <- (BArray176.get64 w (11 + i));
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray88.is_init b_s (i * 8) 8))]);
      x <- (cf ? (BArray88.get64 s i) : x);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i x);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__MUL__XREG____mont_redM);
  }
  proc h__MUL___muln_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var aux_3:BArray176.t;
    var aux_4:BArray176.t;
    var aux_5:BArray176.t;
    var aux_6:BArray176.t;
    var aux_7:BArray176.t;
    var aux_8:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_param_0:BArray176.t;
    var param_2:BArray176.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var b_param_1:BArray176.t;
    var param_5:BArray176.t;
    var param_6:BArray88.t;
    var param_7:BArray88.t;
    var result_1:BArray176.t;
    var b_result_1:BArray176.t;
    var b_param_2:BArray176.t;
    var param_8:BArray176.t;
    var param_9:BArray88.t;
    var param_10:BArray88.t;
    var result_2:BArray176.t;
    var b_result_2:BArray176.t;
    var b_param_3:BArray176.t;
    var param_11:BArray176.t;
    var param_12:BArray88.t;
    var param_13:BArray88.t;
    var result_3:BArray176.t;
    var b_result_3:BArray176.t;
    var trace_h__MUL___muln_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
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
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__MUL___muln_ <- [];
    trace_h__MUL___muln_ <-
    (trace_h__MUL___muln_ ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    if ((((W256.of_int 19) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((11 <= 23)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- b;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG___os_muln_ (param,
        b_param, param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
        (BArray88.init_arr (W8.of_int 255)));
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
        trace_h__MUL___muln_ <-
        (trace_h__MUL___muln_ ++
        [(Assert, (BArray176.is_init b_result 0 176))]);
        r <- result;
      } else {
        if ((11 <= 17)) {
          b_param_0 <- b_r;
          param_2 <- r;
          param_3 <- a;
          param_4 <- b;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR___os_muln_ (param_2,
          b_param_0, param_3, (BArray88.init_arr (W8.of_int 255)), param_4,
          (BArray88.init_arr (W8.of_int 255)));
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
          trace_h__MUL___muln_ <-
          (trace_h__MUL___muln_ ++
          [(Assert, (BArray176.is_init b_result_0 0 176))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_5 <- r;
          param_6 <- a;
          param_7 <- b;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP___os_muln_ (param_5,
          b_param_1, param_6, (BArray88.init_arr (W8.of_int 255)), param_7,
          (BArray88.init_arr (W8.of_int 255)));
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
          trace_h__MUL___muln_ <-
          (trace_h__MUL___muln_ ++
          [(Assert, (BArray176.is_init b_result_1 0 176))]);
          r <- result_1;
        }
      }
    } else {
      if ((11 <= 17)) {
        b_param_2 <- b_r;
        param_8 <- r;
        param_9 <- a;
        param_10 <- b;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR___ps_muln_ (param_8,
        b_param_2, param_9, (BArray88.init_arr (W8.of_int 255)), param_10,
        (BArray88.init_arr (W8.of_int 255)));
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
        trace_h__MUL___muln_ <-
        (trace_h__MUL___muln_ ++
        [(Assert, (BArray176.is_init b_result_2 0 176))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- b;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_muln_ (param_11,
        b_param_3, param_12, (BArray88.init_arr (W8.of_int 255)), param_13,
        (BArray88.init_arr (W8.of_int 255)));
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL___muln_ <- (trace_h__MUL___muln_ ++ tmp__trace);
        trace_h__MUL___muln_ <-
        (trace_h__MUL___muln_ ++
        [(Assert, (BArray176.is_init b_result_3 0 176))]);
        r <- result_3;
      }
    }
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___muln_);
  }
  proc h__MUL___sqrn_ (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                       b_a:BArray88.t) : BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray176.t;
    var aux_2:BArray176.t;
    var aux_3:BArray176.t;
    var aux_4:BArray176.t;
    var aux_5:BArray176.t;
    var aux_6:BArray176.t;
    var aux_7:BArray176.t;
    var aux_8:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_param_0:BArray176.t;
    var param_1:BArray176.t;
    var param_2:BArray88.t;
    var result_0:BArray176.t;
    var b_result_0:BArray176.t;
    var b_param_1:BArray176.t;
    var param_3:BArray176.t;
    var param_4:BArray88.t;
    var result_1:BArray176.t;
    var b_result_1:BArray176.t;
    var b_param_2:BArray176.t;
    var param_5:BArray176.t;
    var param_6:BArray88.t;
    var result_2:BArray176.t;
    var b_result_2:BArray176.t;
    var b_param_3:BArray176.t;
    var param_7:BArray176.t;
    var param_8:BArray88.t;
    var result_3:BArray176.t;
    var b_result_3:BArray176.t;
    var trace_h__MUL___sqrn_:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
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
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__MUL___sqrn_ <- [];
    trace_h__MUL___sqrn_ <-
    (trace_h__MUL___sqrn_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    if ((((W256.of_int 19) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((11 <= 23)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG___os_sqrn_ (param,
        b_param, param_0, (BArray88.init_arr (W8.of_int 255)));
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
        trace_h__MUL___sqrn_ <-
        (trace_h__MUL___sqrn_ ++
        [(Assert, (BArray176.is_init b_result 0 176))]);
        r <- result;
      } else {
        if ((11 <= 17)) {
          b_param_0 <- b_r;
          param_1 <- r;
          param_2 <- a;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR___os_sqrn_ (param_1,
          b_param_0, param_2, (BArray88.init_arr (W8.of_int 255)));
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
          trace_h__MUL___sqrn_ <-
          (trace_h__MUL___sqrn_ ++
          [(Assert, (BArray176.is_init b_result_0 0 176))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_3 <- r;
          param_4 <- a;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP___os_sqrn_ (param_3,
          b_param_1, param_4, (BArray88.init_arr (W8.of_int 255)));
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
          trace_h__MUL___sqrn_ <-
          (trace_h__MUL___sqrn_ ++
          [(Assert, (BArray176.is_init b_result_1 0 176))]);
          r <- result_1;
        }
      }
    } else {
      if ((11 <= 17)) {
        b_param_2 <- b_r;
        param_5 <- r;
        param_6 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR___ps_sqrn_ (param_5,
        b_param_2, param_6, (BArray88.init_arr (W8.of_int 255)));
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
        trace_h__MUL___sqrn_ <-
        (trace_h__MUL___sqrn_ ++
        [(Assert, (BArray176.is_init b_result_2 0 176))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_7 <- r;
        param_8 <- a;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP___os_sqrn_ (param_7,
        b_param_3, param_8, (BArray88.init_arr (W8.of_int 255)));
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL___sqrn_ <- (trace_h__MUL___sqrn_ ++ tmp__trace);
        trace_h__MUL___sqrn_ <-
        (trace_h__MUL___sqrn_ ++
        [(Assert, (BArray176.is_init b_result_3 0 176))]);
        r <- result_3;
      }
    }
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___sqrn_);
  }
  proc h__MUL____mont_redM (r:BArray88.t, b_r:BArray88.t, a:BArray176.t,
                            b_a:BArray176.t, _P_mP:BArray176.t,
                            b__P_mP:BArray176.t, _U0:W64.t) : BArray88.t *
                                                              BArray88.t *
                                                              trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_6:BArray88.t;
    var aux_7:BArray88.t;
    var aux_8:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray176.t;
    var param_1:BArray176.t;
    var param_2:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray176.t;
    var param_5:BArray176.t;
    var param_6:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var b_param_1:BArray88.t;
    var param_7:BArray88.t;
    var param_8:BArray176.t;
    var param_9:BArray176.t;
    var param_10:W64.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var b_param_2:BArray88.t;
    var param_11:BArray88.t;
    var param_12:BArray176.t;
    var param_13:BArray176.t;
    var param_14:W64.t;
    var result_2:BArray88.t;
    var b_result_2:BArray88.t;
    var b_param_3:BArray88.t;
    var param_15:BArray88.t;
    var param_16:BArray176.t;
    var param_17:BArray176.t;
    var param_18:W64.t;
    var result_3:BArray88.t;
    var b_result_3:BArray88.t;
    var trace_h__MUL____mont_redM:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    param_11 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    trace_h__MUL____mont_redM <- [];
    trace_h__MUL____mont_redM <-
    (trace_h__MUL____mont_redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray176.is_init b__P_mP 0 176)))]);
    if ((((W256.of_int 19) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((11 <= 23)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- _P_mP;
        param_2 <- _U0;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG____mont_redM (param,
        b_param, param_0, (BArray176.init_arr (W8.of_int 255)), param_1,
        (BArray176.init_arr (W8.of_int 255)), param_2);
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray88.is_init b_result 0 88))]);
        r <- result;
      } else {
        if ((11 <= 17)) {
          b_param_0 <- b_r;
          param_3 <- r;
          param_4 <- a;
          param_5 <- _P_mP;
          param_6 <- _U0;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR____mont_redM (param_3,
          b_param_0, param_4, (BArray176.init_arr (W8.of_int 255)), param_5,
          (BArray176.init_arr (W8.of_int 255)), param_6);
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++ tmp__trace);
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++
          [(Assert, (BArray88.is_init b_result_0 0 88))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_7 <- r;
          param_8 <- a;
          param_9 <- _P_mP;
          param_10 <- _U0;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP____mont_redM (param_7,
          b_param_1, param_8, (BArray176.init_arr (W8.of_int 255)), param_9,
          (BArray176.init_arr (W8.of_int 255)), param_10);
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++ tmp__trace);
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++
          [(Assert, (BArray88.is_init b_result_1 0 88))]);
          r <- result_1;
        }
      }
    } else {
      if ((11 <= 17)) {
        b_param_2 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- _P_mP;
        param_14 <- _U0;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR____mont_redM (param_11,
        b_param_2, param_12, (BArray176.init_arr (W8.of_int 255)), param_13,
        (BArray176.init_arr (W8.of_int 255)), param_14);
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray88.is_init b_result_2 0 88))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_15 <- r;
        param_16 <- a;
        param_17 <- _P_mP;
        param_18 <- _U0;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mont_redM (param_15,
        b_param_3, param_16, (BArray176.init_arr (W8.of_int 255)), param_17,
        (BArray176.init_arr (W8.of_int 255)), param_18);
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray88.is_init b_result_3 0 88))]);
        r <- result_3;
      }
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL____mont_redM);
  }
  proc h__FPM__fun_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
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
    var trace_h__FPM__fun_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM__fun_muln <- [];
    trace_h__FPM__fun_muln <-
    (trace_h__FPM__fun_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL___muln_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_muln <- (trace_h__FPM__fun_muln ++ tmp__trace);
    trace_h__FPM__fun_muln <-
    (trace_h__FPM__fun_muln ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_muln);
  }
  proc h__FPM__fun_sqrn (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                         b_a:BArray88.t) : BArray176.t * BArray176.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var trace_h__FPM__fun_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__FPM__fun_sqrn <- [];
    trace_h__FPM__fun_sqrn <-
    (trace_h__FPM__fun_sqrn ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL___sqrn_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_sqrn <- (trace_h__FPM__fun_sqrn ++ tmp__trace);
    trace_h__FPM__fun_sqrn <-
    (trace_h__FPM__fun_sqrn ++
    [(Assert, (BArray176.is_init b_result 0 176))]);
    r <- result;
    b_r <- (BArray176.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_sqrn);
  }
  proc h__FPM___redM (r:BArray88.t, b_r:BArray88.t, a:BArray176.t,
                      b_a:BArray176.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var t:W64.t;
    var _u0:W64.t;
    var b_PmP:BArray176.t;
    var pmP:BArray176.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray176.t;
    var b_param_0:BArray176.t;
    var param_1:BArray176.t;
    var param_2:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM___redM:trace;
    pmP <- witness;
    b_PmP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM___redM <- [];
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray360.is_init b_ctx 0 360)))]);
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert, ((0 <= (44 * 8)) /\ (((44 * 8) + 8) <= 360)))]);
    t <- (BArray360.get64 ctx 44);
    _u0 <- t;
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 176) <= 360)))]);
    b_PmP <- (SBArray360_176.get_sub64 b_ctx 0);
    pmP <- (SBArray360_176.get_sub64 ctx 0);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    b_param_0 <- b_PmP;
    param_1 <- pmP;
    param_2 <- _u0;
    (aux, aux_0, tmp__trace) <@ h__MUL____mont_redM (param, b_param, 
    param_0, (BArray176.init_arr (W8.of_int 255)), param_1, b_param_0,
    param_2);
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___redM <- (trace_h__FPM___redM ++ tmp__trace);
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___redM);
  }
  proc h__FPM___redM_ (r:BArray88.t, b_r:BArray88.t, a:BArray176.t,
                       b_a:BArray176.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray176.t;
    var param_1:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM___redM_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM___redM_ <- [];
    trace_h__FPM___redM_ <-
    (trace_h__FPM___redM_ ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray360.is_init b_ctx 0 360)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    ctx <- ctx;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___redM (param, b_param, param_0,
    (BArray176.init_arr (W8.of_int 255)), param_1,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___redM_ <- (trace_h__FPM___redM_ ++ tmp__trace);
    trace_h__FPM___redM_ <-
    (trace_h__FPM___redM_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___redM_);
  }
  proc h__FPM___fromM_ (a:BArray88.t, b_a:BArray88.t, ctx:BArray360.t,
                        b_ctx:BArray360.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__tmp:BArray176.t;
    var b_tmp2:BArray88.t;
    var tmp2:BArray88.t;
    var _tmp:BArray176.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var param_2:BArray88.t;
    var b_param_1:BArray176.t;
    var param_3:BArray176.t;
    var param_4:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var trace_h__FPM___fromM_:trace;
    _tmp <- witness;
    b__tmp <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_tmp <- witness;
    b_tmp2 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    tmp <- witness;
    tmp2 <- witness;
    trace_h__FPM___fromM_ <- [];
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    b_tmp2 <- (SBArray176_88.get_sub64 b__tmp 0);
    tmp2 <- (SBArray176_88.get_sub64 _tmp 0);
    b_param <- b_tmp2;
    param <- tmp2;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    tmp2 <- result;
    b__tmp <-
    (SBArray176_88.set_sub64 b__tmp 0 (BArray88.init_arr (W8.of_int 255)));
    _tmp <- (SBArray176_88.set_sub64 _tmp 0 tmp2);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b_tmp2 <- (SBArray176_88.get_sub64 b__tmp 11);
    tmp2 <- (SBArray176_88.get_sub64 _tmp 11);
    b_param_0 <- b_tmp2;
    param_1 <- tmp2;
    (aux_1, aux_2, tmp__trace) <@ h__BN___set0_ (param_1, b_param_0);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    tmp2 <- result_0;
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 176)))]);
    b__tmp <-
    (SBArray176_88.set_sub64 b__tmp 11 (BArray88.init_arr (W8.of_int 255)));
    _tmp <- (SBArray176_88.set_sub64 _tmp 11 tmp2);
    b_tmp <- b__tmp;
    tmp <- _tmp;
    param_2 <- a;
    b_param_1 <- b_tmp;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM___redM_ (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3, b_param_1, param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    a <- result_1;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___fromM_);
  }
  proc h__FPM__fun_red (r:BArray88.t, b_r:BArray88.t, a:BArray176.t,
                        b_a:BArray176.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray176.t;
    var param_1:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM__fun_red:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM__fun_red <- [];
    trace_h__FPM__fun_red <-
    (trace_h__FPM__fun_red ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray360.is_init b_ctx 0 360)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___redM_ (param, b_param, param_0,
    (BArray176.init_arr (W8.of_int 255)), param_1,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_red <- (trace_h__FPM__fun_red ++ tmp__trace);
    trace_h__FPM__fun_red <-
    (trace_h__FPM__fun_red ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_red);
  }
  proc h__FPM___addm_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                       ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                             BArray88.t *
                                                             trace = {
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
    var lastbit:W64.t;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var param_2:BArray88.t;
    var b_param_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:W64.t;
    var result_1:BArray88.t;
    var b_result_0:BArray88.t;
    var  _0:bool;
    var trace_h__FPM___addm_:trace;
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
    trace_h__FPM___addm_ <- [];
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 88 88)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param, b_param, 
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FPM___addm_ <- (trace_h__FPM___addm_ ++ tmp__trace);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    r <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 360)))]);
    b_tmp <- (SBArray360_88.get_sub64 b_ctx 11);
    tmp <- (SBArray360_88.get_sub64 ctx 11);
    param_2 <- r;
    b_param_0 <- b_tmp;
    param_3 <- tmp;
    param_4 <- lastbit;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cminusP_ (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3, b_param_0, param_4);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___addm_ <- (trace_h__FPM___addm_ ++ tmp__trace);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_1;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___addm_);
  }
  proc h__FPM___addmU_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var cf:bool;
    var lastbit:W64.t;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var param_1:BArray88.t;
    var b_param:BArray88.t;
    var param_2:BArray88.t;
    var param_3:W64.t;
    var result_1:BArray88.t;
    var b_result_0:BArray88.t;
    var  _0:bool;
    var trace_h__FPM___addmU_:trace;
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
    trace_h__FPM___addmU_ <- [];
    trace_h__FPM___addmU_ <-
    (trace_h__FPM___addmU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM___addmU_ <-
    (trace_h__FPM___addmU_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FPM___addmU_ <-
    (trace_h__FPM___addmU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    param <- a;
    param_0 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___addU_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FPM___addmU_ <- (trace_h__FPM___addmU_ ++ tmp__trace);
    trace_h__FPM___addmU_ <-
    (trace_h__FPM___addmU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__FPM___addmU_ <-
    (trace_h__FPM___addmU_ ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 360)))]);
    b_tmp <- (SBArray360_88.get_sub64 b_ctx 11);
    tmp <- (SBArray360_88.get_sub64 ctx 11);
    param_1 <- a;
    b_param <- b_tmp;
    param_2 <- tmp;
    param_3 <- lastbit;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cminusP_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2, b_param, param_3);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___addmU_ <- (trace_h__FPM___addmU_ ++ tmp__trace);
    trace_h__FPM___addmU_ <-
    (trace_h__FPM___addmU_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_1;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___addmU_);
  }
  proc h__FPM___submU_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux:bool;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:bool;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var cf:bool;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var param_1:BArray88.t;
    var param_2:bool;
    var b_param:BArray88.t;
    var param_3:BArray88.t;
    var result_1:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM___submU_:trace;
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
    trace_h__FPM___submU_ <- [];
    trace_h__FPM___submU_ <-
    (trace_h__FPM___submU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM___submU_ <-
    (trace_h__FPM___submU_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FPM___submU_ <-
    (trace_h__FPM___submU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    param <- a;
    param_0 <- b;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___subU_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__FPM___submU_ <- (trace_h__FPM___submU_ ++ tmp__trace);
    trace_h__FPM___submU_ <-
    (trace_h__FPM___submU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    cf <- result;
    a <- result_0;
    trace_h__FPM___submU_ <-
    (trace_h__FPM___submU_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 88) <= 360)))]);
    b_tmp <- (SBArray360_88.get_sub64 b_ctx 0);
    tmp <- (SBArray360_88.get_sub64 ctx 0);
    param_1 <- a;
    param_2 <- cf;
    b_param <- b_tmp;
    param_3 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___caddU_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2, param_3, b_param);
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___submU_ <- (trace_h__FPM___submU_ ++ tmp__trace);
    trace_h__FPM___submU_ <-
    (trace_h__FPM___submU_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_1;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___submU_);
  }
  proc h__FPM___mulm_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                       ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                             BArray88.t *
                                                             trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray176.t;
    var b__r:BArray88.t;
    var _r:BArray88.t;
    var _ctx:BArray360.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_param_0:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray176.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM___mulm_:trace;
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
    trace_h__FPM___mulm_ <- [];
    trace_h__FPM___mulm_ <-
    (trace_h__FPM___mulm_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_muln (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___mulm_ <- (trace_h__FPM___mulm_ ++ tmp__trace);
    trace_h__FPM___mulm_ <-
    (trace_h__FPM___mulm_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_2 <- r;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_2, b_param_0,
    param_3, (BArray176.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___mulm_ <- (trace_h__FPM___mulm_ ++ tmp__trace);
    trace_h__FPM___mulm_ <-
    (trace_h__FPM___mulm_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___mulm_);
  }
  proc h__FPM___mulmU_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                        b_b:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray176.t;
    var _a:BArray88.t;
    var _ctx:BArray360.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var param_2:BArray88.t;
    var param_3:BArray176.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM___mulmU_:trace;
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
    trace_h__FPM___mulmU_ <- [];
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_muln (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___mulmU_ <- (trace_h__FPM___mulmU_ ++ tmp__trace);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray176.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___mulmU_ <- (trace_h__FPM___mulmU_ ++ tmp__trace);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___mulmU_);
  }
  proc h__FPM___sqrm_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray176.t;
    var b__r:BArray88.t;
    var _r:BArray88.t;
    var _ctx:BArray360.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray176.t;
    var param_3:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM___sqrm_:trace;
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
    trace_h__FPM___sqrm_ <- [];
    trace_h__FPM___sqrm_ <-
    (trace_h__FPM___sqrm_ ++
    [(Assert,
     ((BArray88.is_init b_a 0 88) /\ (BArray360.is_init b_ctx 0 360)))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_sqrn (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___sqrm_ <- (trace_h__FPM___sqrm_ ++ tmp__trace);
    trace_h__FPM___sqrm_ <-
    (trace_h__FPM___sqrm_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- tmp;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_1, b_param_0,
    param_2, (BArray176.init_arr (W8.of_int 255)), param_3,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___sqrm_ <- (trace_h__FPM___sqrm_ ++ tmp__trace);
    trace_h__FPM___sqrm_ <-
    (trace_h__FPM___sqrm_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___sqrm_);
  }
  proc h__FPM___sqrmU_ (a:BArray88.t, b_a:BArray88.t, ctx:BArray360.t,
                        b_ctx:BArray360.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray176.t;
    var _a:BArray88.t;
    var _ctx:BArray360.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var param_1:BArray88.t;
    var param_2:BArray176.t;
    var param_3:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM___sqrmU_:trace;
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
    trace_h__FPM___sqrmU_ <- [];
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_sqrn (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___sqrmU_ <- (trace_h__FPM___sqrmU_ ++ tmp__trace);
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray176.init_arr (W8.of_int 255)), param_3,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___sqrmU_ <- (trace_h__FPM___sqrmU_ ++ tmp__trace);
    trace_h__FPM___sqrmU_ <-
    (trace_h__FPM___sqrmU_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___sqrmU_);
  }
  proc h__FPM__fun_mulU (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                         b_b:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM__fun_mulU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM__fun_mulU <- [];
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    param <- a;
    param_0 <- b;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___mulmU_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_mulU <- (trace_h__FPM__fun_mulU ++ tmp__trace);
    trace_h__FPM__fun_mulU <-
    (trace_h__FPM__fun_mulU ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM__fun_mulU);
  }
  proc h__FPM__fun_sqrU (a:BArray88.t, b_a:BArray88.t, ctx:BArray360.t,
                         b_ctx:BArray360.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM__fun_sqrU:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__FPM__fun_sqrU <- [];
    trace_h__FPM__fun_sqrU <-
    (trace_h__FPM__fun_sqrU ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM__fun_sqrU <-
    (trace_h__FPM__fun_sqrU ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    param <- a;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___sqrmU_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_sqrU <- (trace_h__FPM__fun_sqrU ++ tmp__trace);
    trace_h__FPM__fun_sqrU <-
    (trace_h__FPM__fun_sqrU ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM__fun_sqrU);
  }
  proc h__FPM__EXP___expm_noct (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                                b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                                ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_6:BArray88.t;
    var aux_7:BArray88.t;
    var aux_8:BArray88.t;
    var b__x:BArray88.t;
    var _b:BArray88.t;
    var _ctx:BArray360.t;
    var b_x:BArray88.t;
    var x:BArray88.t;
    var _x:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var j:int;
    var t:W64.t;
    var _k:W64.t;
    var cf:bool;
    var _t:W64.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var _r:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var trace_h__FPM__EXP___expm_noct:trace;
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
    trace_h__FPM__EXP___expm_noct <- [];
    trace_h__FPM__EXP___expm_noct <-
    (trace_h__FPM__EXP___expm_noct ++
    [(Assert, (BArray88.is_init b_r 0 88))]);
    trace_h__FPM__EXP___expm_noct <-
    (trace_h__FPM__EXP___expm_noct ++
    [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM__EXP___expm_noct <-
    (trace_h__FPM__EXP___expm_noct ++
    [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FPM__EXP___expm_noct <-
    (trace_h__FPM__EXP___expm_noct ++
    [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__x <- (BArray88.init_arr (W8.of_int 0));
    _b <- b;
    _ctx <- ctx;
    b_x <- b__x;
    x <- _x;
    b_param <- b_x;
    param <- x;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXP___expm_noct <-
    (trace_h__FPM__EXP___expm_noct ++ tmp__trace);
    trace_h__FPM__EXP___expm_noct <-
    (trace_h__FPM__EXP___expm_noct ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    x <- result;
    _x <- x;
    j <- 0;
    while ((j < 11)) {
      b <- _b;
      trace_h__FPM__EXP___expm_noct <-
      (trace_h__FPM__EXP___expm_noct ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 b j);
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- (SHR_64 t (W8.of_int 1));
      _t <- t;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_1 <- r;
        param_2 <- x;
        param_3 <- ctx;
        (aux_5, aux_6, tmp__trace) <@ h__FPM__fun_mulU (param_1,
        (BArray88.init_arr (W8.of_int 255)), param_2,
        (BArray88.init_arr (W8.of_int 255)), param_3,
        (BArray360.init_arr (W8.of_int 255)));
        result_0 <- aux_5;
        b_result_0 <- aux_6;
        trace_h__FPM__EXP___expm_noct <-
        (trace_h__FPM__EXP___expm_noct ++ tmp__trace);
        trace_h__FPM__EXP___expm_noct <-
        (trace_h__FPM__EXP___expm_noct ++
        [(Assert, (BArray88.is_init b_result_0 0 88))]);
        r <- result_0;
      } else {
        
      }
      _r <- r;
      x <- _x;
      ctx <- _ctx;
      param_4 <- x;
      param_5 <- ctx;
      (aux_7, aux_8, tmp__trace) <@ h__FPM__fun_sqrU (param_4,
      (BArray88.init_arr (W8.of_int 255)), param_5,
      (BArray360.init_arr (W8.of_int 255)));
      result_1 <- aux_7;
      b_result_1 <- aux_8;
      trace_h__FPM__EXP___expm_noct <-
      (trace_h__FPM__EXP___expm_noct ++ tmp__trace);
      trace_h__FPM__EXP___expm_noct <-
      (trace_h__FPM__EXP___expm_noct ++
      [(Assert, (BArray88.is_init b_result_1 0 88))]);
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
          (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_mulU (param_1,
          (BArray88.init_arr (W8.of_int 255)), param_2,
          (BArray88.init_arr (W8.of_int 255)), param_3,
          (BArray360.init_arr (W8.of_int 255)));
          result_0 <- aux_1;
          b_result_0 <- aux_2;
          trace_h__FPM__EXP___expm_noct <-
          (trace_h__FPM__EXP___expm_noct ++ tmp__trace);
          trace_h__FPM__EXP___expm_noct <-
          (trace_h__FPM__EXP___expm_noct ++
          [(Assert, (BArray88.is_init b_result_0 0 88))]);
          r <- result_0;
        } else {
          
        }
        _r <- r;
        x <- _x;
        ctx <- _ctx;
        param_4 <- x;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__FPM__fun_sqrU (param_4,
        (BArray88.init_arr (W8.of_int 255)), param_5,
        (BArray360.init_arr (W8.of_int 255)));
        result_1 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__FPM__EXP___expm_noct <-
        (trace_h__FPM__EXP___expm_noct ++ tmp__trace);
        trace_h__FPM__EXP___expm_noct <-
        (trace_h__FPM__EXP___expm_noct ++
        [(Assert, (BArray88.is_init b_result_1 0 88))]);
        x <- result_1;
        _x <- x;
        r <- _r;
        t <- _t;
        ( _4,  _5,  _6, zf, _k) <- (DEC_64 _k);
      }
      j <- (j + 1);
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXP___expm_noct);
  }
  proc h__FPM__EXP___expm_noct_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                                 b_a:BArray88.t, b:BArray88.t,
                                 b_b:BArray88.t, ctx:BArray360.t,
                                 b_ctx:BArray360.t) : BArray88.t *
                                                      BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b_exp0:BArray88.t;
    var exp0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var b_param_0:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM__EXP___expm_noct_:trace;
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
    trace_h__FPM__EXP___expm_noct_ <- [];
    trace_h__FPM__EXP___expm_noct_ <-
    (trace_h__FPM__EXP___expm_noct_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    trace_h__FPM__EXP___expm_noct_ <-
    (trace_h__FPM__EXP___expm_noct_ ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_exp0 <- (SBArray360_88.get_sub64 b_ctx 22);
    exp0 <- (SBArray360_88.get_sub64 ctx 22);
    b_param <- b_r;
    param <- r;
    b_param_0 <- b_exp0;
    param_0 <- exp0;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXP___expm_noct_ <-
    (trace_h__FPM__EXP___expm_noct_ ++ tmp__trace);
    trace_h__FPM__EXP___expm_noct_ <-
    (trace_h__FPM__EXP___expm_noct_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    a <- a;
    b <- b;
    param_1 <- r;
    param_2 <- a;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__EXP___expm_noct (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM__EXP___expm_noct_ <-
    (trace_h__FPM__EXP___expm_noct_ ++ tmp__trace);
    trace_h__FPM__EXP___expm_noct_ <-
    (trace_h__FPM__EXP___expm_noct_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXP___expm_noct_);
  }
  proc h__FPM__EXP___expm (x0:BArray88.t, b_x0:BArray88.t, x1:BArray88.t,
                           b_x1:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                           ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                 BArray88.t *
                                                                 BArray88.t *
                                                                 BArray88.t *
                                                                 trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_6:BArray88.t;
    var aux_7:BArray88.t;
    var aux_8:BArray88.t;
    var aux_9:BArray88.t;
    var aux_10:BArray88.t;
    var aux_11:BArray88.t;
    var aux_12:BArray88.t;
    var aux_13:BArray88.t;
    var aux_14:BArray88.t;
    var aux_15:BArray88.t;
    var aux_16:BArray88.t;
    var aux_17:BArray88.t;
    var aux_18:BArray88.t;
    var _b:BArray88.t;
    var _ctx:BArray360.t;
    var _mask:W64.t;
    var j:int;
    var t:W64.t;
    var _k:W64.t;
    var cf:bool;
    var _t:W64.t;
    var param:bool;
    var result:W64.t;
    var mask:W64.t;
    var swap_0:W64.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result:BArray88.t;
    var result_1:BArray88.t;
    var b_result_0:BArray88.t;
    var _x0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray360.t;
    var result_2:BArray88.t;
    var b_result_1:BArray88.t;
    var _x1:BArray88.t;
    var param_6:BArray88.t;
    var param_7:BArray360.t;
    var result_3:BArray88.t;
    var b_result_2:BArray88.t;
    var zf:bool;
    var param_8:BArray88.t;
    var param_9:BArray88.t;
    var param_10:W64.t;
    var result_4:BArray88.t;
    var b_result_3:BArray88.t;
    var result_5:BArray88.t;
    var b_result_4:BArray88.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var trace_h__FPM__EXP___expm:trace;
    _b <- witness;
    _ctx <- witness;
    _x0 <- witness;
    _x1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    param_9 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    trace_h__FPM__EXP___expm <- [];
    trace_h__FPM__EXP___expm <-
    (trace_h__FPM__EXP___expm ++ [(Assert, (BArray88.is_init b_x0 0 88))]);
    trace_h__FPM__EXP___expm <-
    (trace_h__FPM__EXP___expm ++ [(Assert, (BArray88.is_init b_x1 0 88))]);
    trace_h__FPM__EXP___expm <-
    (trace_h__FPM__EXP___expm ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FPM__EXP___expm <-
    (trace_h__FPM__EXP___expm ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    _b <- b;
    _ctx <- ctx;
    _mask <- (W64.of_int 0);
    j <- (11 - 1);
    while (((-1) < j)) {
      b <- _b;
      trace_h__FPM__EXP___expm <-
      (trace_h__FPM__EXP___expm ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 b j);
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- (SHL_64 t (W8.of_int 1));
      _t <- t;
      param <- cf;
      (result, tmp__trace) <@ uTIL____cf_mask (param);
      trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
      mask <- result;
      swap_0 <- _mask;
      swap_0 <- (swap_0 `^` mask);
      _mask <- mask;
      param_0 <- x0;
      param_1 <- x1;
      param_2 <- swap_0;
      (aux_7, aux_8, aux_9, aux_10, tmp__trace) <@ h__BN___cswap_mask_ (
      param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
      (BArray88.init_arr (W8.of_int 255)), param_2);
      result_0 <- aux_7;
      b_result <- aux_8;
      result_1 <- aux_9;
      b_result_0 <- aux_10;
      trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
      trace_h__FPM__EXP___expm <-
      (trace_h__FPM__EXP___expm ++
      [(Assert, (BArray88.is_init b_result 0 88))]);
      trace_h__FPM__EXP___expm <-
      (trace_h__FPM__EXP___expm ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      x0 <- result_0;
      x1 <- result_1;
      _x0 <- x0;
      ctx <- _ctx;
      param_3 <- x1;
      param_4 <- x0;
      param_5 <- ctx;
      (aux_11, aux_12, tmp__trace) <@ h__FPM__fun_mulU (param_3,
      (BArray88.init_arr (W8.of_int 255)), param_4,
      (BArray88.init_arr (W8.of_int 255)), param_5,
      (BArray360.init_arr (W8.of_int 255)));
      result_2 <- aux_11;
      b_result_1 <- aux_12;
      trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
      trace_h__FPM__EXP___expm <-
      (trace_h__FPM__EXP___expm ++
      [(Assert, (BArray88.is_init b_result_1 0 88))]);
      x1 <- result_2;
      _x1 <- x1;
      x0 <- _x0;
      ctx <- _ctx;
      param_6 <- x0;
      param_7 <- ctx;
      (aux_13, aux_14, tmp__trace) <@ h__FPM__fun_sqrU (param_6,
      (BArray88.init_arr (W8.of_int 255)), param_7,
      (BArray360.init_arr (W8.of_int 255)));
      result_3 <- aux_13;
      b_result_2 <- aux_14;
      trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
      trace_h__FPM__EXP___expm <-
      (trace_h__FPM__EXP___expm ++
      [(Assert, (BArray88.is_init b_result_2 0 88))]);
      x0 <- result_3;
      x1 <- _x1;
      t <- _t;
      ( _4,  _5,  _6, zf, _k) <- (DEC_64 _k);
      while ((! zf)) {
        ( _0, cf,  _1,  _2,  _3, t) <- (SHL_64 t (W8.of_int 1));
        _t <- t;
        param <- cf;
        (result, tmp__trace) <@ uTIL____cf_mask (param);
        trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
        mask <- result;
        swap_0 <- _mask;
        swap_0 <- (swap_0 `^` mask);
        _mask <- mask;
        param_0 <- x0;
        param_1 <- x1;
        param_2 <- swap_0;
        (aux, aux_0, aux_1, aux_2, tmp__trace) <@ h__BN___cswap_mask_ (
        param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
        (BArray88.init_arr (W8.of_int 255)), param_2);
        result_0 <- aux;
        b_result <- aux_0;
        result_1 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
        trace_h__FPM__EXP___expm <-
        (trace_h__FPM__EXP___expm ++
        [(Assert, (BArray88.is_init b_result 0 88))]);
        trace_h__FPM__EXP___expm <-
        (trace_h__FPM__EXP___expm ++
        [(Assert, (BArray88.is_init b_result_0 0 88))]);
        x0 <- result_0;
        x1 <- result_1;
        _x0 <- x0;
        ctx <- _ctx;
        param_3 <- x1;
        param_4 <- x0;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__FPM__fun_mulU (param_3,
        (BArray88.init_arr (W8.of_int 255)), param_4,
        (BArray88.init_arr (W8.of_int 255)), param_5,
        (BArray360.init_arr (W8.of_int 255)));
        result_2 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
        trace_h__FPM__EXP___expm <-
        (trace_h__FPM__EXP___expm ++
        [(Assert, (BArray88.is_init b_result_1 0 88))]);
        x1 <- result_2;
        _x1 <- x1;
        x0 <- _x0;
        ctx <- _ctx;
        param_6 <- x0;
        param_7 <- ctx;
        (aux_5, aux_6, tmp__trace) <@ h__FPM__fun_sqrU (param_6,
        (BArray88.init_arr (W8.of_int 255)), param_7,
        (BArray360.init_arr (W8.of_int 255)));
        result_3 <- aux_5;
        b_result_2 <- aux_6;
        trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
        trace_h__FPM__EXP___expm <-
        (trace_h__FPM__EXP___expm ++
        [(Assert, (BArray88.is_init b_result_2 0 88))]);
        x0 <- result_3;
        x1 <- _x1;
        t <- _t;
        ( _4,  _5,  _6, zf, _k) <- (DEC_64 _k);
      }
      j <- (j - 1);
    }
    mask <- _mask;
    param_8 <- x0;
    param_9 <- x1;
    param_10 <- mask;
    (aux_15, aux_16, aux_17, aux_18, tmp__trace) <@ h__BN___cswap_mask_ (
    param_8, (BArray88.init_arr (W8.of_int 255)), param_9,
    (BArray88.init_arr (W8.of_int 255)), param_10);
    result_4 <- aux_15;
    b_result_3 <- aux_16;
    result_5 <- aux_17;
    b_result_4 <- aux_18;
    trace_h__FPM__EXP___expm <- (trace_h__FPM__EXP___expm ++ tmp__trace);
    trace_h__FPM__EXP___expm <-
    (trace_h__FPM__EXP___expm ++
    [(Assert, (BArray88.is_init b_result_3 0 88))]);
    trace_h__FPM__EXP___expm <-
    (trace_h__FPM__EXP___expm ++
    [(Assert, (BArray88.is_init b_result_4 0 88))]);
    x0 <- result_4;
    x1 <- result_5;
    b_x0 <- (BArray88.init_arr (W8.of_int 255));
    b_x1 <- (BArray88.init_arr (W8.of_int 255));
    return (x0, b_x0, x1, b_x1, trace_h__FPM__EXP___expm);
  }
  proc h__FPM__EXP___expm_ (x0:BArray88.t, b_x0:BArray88.t, a:BArray88.t,
                            b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                            ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                  BArray88.t *
                                                                  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_6:BArray88.t;
    var b__x1:BArray88.t;
    var b_x1:BArray88.t;
    var x1:BArray88.t;
    var _x1:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_exp0:BArray88.t;
    var exp0:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var b_param_1:BArray88.t;
    var param_2:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var result_2:BArray88.t;
    var b_result_2:BArray88.t;
    var trace_h__FPM__EXP___expm_:trace;
    _x1 <- witness;
    b__x1 <- witness;
    b_exp0 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_x1 <- witness;
    exp0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    x1 <- witness;
    trace_h__FPM__EXP___expm_ <- [];
    trace_h__FPM__EXP___expm_ <-
    (trace_h__FPM__EXP___expm_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__x1 <- (BArray88.init_arr (W8.of_int 0));
    b_x1 <- b__x1;
    x1 <- _x1;
    b_param <- b_x1;
    param <- x1;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXP___expm_ <- (trace_h__FPM__EXP___expm_ ++ tmp__trace);
    trace_h__FPM__EXP___expm_ <-
    (trace_h__FPM__EXP___expm_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    x1 <- result;
    trace_h__FPM__EXP___expm_ <-
    (trace_h__FPM__EXP___expm_ ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_exp0 <- (SBArray360_88.get_sub64 b_ctx 22);
    exp0 <- (SBArray360_88.get_sub64 ctx 22);
    b_param_0 <- b_x0;
    param_1 <- x0;
    b_param_1 <- b_exp0;
    param_2 <- exp0;
    (aux_1, aux_2, tmp__trace) <@ h__BN___mov_ (param_1, b_param_0, param_2,
    b_param_1);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM__EXP___expm_ <- (trace_h__FPM__EXP___expm_ ++ tmp__trace);
    trace_h__FPM__EXP___expm_ <-
    (trace_h__FPM__EXP___expm_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    x0 <- result_0;
    b <- b;
    param_3 <- x0;
    param_4 <- x1;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, aux_5, aux_6, tmp__trace) <@ h__FPM__EXP___expm (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray88.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__FPM__EXP___expm_ <- (trace_h__FPM__EXP___expm_ ++ tmp__trace);
    trace_h__FPM__EXP___expm_ <-
    (trace_h__FPM__EXP___expm_ ++
    [(Assert, (BArray88.is_init b_result_1 0 88))]);
    trace_h__FPM__EXP___expm_ <-
    (trace_h__FPM__EXP___expm_ ++
    [(Assert, (BArray88.is_init b_result_2 0 88))]);
    x0 <- result_1;
    x0 <- x0;
    b_x0 <- (BArray88.init_arr (W8.of_int 255));
    return (x0, b_x0, trace_h__FPM__EXP___expm_);
  }
  proc h__FPM__EXP____tblsel (r:BArray88.t, b_r:BArray88.t, tbl:BArray1408.t,
                              b_tbl:BArray1408.t, idx:W64.t) : BArray88.t *
                                                               BArray88.t *
                                                               trace = {
    var k:W64.t;
    var t:W64.t;
    var i:int;
    var zf:bool;
    var trace_h__FPM__EXP____tblsel:trace;
    trace_h__FPM__EXP____tblsel <- [];
    trace_h__FPM__EXP____tblsel <-
    (trace_h__FPM__EXP____tblsel ++
    [(Assert, (BArray1408.is_init b_tbl 0 1408))]);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 11))) {
      trace_h__FPM__EXP____tblsel <-
      (trace_h__FPM__EXP____tblsel ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\
       ((((W64.to_uint k) * 8) + 8) <= 1408)))]);
      t <- (BArray1408.get64 tbl (W64.to_uint k));
      i <- 1;
      while ((i < 16)) {
        zf <- (idx = (W64.of_int i));
        trace_h__FPM__EXP____tblsel <-
        (trace_h__FPM__EXP____tblsel ++
        [(Assert,
         ((0 <= ((W64.to_uint (k + (W64.of_int (i * 11)))) * 8)) /\
         ((((W64.to_uint (k + (W64.of_int (i * 11)))) * 8) + 8) <= 1408)))]);
        t <-
        (zf ? (BArray1408.get64 tbl (W64.to_uint (k + (W64.of_int (i * 11))))
              ) : t);
        i <- (i + 1);
      }
      trace_h__FPM__EXP____tblsel <-
      (trace_h__FPM__EXP____tblsel ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 88)))]);
      b_r <-
      (BArray88.set64d b_r ((W64.to_uint k) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r (W64.to_uint k) t);
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__FPM__EXP____tblsel);
  }
  proc h__FPM__EXP___expmW (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                            b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                            ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                  BArray88.t *
                                                                  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_6:BArray88.t;
    var aux_7:BArray88.t;
    var aux_8:BArray88.t;
    var aux_9:BArray88.t;
    var aux_10:BArray88.t;
    var aux_11:BArray88.t;
    var aux_12:BArray88.t;
    var aux_13:BArray88.t;
    var aux_14:BArray88.t;
    var b_tbl:BArray1408.t;
    var b_sel:BArray88.t;
    var b__r:BArray88.t;
    var _r:BArray88.t;
    var _a:BArray88.t;
    var _b:BArray88.t;
    var _ctx:BArray360.t;
    var b_one:BArray88.t;
    var one:BArray88.t;
    var b_p:BArray88.t;
    var p:BArray88.t;
    var tbl:BArray1408.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var b_param_0:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_1:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var i:int;
    var b_param_2:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var b_q:BArray88.t;
    var q:BArray88.t;
    var b_param_3:BArray88.t;
    var param_5:BArray88.t;
    var b_param_4:BArray88.t;
    var param_6:BArray88.t;
    var param_7:BArray360.t;
    var result_2:BArray88.t;
    var b_result_2:BArray88.t;
    var b_param_5:BArray88.t;
    var param_8:BArray88.t;
    var b_param_6:BArray88.t;
    var param_9:BArray88.t;
    var result_3:BArray88.t;
    var b_result_3:BArray88.t;
    var j:W64.t;
    var _j:W64.t;
    var t:W64.t;
    var _t:W64.t;
    var k:W64.t;
    var _k:W64.t;
    var idx:W64.t;
    var b_psel:BArray88.t;
    var psel:BArray88.t;
    var sel:BArray88.t;
    var b_ptbl:BArray1408.t;
    var ptbl:BArray1408.t;
    var b_param_7:BArray88.t;
    var param_10:BArray88.t;
    var b_param_8:BArray1408.t;
    var param_11:BArray1408.t;
    var param_12:W64.t;
    var result_4:BArray88.t;
    var b_result_4:BArray88.t;
    var s:int;
    var param_13:BArray88.t;
    var param_14:BArray360.t;
    var result_5:BArray88.t;
    var b_result_5:BArray88.t;
    var param_15:BArray88.t;
    var param_16:BArray88.t;
    var param_17:BArray360.t;
    var result_6:BArray88.t;
    var b_result_6:BArray88.t;
    var trace_h__FPM__EXP___expmW:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
    _r <- witness;
    b__r <- witness;
    b_one <- witness;
    b_p <- witness;
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
    b_psel <- witness;
    b_ptbl <- witness;
    b_q <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_sel <- witness;
    b_tbl <- witness;
    one <- witness;
    p <- witness;
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
    param_13 <- witness;
    param_14 <- witness;
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    psel <- witness;
    ptbl <- witness;
    q <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    sel <- witness;
    tbl <- witness;
    trace_h__FPM__EXP___expmW <- [];
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b_tbl <- (BArray1408.init_arr (W8.of_int 0));
    b_sel <- (BArray88.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _a <- a;
    _b <- b;
    _ctx <- ctx;
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_one <- (SBArray360_88.get_sub64 b_ctx 22);
    one <- (SBArray360_88.get_sub64 ctx 22);
    b_p <- (SBArray1408_88.get_sub64 b_tbl 0);
    p <- (SBArray1408_88.get_sub64 tbl 0);
    b_param <- b_p;
    param <- p;
    b_param_0 <- b_one;
    param_0 <- one;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    b_param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXP___expmW <- (trace_h__FPM__EXP___expmW ++ tmp__trace);
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    p <- result;
    b_tbl <-
    (SBArray1408_88.set_sub64 b_tbl 0 (BArray88.init_arr (W8.of_int 255)));
    tbl <- (SBArray1408_88.set_sub64 tbl 0 p);
    a <- _a;
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 1408)))]);
    b_p <- (SBArray1408_88.get_sub64 b_tbl 11);
    p <- (SBArray1408_88.get_sub64 tbl 11);
    b_param_1 <- b_p;
    param_1 <- p;
    param_2 <- a;
    (aux_1, aux_2, tmp__trace) <@ h__BN___mov_ (param_1, b_param_1, param_2,
    (BArray88.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM__EXP___expmW <- (trace_h__FPM__EXP___expmW ++ tmp__trace);
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    p <- result_0;
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 1408)))]);
    b_tbl <-
    (SBArray1408_88.set_sub64 b_tbl 11 (BArray88.init_arr (W8.of_int 255)));
    tbl <- (SBArray1408_88.set_sub64 tbl 11 p);
    i <- 2;
    while ((i < 16)) {
      a <- _a;
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 11) * 8)) /\ ((((i * 11) * 8) + 88) <= 1408)))]);
      b_p <- (SBArray1408_88.get_sub64 b_tbl (i * 11));
      p <- (SBArray1408_88.get_sub64 tbl (i * 11));
      b_param_2 <- b_p;
      param_3 <- p;
      param_4 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__BN___mov_ (param_3, b_param_2,
      param_4, (BArray88.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__FPM__EXP___expmW <- (trace_h__FPM__EXP___expmW ++ tmp__trace);
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert, (BArray88.is_init b_result_1 0 88))]);
      p <- result_1;
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 11) * 8)) /\ ((((i * 11) * 8) + 88) <= 1408)))]);
      b_tbl <-
      (SBArray1408_88.set_sub64 b_tbl (i * 11)
      (BArray88.init_arr (W8.of_int 255)));
      tbl <- (SBArray1408_88.set_sub64 tbl (i * 11) p);
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert,
       ((0 <= (((i - 1) * 11) * 8)) /\ (((((i - 1) * 11) * 8) + 88) <= 1408)))]);
      b_q <- (SBArray1408_88.get_sub64 b_tbl ((i - 1) * 11));
      q <- (SBArray1408_88.get_sub64 tbl ((i - 1) * 11));
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 11) * 8)) /\ ((((i * 11) * 8) + 88) <= 1408)))]);
      b_p <- (SBArray1408_88.get_sub64 b_tbl (i * 11));
      p <- (SBArray1408_88.get_sub64 tbl (i * 11));
      ctx <- _ctx;
      b_param_3 <- b_p;
      param_5 <- p;
      b_param_4 <- b_q;
      param_6 <- q;
      param_7 <- ctx;
      (aux_5, aux_6, tmp__trace) <@ h__FPM__fun_mulU (param_5, b_param_3,
      param_6, b_param_4, param_7, (BArray360.init_arr (W8.of_int 255)));
      result_2 <- aux_5;
      b_result_2 <- aux_6;
      trace_h__FPM__EXP___expmW <- (trace_h__FPM__EXP___expmW ++ tmp__trace);
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert, (BArray88.is_init b_result_2 0 88))]);
      p <- result_2;
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert, ((0 <= ((i * 11) * 8)) /\ ((((i * 11) * 8) + 88) <= 1408)))]);
      b_tbl <-
      (SBArray1408_88.set_sub64 b_tbl (i * 11)
      (BArray88.init_arr (W8.of_int 255)));
      tbl <- (SBArray1408_88.set_sub64 tbl (i * 11) p);
      i <- (i + 1);
    }
    b_r <- b__r;
    r <- _r;
    b_ctx <- (BArray360.init_arr (W8.of_int 255));
    ctx <- _ctx;
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_one <- (SBArray360_88.get_sub64 b_ctx 22);
    one <- (SBArray360_88.get_sub64 ctx 22);
    b_param_5 <- b_r;
    param_8 <- r;
    b_param_6 <- b_one;
    param_9 <- one;
    (aux_7, aux_8, tmp__trace) <@ h__BN___mov_ (param_8, b_param_5, param_9,
    b_param_6);
    result_3 <- aux_7;
    b_result_3 <- aux_8;
    trace_h__FPM__EXP___expmW <- (trace_h__FPM__EXP___expmW ++ tmp__trace);
    trace_h__FPM__EXP___expmW <-
    (trace_h__FPM__EXP___expmW ++
    [(Assert, (BArray88.is_init b_result_3 0 88))]);
    r <- result_3;
    j <- (W64.of_int 11);
    while ((j <> (W64.of_int 0))) {
      j <- (j - (W64.of_int 1));
      _j <- j;
      b <- _b;
      trace_h__FPM__EXP___expmW <-
      (trace_h__FPM__EXP___expmW ++
      [(Assert,
       ((0 <= ((W64.to_uint j) * 8)) /\ ((((W64.to_uint j) * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 b (W64.to_uint j));
      _t <- t;
      k <- (W64.of_int 16);
      while ((k <> (W64.of_int 0))) {
        _k <- k;
        t <- _t;
        idx <- t;
        idx <- (idx `>>` (W8.of_int 60));
        t <- (t `<<` (W8.of_int 4));
        _t <- t;
        b_psel <- b_sel;
        psel <- sel;
        b_ptbl <- b_tbl;
        ptbl <- tbl;
        b_param_7 <- b_psel;
        param_10 <- psel;
        b_param_8 <- b_ptbl;
        param_11 <- ptbl;
        param_12 <- idx;
        (aux_9, aux_10, tmp__trace) <@ h__FPM__EXP____tblsel (param_10,
        b_param_7, param_11, b_param_8, param_12);
        result_4 <- aux_9;
        b_result_4 <- aux_10;
        trace_h__FPM__EXP___expmW <-
        (trace_h__FPM__EXP___expmW ++ tmp__trace);
        trace_h__FPM__EXP___expmW <-
        (trace_h__FPM__EXP___expmW ++
        [(Assert, (BArray88.is_init b_result_4 0 88))]);
        psel <- result_4;
        b_sel <- (BArray88.init_arr (W8.of_int 255));
        sel <- psel;
        s <- 0;
        while ((s < 4)) {
          ctx <- _ctx;
          param_13 <- r;
          param_14 <- ctx;
          (aux_11, aux_12, tmp__trace) <@ h__FPM__fun_sqrU (param_13,
          (BArray88.init_arr (W8.of_int 255)), param_14,
          (BArray360.init_arr (W8.of_int 255)));
          result_5 <- aux_11;
          b_result_5 <- aux_12;
          trace_h__FPM__EXP___expmW <-
          (trace_h__FPM__EXP___expmW ++ tmp__trace);
          trace_h__FPM__EXP___expmW <-
          (trace_h__FPM__EXP___expmW ++
          [(Assert, (BArray88.is_init b_result_5 0 88))]);
          r <- result_5;
          s <- (s + 1);
        }
        psel <- sel;
        ctx <- _ctx;
        param_15 <- r;
        param_16 <- psel;
        param_17 <- ctx;
        (aux_13, aux_14, tmp__trace) <@ h__FPM__fun_mulU (param_15,
        (BArray88.init_arr (W8.of_int 255)), param_16,
        (BArray88.init_arr (W8.of_int 255)), param_17,
        (BArray360.init_arr (W8.of_int 255)));
        result_6 <- aux_13;
        b_result_6 <- aux_14;
        trace_h__FPM__EXP___expmW <-
        (trace_h__FPM__EXP___expmW ++ tmp__trace);
        trace_h__FPM__EXP___expmW <-
        (trace_h__FPM__EXP___expmW ++
        [(Assert, (BArray88.is_init b_result_6 0 88))]);
        r <- result_6;
        k <- _k;
        k <- (k - (W64.of_int 1));
      }
      j <- _j;
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXP___expmW);
  }
  proc h__FPM__EXP___expmW_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                             b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                             ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                   BArray88.t *
                                                                   trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM__EXP___expmW_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    trace_h__FPM__EXP___expmW_ <- [];
    trace_h__FPM__EXP___expmW_ <-
    (trace_h__FPM__EXP___expmW_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    param_2 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM__EXP___expmW (param, b_param, 
    param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__EXP___expmW_ <- (trace_h__FPM__EXP___expmW_ ++ tmp__trace);
    trace_h__FPM__EXP___expmW_ <-
    (trace_h__FPM__EXP___expmW_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__EXP___expmW_);
  }
  proc h__FPM____Pm2 (r:BArray88.t, b_r:BArray88.t, ctx:BArray360.t,
                      b_ctx:BArray360.t) : BArray88.t * BArray88.t * trace = {
    var t:W64.t;
    var cf:bool;
    var i:int;
    var trace_h__FPM____Pm2:trace;
    trace_h__FPM____Pm2 <- [];
    trace_h__FPM____Pm2 <-
    (trace_h__FPM____Pm2 ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    trace_h__FPM____Pm2 <-
    (trace_h__FPM____Pm2 ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 360)))]);
    t <- (BArray360.get64 ctx 0);
    (cf, t) <- (sbb_64 t (W64.of_int 2) false);
    b_r <- (BArray88.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray88.set64 r 0 t);
    i <- 1;
    while ((i < 11)) {
      trace_h__FPM____Pm2 <-
      (trace_h__FPM____Pm2 ++
      [(Assert, ((0 <= ((0 + i) * 8)) /\ ((((0 + i) * 8) + 8) <= 360)))]);
      t <- (BArray360.get64 ctx (0 + i));
      (cf, t) <- (sbb_64 t (W64.of_int 0) cf);
      trace_h__FPM____Pm2 <-
      (trace_h__FPM____Pm2 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      b_r <- (BArray88.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__FPM____Pm2);
  }
  proc h__FPM___invm_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__Pm2:BArray88.t;
    var b_Pm2:BArray88.t;
    var pm2:BArray88.t;
    var _Pm2:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FPM___invm_:trace;
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
    trace_h__FPM___invm_ <- [];
    trace_h__FPM___invm_ <-
    (trace_h__FPM___invm_ ++
    [(Assert,
     ((BArray88.is_init b_a 0 88) /\ (BArray360.is_init b_ctx 0 360)))]);
    b__Pm2 <- (BArray88.init_arr (W8.of_int 0));
    b_Pm2 <- b__Pm2;
    pm2 <- _Pm2;
    b_param <- b_Pm2;
    param <- pm2;
    param_0 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM____Pm2 (param, b_param, param_0,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___invm_ <- (trace_h__FPM___invm_ ++ tmp__trace);
    trace_h__FPM___invm_ <-
    (trace_h__FPM___invm_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    pm2 <- result;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- a;
    param_3 <- pm2;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__EXP___expm_noct_ (param_1,
    b_param_0, param_2, (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___invm_ <- (trace_h__FPM___invm_ ++ tmp__trace);
    trace_h__FPM___invm_ <-
    (trace_h__FPM___invm_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___invm_);
  }
  proc h__FPM___toM_ (a:BArray88.t, b_a:BArray88.t, ctx:BArray360.t,
                      b_ctx:BArray360.t) : BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_R2:BArray88.t;
    var r2:BArray88.t;
    var param:BArray88.t;
    var b_param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__FPM___toM_:trace;
    r2 <- witness;
    b_R2 <- witness;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPM___toM_ <- [];
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++
    [(Assert, ((0 <= (33 * 8)) /\ (((33 * 8) + 88) <= 360)))]);
    b_R2 <- (SBArray360_88.get_sub64 b_ctx 33);
    r2 <- (SBArray360_88.get_sub64 ctx 33);
    param <- a;
    b_param <- b_R2;
    param_0 <- r2;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___mulmU_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0, b_param, param_1,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___toM_ <- (trace_h__FPM___toM_ ++ tmp__trace);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___toM_);
  }
  proc h__FPM___ctx_init_ (ctx:BArray360.t, b_ctx:BArray360.t, p:BArray88.t,
                           b_P:BArray88.t) : BArray360.t * BArray360.t *
                                             trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_6:BArray88.t;
    var aux_7:BArray88.t;
    var aux_8:BArray88.t;
    var aux_9:BArray88.t;
    var aux_10:BArray88.t;
    var aux_11:BArray88.t;
    var aux_12:BArray88.t;
    var aux_13:BArray88.t;
    var aux_14:BArray88.t;
    var aux_15:BArray88.t;
    var aux_16:BArray88.t;
    var aux_17:BArray88.t;
    var aux_1:bool;
    var b__x:BArray88.t;
    var b__y:BArray88.t;
    var b_t:BArray88.t;
    var t:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var result_0:bool;
    var result_1:BArray88.t;
    var b_result_0:BArray88.t;
    var p0:W64.t;
    var inv:W64.t;
    var j:int;
    var d:W64.t;
    var u0:W64.t;
    var b_x:BArray88.t;
    var x:BArray88.t;
    var _x:BArray88.t;
    var b_param_1:BArray88.t;
    var param_3:BArray88.t;
    var result_2:BArray88.t;
    var b_result_1:BArray88.t;
    var i:W64.t;
    var _i:W64.t;
    var b_y:BArray88.t;
    var y:BArray88.t;
    var _y:BArray88.t;
    var b_param_2:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray88.t;
    var b_param_3:BArray360.t;
    var param_7:BArray360.t;
    var result_3:BArray88.t;
    var b_result_2:BArray88.t;
    var param_8:BArray88.t;
    var param_9:BArray88.t;
    var param_10:BArray88.t;
    var b_param_4:BArray360.t;
    var param_11:BArray360.t;
    var result_4:BArray88.t;
    var b_result_3:BArray88.t;
    var b_param_5:BArray88.t;
    var param_12:BArray88.t;
    var param_13:BArray88.t;
    var result_5:BArray88.t;
    var b_result_4:BArray88.t;
    var b_param_6:BArray88.t;
    var param_14:BArray88.t;
    var param_15:BArray88.t;
    var param_16:BArray88.t;
    var b_param_7:BArray360.t;
    var param_17:BArray360.t;
    var result_6:BArray88.t;
    var b_result_5:BArray88.t;
    var param_18:BArray88.t;
    var param_19:BArray88.t;
    var param_20:BArray88.t;
    var b_param_8:BArray360.t;
    var param_21:BArray360.t;
    var result_7:BArray88.t;
    var b_result_6:BArray88.t;
    var b_param_9:BArray88.t;
    var param_22:BArray88.t;
    var param_23:BArray88.t;
    var result_8:BArray88.t;
    var b_result_7:BArray88.t;
    var trace_h__FPM___ctx_init_:trace;
    _x <- witness;
    _y <- witness;
    b__x <- witness;
    b__y <- witness;
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
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_t <- witness;
    b_x <- witness;
    b_y <- witness;
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
    param_15 <- witness;
    param_16 <- witness;
    param_17 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_20 <- witness;
    param_21 <- witness;
    param_22 <- witness;
    param_23 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_7 <- witness;
    result_8 <- witness;
    t <- witness;
    x <- witness;
    y <- witness;
    trace_h__FPM___ctx_init_ <- [];
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++ [(Assert, (BArray88.is_init b_P 0 88))]);
    b__x <- (BArray88.init_arr (W8.of_int 0));
    b__y <- (BArray88.init_arr (W8.of_int 0));
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 88) <= 360)))]);
    b_t <- (SBArray360_88.get_sub64 b_ctx 0);
    t <- (SBArray360_88.get_sub64 ctx 0);
    b_param <- b_t;
    param <- t;
    param_0 <- p;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    t <- result;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 88) <= 360)))]);
    b_ctx <-
    (SBArray360_88.set_sub64 b_ctx 0 (BArray88.init_arr (W8.of_int 255)));
    ctx <- (SBArray360_88.set_sub64 ctx 0 t);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 360)))]);
    b_t <- (SBArray360_88.get_sub64 b_ctx 11);
    t <- (SBArray360_88.get_sub64 ctx 11);
    b_param_0 <- b_t;
    param_1 <- t;
    param_2 <- p;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___neg_ (param_1, b_param_0,
    param_2, (BArray88.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    t <- result_1;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 360)))]);
    b_ctx <-
    (SBArray360_88.set_sub64 b_ctx 11 (BArray88.init_arr (W8.of_int 255)));
    ctx <- (SBArray360_88.set_sub64 ctx 11 t);
    p0 <- (BArray88.get64 p 0);
    inv <- p0;
    j <- 0;
    while ((j < 5)) {
      d <- p0;
      d <- (d * inv);
      d <- (- d);
      d <- (d + (W64.of_int 2));
      inv <- (inv * d);
      j <- (j + 1);
    }
    u0 <- (- inv);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (44 * 8)) /\ (((44 * 8) + 8) <= 360)))]);
    b_ctx <-
    (BArray360.set64d b_ctx (44 * 8) (W64.of_int 18446744073709551615));
    ctx <- (BArray360.set64 ctx 44 u0);
    b_x <- b__x;
    x <- _x;
    b_param_1 <- b_x;
    param_3 <- x;
    (aux_4, aux_5, tmp__trace) <@ h__BN___set0_ (param_3, b_param_1);
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray88.is_init b_result_1 0 88))]);
    x <- result_2;
    x <- (BArray88.set64 x 0 (W64.of_int 1));
    _x <- x;
    i <- (W64.of_int (32 * 11));
    while (((W64.of_int 0) \ult i)) {
      _i <- i;
      x <- _x;
      b_y <- b__y;
      y <- _y;
      b_param_2 <- b_y;
      param_4 <- y;
      param_5 <- x;
      param_6 <- x;
      b_param_3 <- b_ctx;
      param_7 <- ctx;
      (aux_6, aux_7, tmp__trace) <@ h__FPM___addm_ (param_4, b_param_2,
      param_5, (BArray88.init_arr (W8.of_int 255)), param_6,
      (BArray88.init_arr (W8.of_int 255)), param_7, b_param_3);
      result_3 <- aux_6;
      b_result_2 <- aux_7;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray88.is_init b_result_2 0 88))]);
      y <- result_3;
      b__y <- (BArray88.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_8 <- x;
      param_9 <- y;
      param_10 <- y;
      b_param_4 <- b_ctx;
      param_11 <- ctx;
      (aux_8, aux_9, tmp__trace) <@ h__FPM___addm_ (param_8,
      (BArray88.init_arr (W8.of_int 255)), param_9,
      (BArray88.init_arr (W8.of_int 255)), param_10,
      (BArray88.init_arr (W8.of_int 255)), param_11, b_param_4);
      result_4 <- aux_8;
      b_result_3 <- aux_9;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray88.is_init b_result_3 0 88))]);
      x <- result_4;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_t <- (SBArray360_88.get_sub64 b_ctx 22);
    t <- (SBArray360_88.get_sub64 ctx 22);
    b_param_5 <- b_t;
    param_12 <- t;
    param_13 <- x;
    (aux_10, aux_11, tmp__trace) <@ h__BN___mov_ (param_12, b_param_5,
    param_13, (BArray88.init_arr (W8.of_int 255)));
    result_5 <- aux_10;
    b_result_4 <- aux_11;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray88.is_init b_result_4 0 88))]);
    t <- result_5;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_ctx <-
    (SBArray360_88.set_sub64 b_ctx 22 (BArray88.init_arr (W8.of_int 255)));
    ctx <- (SBArray360_88.set_sub64 ctx 22 t);
    i <- (W64.of_int (32 * 11));
    while (((W64.of_int 0) \ult i)) {
      _i <- i;
      x <- _x;
      b_y <- b__y;
      y <- _y;
      b_param_6 <- b_y;
      param_14 <- y;
      param_15 <- x;
      param_16 <- x;
      b_param_7 <- b_ctx;
      param_17 <- ctx;
      (aux_12, aux_13, tmp__trace) <@ h__FPM___addm_ (param_14, b_param_6,
      param_15, (BArray88.init_arr (W8.of_int 255)), param_16,
      (BArray88.init_arr (W8.of_int 255)), param_17, b_param_7);
      result_6 <- aux_12;
      b_result_5 <- aux_13;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray88.is_init b_result_5 0 88))]);
      y <- result_6;
      b__y <- (BArray88.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_18 <- x;
      param_19 <- y;
      param_20 <- y;
      b_param_8 <- b_ctx;
      param_21 <- ctx;
      (aux_14, aux_15, tmp__trace) <@ h__FPM___addm_ (param_18,
      (BArray88.init_arr (W8.of_int 255)), param_19,
      (BArray88.init_arr (W8.of_int 255)), param_20,
      (BArray88.init_arr (W8.of_int 255)), param_21, b_param_8);
      result_7 <- aux_14;
      b_result_6 <- aux_15;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray88.is_init b_result_6 0 88))]);
      x <- result_7;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (33 * 8)) /\ (((33 * 8) + 88) <= 360)))]);
    b_t <- (SBArray360_88.get_sub64 b_ctx 33);
    t <- (SBArray360_88.get_sub64 ctx 33);
    b_param_9 <- b_t;
    param_22 <- t;
    param_23 <- x;
    (aux_16, aux_17, tmp__trace) <@ h__BN___mov_ (param_22, b_param_9,
    param_23, (BArray88.init_arr (W8.of_int 255)));
    result_8 <- aux_16;
    b_result_7 <- aux_17;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray88.is_init b_result_7 0 88))]);
    t <- result_8;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (33 * 8)) /\ (((33 * 8) + 88) <= 360)))]);
    b_ctx <-
    (SBArray360_88.set_sub64 b_ctx 33 (BArray88.init_arr (W8.of_int 255)));
    ctx <- (SBArray360_88.set_sub64 ctx 33 t);
    return (ctx, b_ctx, trace_h__FPM___ctx_init_);
  }
  proc fpc_ctx_init (ctx:BArray360.t, b_ctx:BArray360.t, pp:W64.t) : 
  BArray360.t * BArray360.t * trace = {
    var aux_1:BArray360.t;
    var aux_2:BArray360.t;
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b__p:BArray88.t;
    var b__ctx:BArray360.t;
    var _ctx:BArray360.t;
    var b_p:BArray88.t;
    var p:BArray88.t;
    var _p:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray360.t;
    var param_1:BArray360.t;
    var param_2:BArray88.t;
    var result_0:BArray360.t;
    var b_result_0:BArray360.t;
    var trace_fpc_ctx_init:trace;
    _ctx <- witness;
    _p <- witness;
    b__ctx <- witness;
    b__p <- witness;
    b_p <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    p <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_fpc_ctx_init <- [];
    trace_fpc_ctx_init <-
    (trace_fpc_ctx_init ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint pp) (8 * 11)))]);
    b__p <- (BArray88.init_arr (W8.of_int 0));
    b__ctx <- b_ctx;
    _ctx <- ctx;
    b_p <- b__p;
    p <- _p;
    b_param <- b_p;
    param <- p;
    param_0 <- pp;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_ctx_init <- (trace_fpc_ctx_init ++ tmp__trace);
    trace_fpc_ctx_init <-
    (trace_fpc_ctx_init ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    p <- result;
    b_ctx <- b__ctx;
    ctx <- _ctx;
    b_param_0 <- b_ctx;
    param_1 <- ctx;
    param_2 <- p;
    (aux_1, aux_2, tmp__trace) <@ h__FPM___ctx_init_ (param_1, b_param_0,
    param_2, (BArray88.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_fpc_ctx_init <- (trace_fpc_ctx_init ++ tmp__trace);
    trace_fpc_ctx_init <-
    (trace_fpc_ctx_init ++ [(Assert, (BArray360.is_init b_result_0 0 360))]);
    ctx <- result_0;
    b_ctx <- (BArray360.init_arr (W8.of_int 255));
    return (ctx, b_ctx, trace_fpc_ctx_init);
  }
  proc fpc_add (rp:W64.t, ap:W64.t, bp:W64.t, ctx:BArray360.t,
                b_ctx:BArray360.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_b:BArray88.t;
    var b:BArray88.t;
    var _b:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var param_6:W64.t;
    var param_7:BArray88.t;
    var trace_fpc_add:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
    a <- witness;
    b <- witness;
    b__a <- witness;
    b__b <- witness;
    b_a <- witness;
    b_b <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_fpc_add <- [];
    trace_fpc_add <-
    (trace_fpc_add ++
    [(Assert,
     ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
       (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_add <- (trace_fpc_add ++ tmp__trace);
    trace_fpc_add <-
    (trace_fpc_add ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_fpc_add <- (trace_fpc_add ++ tmp__trace);
    trace_fpc_add <-
    (trace_fpc_add ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    ctx <- _ctx;
    param_3 <- a;
    param_4 <- b;
    param_5 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM___addmU_ (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_fpc_add <- (trace_fpc_add ++ tmp__trace);
    trace_fpc_add <-
    (trace_fpc_add ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    a <- result_1;
    rp <- _rp;
    param_6 <- rp;
    param_7 <- a;
    tmp__trace <@ h__BN___store_ (param_6, param_7,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_add <- (trace_fpc_add ++ tmp__trace);
    return (trace_fpc_add);
  }
  proc fpc_sub (rp:W64.t, ap:W64.t, bp:W64.t, ctx:BArray360.t,
                b_ctx:BArray360.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_b:BArray88.t;
    var b:BArray88.t;
    var _b:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var param_6:W64.t;
    var param_7:BArray88.t;
    var trace_fpc_sub:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
    a <- witness;
    b <- witness;
    b__a <- witness;
    b__b <- witness;
    b_a <- witness;
    b_b <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_fpc_sub <- [];
    trace_fpc_sub <-
    (trace_fpc_sub ++
    [(Assert,
     ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
       (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_sub <- (trace_fpc_sub ++ tmp__trace);
    trace_fpc_sub <-
    (trace_fpc_sub ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_fpc_sub <- (trace_fpc_sub ++ tmp__trace);
    trace_fpc_sub <-
    (trace_fpc_sub ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    ctx <- _ctx;
    param_3 <- a;
    param_4 <- b;
    param_5 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM___submU_ (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_fpc_sub <- (trace_fpc_sub ++ tmp__trace);
    trace_fpc_sub <-
    (trace_fpc_sub ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    a <- result_1;
    rp <- _rp;
    param_6 <- rp;
    param_7 <- a;
    tmp__trace <@ h__BN___store_ (param_6, param_7,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_sub <- (trace_fpc_sub ++ tmp__trace);
    return (trace_fpc_sub);
  }
  proc fpc_mul (rp:W64.t, ap:W64.t, bp:W64.t, ctx:BArray360.t,
                b_ctx:BArray360.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
    var b__r:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_b:BArray88.t;
    var b:BArray88.t;
    var _b:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var b_r:BArray88.t;
    var r:BArray88.t;
    var _r:BArray88.t;
    var b_param_1:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var param_7:W64.t;
    var param_8:BArray88.t;
    var trace_fpc_mul:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
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
    param_6 <- witness;
    param_8 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_fpc_mul <- [];
    trace_fpc_mul <-
    (trace_fpc_mul ++
    [(Assert,
     ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
       (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b__r <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_mul <- (trace_fpc_mul ++ tmp__trace);
    trace_fpc_mul <-
    (trace_fpc_mul ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_fpc_mul <- (trace_fpc_mul ++ tmp__trace);
    trace_fpc_mul <-
    (trace_fpc_mul ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM___mulm_ (param_3, b_param_1,
    param_4, (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray88.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_fpc_mul <- (trace_fpc_mul ++ tmp__trace);
    trace_fpc_mul <-
    (trace_fpc_mul ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    r <- result_1;
    rp <- _rp;
    param_7 <- rp;
    param_8 <- r;
    tmp__trace <@ h__BN___store_ (param_7, param_8,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_mul <- (trace_fpc_mul ++ tmp__trace);
    return (trace_fpc_mul);
  }
  proc fpc_sqr (rp:W64.t, ap:W64.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__a:BArray88.t;
    var b__r:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_r:BArray88.t;
    var r:BArray88.t;
    var _r:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var trace_fpc_sqr:trace;
    _a <- witness;
    _ctx <- witness;
    _r <- witness;
    a <- witness;
    b__a <- witness;
    b__r <- witness;
    b_a <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_r <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    trace_fpc_sqr <- [];
    trace_fpc_sqr <-
    (trace_fpc_sqr ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__r <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_sqr <- (trace_fpc_sqr ++ tmp__trace);
    trace_fpc_sqr <-
    (trace_fpc_sqr ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- a;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM___sqrm_ (param_1, b_param_0,
    param_2, (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_fpc_sqr <- (trace_fpc_sqr ++ tmp__trace);
    trace_fpc_sqr <-
    (trace_fpc_sqr ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    rp <- _rp;
    param_4 <- rp;
    param_5 <- r;
    tmp__trace <@ h__BN___store_ (param_4, param_5,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_sqr <- (trace_fpc_sqr ++ tmp__trace);
    return (trace_fpc_sqr);
  }
  proc fpc_exp (rp:W64.t, ap:W64.t, bp:W64.t, ctx:BArray360.t,
                b_ctx:BArray360.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
    var b__r:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_b:BArray88.t;
    var b:BArray88.t;
    var _b:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var b_r:BArray88.t;
    var r:BArray88.t;
    var _r:BArray88.t;
    var b_param_1:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var param_7:W64.t;
    var param_8:BArray88.t;
    var trace_fpc_exp:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
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
    param_6 <- witness;
    param_8 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_fpc_exp <- [];
    trace_fpc_exp <-
    (trace_fpc_exp ++
    [(Assert,
     ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
       (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b__r <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_exp <- (trace_fpc_exp ++ tmp__trace);
    trace_fpc_exp <-
    (trace_fpc_exp ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_fpc_exp <- (trace_fpc_exp ++ tmp__trace);
    trace_fpc_exp <-
    (trace_fpc_exp ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM__EXP___expm_ (param_3, b_param_1,
    param_4, (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray88.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_fpc_exp <- (trace_fpc_exp ++ tmp__trace);
    trace_fpc_exp <-
    (trace_fpc_exp ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    r <- result_1;
    rp <- _rp;
    param_7 <- rp;
    param_8 <- r;
    tmp__trace <@ h__BN___store_ (param_7, param_8,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_exp <- (trace_fpc_exp ++ tmp__trace);
    return (trace_fpc_exp);
  }
  proc fpc_expw (rp:W64.t, ap:W64.t, bp:W64.t, ctx:BArray360.t,
                 b_ctx:BArray360.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
    var b__r:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_b:BArray88.t;
    var b:BArray88.t;
    var _b:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var b_r:BArray88.t;
    var r:BArray88.t;
    var _r:BArray88.t;
    var b_param_1:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var param_7:W64.t;
    var param_8:BArray88.t;
    var trace_fpc_expw:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
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
    param_6 <- witness;
    param_8 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_fpc_expw <- [];
    trace_fpc_expw <-
    (trace_fpc_expw ++
    [(Assert,
     ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
       (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b__r <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_expw <- (trace_fpc_expw ++ tmp__trace);
    trace_fpc_expw <-
    (trace_fpc_expw ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_fpc_expw <- (trace_fpc_expw ++ tmp__trace);
    trace_fpc_expw <-
    (trace_fpc_expw ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM__EXP___expmW_ (param_3, b_param_1,
    param_4, (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray88.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_fpc_expw <- (trace_fpc_expw ++ tmp__trace);
    trace_fpc_expw <-
    (trace_fpc_expw ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    r <- result_1;
    rp <- _rp;
    param_7 <- rp;
    param_8 <- r;
    tmp__trace <@ h__BN___store_ (param_7, param_8,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_expw <- (trace_fpc_expw ++ tmp__trace);
    return (trace_fpc_expw);
  }
  proc fpc_exp_noct (rp:W64.t, ap:W64.t, bp:W64.t, ctx:BArray360.t,
                     b_ctx:BArray360.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
    var b__r:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_b:BArray88.t;
    var b:BArray88.t;
    var _b:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:W64.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var b_r:BArray88.t;
    var r:BArray88.t;
    var _r:BArray88.t;
    var b_param_1:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var param_7:W64.t;
    var param_8:BArray88.t;
    var trace_fpc_exp_noct:trace;
    _a <- witness;
    _b <- witness;
    _ctx <- witness;
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
    param_6 <- witness;
    param_8 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_fpc_exp_noct <- [];
    trace_fpc_exp_noct <-
    (trace_fpc_exp_noct ++
    [(Assert,
     ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
       (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b__r <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_exp_noct <- (trace_fpc_exp_noct ++ tmp__trace);
    trace_fpc_exp_noct <-
    (trace_fpc_exp_noct ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_fpc_exp_noct <- (trace_fpc_exp_noct ++ tmp__trace);
    trace_fpc_exp_noct <-
    (trace_fpc_exp_noct ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM__EXP___expm_noct_ (param_3,
    b_param_1, param_4, (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray88.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_fpc_exp_noct <- (trace_fpc_exp_noct ++ tmp__trace);
    trace_fpc_exp_noct <-
    (trace_fpc_exp_noct ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    r <- result_1;
    rp <- _rp;
    param_7 <- rp;
    param_8 <- r;
    tmp__trace <@ h__BN___store_ (param_7, param_8,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_exp_noct <- (trace_fpc_exp_noct ++ tmp__trace);
    return (trace_fpc_exp_noct);
  }
  proc fpc_inv (rp:W64.t, ap:W64.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__a:BArray88.t;
    var b__r:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_r:BArray88.t;
    var r:BArray88.t;
    var _r:BArray88.t;
    var b_param_0:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_4:W64.t;
    var param_5:BArray88.t;
    var trace_fpc_inv:trace;
    _a <- witness;
    _ctx <- witness;
    _r <- witness;
    a <- witness;
    b__a <- witness;
    b__r <- witness;
    b_a <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_r <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_5 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    trace_fpc_inv <- [];
    trace_fpc_inv <-
    (trace_fpc_inv ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__r <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_inv <- (trace_fpc_inv ++ tmp__trace);
    trace_fpc_inv <-
    (trace_fpc_inv ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- a;
    param_3 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM___invm_ (param_1, b_param_0,
    param_2, (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_fpc_inv <- (trace_fpc_inv ++ tmp__trace);
    trace_fpc_inv <-
    (trace_fpc_inv ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    rp <- _rp;
    param_4 <- rp;
    param_5 <- r;
    tmp__trace <@ h__BN___store_ (param_4, param_5,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_inv <- (trace_fpc_inv ++ tmp__trace);
    return (trace_fpc_inv);
  }
  proc fpc_toM (rp:W64.t, ap:W64.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__a:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:W64.t;
    var param_4:BArray88.t;
    var trace_fpc_toM:trace;
    _a <- witness;
    _ctx <- witness;
    a <- witness;
    b__a <- witness;
    b_a <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_fpc_toM <- [];
    trace_fpc_toM <-
    (trace_fpc_toM ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_toM <- (trace_fpc_toM ++ tmp__trace);
    trace_fpc_toM <-
    (trace_fpc_toM ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    ctx <- _ctx;
    param_1 <- a;
    param_2 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM___toM_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_fpc_toM <- (trace_fpc_toM ++ tmp__trace);
    trace_fpc_toM <-
    (trace_fpc_toM ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    rp <- _rp;
    param_3 <- rp;
    param_4 <- a;
    tmp__trace <@ h__BN___store_ (param_3, param_4,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_toM <- (trace_fpc_toM ++ tmp__trace);
    return (trace_fpc_toM);
  }
  proc fpc_fromM (rp:W64.t, ap:W64.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__a:BArray88.t;
    var _rp:W64.t;
    var _ctx:BArray360.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:W64.t;
    var param_4:BArray88.t;
    var trace_fpc_fromM:trace;
    _a <- witness;
    _ctx <- witness;
    a <- witness;
    b__a <- witness;
    b_a <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_fpc_fromM <- [];
    trace_fpc_fromM <-
    (trace_fpc_fromM ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    _rp <- rp;
    _ctx <- ctx;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_fpc_fromM <- (trace_fpc_fromM ++ tmp__trace);
    trace_fpc_fromM <-
    (trace_fpc_fromM ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    ctx <- _ctx;
    param_1 <- a;
    param_2 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM___fromM_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_fpc_fromM <- (trace_fpc_fromM ++ tmp__trace);
    trace_fpc_fromM <-
    (trace_fpc_fromM ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    rp <- _rp;
    param_3 <- rp;
    param_4 <- a;
    tmp__trace <@ h__BN___store_ (param_3, param_4,
    (BArray88.init_arr (W8.of_int 255)));
    trace_fpc_fromM <- (trace_fpc_fromM ++ tmp__trace);
    return (trace_fpc_fromM);
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

op uTIL____addacc3x2_spec _a _b_a _x _y _k =
   hoare [M.uTIL____addacc3x2 :
   (((_k = k) /\ ((_y = y) /\ ((_x = x) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   (BArray24.is_init _b_a 0 24)) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__BN____load_spec _a _b_a _ap =
   hoare [M.h__BN____load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN___load_spec _a _b_a _ap =
   hoare [M.h__BN___load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN___load__spec _a _b_a _ap =
   hoare [M.h__BN___load_ :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN____store_spec _ap _a _b_a =
   hoare [M.h__BN____store :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
   (BArray88.is_init _b_a 0 (8 * 11))))) ==> (true /\ (valid res))].

op h__BN___store__spec _ap _a _b_a =
   hoare [M.h__BN___store_ :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
   (BArray88.is_init _b_a 0 (8 * 11))))) ==> (true /\ (valid res))].

op h__BN____mov_spec _r _b_r _a _b_a =
   hoare [M.h__BN____mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN___mov_spec _r _b_r _a _b_a =
   hoare [M.h__BN___mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN___mov__spec _r _b_r _a _b_a =
   hoare [M.h__BN___mov_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN____cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN____cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__BN___cmov_spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__BN___cmov__spec _a _b_a _cond _b _b_b =
   hoare [M.h__BN___cmov_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__BN____cswap_mask_spec _x _b_x _y _b_y _mask =
   hoare [M.h__BN____cswap_mask :
   (((_mask = mask) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray88.is_init _b_y 0 88) /\ (BArray88.is_init _b_x 0 88))) ==>
   (((BArray88.is_init res.`4 0 88) /\ (BArray88.is_init res.`2 0 88)) /\
   (valid res.`5))].

op h__BN___cswap_mask_spec _x _b_x _y _b_y _mask =
   hoare [M.h__BN___cswap_mask :
   (((_mask = mask) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray88.is_init _b_y 0 88) /\ (BArray88.is_init _b_x 0 88))) ==>
   (((BArray88.is_init res.`4 0 88) /\ (BArray88.is_init res.`2 0 88)) /\
   (valid res.`5))].

op h__BN___cswap_mask__spec _x _b_x _y _b_y _mask =
   hoare [M.h__BN___cswap_mask_ :
   (((_mask = mask) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray88.is_init _b_y 0 88) /\ (BArray88.is_init _b_x 0 88))) ==>
   (((BArray88.is_init res.`4 0 88) /\ (BArray88.is_init res.`2 0 88)) /\
   (valid res.`5))].

op h__BN____fill_spec _a _b_a _x =
   hoare [M.h__BN____fill :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN___fill__spec _a _b_a _x =
   hoare [M.h__BN___fill_ :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN___set0__spec _a _b_a =
   hoare [M.h__BN___set0_ :
   (((_b_a = b_a) /\ (_a = a)) /\ true) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__BN____addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN___addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN___addc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN___addU__spec _a _b_a _b _b_b =
   hoare [M.h__BN___addU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN____addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN____addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11))) /\
   (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___addc1_spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1 :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11))) /\
   (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___addc1__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc1_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   (((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11))) /\
   (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___add__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__BN___add_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN____subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN____subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN___subc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN___subc1U__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN___subU__spec _a _b_a _b _b_b =
   hoare [M.h__BN___subU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`3 0 88) /\ (valid res.`4))].

op h__BN____negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN____negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___negc1_spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1 :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___negc1__spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc1_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   ((BArray88.is_init _b_r 0 8) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___neg__spec _r _b_r _a _b_a =
   hoare [M.h__BN___neg_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray88.is_init res.`3 0 (8 * 11)) /\ (valid res.`4))].

op h__BN___caddU__spec _x _b_x _cf _y _b_y =
   hoare [M.h__BN___caddU_ :
   (((_b_y = b_y) /\
    ((_y = y) /\ ((_cf = cf) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray88.is_init _b_y 0 88) /\ (BArray88.is_init _b_x 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit =
   hoare [M.h__BN___cminusP_ :
   (((_lastbit = lastbit) /\
    ((_b_mP = b_mP) /\ ((_mP = mP) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray88.is_init _b_mP 0 88) /\ (BArray88.is_init _b_x 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__MUL__UNR____muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR____muln_innerloop :
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

op h__MUL__UNR____ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR____ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__UNR___ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR___ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__UNR___ps_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__UNR___ps_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__UNR____sqrn_innerloop_spec _x _b_x _k _istart _iend _a _b_a =
   hoare [M.h__MUL__UNR____sqrn_innerloop :
   (((_b_a = b_a) /\
    ((_a = a) /\
    ((_iend = iend) /\
    ((_istart = istart) /\ ((_k = k) /\ ((_b_x = b_x) /\ (_x = x))))))) /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   (true /\
   ((((((0 <= _istart) /\ (_iend <= 11)) /\ (0 <= (_k - (_iend - 1)))) /\
     ((_k - _istart) < 11)) /\
    (BArray24.is_init _b_x 0 24)) /\
   (BArray88.is_init _b_a 0 (8 * 11)))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__MUL__UNR____ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__UNR____ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__UNR___ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__UNR___ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__UNR___ps_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__UNR___ps_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__UNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__UNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray176.is_init _b__P_mP 0 (16 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__MUL__LOOP____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__LOOP____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray88.is_init _b_b 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (8 * (11 + 1))) /\ (valid res.`3))].

op h__MUL__LOOP____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__LOOP____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 11)) /\
    (BArray176.is_init _b_r 0 (8 * ((W64.to_uint _k) + 11)))) /\
   (BArray88.is_init _b_b 0 (8 * 11))))))) ==>
   ((true /\
    (BArray176.is_init res.`2 0 (8 * (((W64.to_uint _k) + 11) + 1)))) /\
   (valid res.`3))].

op h__MUL__LOOP___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__LOOP___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__LOOP___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__LOOP___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__LOOP___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__LOOP___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__LOOP___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__LOOP___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__LOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__LOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray176.is_init _b__P_mP 0 (16 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XUNR____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray88.is_init _b_b 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (8 * (11 + 1))) /\ (valid res.`3))].

op h__MUL__XUNR____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XUNR____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 11)) /\ (BArray176.is_init _b_r 0 (8 * (_k + 11)))) /\
   (BArray88.is_init _b_b 0 (8 * 11))))))) ==>
   ((true /\ (BArray176.is_init res.`2 0 (8 * ((_k + 11) + 1)))) /\
   (valid res.`3))].

op h__MUL__XUNR___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XUNR___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XUNR___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_row0_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_row0 :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   ((2 <= 11) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 8 (8 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_rowacc_spec _i _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_rowacc :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (11 - 1))) /\
    (BArray176.is_init _b_r 8 (8 * ((_i + 11) - 1)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))))))) ==>
   ((true /\ (BArray176.is_init res.`2 8 (8 * (_i + 11)))) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_diag_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_diag :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (((2 <= 11) /\ (BArray176.is_init _b_r 8 (8 * ((2 * 11) - 2)))) /\
   (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XUNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XUNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray176.is_init _b__P_mP 0 (16 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__MUL__XLOOP____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XLOOP____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray88.is_init _b_b 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (8 * (11 + 1))) /\ (valid res.`3))].

op h__MUL__XLOOP____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XLOOP____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 11)) /\
    (BArray176.is_init _b_r 0 (8 * ((W64.to_uint _k) + 11)))) /\
   (BArray88.is_init _b_b 0 (8 * 11))))))) ==>
   ((true /\
    (BArray176.is_init res.`2 0 (8 * (((W64.to_uint _k) + 11) + 1)))) /\
   (valid res.`3))].

op h__MUL__XLOOP___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XLOOP___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XLOOP___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XLOOP___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XLOOP___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XLOOP___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XLOOP___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XLOOP___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XLOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XLOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray176.is_init _b__P_mP 0 (16 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__MUL__XREG____mulr_row0_spec _a _b _b_b =
   hoare [M.h__MUL__XREG____mulr_row0 :
   (((_b_b = b_b) /\ ((_b = b) /\ (_a = a))) /\
   (BArray88.is_init _b_b 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (8 * (11 + 1))) /\ (valid res.`3))].

op h__MUL__XREG____mulr_rowk_spec _k _t _b_t _a _b _b_b =
   hoare [M.h__MUL__XREG____mulr_rowk :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 11)) /\ (BArray176.is_init _b_t 0 (8 * (_k + 11)))) /\
   (BArray88.is_init _b_b 0 (8 * 11))))))) ==>
   ((true /\ (BArray176.is_init res.`2 0 (8 * ((_k + 11) + 1)))) /\
   (valid res.`3))].

op h__MUL__XREG___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XREG___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XREG___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XREG___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XREG____sqrr_row0_spec _a _b_a =
   hoare [M.h__MUL__XREG____sqrr_row0 :
   (((_b_a = b_a) /\ (_a = a)) /\
   ((2 <= 11) /\ (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 8 (8 * 11)) /\ (valid res.`3))].

op h__MUL__XREG____sqrr_rowi_spec _i _t _b_t _a _b_a =
   hoare [M.h__MUL__XREG____sqrr_rowi :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (11 - 1))) /\
    (BArray176.is_init _b_t 8 (8 * ((_i + 11) - 1)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))))))) ==>
   ((true /\ (BArray176.is_init res.`2 8 (8 * (_i + 11)))) /\ (valid res.`3))].

op h__MUL__XREG____sqrr_diag_spec _r _b_r _t _b_t _a _b_a =
   hoare [M.h__MUL__XREG____sqrr_diag :
   (((_b_a = b_a) /\
    ((_a = a) /\ ((_b_t = b_t) /\ ((_t = t) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((((2 <= 11) /\ (BArray176.is_init _b_r 8 (8 * ((2 * 11) - 10)))) /\
    (BArray176.is_init _b_t 8 (8 * ((2 * 11) - 2)))) /\
   (BArray88.is_init _b_a 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XREG___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XREG___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XREG___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XREG___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL__XREG____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XREG____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray176.is_init _b__P_mP 0 (16 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__MUL___muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL___muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL___sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL___sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__MUL____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray176.is_init _b__P_mP 0 (16 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FPM__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__FPM__fun_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__FPM__fun_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray88.is_init _b_a 0 (8 * 11))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__FPM___redM_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___redM :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___redM__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___redM_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___fromM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___fromM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray360.is_init _b_ctx 0 360) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___addm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___addm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx (8 * 11) (8 * 11)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___addmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___addmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM___submU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___submU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM___mulm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___mulm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM___sqrm__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___sqrm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___sqrmU__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___sqrmU_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray360.is_init _b_ctx 0 360) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM__fun_mulU_spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__fun_mulU :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM__fun_sqrU_spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM__fun_sqrU :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray360.is_init _b_ctx 0 360) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM__EXP___expm_noct_spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXP___expm_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\
   ((BArray88.is_init _b_a 0 88) /\ (BArray88.is_init _b_r 0 88))))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM__EXP___expm_noct__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXP___expm_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM__EXP___expm_spec _x0 _b_x0 _x1 _b_x1 _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXP___expm :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_x1 = b_x1) /\ ((_x1 = x1) /\ ((_b_x0 = b_x0) /\ (_x0 = x0)))))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\
   ((BArray88.is_init _b_x1 0 88) /\ (BArray88.is_init _b_x0 0 88))))) ==>
   (((BArray88.is_init res.`4 0 88) /\ (BArray88.is_init res.`2 0 88)) /\
   (valid res.`5))].

op h__FPM__EXP___expm__spec _x0 _b_x0 _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXP___expm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_x0 = b_x0) /\ (_x0 = x0)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM__EXP____tblsel_spec _r _b_r _tbl _b_tbl _idx =
   hoare [M.h__FPM__EXP____tblsel :
   (((_idx = idx) /\
    ((_b_tbl = b_tbl) /\ ((_tbl = tbl) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray1408.is_init _b_tbl 0 (128 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM__EXP___expmW_spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXP___expmW :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM__EXP___expmW__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM__EXP___expmW_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM____Pm2_spec _r _b_r _ctx _b_ctx =
   hoare [M.h__FPM____Pm2 :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___invm__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___invm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FPM___toM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___toM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray360.is_init _b_ctx 0 360) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__FPM___ctx_init__spec _ctx _b_ctx _p _b_P =
   hoare [M.h__FPM___ctx_init_ :
   (((_b_P = b_P) /\ ((_p = p) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray88.is_init _b_P 0 (8 * 11))) ==>
   ((BArray360.is_init res.`2 0 (8 * 45)) /\ (valid res.`3))].

op fpc_ctx_init_spec _ctx _b_ctx _pp =
   hoare [M.fpc_ctx_init :
   (((_pp = pp) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _pp) (8 * 11)))) ==>
   ((BArray360.is_init res.`2 0 (8 * 45)) /\ (valid res.`3))].

op fpc_add_spec _rp _ap _bp _ctx _b_ctx =
   hoare [M.fpc_add :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))))) /\
   (true /\
   (true /\
   (true /\
   ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))))))) ==> (true /\ (valid res))].

op fpc_sub_spec _rp _ap _bp _ctx _b_ctx =
   hoare [M.fpc_sub :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))))) /\
   (true /\
   (true /\
   (true /\
   ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))))))) ==> (true /\ (valid res))].

op fpc_mul_spec _rp _ap _bp _ctx _b_ctx =
   hoare [M.fpc_mul :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))))) /\
   (true /\
   (true /\
   (true /\
   ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))))))) ==> (true /\ (valid res))].

op fpc_sqr_spec _rp _ap _ctx _b_ctx =
   hoare [M.fpc_sqr :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_ap = ap) /\ (_rp = rp)))) /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))))) ==> (true /\ (valid res))].

op fpc_exp_spec _rp _ap _bp _ctx _b_ctx =
   hoare [M.fpc_exp :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))))) /\
   (true /\
   (true /\
   (true /\
   ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))))))) ==> (true /\ (valid res))].

op fpc_expw_spec _rp _ap _bp _ctx _b_ctx =
   hoare [M.fpc_expw :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))))) /\
   (true /\
   (true /\
   (true /\
   ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))))))) ==> (true /\ (valid res))].

op fpc_exp_noct_spec _rp _ap _bp _ctx _b_ctx =
   hoare [M.fpc_exp_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\ ((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))))) /\
   (true /\
   (true /\
   (true /\
   ((((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45))))))) ==> (true /\ (valid res))].

op fpc_inv_spec _rp _ap _ctx _b_ctx =
   hoare [M.fpc_inv :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_ap = ap) /\ (_rp = rp)))) /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))))) ==> (true /\ (valid res))].

op fpc_toM_spec _rp _ap _ctx _b_ctx =
   hoare [M.fpc_toM :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_ap = ap) /\ (_rp = rp)))) /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))))) ==> (true /\ (valid res))].

op fpc_fromM_spec _rp _ap _ctx _b_ctx =
   hoare [M.fpc_fromM :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_ap = ap) /\ (_rp = rp)))) /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))))) ==> (true /\ (valid res))].
