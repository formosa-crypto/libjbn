require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array3 Array11 Array22 Array24 Array88 Array176 BArray24 BArray88 BArray176
SBArray176_88.

module M = {
  var tmp__trace : trace
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
}.

(* The post and trace are valid. *)

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
