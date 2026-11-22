require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array7 Array14 Array56 Array112 BArray56 BArray112 SBArray112_56.

module M = {
  var tmp__trace : trace
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
  proc h__BN___cminusP_ (x:BArray56.t, b_x:BArray56.t, mP:BArray56.t,
                         b_mP:BArray56.t, lastbit:W64.t) : BArray56.t *
                                                           BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux:bool;
    var b__tmp:BArray56.t;
    var b_tmp:BArray56.t;
    var tmp:BArray56.t;
    var _tmp:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var _cf:bool;
    var param_2:BArray56.t;
    var param_3:bool;
    var param_4:BArray56.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
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
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray56.is_init b_mP 0 56))]);
    b__tmp <- (BArray56.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- x;
    param_1 <- mP;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___add_ (param, b_param, 
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    _cf <- result;
    tmp <- result_0;
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) _cf);
    ( _1, _cf,  _2,  _3,  _4,  _5) <- (NEG_64 lastbit);
    param_2 <- x;
    param_3 <- _cf;
    param_4 <- tmp;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cmov_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray56.init_arr (W8.of_int 255)));
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___cminusP_ <- (trace_h__BN___cminusP_ ++ tmp__trace);
    trace_h__BN___cminusP_ <-
    (trace_h__BN___cminusP_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    x <- result_1;
    b_x <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__BN___cminusP_);
  }
  proc h__MUL__XUNR____mul1 (r:BArray112.t, b_r:BArray112.t, a:W64.t,
                             b:BArray56.t, b_b:BArray56.t) : BArray112.t *
                                                             BArray112.t *
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
    (trace_h__MUL__XUNR____mul1 ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray56.get64 b 0));
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 lo);
    i <- 1;
    while ((i < 7)) {
      t <- hi;
      trace_h__MUL__XUNR____mul1 <-
      (trace_h__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 a (BArray56.get64 b i));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XUNR____mul1 <-
      (trace_h__MUL__XUNR____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XUNR____mul1 <-
    (trace_h__MUL__XUNR____mul1 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    b_r <- (BArray112.set64d b_r (7 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 7 hi);
    return (r, b_r, trace_h__MUL__XUNR____mul1);
  }
  proc h__MUL__XUNR____mul1acc (k:int, r:BArray112.t, b_r:BArray112.t,
                                a:W64.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
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
     ((((1 <= k) /\ (k < 7)) /\ (BArray112.is_init b_r 0 (8 * (k + 7)))) /\
     (BArray56.is_init b_b 0 56)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    (hi, lo) <- (MULX_64 a (BArray56.get64 b 0));
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, (BArray112.is_init b_r (k * 8) 8))]);
    t <- (BArray112.get64 r k);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
    b_r <- (BArray112.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r k t);
    i <- 1;
    while ((i < 7)) {
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, (BArray112.is_init b_r ((k + i) * 8) 8))]);
      t <- (BArray112.get64 r (k + i));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 a (BArray56.get64 b i));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____mul1acc <-
      (trace_h__MUL__XUNR____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r ((k + i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r (k + i) t);
      i <- (i + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____mul1acc <-
    (trace_h__MUL__XUNR____mul1acc ++
    [(Assert, ((0 <= ((k + 7) * 8)) /\ ((((k + 7) * 8) + 8) <= 112)))]);
    b_r <-
    (BArray112.set64d b_r ((k + 7) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r (k + 7) hi);
    return (r, b_r, trace_h__MUL__XUNR____mul1acc);
  }
  proc h__MUL__XUNR___os_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                               b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux_2:BArray112.t;
    var ai:W64.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:W64.t;
    var param_1:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var k:int;
    var param_2:int;
    var b_param_0:BArray112.t;
    var param_3:BArray112.t;
    var param_4:W64.t;
    var param_5:BArray56.t;
    var result_0:BArray112.t;
    var b_result_0:BArray112.t;
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
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    ai <- (BArray56.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR____mul1 (param, b_param,
    param_0, param_1, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++ tmp__trace);
    trace_h__MUL__XUNR___os_muln <-
    (trace_h__MUL__XUNR___os_muln ++
    [(Assert, (BArray112.is_init b_result 0 64))]);
    b_r <- b_result;
    r <- result;
    k <- 1;
    while ((k < 7)) {
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a k);
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL__XUNR____mul1acc (param_2,
      param_3, b_param_0, param_4, param_5,
      (BArray56.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++ tmp__trace);
      trace_h__MUL__XUNR___os_muln <-
      (trace_h__MUL__XUNR___os_muln ++
      [(Assert, (BArray112.is_init b_result_0 0 (8 * ((param_2 + 7) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + 1);
    }
    return (r, b_r, trace_h__MUL__XUNR___os_muln);
  }
  proc h__MUL__XUNR___os_muln_ (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                                b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
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
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR___os_muln (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++ tmp__trace);
    trace_h__MUL__XUNR___os_muln_ <-
    (trace_h__MUL__XUNR___os_muln_ ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    r <- r;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR___os_muln_);
  }
  proc h__MUL__XUNR____sqr_row0 (r:BArray112.t, b_r:BArray112.t,
                                 a:BArray56.t, b_a:BArray56.t) : BArray112.t *
                                                                 BArray112.t *
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
    [(Assert, ((2 <= 7) /\ (BArray56.is_init b_a 0 56)))]);
    ( _0, cf,  _1,  _2,  _3, _zero) <- (set0_64);
    ai <- (BArray56.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray56.get64 a 1));
    b_r <- (BArray112.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 1 lo);
    j <- 2;
    while ((j < 7)) {
      t <- hi;
      trace_h__MUL__XUNR____sqr_row0 <-
      (trace_h__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 ai (BArray56.get64 a j));
      (cf, t) <- (ADCX_64 t lo cf);
      trace_h__MUL__XUNR____sqr_row0 <-
      (trace_h__MUL__XUNR____sqr_row0 ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (j * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r j t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    trace_h__MUL__XUNR____sqr_row0 <-
    (trace_h__MUL__XUNR____sqr_row0 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    b_r <- (BArray112.set64d b_r (7 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 7 hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_row0);
  }
  proc h__MUL__XUNR____sqr_rowacc (i:int, r:BArray112.t, b_r:BArray112.t,
                                   a:BArray56.t, b_a:BArray56.t) : BArray112.t *
                                                                   BArray112.t *
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
     ((((1 <= i) /\ (i < (7 - 1))) /\
      (BArray112.is_init b_r 8 (8 * ((i + 7) - 1)))) /\
     (BArray56.is_init b_a 0 56)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
    ai <- (BArray56.get64 a i);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 56)))]);
    (hi, lo) <- (MULX_64 ai (BArray56.get64 a (i + 1)));
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 112)))]);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, (BArray112.is_init b_r (((2 * i) + 1) * 8) 8))]);
    t <- (BArray112.get64 r ((2 * i) + 1));
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert,
     ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 112)))]);
    b_r <-
    (BArray112.set64d b_r (((2 * i) + 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r ((2 * i) + 1) t);
    j <- (i + 2);
    while ((j < 7)) {
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 112)))]);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, (BArray112.is_init b_r ((i + j) * 8) 8))]);
      t <- (BArray112.get64 r (i + j));
      (cf, t) <- (ADCX_64 t hi cf);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 ai (BArray56.get64 a j));
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____sqr_rowacc <-
      (trace_h__MUL__XUNR____sqr_rowacc ++
      [(Assert, ((0 <= ((i + j) * 8)) /\ ((((i + j) * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r ((i + j) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r (i + j) t);
      j <- (j + 1);
    }
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____sqr_rowacc <-
    (trace_h__MUL__XUNR____sqr_rowacc ++
    [(Assert, ((0 <= ((i + 7) * 8)) /\ ((((i + 7) * 8) + 8) <= 112)))]);
    b_r <-
    (BArray112.set64d b_r ((i + 7) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r (i + 7) hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_rowacc);
  }
  proc h__MUL__XUNR____sqr_diag (r:BArray112.t, b_r:BArray112.t,
                                 a:BArray56.t, b_a:BArray56.t) : BArray112.t *
                                                                 BArray112.t *
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
     (((2 <= 7) /\ (BArray112.is_init b_r 8 96)) /\
     (BArray56.is_init b_a 0 56)))]);
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    ai <- (BArray56.get64 a 0);
    (hi, lo) <- (MULX_64 ai (BArray56.get64 a 0));
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 lo);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray112.is_init b_r 8 8))]);
    t <- (BArray112.get64 r 1);
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t hi of_0);
    b_r <- (BArray112.set64d b_r 8 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 1 t);
    inc <- (7 - 1);
    i <- 1;
    while ((i < inc)) {
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a i);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 ai (BArray56.get64 a i));
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 112)))]);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray112.is_init b_r ((2 * i) * 8) 8))]);
      t <- (BArray112.get64 r (2 * i));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t lo of_0);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, ((0 <= ((2 * i) * 8)) /\ ((((2 * i) * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r ((2 * i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r (2 * i) t);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 112)))]);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert, (BArray112.is_init b_r (((2 * i) + 1) * 8) 8))]);
      t <- (BArray112.get64 r ((2 * i) + 1));
      (cf, t) <- (ADCX_64 t t cf);
      (of_0, t) <- (ADOX_64 t hi of_0);
      trace_h__MUL__XUNR____sqr_diag <-
      (trace_h__MUL__XUNR____sqr_diag ++
      [(Assert,
       ((0 <= (((2 * i) + 1) * 8)) /\ (((((2 * i) + 1) * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (((2 * i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r ((2 * i) + 1) t);
      i <- (i + 1);
    }
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
    ai <- (BArray56.get64 a (7 - 1));
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
    (hi, lo) <- (MULX_64 ai (BArray56.get64 a (7 - 1)));
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 7) - 2) * 8)) /\ (((((2 * 7) - 2) * 8) + 8) <= 112)))]);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert, (BArray112.is_init b_r (((2 * 7) - 2) * 8) 8))]);
    t <- (BArray112.get64 r ((2 * 7) - 2));
    (cf, t) <- (ADCX_64 t t cf);
    (of_0, t) <- (ADOX_64 t lo of_0);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 7) - 2) * 8)) /\ (((((2 * 7) - 2) * 8) + 8) <= 112)))]);
    b_r <-
    (BArray112.set64d b_r (((2 * 7) - 2) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r ((2 * 7) - 2) t);
    (cf, hi) <- (ADCX_64 hi _zero cf);
    (of_0, hi) <- (ADOX_64 hi _zero of_0);
    trace_h__MUL__XUNR____sqr_diag <-
    (trace_h__MUL__XUNR____sqr_diag ++
    [(Assert,
     ((0 <= (((2 * 7) - 1) * 8)) /\ (((((2 * 7) - 1) * 8) + 8) <= 112)))]);
    b_r <-
    (BArray112.set64d b_r (((2 * 7) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r ((2 * 7) - 1) hi);
    return (r, b_r, trace_h__MUL__XUNR____sqr_diag);
  }
  proc h__MUL__XUNR___os_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                               b_a:BArray56.t) : BArray112.t * BArray112.t *
                                                 trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var aux_1:BArray112.t;
    var aux_2:BArray112.t;
    var aux_3:BArray112.t;
    var aux_4:BArray112.t;
    var inc:int;
    var ai:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var i:int;
    var param_1:int;
    var b_param_0:BArray112.t;
    var param_2:BArray112.t;
    var param_3:BArray56.t;
    var result_0:BArray112.t;
    var b_result_0:BArray112.t;
    var b_param_1:BArray112.t;
    var param_4:BArray112.t;
    var param_5:BArray56.t;
    var result_1:BArray112.t;
    var b_result_1:BArray112.t;
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
    (trace_h__MUL__XUNR___os_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    if ((7 = 1)) {
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a 0);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 ai (BArray56.get64 a 0));
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (0 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r 0 lo);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, ((0 <= (1 * 8)) /\ (((1 * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (1 * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r 1 hi);
    } else {
      b_param <- b_r;
      param <- r;
      param_0 <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL__XUNR____sqr_row0 (param, b_param,
      param_0, (BArray56.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray112.is_init b_result 8 56))]);
      b_r <- b_result;
      r <- result;
      inc <- (7 - 1);
      i <- 1;
      while ((i < inc)) {
        param_1 <- i;
        b_param_0 <- b_r;
        param_2 <- r;
        param_3 <- a;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__XUNR____sqr_rowacc (param_1,
        param_2, b_param_0, param_3, (BArray56.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL__XUNR___os_sqrn <-
        (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
        trace_h__MUL__XUNR___os_sqrn <-
        (trace_h__MUL__XUNR___os_sqrn ++
        [(Assert, (BArray112.is_init b_result_0 8 (8 * (param_1 + 7))))]);
        b_r <- b_result_0;
        r <- result_0;
        i <- (i + 1);
      }
      b_param_1 <- b_r;
      param_4 <- r;
      param_5 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL__XUNR____sqr_diag (param_4,
      b_param_1, param_5, (BArray56.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++ tmp__trace);
      trace_h__MUL__XUNR___os_sqrn <-
      (trace_h__MUL__XUNR___os_sqrn ++
      [(Assert, (BArray112.is_init b_result_1 0 112))]);
      b_r <- (BArray112.init_arr (W8.of_int 255));
      r <- result_1;
    }
    return (r, b_r, trace_h__MUL__XUNR___os_sqrn);
  }
  proc h__MUL__XUNR___os_sqrn_ (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                                b_a:BArray56.t) : BArray112.t * BArray112.t *
                                                  trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var trace_h__MUL__XUNR___os_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL__XUNR___os_sqrn_ <- [];
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray56.is_init b_a 0 56))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL__XUNR___os_sqrn (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++ tmp__trace);
    trace_h__MUL__XUNR___os_sqrn_ <-
    (trace_h__MUL__XUNR___os_sqrn_ ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    r <- r;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR___os_sqrn_);
  }
  proc h__MUL__XUNR____mont_redM (r:BArray56.t, b_r:BArray56.t,
                                  a:BArray112.t, b_a:BArray112.t,
                                  _P_mP:BArray112.t, b__P_mP:BArray112.t,
                                  _U0:W64.t) : BArray56.t * BArray56.t *
                                               trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
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
    var b_mP:BArray56.t;
    var mP:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var b_param_0:BArray56.t;
    var param_0:BArray56.t;
    var param_1:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b__P_mP 0 112)))]);
    c <- (W64.of_int 0);
    w0 <- (BArray112.get64 a 0);
    k <- 0;
    while ((k < 7)) {
      m <- w0;
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray112.get64 _P_mP 0));
      (of_0, w0) <- (ADOX_64 w0 lo of_0);
      i <- 1;
      while ((i < 7)) {
        if ((k = 0)) {
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
          t <- (BArray112.get64 a i);
        } else {
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
          trace_h__MUL__XUNR____mont_redM <-
          (trace_h__MUL__XUNR____mont_redM ++
          [(Assert, (BArray56.is_init b_r (i * 8) 8))]);
          t <- (BArray56.get64 r i);
        }
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
        (hi, lo) <- (MULX_64 m (BArray112.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 56)))]);
        b_r <-
        (BArray56.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615));
        r <- (BArray56.set64 r (i - 1) t);
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
        [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
        (cf, hi) <- (adc_64 hi (BArray112.get64 a 7) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__MUL__XUNR____mont_redM <-
        (trace_h__MUL__XUNR____mont_redM ++
        [(Assert, ((0 <= ((k + 7) * 8)) /\ ((((k + 7) * 8) + 8) <= 112)))]);
        (cf, hi) <- (adc_64 hi (BArray112.get64 a (k + 7)) cf);
      }
      trace_h__MUL__XUNR____mont_redM <-
      (trace_h__MUL__XUNR____mont_redM ++
      [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
      b_r <-
      (BArray56.set64d b_r ((7 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r (7 - 1) hi);
      if ((7 = 1)) {
        w0 <- hi;
      } else {
        
      }
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    trace_h__MUL__XUNR____mont_redM <-
    (trace_h__MUL__XUNR____mont_redM ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_mP <- (SBArray112_56.get_sub64 b__P_mP 7);
    mP <- (SBArray112_56.get_sub64 _P_mP 7);
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
    [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XUNR____mont_redM);
  }
}.

(* The post and trace are valid. *)

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

op h__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit =
   hoare [M.h__BN___cminusP_ :
   (((_lastbit = lastbit) /\
    ((_b_mP = b_mP) /\ ((_mP = mP) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_mP 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__MUL__XUNR____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XUNR____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray56.is_init _b_b 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (8 * (7 + 1))) /\ (valid res.`3))].

op h__MUL__XUNR____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL__XUNR____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 7)) /\ (BArray112.is_init _b_r 0 (8 * (_k + 7)))) /\
   (BArray56.is_init _b_b 0 (8 * 7))))))) ==>
   ((true /\ (BArray112.is_init res.`2 0 (8 * ((_k + 7) + 1)))) /\
   (valid res.`3))].

op h__MUL__XUNR___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XUNR___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR___os_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL__XUNR___os_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_row0_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_row0 :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   ((2 <= 7) /\ (BArray56.is_init _b_a 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 8 (8 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_rowacc_spec _i _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_rowacc :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_i = i))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _i) /\ (_i < (7 - 1))) /\
    (BArray112.is_init _b_r 8 (8 * ((_i + 7) - 1)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))))))) ==>
   ((true /\ (BArray112.is_init res.`2 8 (8 * (_i + 7)))) /\ (valid res.`3))].

op h__MUL__XUNR____sqr_diag_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR____sqr_diag :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (((2 <= 7) /\ (BArray112.is_init _b_r 8 (8 * ((2 * 7) - 2)))) /\
   (BArray56.is_init _b_a 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR___os_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL__XUNR___os_sqrn_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XUNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].
