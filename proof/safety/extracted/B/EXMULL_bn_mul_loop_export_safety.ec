require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import Array7 Array14 Array56 Array112 BArray56 BArray112.

module M = {
  var tmp__trace : trace
  proc h__BN____load (a:BArray56.t, b_a:BArray56.t, ap:W64.t) : BArray56.t *
                                                                BArray56.t *
                                                                trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____load:trace;
    trace_h__BN____load <- [];
    trace_h__BN____load <-
    (trace_h__BN____load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_a <- (BArray56.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray56.set64 a i t);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____load);
  }
  proc h__BN___load (a:BArray56.t, b_a:BArray56.t, ap:W64.t) : BArray56.t *
                                                               BArray56.t *
                                                               trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___load:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load <- [];
    trace_h__BN___load <-
    (trace_h__BN___load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)))]);
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN____load (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___load <- (trace_h__BN___load ++ tmp__trace);
    trace_h__BN___load <-
    (trace_h__BN___load ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load);
  }
  proc h__BN___load_ (a:BArray56.t, b_a:BArray56.t, ap:W64.t) : BArray56.t *
                                                                BArray56.t *
                                                                trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___load_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load_ <- [];
    trace_h__BN___load_ <-
    (trace_h__BN___load_ ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)))]);
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
    (trace_h__BN___load_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load_);
  }
  proc h__MUL____mul1 (r:BArray112.t, b_r:BArray112.t, a:W64.t, b:BArray56.t,
                       b_b:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var lo:W64.t;
    var hi:W64.t;
    var c:W64.t;
    var i:int;
    var cf:bool;
    var  _0:bool;
    var trace_h__MUL____mul1:trace;
    trace_h__MUL____mul1 <- [];
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    lo <- (BArray56.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 lo);
    c <- hi;
    i <- 1;
    while ((i < 7)) {
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      lo <- (BArray56.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      (cf, lo) <- (adc_64 lo c false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    b_r <- (BArray112.set64d b_r (7 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 7 c);
    return (r, b_r, trace_h__MUL____mul1);
  }
  proc h__MUL____mul1acc (k:W64.t, r:BArray112.t, b_r:BArray112.t, a:W64.t,
                          b:BArray56.t, b_b:BArray56.t) : BArray112.t *
                                                          BArray112.t * trace = {
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
    var trace_h__MUL____mul1acc:trace;
    trace_h__MUL____mul1acc <- [];
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert,
     ((((1 <= (W64.to_uint k)) /\ ((W64.to_uint k) < 7)) /\
      (BArray112.is_init b_r 0 (8 * ((W64.to_uint k) + 7)))) /\
     (BArray56.is_init b_b 0 56)))]);
    lo <- (BArray56.get64 b 0);
    (hi, lo) <- (mulu_64 lo a);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 112)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 112)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray112.is_init b_r ((W64.to_uint k) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r ((W64.to_uint k) * 8)
    (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (adc_64 (BArray112.get64 r (W64.to_uint k)) lo false);
    cf <- aux;
    r <- (BArray112.set64 r (W64.to_uint k) aux_0);
    ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
    c <- hi;
    i <- 1;
    while ((i < 7)) {
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      lo <- (BArray56.get64 b i);
      (hi, lo) <- (mulu_64 lo a);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 112)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert,
       (BArray112.is_init b_r ((W64.to_uint (k + (W64.of_int i))) * 8) 8))]);
      (cf, lo) <-
      (adc_64 lo (BArray112.get64 r (W64.to_uint (k + (W64.of_int i)))) false
      );
      ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
      (cf, lo) <- (adc_64 lo c false);
      ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int i))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int i))) * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r ((W64.to_uint (k + (W64.of_int i))) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r (W64.to_uint (k + (W64.of_int i))) lo);
      c <- hi;
      i <- (i + 1);
    }
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert,
     ((0 <= ((W64.to_uint (k + (W64.of_int 7))) * 8)) /\
     ((((W64.to_uint (k + (W64.of_int 7))) * 8) + 8) <= 112)))]);
    b_r <-
    (BArray112.set64d b_r ((W64.to_uint (k + (W64.of_int 7))) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r (W64.to_uint (k + (W64.of_int 7))) c);
    return (r, b_r, trace_h__MUL____mul1acc);
  }
  proc h__MUL___os_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
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
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray112.t;
    var param_3:BArray112.t;
    var param_4:W64.t;
    var param_5:BArray56.t;
    var result_0:BArray112.t;
    var b_result_0:BArray112.t;
    var trace_h__MUL___os_muln:trace;
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
    trace_h__MUL___os_muln <- [];
    trace_h__MUL___os_muln <-
    (trace_h__MUL___os_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    ai <- (BArray56.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL____mul1 (param, b_param, param_0,
    param_1, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL___os_muln <- (trace_h__MUL___os_muln ++ tmp__trace);
    trace_h__MUL___os_muln <-
    (trace_h__MUL___os_muln ++ [(Assert, (BArray112.is_init b_result 0 64))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 7))) {
      trace_h__MUL___os_muln <-
      (trace_h__MUL___os_muln ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL____mul1acc (param_2, param_3,
      b_param_0, param_4, param_5, (BArray56.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL___os_muln <- (trace_h__MUL___os_muln ++ tmp__trace);
      trace_h__MUL___os_muln <-
      (trace_h__MUL___os_muln ++
      [(Assert,
       (BArray112.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 7) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL___os_muln);
  }
  proc h__MUL___os_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                         b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
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
    var k:W64.t;
    var param_2:W64.t;
    var b_param_0:BArray112.t;
    var param_3:BArray112.t;
    var param_4:W64.t;
    var param_5:BArray56.t;
    var result_0:BArray112.t;
    var b_result_0:BArray112.t;
    var trace_h__MUL___os_sqrn:trace;
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
    trace_h__MUL___os_sqrn <- [];
    trace_h__MUL___os_sqrn <-
    (trace_h__MUL___os_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    ai <- (BArray56.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL____mul1 (param, b_param, param_0,
    param_1, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL___os_sqrn <- (trace_h__MUL___os_sqrn ++ tmp__trace);
    trace_h__MUL___os_sqrn <-
    (trace_h__MUL___os_sqrn ++ [(Assert, (BArray112.is_init b_result 0 64))]);
    b_r <- b_result;
    r <- result;
    k <- (W64.of_int 1);
    while ((k \ult (W64.of_int 7))) {
      trace_h__MUL___os_sqrn <-
      (trace_h__MUL___os_sqrn ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a (W64.to_uint k));
      param_2 <- k;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- a;
      (aux_1, aux_2, tmp__trace) <@ h__MUL____mul1acc (param_2, param_3,
      b_param_0, param_4, param_5, (BArray56.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL___os_sqrn <- (trace_h__MUL___os_sqrn ++ tmp__trace);
      trace_h__MUL___os_sqrn <-
      (trace_h__MUL___os_sqrn ++
      [(Assert,
       (BArray112.is_init b_result_0 0
       (8 * (((W64.to_uint param_2) + 7) + 1))))]);
      b_r <- b_result_0;
      r <- result_0;
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__MUL___os_sqrn);
  }
  proc bN____store (ap:W64.t, a:BArray112.t, b_a:BArray112.t) : trace = {
    var i:int;
    var t:W64.t;
    var trace_bN____store:trace;
    trace_bN____store <- [];
    trace_bN____store <-
    (trace_bN____store ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 14)) /\
     (BArray112.is_init b_a 0 112)))]);
    i <- 0;
    while ((i < 14)) {
      trace_bN____store <-
      (trace_bN____store ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      t <- (BArray112.get64 a i);
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
  proc bN___store_ (ap:W64.t, a:BArray112.t, b_a:BArray112.t) : trace = {
    var param:W64.t;
    var param_0:BArray112.t;
    var trace_bN___store_:trace;
    param_0 <- witness;
    trace_bN___store_ <- [];
    trace_bN___store_ <-
    (trace_bN___store_ ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 14)) /\
     (BArray112.is_init b_a 0 112)))]);
    ap <- ap;
    a <- a;
    param <- ap;
    param_0 <- a;
    tmp__trace <@ bN____store (param, param_0,
    (BArray112.init_arr (W8.of_int 255)));
    trace_bN___store_ <- (trace_bN___store_ ++ tmp__trace);
    return (trace_bN___store_);
  }
  proc bn_os_muln (rp:W64.t, ap:W64.t, bp:W64.t) : trace = {
    var aux_3:BArray112.t;
    var aux_4:BArray112.t;
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var b__a:BArray56.t;
    var b__b:BArray56.t;
    var b__r:BArray112.t;
    var _rp:W64.t;
    var b_a:BArray56.t;
    var a:BArray56.t;
    var _a:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var b_b:BArray56.t;
    var b:BArray56.t;
    var _b:BArray56.t;
    var b_param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:W64.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var b_r:BArray112.t;
    var r:BArray112.t;
    var _r:BArray112.t;
    var b_param_1:BArray112.t;
    var param_3:BArray112.t;
    var param_4:BArray56.t;
    var param_5:BArray56.t;
    var result_1:BArray112.t;
    var b_result_1:BArray112.t;
    var param_6:W64.t;
    var param_7:BArray112.t;
    var trace_bn_os_muln:trace;
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
    trace_bn_os_muln <- [];
    trace_bn_os_muln <-
    (trace_bn_os_muln ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 7))) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 14))))]);
    b__a <- (BArray56.init_arr (W8.of_int 0));
    b__b <- (BArray56.init_arr (W8.of_int 0));
    b__r <- (BArray112.init_arr (W8.of_int 0));
    _rp <- rp;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_os_muln <- (trace_bn_os_muln ++ tmp__trace);
    trace_bn_os_muln <-
    (trace_bn_os_muln ++ [(Assert, (BArray56.is_init b_result 0 56))]);
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
    trace_bn_os_muln <- (trace_bn_os_muln ++ tmp__trace);
    trace_bn_os_muln <-
    (trace_bn_os_muln ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    (aux_3, aux_4, tmp__trace) <@ h__MUL___os_muln (param_3, b_param_1,
    param_4, (BArray56.init_arr (W8.of_int 255)), param_5,
    (BArray56.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_bn_os_muln <- (trace_bn_os_muln ++ tmp__trace);
    trace_bn_os_muln <-
    (trace_bn_os_muln ++ [(Assert, (BArray112.is_init b_result_1 0 112))]);
    r <- result_1;
    rp <- _rp;
    param_6 <- rp;
    param_7 <- r;
    tmp__trace <@ bN___store_ (param_6, param_7,
    (BArray112.init_arr (W8.of_int 255)));
    trace_bn_os_muln <- (trace_bn_os_muln ++ tmp__trace);
    return (trace_bn_os_muln);
  }
  proc bn_os_sqrn (rp:W64.t, ap:W64.t) : trace = {
    var aux_1:BArray112.t;
    var aux_2:BArray112.t;
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b__a:BArray56.t;
    var b__r:BArray112.t;
    var _rp:W64.t;
    var b_a:BArray56.t;
    var a:BArray56.t;
    var _a:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var b_r:BArray112.t;
    var r:BArray112.t;
    var _r:BArray112.t;
    var b_param_0:BArray112.t;
    var param_1:BArray112.t;
    var param_2:BArray56.t;
    var result_0:BArray112.t;
    var b_result_0:BArray112.t;
    var param_3:W64.t;
    var param_4:BArray112.t;
    var trace_bn_os_sqrn:trace;
    _a <- witness;
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
    param_4 <- witness;
    r <- witness;
    result <- witness;
    result_0 <- witness;
    trace_bn_os_sqrn <- [];
    trace_bn_os_sqrn <-
    (trace_bn_os_sqrn ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 14))))]);
    b__a <- (BArray56.init_arr (W8.of_int 0));
    b__r <- (BArray112.init_arr (W8.of_int 0));
    _rp <- rp;
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_os_sqrn <- (trace_bn_os_sqrn ++ tmp__trace);
    trace_bn_os_sqrn <-
    (trace_bn_os_sqrn ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_r <- b__r;
    r <- _r;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- a;
    (aux_1, aux_2, tmp__trace) <@ h__MUL___os_sqrn (param_1, b_param_0,
    param_2, (BArray56.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_bn_os_sqrn <- (trace_bn_os_sqrn ++ tmp__trace);
    trace_bn_os_sqrn <-
    (trace_bn_os_sqrn ++ [(Assert, (BArray112.is_init b_result_0 0 112))]);
    r <- result_0;
    rp <- _rp;
    param_3 <- rp;
    param_4 <- r;
    tmp__trace <@ bN___store_ (param_3, param_4,
    (BArray112.init_arr (W8.of_int 255)));
    trace_bn_os_sqrn <- (trace_bn_os_sqrn ++ tmp__trace);
    return (trace_bn_os_sqrn);
  }
}.

(* The post and trace are valid. *)

op h__BN____load_spec _a _b_a _ap =
   hoare [M.h__BN____load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__BN___load_spec _a _b_a _ap =
   hoare [M.h__BN___load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__BN___load__spec _a _b_a _ap =
   hoare [M.h__BN___load_ :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__MUL____mul1_spec _r _b_r _a _b _b_b =
   hoare [M.h__MUL____mul1 :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray56.is_init _b_b 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (8 * (7 + 1))) /\ (valid res.`3))].

op h__MUL____mul1acc_spec _k _r _b_r _a _b _b_b =
   hoare [M.h__MUL____mul1acc :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k)))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= (W64.to_uint _k)) /\ ((W64.to_uint _k) < 7)) /\
    (BArray112.is_init _b_r 0 (8 * ((W64.to_uint _k) + 7)))) /\
   (BArray56.is_init _b_b 0 (8 * 7))))))) ==>
   ((true /\ (BArray112.is_init res.`2 0 (8 * (((W64.to_uint _k) + 7) + 1)))) /\
   (valid res.`3))].

op h__MUL___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL___os_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL___os_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op bN____store_spec _ap _a _b_a =
   hoare [M.bN____store :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 14)) /\
   (BArray112.is_init _b_a 0 (8 * 14))))) ==> (true /\ (valid res))].

op bN___store__spec _ap _a _b_a =
   hoare [M.bN___store_ :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 14)) /\
   (BArray112.is_init _b_a 0 (8 * 14))))) ==> (true /\ (valid res))].

op bn_os_muln_spec _rp _ap _bp =
   hoare [M.bn_os_muln :
   (((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))) /\
   (true /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 7))) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 14))))))) ==>
   (true /\ (valid res))].

op bn_os_sqrn_spec _rp _ap =
   hoare [M.bn_os_sqrn :
   (((_ap = ap) /\ (_rp = rp)) /\
   (true /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 14)))))) ==>
   (true /\ (valid res))].
