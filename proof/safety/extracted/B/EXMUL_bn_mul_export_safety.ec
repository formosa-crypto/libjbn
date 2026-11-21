require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array3 Array7 Array8 Array14 Array24 Array56 Array64 Array112 BArray24
BArray56 BArray64 BArray112.

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
                       b_b:BArray56.t) : W64.t * bool * bool * BArray112.t *
                                         BArray112.t * trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_rr:BArray64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var rr:BArray64.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MUL____mul1:trace;
    b_rr <- witness;
    rr <- witness;
    trace_h__MUL____mul1 <- [];
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    b_rr <- (BArray64.init_arr (W8.of_int 0));
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    b_rr <- (BArray64.set64d b_rr 8 (W64.of_int 18446744073709551615));
    b_rr <- (BArray64.set64d b_rr 0 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 a (BArray56.get64 b 0));
    rr <- (BArray64.set64 rr 1 aux);
    rr <- (BArray64.set64 rr 0 aux_0);
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++ [(Assert, (BArray64.is_init b_rr 0 8))]);
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 (BArray64.get64 rr 0));
    i <- 1;
    while ((i < 7)) {
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_rr <-
      (BArray64.set64d b_rr ((i + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 a (BArray56.get64 b i));
      rr <- (BArray64.set64 rr (i + 1) aux_1);
      lo <- aux_2;
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++ [(Assert, (BArray64.is_init b_rr (i * 8) 8))]);
      b_rr <-
      (BArray64.set64d b_rr (i * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray64.get64 rr i) lo cf);
      cf <- aux_3;
      rr <- (BArray64.set64 rr i aux_4);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1 <-
      (trace_h__MUL____mul1 ++ [(Assert, (BArray64.is_init b_rr (i * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i (BArray64.get64 rr i));
      i <- (i + 1);
    }
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++ [(Assert, (BArray64.is_init b_rr (7 * 8) 8))]);
    b_rr <- (BArray64.set64d b_rr (7 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray64.get64 rr 7) _zero cf);
    cf <- aux_5;
    rr <- (BArray64.set64 rr 7 aux_6);
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1 <-
    (trace_h__MUL____mul1 ++ [(Assert, (BArray64.is_init b_rr (7 * 8) 8))]);
    b_r <- (BArray112.set64d b_r (7 * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 7 (BArray64.get64 rr 7));
    return (_zero, of_0, cf, r, b_r, trace_h__MUL____mul1);
  }
  proc h__MUL____mul1acc (k:int, r:BArray112.t, b_r:BArray112.t, a:W64.t,
                          b:BArray56.t, b_b:BArray56.t, _zero:W64.t,
                          of_0:bool, cf:bool) : W64.t * bool * bool *
                                                BArray112.t * BArray112.t *
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
    var b_rr:BArray64.t;
    var rr:BArray64.t;
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    var trace_h__MUL____mul1acc:trace;
    b_rr <- witness;
    rr <- witness;
    trace_h__MUL____mul1acc <- [];
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert,
     ((((1 <= k) /\ (k < 7)) /\ (BArray112.is_init b_r 0 (8 * (k + 7)))) /\
     (BArray56.is_init b_b 0 56)))]);
    b_rr <- (BArray64.init_arr (W8.of_int 0));
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray112.is_init b_r (k * 8) 8))]);
    b_rr <- (BArray64.set64d b_rr 0 (W64.of_int 18446744073709551615));
    rr <- (BArray64.set64 rr 0 (BArray112.get64 r k));
    inc <- (7 - 1);
    i <- 0;
    while ((i < inc)) {
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 112)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, (BArray112.is_init b_r (((k + i) + 1) * 8) 8))]);
      b_rr <-
      (BArray64.set64d b_rr ((i + 1) * 8) (W64.of_int 18446744073709551615));
      rr <- (BArray64.set64 rr (i + 1) (BArray112.get64 r ((k + i) + 1)));
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 a (BArray56.get64 b i));
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, (BArray64.is_init b_rr (i * 8) 8))]);
      b_rr <-
      (BArray64.set64d b_rr (i * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray64.get64 rr i) lo of_0);
      of_0 <- aux;
      rr <- (BArray64.set64 rr i aux_0);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, (BArray64.is_init b_rr (i * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r ((k + i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r (k + i) (BArray64.get64 rr i));
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 64)))]);
      trace_h__MUL____mul1acc <-
      (trace_h__MUL____mul1acc ++
      [(Assert, (BArray64.is_init b_rr ((i + 1) * 8) 8))]);
      b_rr <-
      (BArray64.set64d b_rr ((i + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray64.get64 rr (i + 1)) hi cf);
      cf <- aux_1;
      rr <- (BArray64.set64 rr (i + 1) aux_2);
      i <- (i + 1);
    }
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
    b_rr <- (BArray64.set64d b_rr (7 * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 a (BArray56.get64 b (7 - 1)));
    rr <- (BArray64.set64 rr 7 aux_3);
    lo <- aux_4;
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray64.is_init b_rr ((7 - 1) * 8) 8))]);
    b_rr <-
    (BArray64.set64d b_rr ((7 - 1) * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray64.get64 rr (7 - 1)) lo of_0);
    of_0 <- aux_5;
    rr <- (BArray64.set64 rr (7 - 1) aux_6);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert,
     ((0 <= (((k + 7) - 1) * 8)) /\ (((((k + 7) - 1) * 8) + 8) <= 112)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray64.is_init b_rr ((7 - 1) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r (((k + 7) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r ((k + 7) - 1) (BArray64.get64 rr (7 - 1)));
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray64.is_init b_rr (7 * 8) 8))]);
    b_rr <- (BArray64.set64d b_rr (7 * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray64.get64 rr 7) _zero cf);
    cf <- aux_7;
    rr <- (BArray64.set64 rr 7 aux_8);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray64.is_init b_rr (7 * 8) 8))]);
    b_rr <- (BArray64.set64d b_rr (7 * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray64.get64 rr 7) _zero of_0);
    of_0 <- aux_9;
    rr <- (BArray64.set64 rr 7 aux_10);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= ((k + 7) * 8)) /\ ((((k + 7) * 8) + 8) <= 112)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 64)))]);
    trace_h__MUL____mul1acc <-
    (trace_h__MUL____mul1acc ++
    [(Assert, (BArray64.is_init b_rr (7 * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r ((k + 7) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r (k + 7) (BArray64.get64 rr 7));
    return (_zero, of_0, cf, r, b_r, trace_h__MUL____mul1acc);
  }
  proc h__MUL___os_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                         b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var aux_2:BArray112.t;
    var aux_3:BArray112.t;
    var aux_7:BArray112.t;
    var aux_8:BArray112.t;
    var aux:W64.t;
    var aux_4:W64.t;
    var aux_0:bool;
    var aux_1:bool;
    var aux_5:bool;
    var aux_6:bool;
    var ai:W64.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:W64.t;
    var param_1:BArray56.t;
    var result:W64.t;
    var result_0:bool;
    var result_1:bool;
    var result_2:BArray112.t;
    var b_result:BArray112.t;
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var i:int;
    var param_2:int;
    var b_param_0:BArray112.t;
    var param_3:BArray112.t;
    var param_4:W64.t;
    var param_5:BArray56.t;
    var param_6:W64.t;
    var param_7:bool;
    var param_8:bool;
    var result_3:W64.t;
    var result_4:bool;
    var result_5:bool;
    var result_6:BArray112.t;
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
    result_2 <- witness;
    result_6 <- witness;
    trace_h__MUL___os_muln <- [];
    trace_h__MUL___os_muln <-
    (trace_h__MUL___os_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    ai <- (BArray56.get64 a 0);
    b_param <- b_r;
    param <- r;
    param_0 <- ai;
    param_1 <- b;
    (aux, aux_0, aux_1, aux_2, aux_3, tmp__trace) <@ h__MUL____mul1 (
    param, b_param, param_0, param_1, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    result_1 <- aux_1;
    result_2 <- aux_2;
    b_result <- aux_3;
    trace_h__MUL___os_muln <- (trace_h__MUL___os_muln ++ tmp__trace);
    trace_h__MUL___os_muln <-
    (trace_h__MUL___os_muln ++ [(Assert, (BArray112.is_init b_result 0 64))]);
    _zero <- result;
    of_0 <- result_0;
    cf <- result_1;
    b_r <- b_result;
    r <- result_2;
    i <- 1;
    while ((i < 7)) {
      trace_h__MUL___os_muln <-
      (trace_h__MUL___os_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a i);
      param_2 <- i;
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- ai;
      param_5 <- b;
      param_6 <- _zero;
      param_7 <- of_0;
      param_8 <- cf;
      (aux_4, aux_5, aux_6, aux_7, aux_8, tmp__trace) <@ h__MUL____mul1acc (
      param_2, param_3, b_param_0, param_4, param_5,
      (BArray56.init_arr (W8.of_int 255)), param_6, param_7, param_8);
      result_3 <- aux_4;
      result_4 <- aux_5;
      result_5 <- aux_6;
      result_6 <- aux_7;
      b_result_0 <- aux_8;
      trace_h__MUL___os_muln <- (trace_h__MUL___os_muln ++ tmp__trace);
      trace_h__MUL___os_muln <-
      (trace_h__MUL___os_muln ++
      [(Assert, (BArray112.is_init b_result_0 0 (8 * ((param_2 + 7) + 1))))]);
      _zero <- result_3;
      of_0 <- result_4;
      cf <- result_5;
      b_r <- b_result_0;
      r <- result_6;
      i <- (i + 1);
    }
    return (r, b_r, trace_h__MUL___os_muln);
  }
  proc h__MUL____muln_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                 istart:int, iend:int, a:BArray56.t,
                                 b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray24.t * BArray24.t * trace = {
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
    var trace_h__MUL____muln_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__MUL____muln_innerloop <- [];
    trace_h__MUL____muln_innerloop <-
    (trace_h__MUL____muln_innerloop ++
    [(Assert,
     (((((((0 <= istart) /\ (iend <= 7)) /\ (0 <= (k - (iend - 1)))) /\
        ((k - istart) < 7)) /\
       (BArray24.is_init b_x 0 24)) /\
      (BArray56.is_init b_a (8 * istart) (8 * (iend - istart)))) /\
     (BArray56.is_init b_b 0 56)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__MUL____muln_innerloop <-
      (trace_h__MUL____muln_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MUL____muln_innerloop <-
      (trace_h__MUL____muln_innerloop ++
      [(Assert, (BArray56.is_init b_a (i * 8) 8))]);
      t0 <- (BArray56.get64 a i);
      trace_h__MUL____muln_innerloop <-
      (trace_h__MUL____muln_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 56)))]);
      (t1, t0) <- (mulu_64 t0 (BArray56.get64 b j));
      param <- x;
      param_0 <- t1;
      param_1 <- t0;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL____muln_innerloop <-
      (trace_h__MUL____muln_innerloop ++ tmp__trace);
      trace_h__MUL____muln_innerloop <-
      (trace_h__MUL____muln_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__MUL____muln_innerloop);
  }
  proc h__MUL____ps_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                          b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
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
    var param_3:BArray56.t;
    var param_4:BArray56.t;
    var result:BArray24.t;
    var b_result:BArray24.t;
    var b_param_0:BArray24.t;
    var param_5:BArray24.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:BArray56.t;
    var param_10:BArray56.t;
    var result_0:BArray24.t;
    var b_result_0:BArray24.t;
    var trace_h__MUL____ps_muln:trace;
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
    trace_h__MUL____ps_muln <- [];
    trace_h__MUL____ps_muln <-
    (trace_h__MUL____ps_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray56.get64 a 0);
    (t1, t0) <- (mulu_64 t0 (BArray56.get64 b 0));
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 7)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- (k + 1);
      param_3 <- a;
      param_4 <- b;
      (aux, aux_0, tmp__trace) <@ h__MUL____muln_innerloop (param, b_param,
      param_0, param_1, param_2, param_3,
      (BArray56.init_arr (W8.of_int 255)), param_4,
      (BArray56.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL____ps_muln <- (trace_h__MUL____ps_muln ++ tmp__trace);
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 7) - 1);
    k <- 7;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_5 <- x;
      param_6 <- k;
      param_7 <- ((k - 7) + 1);
      param_8 <- 7;
      param_9 <- a;
      param_10 <- b;
      (aux_1, aux_2, tmp__trace) <@ h__MUL____muln_innerloop (param_5,
      b_param_0, param_6, param_7, param_8, param_9,
      (BArray56.init_arr (W8.of_int 255)), param_10,
      (BArray56.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__MUL____ps_muln <- (trace_h__MUL____ps_muln ++ tmp__trace);
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, (BArray24.is_init b_result_0 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_0;
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL____ps_muln <-
      (trace_h__MUL____ps_muln ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__MUL____ps_muln <-
    (trace_h__MUL____ps_muln ++
    [(Assert,
     ((0 <= (((2 * 7) - 1) * 8)) /\ (((((2 * 7) - 1) * 8) + 8) <= 112)))]);
    trace_h__MUL____ps_muln <-
    (trace_h__MUL____ps_muln ++
    [(Assert,
     ((0 <= ((((2 * 7) - 1) %% 3) * 8)) /\
     ((((((2 * 7) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL____ps_muln <-
    (trace_h__MUL____ps_muln ++
    [(Assert, (BArray24.is_init b_x ((((2 * 7) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r (((2 * 7) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray112.set64 r ((2 * 7) - 1) (BArray24.get64 x (((2 * 7) - 1) %% 3)));
    return (r, b_r, trace_h__MUL____ps_muln);
  }
  proc h__MUL___ps_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
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
    var trace_h__MUL___ps_muln:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MUL___ps_muln <- [];
    trace_h__MUL___ps_muln <-
    (trace_h__MUL___ps_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MUL____ps_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL___ps_muln <- (trace_h__MUL___ps_muln ++ tmp__trace);
    trace_h__MUL___ps_muln <-
    (trace_h__MUL___ps_muln ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___ps_muln);
  }
  proc h__MUL____sqrn_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                 istart:int, iend:int, a:BArray56.t,
                                 b_a:BArray56.t) : BArray24.t * BArray24.t *
                                                   trace = {
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
    var trace_h__MUL____sqrn_innerloop:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__MUL____sqrn_innerloop <- [];
    trace_h__MUL____sqrn_innerloop <-
    (trace_h__MUL____sqrn_innerloop ++
    [(Assert,
     ((((((0 <= istart) /\ (iend <= 7)) /\ (0 <= (k - (iend - 1)))) /\
       ((k - istart) < 7)) /\
      (BArray24.is_init b_x 0 24)) /\
     (BArray56.is_init b_a 0 56)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__MUL____sqrn_innerloop <-
      (trace_h__MUL____sqrn_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      ti <- (BArray56.get64 a i);
      trace_h__MUL____sqrn_innerloop <-
      (trace_h__MUL____sqrn_innerloop ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 56)))]);
      tj <- (BArray56.get64 a j);
      param <- x;
      param_0 <- ti;
      param_1 <- tj;
      param_2 <- k;
      (aux, aux_0, tmp__trace) <@ uTIL____addacc3x2 (param,
      (BArray24.init_arr (W8.of_int 255)), param_0, param_1, param_2);
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL____sqrn_innerloop <-
      (trace_h__MUL____sqrn_innerloop ++ tmp__trace);
      trace_h__MUL____sqrn_innerloop <-
      (trace_h__MUL____sqrn_innerloop ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      x <- result;
      i <- (i + 1);
    }
    b_x <- (BArray24.init_arr (W8.of_int 255));
    return (x, b_x, trace_h__MUL____sqrn_innerloop);
  }
  proc h__MUL____ps_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                          b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
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
    var param_3:BArray56.t;
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
    var param_12:BArray56.t;
    var result_1:BArray24.t;
    var b_result_1:BArray24.t;
    var param_13:BArray24.t;
    var param_14:W64.t;
    var param_15:W64.t;
    var param_16:int;
    var result_2:BArray24.t;
    var b_result_2:BArray24.t;
    var trace_h__MUL____ps_sqrn:trace;
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
    trace_h__MUL____ps_sqrn <- [];
    trace_h__MUL____ps_sqrn <-
    (trace_h__MUL____ps_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    t0 <- (BArray56.get64 a 0);
    (t1, t0) <- (mulu_64 t0 t0);
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 t0);
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 t1);
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    k <- 1;
    while ((k < 7)) {
      b_param <- b_x;
      param <- x;
      param_0 <- k;
      param_1 <- 0;
      param_2 <- ((k + 1) %/ 2);
      param_3 <- a;
      (aux, aux_0, tmp__trace) <@ h__MUL____sqrn_innerloop (param, b_param,
      param_0, param_1, param_2, param_3,
      (BArray56.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__MUL____ps_sqrn <- (trace_h__MUL____ps_sqrn ++ tmp__trace);
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result;
      if (((k %% 2) = 0)) {
        trace_h__MUL____ps_sqrn <-
        (trace_h__MUL____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 56)))]);
        t0 <- (BArray56.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_4 <- x;
        param_5 <- t1;
        param_6 <- t0;
        param_7 <- k;
        (aux_1, aux_2, tmp__trace) <@ uTIL____addacc3 (param_4,
        (BArray24.init_arr (W8.of_int 255)), param_5, param_6, param_7);
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__MUL____ps_sqrn <- (trace_h__MUL____ps_sqrn ++ tmp__trace);
        trace_h__MUL____ps_sqrn <-
        (trace_h__MUL____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_0 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_0;
      } else {
        
      }
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r k t0);
      k <- (k + 1);
    }
    inc <- ((2 * 7) - 1);
    k <- 7;
    while ((k < inc)) {
      b_param_0 <- b_x;
      param_8 <- x;
      param_9 <- k;
      param_10 <- ((k - 7) + 1);
      param_11 <- ((k + 1) %/ 2);
      param_12 <- a;
      (aux_3, aux_4, tmp__trace) <@ h__MUL____sqrn_innerloop (param_8,
      b_param_0, param_9, param_10, param_11, param_12,
      (BArray56.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__MUL____ps_sqrn <- (trace_h__MUL____ps_sqrn ++ tmp__trace);
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, (BArray24.is_init b_result_1 0 24))]);
      b_x <- (BArray24.init_arr (W8.of_int 255));
      x <- result_1;
      if (((k %% 2) = 0)) {
        trace_h__MUL____ps_sqrn <-
        (trace_h__MUL____ps_sqrn ++
        [(Assert, ((0 <= ((k %/ 2) * 8)) /\ ((((k %/ 2) * 8) + 8) <= 56)))]);
        t0 <- (BArray56.get64 a (k %/ 2));
        (t1, t0) <- (mulu_64 t0 t0);
        param_13 <- x;
        param_14 <- t1;
        param_15 <- t0;
        param_16 <- k;
        (aux_5, aux_6, tmp__trace) <@ uTIL____addacc3 (param_13,
        (BArray24.init_arr (W8.of_int 255)), param_14, param_15, param_16);
        result_2 <- aux_5;
        b_result_2 <- aux_6;
        trace_h__MUL____ps_sqrn <- (trace_h__MUL____ps_sqrn ++ tmp__trace);
        trace_h__MUL____ps_sqrn <-
        (trace_h__MUL____ps_sqrn ++
        [(Assert, (BArray24.is_init b_result_2 0 24))]);
        b_x <- (BArray24.init_arr (W8.of_int 255));
        x <- result_2;
      } else {
        
      }
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      t0 <- (BArray24.get64 x (k %% 3));
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, ((0 <= ((k %% 3) * 8)) /\ ((((k %% 3) * 8) + 8) <= 24)))]);
      b_x <-
      (BArray24.set64d b_x ((k %% 3) * 8) (W64.of_int 18446744073709551615));
      x <- (BArray24.set64 x (k %% 3) (W64.of_int 0));
      trace_h__MUL____ps_sqrn <-
      (trace_h__MUL____ps_sqrn ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r k t0);
      k <- (k + 1);
    }
    trace_h__MUL____ps_sqrn <-
    (trace_h__MUL____ps_sqrn ++
    [(Assert,
     ((0 <= (((2 * 7) - 1) * 8)) /\ (((((2 * 7) - 1) * 8) + 8) <= 112)))]);
    trace_h__MUL____ps_sqrn <-
    (trace_h__MUL____ps_sqrn ++
    [(Assert,
     ((0 <= ((((2 * 7) - 1) %% 3) * 8)) /\
     ((((((2 * 7) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL____ps_sqrn <-
    (trace_h__MUL____ps_sqrn ++
    [(Assert, (BArray24.is_init b_x ((((2 * 7) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r (((2 * 7) - 1) * 8)
    (W64.of_int 18446744073709551615));
    r <-
    (BArray112.set64 r ((2 * 7) - 1) (BArray24.get64 x (((2 * 7) - 1) %% 3)));
    return (r, b_r, trace_h__MUL____ps_sqrn);
  }
  proc h__MUL___ps_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                         b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var trace_h__MUL___ps_sqrn:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL___ps_sqrn <- [];
    trace_h__MUL___ps_sqrn <-
    (trace_h__MUL___ps_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL____ps_sqrn (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL___ps_sqrn <- (trace_h__MUL___ps_sqrn ++ tmp__trace);
    trace_h__MUL___ps_sqrn <-
    (trace_h__MUL___ps_sqrn ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___ps_sqrn);
  }
  proc h__MUL___ps_sqrn_ (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                          b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var trace_h__MUL___ps_sqrn_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__MUL___ps_sqrn_ <- [];
    trace_h__MUL___ps_sqrn_ <-
    (trace_h__MUL___ps_sqrn_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__MUL___ps_sqrn (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MUL___ps_sqrn_ <- (trace_h__MUL___ps_sqrn_ ++ tmp__trace);
    trace_h__MUL___ps_sqrn_ <-
    (trace_h__MUL___ps_sqrn_ ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    r <- r;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL___ps_sqrn_);
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
  proc bn_ps_muln (rp:W64.t, ap:W64.t, bp:W64.t) : trace = {
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
    var trace_bn_ps_muln:trace;
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
    trace_bn_ps_muln <- [];
    trace_bn_ps_muln <-
    (trace_bn_ps_muln ++
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
    trace_bn_ps_muln <- (trace_bn_ps_muln ++ tmp__trace);
    trace_bn_ps_muln <-
    (trace_bn_ps_muln ++ [(Assert, (BArray56.is_init b_result 0 56))]);
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
    trace_bn_ps_muln <- (trace_bn_ps_muln ++ tmp__trace);
    trace_bn_ps_muln <-
    (trace_bn_ps_muln ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    b <- result_0;
    b_r <- b__r;
    r <- _r;
    b_param_1 <- b_r;
    param_3 <- r;
    param_4 <- a;
    param_5 <- b;
    (aux_3, aux_4, tmp__trace) <@ h__MUL___ps_muln (param_3, b_param_1,
    param_4, (BArray56.init_arr (W8.of_int 255)), param_5,
    (BArray56.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_bn_ps_muln <- (trace_bn_ps_muln ++ tmp__trace);
    trace_bn_ps_muln <-
    (trace_bn_ps_muln ++ [(Assert, (BArray112.is_init b_result_1 0 112))]);
    r <- result_1;
    rp <- _rp;
    param_6 <- rp;
    param_7 <- r;
    tmp__trace <@ bN___store_ (param_6, param_7,
    (BArray112.init_arr (W8.of_int 255)));
    trace_bn_ps_muln <- (trace_bn_ps_muln ++ tmp__trace);
    return (trace_bn_ps_muln);
  }
  proc bn_ps_sqrn (rp:W64.t, ap:W64.t) : trace = {
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
    var trace_bn_ps_sqrn:trace;
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
    trace_bn_ps_sqrn <- [];
    trace_bn_ps_sqrn <-
    (trace_bn_ps_sqrn ++
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
    trace_bn_ps_sqrn <- (trace_bn_ps_sqrn ++ tmp__trace);
    trace_bn_ps_sqrn <-
    (trace_bn_ps_sqrn ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_r <- b__r;
    r <- _r;
    b_param_0 <- b_r;
    param_1 <- r;
    param_2 <- a;
    (aux_1, aux_2, tmp__trace) <@ h__MUL___ps_sqrn_ (param_1, b_param_0,
    param_2, (BArray56.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_bn_ps_sqrn <- (trace_bn_ps_sqrn ++ tmp__trace);
    trace_bn_ps_sqrn <-
    (trace_bn_ps_sqrn ++ [(Assert, (BArray112.is_init b_result_0 0 112))]);
    r <- result_0;
    rp <- _rp;
    param_3 <- rp;
    param_4 <- r;
    tmp__trace <@ bN___store_ (param_3, param_4,
    (BArray112.init_arr (W8.of_int 255)));
    trace_bn_ps_sqrn <- (trace_bn_ps_sqrn ++ tmp__trace);
    return (trace_bn_ps_sqrn);
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
   ((BArray112.is_init res.`5 0 (8 * (7 + 1))) /\ (valid res.`6))].

op h__MUL____mul1acc_spec _k _r _b_r _a _b _b_b __zero _of _cf =
   hoare [M.h__MUL____mul1acc :
   (((_cf = cf) /\
    ((_of = of_0) /\
    ((__zero = _zero) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_a = a) /\ ((_b_r = b_r) /\ ((_r = r) /\ (_k = k))))))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 7)) /\ (BArray112.is_init _b_r 0 (8 * (_k + 7)))) /\
   (BArray56.is_init _b_b 0 (8 * 7))))))) ==>
   ((true /\ (BArray112.is_init res.`5 0 (8 * ((_k + 7) + 1)))) /\
   (valid res.`6))].

op h__MUL___os_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL___os_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL____muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b =
   hoare [M.h__MUL____muln_innerloop :
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
   (((((((0 <= _istart) /\ (_iend <= 7)) /\ (0 <= (_k - (_iend - 1)))) /\
      ((_k - _istart) < 7)) /\
     (BArray24.is_init _b_x 0 24)) /\
    (BArray56.is_init _b_a (8 * _istart) (8 * (_iend - _istart)))) /\
   (BArray56.is_init _b_b 0 (8 * 7))))))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__MUL____ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL____ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL___ps_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MUL___ps_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL____sqrn_innerloop_spec _x _b_x _k _istart _iend _a _b_a =
   hoare [M.h__MUL____sqrn_innerloop :
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
   ((((((0 <= _istart) /\ (_iend <= 7)) /\ (0 <= (_k - (_iend - 1)))) /\
     ((_k - _istart) < 7)) /\
    (BArray24.is_init _b_x 0 24)) /\
   (BArray56.is_init _b_a 0 (8 * 7)))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__MUL____ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL____ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL___ps_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__MUL___ps_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MUL___ps_sqrn__spec _r _b_r _a _b_a =
   hoare [M.h__MUL___ps_sqrn_ :
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

op bn_ps_muln_spec _rp _ap _bp =
   hoare [M.bn_ps_muln :
   (((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))) /\
   (true /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 7))) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 14))))))) ==>
   (true /\ (valid res))].

op bn_ps_sqrn_spec _rp _ap =
   hoare [M.bn_ps_sqrn :
   (((_ap = ap) /\ (_rp = rp)) /\
   (true /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 14)))))) ==>
   (true /\ (valid res))].

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
