require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import Array7 Array14 Array56 Array112 BArray56 BArray112.

module M = {
  var tmp__trace : trace
  proc h__MULREG____mul1_reg (a:W64.t, b:BArray56.t, b_b:BArray56.t) : 
  W64.t * bool * bool * BArray112.t * BArray112.t * trace = {
    var aux:W64.t;
    var aux_0:W64.t;
    var aux_1:W64.t;
    var aux_2:W64.t;
    var aux_4:W64.t;
    var aux_6:W64.t;
    var aux_3:bool;
    var aux_5:bool;
    var b_r:BArray112.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var r:BArray112.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var trace_h__MULREG____mul1_reg:trace;
    b_r <- witness;
    r <- witness;
    trace_h__MULREG____mul1_reg <- [];
    trace_h__MULREG____mul1_reg <-
    (trace_h__MULREG____mul1_reg ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    b_r <- (BArray112.init_arr (W8.of_int 0));
    (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
    b_r <- (BArray112.set64d b_r 8 (W64.of_int 18446744073709551615));
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    (aux, aux_0) <- (MULX_64 a (BArray56.get64 b 0));
    r <- (BArray112.set64 r 1 aux);
    r <- (BArray112.set64 r 0 aux_0);
    i <- 1;
    while ((i < 7)) {
      trace_h__MULREG____mul1_reg <-
      (trace_h__MULREG____mul1_reg ++
      [(Assert, ((0 <= ((i + 1) * 8)) /\ ((((i + 1) * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1_reg <-
      (trace_h__MULREG____mul1_reg ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <-
      (BArray112.set64d b_r ((i + 1) * 8) (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (MULX_64 a (BArray56.get64 b i));
      r <- (BArray112.set64 r (i + 1) aux_1);
      lo <- aux_2;
      trace_h__MULREG____mul1_reg <-
      (trace_h__MULREG____mul1_reg ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1_reg <-
      (trace_h__MULREG____mul1_reg ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1_reg <-
      (trace_h__MULREG____mul1_reg ++
      [(Assert, (BArray112.is_init b_r (i * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      (aux_3, aux_4) <- (ADCX_64 (BArray112.get64 r i) lo cf);
      cf <- aux_3;
      r <- (BArray112.set64 r i aux_4);
      i <- (i + 1);
    }
    _zero <- (W64.of_int 0);
    trace_h__MULREG____mul1_reg <-
    (trace_h__MULREG____mul1_reg ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1_reg <-
    (trace_h__MULREG____mul1_reg ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1_reg <-
    (trace_h__MULREG____mul1_reg ++
    [(Assert, (BArray112.is_init b_r (7 * 8) 8))]);
    b_r <- (BArray112.set64d b_r (7 * 8) (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADCX_64 (BArray112.get64 r 7) _zero cf);
    cf <- aux_5;
    r <- (BArray112.set64 r 7 aux_6);
    return (_zero, of_0, cf, r, b_r, trace_h__MULREG____mul1_reg);
  }
  proc h__MULREG____mul1acc_reg (k:int, a:W64.t, b:BArray56.t,
                                 b_b:BArray56.t, r:BArray112.t,
                                 b_r:BArray112.t, _zero:W64.t, of_0:bool,
                                 cf:bool) : W64.t * bool * bool *
                                            BArray112.t * BArray112.t * trace = {
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
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    var trace_h__MULREG____mul1acc_reg:trace;
    trace_h__MULREG____mul1acc_reg <- [];
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert,
     ((((1 <= k) /\ (k < 7)) /\ (BArray56.is_init b_b 0 56)) /\
     (BArray112.is_init b_r 0 (8 * (k + 7)))))]);
    inc <- (7 - 1);
    i <- 0;
    while ((i < inc)) {
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (hi, lo) <- (MULX_64 a (BArray56.get64 b i));
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert, (BArray112.is_init b_r ((k + i) * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r ((k + i) * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray112.get64 r (k + i)) lo of_0);
      of_0 <- aux;
      r <- (BArray112.set64 r (k + i) aux_0);
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert,
       ((0 <= (((k + i) + 1) * 8)) /\ (((((k + i) + 1) * 8) + 8) <= 112)))]);
      trace_h__MULREG____mul1acc_reg <-
      (trace_h__MULREG____mul1acc_reg ++
      [(Assert, (BArray112.is_init b_r (((k + i) + 1) * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r (((k + i) + 1) * 8)
      (W64.of_int 18446744073709551615));
      (aux_1, aux_2) <- (ADCX_64 (BArray112.get64 r ((k + i) + 1)) hi cf);
      cf <- aux_1;
      r <- (BArray112.set64 r ((k + i) + 1) aux_2);
      i <- (i + 1);
    }
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, ((0 <= ((7 + k) * 8)) /\ ((((7 + k) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
    b_r <-
    (BArray112.set64d b_r ((7 + k) * 8) (W64.of_int 18446744073709551615));
    (aux_3, aux_4) <- (MULX_64 a (BArray56.get64 b (7 - 1)));
    r <- (BArray112.set64 r (7 + k) aux_3);
    lo <- aux_4;
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert,
     ((0 <= (((7 + k) - 1) * 8)) /\ (((((7 + k) - 1) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert,
     ((0 <= (((7 + k) - 1) * 8)) /\ (((((7 + k) - 1) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, (BArray112.is_init b_r (((7 + k) - 1) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r (((7 + k) - 1) * 8)
    (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <- (ADOX_64 (BArray112.get64 r ((7 + k) - 1)) lo of_0);
    of_0 <- aux_5;
    r <- (BArray112.set64 r ((7 + k) - 1) aux_6);
    _zero <- (W64.of_int 0);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, ((0 <= ((7 + k) * 8)) /\ ((((7 + k) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, ((0 <= ((7 + k) * 8)) /\ ((((7 + k) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, (BArray112.is_init b_r ((7 + k) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r ((7 + k) * 8) (W64.of_int 18446744073709551615));
    (aux_7, aux_8) <- (ADCX_64 (BArray112.get64 r (7 + k)) _zero cf);
    cf <- aux_7;
    r <- (BArray112.set64 r (7 + k) aux_8);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, ((0 <= ((7 + k) * 8)) /\ ((((7 + k) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, ((0 <= ((7 + k) * 8)) /\ ((((7 + k) * 8) + 8) <= 112)))]);
    trace_h__MULREG____mul1acc_reg <-
    (trace_h__MULREG____mul1acc_reg ++
    [(Assert, (BArray112.is_init b_r ((7 + k) * 8) 8))]);
    b_r <-
    (BArray112.set64d b_r ((7 + k) * 8) (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <- (ADOX_64 (BArray112.get64 r (7 + k)) _zero of_0);
    of_0 <- aux_9;
    r <- (BArray112.set64 r (7 + k) aux_10);
    return (_zero, of_0, cf, r, b_r, trace_h__MULREG____mul1acc_reg);
  }
  proc h__MULREG___osreg_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
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
    var inc:int;
    var b_rb:BArray56.t;
    var ai:W64.t;
    var i:int;
    var rb:BArray56.t;
    var param:W64.t;
    var b_param:BArray56.t;
    var param_0:BArray56.t;
    var result:W64.t;
    var result_0:bool;
    var result_1:bool;
    var result_2:BArray112.t;
    var b_result:BArray112.t;
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var b_rr:BArray112.t;
    var rr:BArray112.t;
    var param_1:int;
    var param_2:W64.t;
    var b_param_0:BArray56.t;
    var param_3:BArray56.t;
    var b_param_1:BArray112.t;
    var param_4:BArray112.t;
    var param_5:W64.t;
    var param_6:bool;
    var param_7:bool;
    var result_3:W64.t;
    var result_4:bool;
    var result_5:bool;
    var result_6:BArray112.t;
    var b_result_0:BArray112.t;
    var trace_h__MULREG___osreg_muln:trace;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_rb <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_rr <- witness;
    param_0 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    rb <- witness;
    result_2 <- witness;
    result_6 <- witness;
    rr <- witness;
    trace_h__MULREG___osreg_muln <- [];
    trace_h__MULREG___osreg_muln <-
    (trace_h__MULREG___osreg_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    b_rb <- (BArray56.init_arr (W8.of_int 0));
    ai <- (BArray56.get64 a 0);
    i <- 0;
    while ((i < 7)) {
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_rb <-
      (BArray56.set64d b_rb (i * 8) (W64.of_int 18446744073709551615));
      rb <- (BArray56.set64 rb i (BArray56.get64 b i));
      i <- (i + 1);
    }
    param <- ai;
    b_param <- b_rb;
    param_0 <- rb;
    (aux, aux_0, aux_1, aux_2, aux_3, tmp__trace) <@ h__MULREG____mul1_reg (
    param, param_0, b_param);
    result <- aux;
    result_0 <- aux_0;
    result_1 <- aux_1;
    result_2 <- aux_2;
    b_result <- aux_3;
    trace_h__MULREG___osreg_muln <-
    (trace_h__MULREG___osreg_muln ++ tmp__trace);
    trace_h__MULREG___osreg_muln <-
    (trace_h__MULREG___osreg_muln ++
    [(Assert, (BArray112.is_init b_result 0 64))]);
    _zero <- result;
    of_0 <- result_0;
    cf <- result_1;
    b_rr <- b_result;
    rr <- result_2;
    trace_h__MULREG___osreg_muln <-
    (trace_h__MULREG___osreg_muln ++
    [(Assert, (BArray112.is_init b_rr 0 8))]);
    b_r <- (BArray112.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray112.set64 r 0 (BArray112.get64 rr 0));
    i <- 1;
    while ((i < 7)) {
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      ai <- (BArray56.get64 a i);
      param_1 <- i;
      param_2 <- ai;
      b_param_0 <- b_rb;
      param_3 <- rb;
      b_param_1 <- b_rr;
      param_4 <- rr;
      param_5 <- _zero;
      param_6 <- of_0;
      param_7 <- cf;
      (aux_4, aux_5, aux_6, aux_7, aux_8, tmp__trace) <@ h__MULREG____mul1acc_reg (
      param_1, param_2, param_3, b_param_0, param_4, b_param_1, param_5,
      param_6, param_7);
      result_3 <- aux_4;
      result_4 <- aux_5;
      result_5 <- aux_6;
      result_6 <- aux_7;
      b_result_0 <- aux_8;
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++ tmp__trace);
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, (BArray112.is_init b_result_0 0 (8 * ((param_1 + 7) + 1))))]);
      _zero <- result_3;
      of_0 <- result_4;
      cf <- result_5;
      b_rr <- b_result_0;
      rr <- result_6;
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, (BArray112.is_init b_rr (i * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i (BArray112.get64 rr i));
      i <- (i + 1);
    }
    inc <- (2 * 7);
    i <- 7;
    while ((i < inc)) {
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MULREG___osreg_muln <-
      (trace_h__MULREG___osreg_muln ++
      [(Assert, (BArray112.is_init b_rr (i * 8) 8))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i (BArray112.get64 rr i));
      i <- (i + 1);
    }
    return (r, b_r, trace_h__MULREG___osreg_muln);
  }
  proc h__MULREG___osreg_muln_ (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
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
    var trace_h__MULREG___osreg_muln_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__MULREG___osreg_muln_ <- [];
    trace_h__MULREG___osreg_muln_ <-
    (trace_h__MULREG___osreg_muln_ ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b <- b;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__MULREG___osreg_muln (param, b_param,
    param_0, (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__MULREG___osreg_muln_ <-
    (trace_h__MULREG___osreg_muln_ ++ tmp__trace);
    trace_h__MULREG___osreg_muln_ <-
    (trace_h__MULREG___osreg_muln_ ++
    [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    r <- r;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MULREG___osreg_muln_);
  }
}.

(* The post and trace are valid. *)

op h__MULREG____mul1_reg_spec _a _b _b_b =
   hoare [M.h__MULREG____mul1_reg :
   (((_b_b = b_b) /\ ((_b = b) /\ (_a = a))) /\
   (BArray56.is_init _b_b 0 (8 * 7))) ==>
   ((BArray112.is_init res.`5 0 (8 * (7 + 1))) /\ (valid res.`6))].

op h__MULREG____mul1acc_reg_spec _k _a _b _b_b _r _b_r __zero _of _cf =
   hoare [M.h__MULREG____mul1acc_reg :
   (((_cf = cf) /\
    ((_of = of_0) /\
    ((__zero = _zero) /\
    ((_b_r = b_r) /\
    ((_r = r) /\ ((_b_b = b_b) /\ ((_b = b) /\ ((_a = a) /\ (_k = k))))))))) /\
   (true /\
   (true /\
   (true /\
   ((((1 <= _k) /\ (_k < 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray112.is_init _b_r 0 (8 * (_k + 7)))))))) ==>
   ((true /\ (BArray112.is_init res.`5 0 (8 * ((_k + 7) + 1)))) /\
   (valid res.`6))].

op h__MULREG___osreg_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MULREG___osreg_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__MULREG___osreg_muln__spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__MULREG___osreg_muln_ :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].
