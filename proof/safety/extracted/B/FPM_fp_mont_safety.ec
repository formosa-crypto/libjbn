require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array3 Array7 Array14 Array24 Array29 Array56 Array112 Array232 BArray24
BArray56 BArray112 BArray232 SBArray112_56 SBArray232_56 SBArray232_112.

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
  proc h__BN____fill (a:BArray56.t, b_a:BArray56.t, x:W64.t) : BArray56.t *
                                                               BArray56.t *
                                                               trace = {
    var i:int;
    var trace_h__BN____fill:trace;
    trace_h__BN____fill <- [];
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____fill <-
      (trace_h__BN____fill ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_a <- (BArray56.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (BArray56.set64 a i x);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____fill);
  }
  proc h__BN___fill_ (a:BArray56.t, b_a:BArray56.t, x:W64.t) : BArray56.t *
                                                               BArray56.t *
                                                               trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
    (trace_h__BN___fill_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___fill_);
  }
  proc h__BN___set0_ (a:BArray56.t, b_a:BArray56.t) : BArray56.t *
                                                      BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var t:W64.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
    (trace_h__BN___set0_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___set0_);
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
  proc h__MUL__UNR____muln_innerloop (x:BArray24.t, b_x:BArray24.t, k:int,
                                      istart:int, iend:int, a:BArray56.t,
                                      b_a:BArray56.t, b:BArray56.t,
                                      b_b:BArray56.t) : BArray24.t *
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
     (((((((0 <= istart) /\ (iend <= 7)) /\ (0 <= (k - (iend - 1)))) /\
        ((k - istart) < 7)) /\
       (BArray24.is_init b_x 0 24)) /\
      (BArray56.is_init b_a (8 * istart) (8 * (iend - istart)))) /\
     (BArray56.is_init b_b 0 56)))]);
    inc <- iend;
    i <- istart;
    while ((i < inc)) {
      j <- (k - i);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
      [(Assert, (BArray56.is_init b_a (i * 8) 8))]);
      t0 <- (BArray56.get64 a i);
      trace_h__MUL__UNR____muln_innerloop <-
      (trace_h__MUL__UNR____muln_innerloop ++
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
  proc h__MUL__UNR____mont_redM (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                                 b_a:BArray112.t, _P_mP:BArray112.t,
                                 b__P_mP:BArray112.t, _U0:W64.t) : BArray56.t *
                                                                   BArray56.t *
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
    var aux_11:BArray56.t;
    var aux_12:BArray56.t;
    var aux_10:W64.t;
    var aux_9:bool;
    var inc:int;
    var b_x:BArray24.t;
    var x:BArray24.t;
    var b_P:BArray56.t;
    var p:BArray56.t;
    var k:int;
    var b_param:BArray24.t;
    var param:BArray24.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var b_param_0:BArray56.t;
    var param_3:BArray56.t;
    var b_param_1:BArray56.t;
    var param_4:BArray56.t;
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
    var b_param_3:BArray56.t;
    var param_17:BArray56.t;
    var b_param_4:BArray56.t;
    var param_18:BArray56.t;
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
    var b_mP:BArray56.t;
    var mP:BArray56.t;
    var b_param_5:BArray56.t;
    var param_23:BArray56.t;
    var b_param_6:BArray56.t;
    var param_24:BArray56.t;
    var param_25:W64.t;
    var result_4:BArray56.t;
    var b_result_4:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b__P_mP 0 112)))]);
    b_x <- (BArray24.init_arr (W8.of_int 0));
    b_x <- (BArray24.set64d b_x 0 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 0 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 8 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 1 (W64.of_int 0));
    b_x <- (BArray24.set64d b_x 16 (W64.of_int 18446744073709551615));
    x <- (BArray24.set64 x 2 (W64.of_int 0));
    b_P <- (SBArray112_56.get_sub64 b__P_mP 0);
    p <- (SBArray112_56.get_sub64 _P_mP 0);
    k <- 0;
    while ((k < 7)) {
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
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      t0 <- (BArray112.get64 a k);
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
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (k * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r k t0);
      trace_h__MUL__UNR____mont_redM <-
      (trace_h__MUL__UNR____mont_redM ++
      [(Assert, (BArray56.is_init b_P 0 8))]);
      (t1, t0) <- (mulu_64 t0 (BArray56.get64 p 0));
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
    inc <- ((2 * 7) - 1);
    k <- 7;
    while ((k < inc)) {
      b_param_2 <- b_x;
      param_13 <- x;
      param_14 <- k;
      param_15 <- ((k - 7) + 1);
      param_16 <- 7;
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
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      t0 <- (BArray112.get64 a k);
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
      [(Assert, ((0 <= ((k - 7) * 8)) /\ ((((k - 7) * 8) + 8) <= 56)))]);
      b_r <-
      (BArray56.set64d b_r ((k - 7) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r (k - 7) t0);
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
     ((0 <= (((2 * 7) %% 3) * 8)) /\ (((((2 * 7) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x (((2 * 7) %% 3) * 8) 8))]);
    lastbit <- (BArray24.get64 x ((2 * 7) %% 3));
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 7) - 1) %% 3) * 8)) /\
     ((((((2 * 7) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 7) - 1) %% 3) * 8)) /\
     ((((((2 * 7) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 7) - 1) %% 3) * 8) 8))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= (((2 * 7) - 1) * 8)) /\ (((((2 * 7) - 1) * 8) + 8) <= 112)))]);
    b_x <-
    (BArray24.set64d b_x ((((2 * 7) - 1) %% 3) * 8)
    (W64.of_int 18446744073709551615));
    (aux_9, aux_10) <-
    (adc_64 (BArray24.get64 x (((2 * 7) - 1) %% 3))
    (BArray112.get64 a ((2 * 7) - 1)) false);
    cf <- aux_9;
    x <- (BArray24.set64 x (((2 * 7) - 1) %% 3) aux_10);
    ( _1, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert,
     ((0 <= ((((2 * 7) - 1) %% 3) * 8)) /\
     ((((((2 * 7) - 1) %% 3) * 8) + 8) <= 24)))]);
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, (BArray24.is_init b_x ((((2 * 7) - 1) %% 3) * 8) 8))]);
    b_r <-
    (BArray56.set64d b_r ((7 - 1) * 8) (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r (7 - 1) (BArray24.get64 x (((2 * 7) - 1) %% 3)));
    trace_h__MUL__UNR____mont_redM <-
    (trace_h__MUL__UNR____mont_redM ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_mP <- (SBArray112_56.get_sub64 b__P_mP 7);
    mP <- (SBArray112_56.get_sub64 _P_mP 7);
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
    [(Assert, (BArray56.is_init b_result_4 0 56))]);
    r <- result_4;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__UNR____mont_redM);
  }
  proc h__MUL__LOOP____mont_redM (r:BArray56.t, b_r:BArray56.t,
                                  a:BArray112.t, b_a:BArray112.t,
                                  _P_mP:BArray112.t, b__P_mP:BArray112.t,
                                  _U0:W64.t) : BArray56.t * BArray56.t *
                                               trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var i:int;
    var lo:W64.t;
    var c:W64.t;
    var k:W64.t;
    var m:W64.t;
    var hi:W64.t;
    var cf:bool;
    var w:W64.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b__P_mP 0 112)))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      lo <- (BArray112.get64 a i);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i lo);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 7))) {
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, (BArray56.is_init b_r 0 8))]);
      m <- (BArray56.get64 r 0);
      m <- (m * _U0);
      lo <- (BArray112.get64 _P_mP 0);
      (hi, lo) <- (mulu_64 lo m);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, (BArray56.is_init b_r 0 8))]);
      (cf, lo) <- (adc_64 lo (BArray56.get64 r 0) false);
      ( _0, hi) <- (adc_64 hi (W64.of_int 0) cf);
      w <- hi;
      i <- 1;
      while ((i < 7)) {
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
        lo <- (BArray112.get64 _P_mP i);
        (hi, lo) <- (mulu_64 lo m);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, (BArray56.is_init b_r (i * 8) 8))]);
        (cf, lo) <- (adc_64 lo (BArray56.get64 r i) false);
        ( _1, hi) <- (adc_64 hi (W64.of_int 0) cf);
        (cf, lo) <- (adc_64 lo w false);
        ( _2, hi) <- (adc_64 hi (W64.of_int 0) cf);
        trace_h__MUL__LOOP____mont_redM <-
        (trace_h__MUL__LOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 56)))]);
        b_r <-
        (BArray56.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615));
        r <- (BArray56.set64 r (i - 1) lo);
        w <- hi;
        i <- (i + 1);
      }
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 7))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 7))) * 8) + 8) <= 112)))]);
      (cf, w) <-
      (adc_64 w (BArray112.get64 a (W64.to_uint (k + (W64.of_int 7)))) cf);
      trace_h__MUL__LOOP____mont_redM <-
      (trace_h__MUL__LOOP____mont_redM ++
      [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
      b_r <-
      (BArray56.set64d b_r ((7 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r (7 - 1) w);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
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
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++ tmp__trace);
    trace_h__MUL__LOOP____mont_redM <-
    (trace_h__MUL__LOOP____mont_redM ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__LOOP____mont_redM);
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
  proc h__MUL__XLOOP____mont_redM (r:BArray56.t, b_r:BArray56.t,
                                   a:BArray112.t, b_a:BArray112.t,
                                   _P_mP:BArray112.t, b__P_mP:BArray112.t,
                                   _U0:W64.t) : BArray56.t * BArray56.t *
                                                trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b__P_mP 0 112)))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      t <- (BArray112.get64 a i);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 7))) {
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray56.is_init b_r 0 8))]);
      m <- (BArray56.get64 r 0);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray112.get64 _P_mP 0));
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, (BArray56.is_init b_r 0 8))]);
      t <- (BArray56.get64 r 0);
      (of_0, t) <- (ADOX_64 t lo of_0);
      i <- 1;
      while ((i < 7)) {
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, (BArray56.is_init b_r (i * 8) 8))]);
        t <- (BArray56.get64 r i);
        (cf, t) <- (ADCX_64 t hi cf);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
        (hi, lo) <- (MULX_64 m (BArray112.get64 _P_mP i));
        (of_0, t) <- (ADOX_64 t lo of_0);
        trace_h__MUL__XLOOP____mont_redM <-
        (trace_h__MUL__XLOOP____mont_redM ++
        [(Assert, ((0 <= ((i - 1) * 8)) /\ ((((i - 1) * 8) + 8) <= 56)))]);
        b_r <-
        (BArray56.set64d b_r ((i - 1) * 8) (W64.of_int 18446744073709551615));
        r <- (BArray56.set64 r (i - 1) t);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert,
       ((0 <= ((W64.to_uint (k + (W64.of_int 7))) * 8)) /\
       ((((W64.to_uint (k + (W64.of_int 7))) * 8) + 8) <= 112)))]);
      (cf, hi) <-
      (adc_64 hi (BArray112.get64 a (W64.to_uint (k + (W64.of_int 7)))) cf);
      trace_h__MUL__XLOOP____mont_redM <-
      (trace_h__MUL__XLOOP____mont_redM ++
      [(Assert, ((0 <= ((7 - 1) * 8)) /\ ((((7 - 1) * 8) + 8) <= 56)))]);
      b_r <-
      (BArray56.set64d b_r ((7 - 1) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r (7 - 1) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + (W64.of_int 1));
    }
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
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
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++ tmp__trace);
    trace_h__MUL__XLOOP____mont_redM <-
    (trace_h__MUL__XLOOP____mont_redM ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL__XLOOP____mont_redM);
  }
  proc h__MUL__XREG____mont_redM (r:BArray56.t, b_r:BArray56.t,
                                  a:BArray112.t, b_a:BArray112.t,
                                  _P_mP:BArray112.t, b__P_mP:BArray112.t,
                                  _U0:W64.t) : BArray56.t * BArray56.t *
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
    var b_w:BArray112.t;
    var b_s:BArray56.t;
    var i:int;
    var w:BArray112.t;
    var c:W64.t;
    var k:int;
    var m:W64.t;
    var of_0:bool;
    var cf:bool;
    var _zero:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var s:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b__P_mP 0 112)))]);
    b_w <- (BArray112.init_arr (W8.of_int 0));
    b_s <- (BArray56.init_arr (W8.of_int 0));
    i <- 0;
    while ((i < 7)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      b_w <-
      (BArray112.set64d b_w (i * 8) (W64.of_int 18446744073709551615));
      w <- (BArray112.set64 w i (BArray112.get64 a i));
      i <- (i + 1);
    }
    c <- (W64.of_int 0);
    k <- 0;
    while ((k < 7)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray112.is_init b_w (k * 8) 8))]);
      m <- (BArray112.get64 w k);
      m <- (m * _U0);
      (of_0, cf,  _0,  _1,  _2, _zero) <- (set0_64);
      (hi, lo) <- (MULX_64 m (BArray112.get64 _P_mP 0));
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (k * 8)) /\ (((k * 8) + 8) <= 112)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray112.is_init b_w (k * 8) 8))]);
      b_w <-
      (BArray112.set64d b_w (k * 8) (W64.of_int 18446744073709551615));
      (aux, aux_0) <- (ADOX_64 (BArray112.get64 w k) lo of_0);
      of_0 <- aux;
      w <- (BArray112.set64 w k aux_0);
      i <- 1;
      while ((i < 7)) {
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, (BArray112.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray112.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_1, aux_2) <- (ADCX_64 (BArray112.get64 w (k + i)) hi cf);
        cf <- aux_1;
        w <- (BArray112.set64 w (k + i) aux_2);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
        (hi, lo) <- (MULX_64 m (BArray112.get64 _P_mP i));
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + i) * 8)) /\ ((((k + i) * 8) + 8) <= 112)))]);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, (BArray112.is_init b_w ((k + i) * 8) 8))]);
        b_w <-
        (BArray112.set64d b_w ((k + i) * 8) (W64.of_int 18446744073709551615)
        );
        (aux_3, aux_4) <- (ADOX_64 (BArray112.get64 w (k + i)) lo of_0);
        of_0 <- aux_3;
        w <- (BArray112.set64 w (k + i) aux_4);
        i <- (i + 1);
      }
      (cf, hi) <- (ADCX_64 hi _zero cf);
      (of_0, hi) <- (ADOX_64 hi _zero of_0);
      if ((k = 0)) {
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
        (cf, hi) <- (adc_64 hi (BArray112.get64 a 7) false);
      } else {
        ( _3, cf,  _4,  _5,  _6, c) <- (NEG_64 c);
        trace_h__MUL__XREG____mont_redM <-
        (trace_h__MUL__XREG____mont_redM ++
        [(Assert, ((0 <= ((k + 7) * 8)) /\ ((((k + 7) * 8) + 8) <= 112)))]);
        (cf, hi) <- (adc_64 hi (BArray112.get64 a (k + 7)) cf);
      }
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((k + 7) * 8)) /\ ((((k + 7) * 8) + 8) <= 112)))]);
      b_w <-
      (BArray112.set64d b_w ((k + 7) * 8) (W64.of_int 18446744073709551615));
      w <- (BArray112.set64 w (k + 7) hi);
      c <- (MOV_64 (W64.of_int 0));
      ( _7, c) <- (adc_64 c (W64.of_int 0) cf);
      k <- (k + 1);
    }
    i <- 0;
    while ((i < 7)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((7 + i) * 8)) /\ ((((7 + i) * 8) + 8) <= 112)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray112.is_init b_w ((7 + i) * 8) 8))]);
      b_s <- (BArray56.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      s <- (BArray56.set64 s i (BArray112.get64 w (7 + i)));
      i <- (i + 1);
    }
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert, (BArray56.is_init b_s 0 8))]);
    trace_h__MUL__XREG____mont_redM <-
    (trace_h__MUL__XREG____mont_redM ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 112)))]);
    b_s <- (BArray56.set64d b_s 0 (W64.of_int 18446744073709551615));
    (aux_5, aux_6) <-
    (adc_64 (BArray56.get64 s 0) (BArray112.get64 _P_mP 7) false);
    cf <- aux_5;
    s <- (BArray56.set64 s 0 aux_6);
    i <- 1;
    while ((i < 7)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray56.is_init b_s (i * 8) 8))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((7 + i) * 8)) /\ ((((7 + i) * 8) + 8) <= 112)))]);
      b_s <- (BArray56.set64d b_s (i * 8) (W64.of_int 18446744073709551615));
      (aux_7, aux_8) <-
      (adc_64 (BArray56.get64 s i) (BArray112.get64 _P_mP (7 + i)) cf);
      cf <- aux_7;
      s <- (BArray56.set64 s i aux_8);
      i <- (i + 1);
    }
    ( _8, c) <- (adc_64 c (W64.of_int 0) cf);
    ( _9, cf,  _10,  _11,  _12,  _13) <- (NEG_64 c);
    i <- 0;
    while ((i < 7)) {
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= ((7 + i) * 8)) /\ ((((7 + i) * 8) + 8) <= 112)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray112.is_init b_w ((7 + i) * 8) 8))]);
      x <- (BArray112.get64 w (7 + i));
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, (BArray56.is_init b_s (i * 8) 8))]);
      x <- (cf ? (BArray56.get64 s i) : x);
      trace_h__MUL__XREG____mont_redM <-
      (trace_h__MUL__XREG____mont_redM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i x);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__MUL__XREG____mont_redM);
  }
  proc h__MUL____mont_redM (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                            b_a:BArray112.t, _P_mP:BArray112.t,
                            b__P_mP:BArray112.t, _U0:W64.t) : BArray56.t *
                                                              BArray56.t *
                                                              trace = {
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
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray112.t;
    var param_1:BArray112.t;
    var param_2:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var b_param_0:BArray56.t;
    var param_3:BArray56.t;
    var param_4:BArray112.t;
    var param_5:BArray112.t;
    var param_6:W64.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var b_param_1:BArray56.t;
    var param_7:BArray56.t;
    var param_8:BArray112.t;
    var param_9:BArray112.t;
    var param_10:W64.t;
    var result_1:BArray56.t;
    var b_result_1:BArray56.t;
    var b_param_2:BArray56.t;
    var param_11:BArray56.t;
    var param_12:BArray112.t;
    var param_13:BArray112.t;
    var param_14:W64.t;
    var result_2:BArray56.t;
    var b_result_2:BArray56.t;
    var b_param_3:BArray56.t;
    var param_15:BArray56.t;
    var param_16:BArray112.t;
    var param_17:BArray112.t;
    var param_18:W64.t;
    var result_3:BArray56.t;
    var b_result_3:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray112.is_init b__P_mP 0 112)))]);
    if ((((W256.of_int 51) `&` (W256.of_int 3)) = (W256.of_int 3))) {
      if ((7 <= 18)) {
        b_param <- b_r;
        param <- r;
        param_0 <- a;
        param_1 <- _P_mP;
        param_2 <- _U0;
        (aux_7, aux_8, tmp__trace) <@ h__MUL__XREG____mont_redM (param,
        b_param, param_0, (BArray112.init_arr (W8.of_int 255)), param_1,
        (BArray112.init_arr (W8.of_int 255)), param_2);
        result <- aux_7;
        b_result <- aux_8;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray56.is_init b_result 0 56))]);
        r <- result;
      } else {
        if ((7 <= 12)) {
          b_param_0 <- b_r;
          param_3 <- r;
          param_4 <- a;
          param_5 <- _P_mP;
          param_6 <- _U0;
          (aux_5, aux_6, tmp__trace) <@ h__MUL__XUNR____mont_redM (param_3,
          b_param_0, param_4, (BArray112.init_arr (W8.of_int 255)), param_5,
          (BArray112.init_arr (W8.of_int 255)), param_6);
          result_0 <- aux_5;
          b_result_0 <- aux_6;
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++ tmp__trace);
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++
          [(Assert, (BArray56.is_init b_result_0 0 56))]);
          r <- result_0;
        } else {
          b_param_1 <- b_r;
          param_7 <- r;
          param_8 <- a;
          param_9 <- _P_mP;
          param_10 <- _U0;
          (aux_3, aux_4, tmp__trace) <@ h__MUL__XLOOP____mont_redM (param_7,
          b_param_1, param_8, (BArray112.init_arr (W8.of_int 255)), param_9,
          (BArray112.init_arr (W8.of_int 255)), param_10);
          result_1 <- aux_3;
          b_result_1 <- aux_4;
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++ tmp__trace);
          trace_h__MUL____mont_redM <-
          (trace_h__MUL____mont_redM ++
          [(Assert, (BArray56.is_init b_result_1 0 56))]);
          r <- result_1;
        }
      }
    } else {
      if ((7 <= 12)) {
        b_param_2 <- b_r;
        param_11 <- r;
        param_12 <- a;
        param_13 <- _P_mP;
        param_14 <- _U0;
        (aux_1, aux_2, tmp__trace) <@ h__MUL__UNR____mont_redM (param_11,
        b_param_2, param_12, (BArray112.init_arr (W8.of_int 255)), param_13,
        (BArray112.init_arr (W8.of_int 255)), param_14);
        result_2 <- aux_1;
        b_result_2 <- aux_2;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray56.is_init b_result_2 0 56))]);
        r <- result_2;
      } else {
        b_param_3 <- b_r;
        param_15 <- r;
        param_16 <- a;
        param_17 <- _P_mP;
        param_18 <- _U0;
        (aux, aux_0, tmp__trace) <@ h__MUL__LOOP____mont_redM (param_15,
        b_param_3, param_16, (BArray112.init_arr (W8.of_int 255)), param_17,
        (BArray112.init_arr (W8.of_int 255)), param_18);
        result_3 <- aux;
        b_result_3 <- aux_0;
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++ tmp__trace);
        trace_h__MUL____mont_redM <-
        (trace_h__MUL____mont_redM ++
        [(Assert, (BArray56.is_init b_result_3 0 56))]);
        r <- result_3;
      }
    }
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__MUL____mont_redM);
  }
  proc h__FPM__fun_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                         b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var trace_h__FPM__fun_muln:trace;
    trace_h__FPM__fun_muln <- [];
    trace_h__FPM__fun_muln <-
    (trace_h__FPM__fun_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    return (r, b_r, trace_h__FPM__fun_muln);
  }
  proc h__FPM__fun_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                         b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var trace_h__FPM__fun_sqrn:trace;
    trace_h__FPM__fun_sqrn <- [];
    trace_h__FPM__fun_sqrn <-
    (trace_h__FPM__fun_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    return (r, b_r, trace_h__FPM__fun_sqrn);
  }
  proc h__FPM___redM (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                      b_a:BArray112.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var t:W64.t;
    var _u0:W64.t;
    var b_PmP:BArray112.t;
    var pmP:BArray112.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray112.t;
    var b_param_0:BArray112.t;
    var param_1:BArray112.t;
    var param_2:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert, ((0 <= (28 * 8)) /\ (((28 * 8) + 8) <= 232)))]);
    t <- (BArray232.get64 ctx 28);
    _u0 <- t;
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 112) <= 232)))]);
    b_PmP <- (SBArray232_112.get_sub64 b_ctx 0);
    pmP <- (SBArray232_112.get_sub64 ctx 0);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    b_param_0 <- b_PmP;
    param_1 <- pmP;
    param_2 <- _u0;
    (aux, aux_0, tmp__trace) <@ h__MUL____mont_redM (param, b_param, 
    param_0, (BArray112.init_arr (W8.of_int 255)), param_1, b_param_0,
    param_2);
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___redM <- (trace_h__FPM___redM ++ tmp__trace);
    trace_h__FPM___redM <-
    (trace_h__FPM___redM ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___redM);
  }
  proc h__FPM___redM_ (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                       b_a:BArray112.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray112.t;
    var param_1:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    ctx <- ctx;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___redM (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___redM_ <- (trace_h__FPM___redM_ ++ tmp__trace);
    trace_h__FPM___redM_ <-
    (trace_h__FPM___redM_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___redM_);
  }
  proc h__FPM___fromM_ (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                        b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_4:BArray56.t;
    var b__tmp:BArray112.t;
    var b_tmp2:BArray56.t;
    var tmp2:BArray56.t;
    var _tmp:BArray112.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var b_param_0:BArray56.t;
    var param_1:BArray56.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var b_tmp:BArray112.t;
    var tmp:BArray112.t;
    var param_2:BArray56.t;
    var b_param_1:BArray112.t;
    var param_3:BArray112.t;
    var param_4:BArray232.t;
    var result_1:BArray56.t;
    var b_result_1:BArray56.t;
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
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    b_tmp2 <- (SBArray112_56.get_sub64 b__tmp 0);
    tmp2 <- (SBArray112_56.get_sub64 _tmp 0);
    b_param <- b_tmp2;
    param <- tmp2;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    tmp2 <- result;
    b__tmp <-
    (SBArray112_56.set_sub64 b__tmp 0 (BArray56.init_arr (W8.of_int 255)));
    _tmp <- (SBArray112_56.set_sub64 _tmp 0 tmp2);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b_tmp2 <- (SBArray112_56.get_sub64 b__tmp 7);
    tmp2 <- (SBArray112_56.get_sub64 _tmp 7);
    b_param_0 <- b_tmp2;
    param_1 <- tmp2;
    (aux_1, aux_2, tmp__trace) <@ h__BN___set0_ (param_1, b_param_0);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    tmp2 <- result_0;
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 112)))]);
    b__tmp <-
    (SBArray112_56.set_sub64 b__tmp 7 (BArray56.init_arr (W8.of_int 255)));
    _tmp <- (SBArray112_56.set_sub64 _tmp 7 tmp2);
    b_tmp <- b__tmp;
    tmp <- _tmp;
    param_2 <- a;
    b_param_1 <- b_tmp;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_3, aux_4, tmp__trace) <@ h__FPM___redM_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3, b_param_1, param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    trace_h__FPM___fromM_ <- (trace_h__FPM___fromM_ ++ tmp__trace);
    trace_h__FPM___fromM_ <-
    (trace_h__FPM___fromM_ ++ [(Assert, (BArray56.is_init b_result_1 0 56))]);
    a <- result_1;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___fromM_);
  }
  proc h__FPM__fun_red (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                        b_a:BArray112.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray112.t;
    var param_1:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___redM_ (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM__fun_red <- (trace_h__FPM__fun_red ++ tmp__trace);
    trace_h__FPM__fun_red <-
    (trace_h__FPM__fun_red ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM__fun_red);
  }
  proc h__FPM___addm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
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
    trace_h__FPM___addm_ <- (trace_h__FPM___addm_ ++ tmp__trace);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    lastbit <- (W64.of_int 0);
    ( _0, lastbit) <- (adc_64 lastbit (W64.of_int 0) cf);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++
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
    trace_h__FPM___addm_ <- (trace_h__FPM___addm_ ++ tmp__trace);
    trace_h__FPM___addm_ <-
    (trace_h__FPM___addm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_1;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPM___addm_);
  }
  proc h__FPM___mulmU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
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
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FPM__fun_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___mulmU_ <- (trace_h__FPM___mulmU_ ++ tmp__trace);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPM__fun_red (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray112.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPM___mulmU_ <- (trace_h__FPM___mulmU_ ++ tmp__trace);
    trace_h__FPM___mulmU_ <-
    (trace_h__FPM___mulmU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___mulmU_);
  }
  proc h__FPM___toM_ (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                      b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var b_R2:BArray56.t;
    var r2:BArray56.t;
    var param:BArray56.t;
    var b_param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray232.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
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
    (trace_h__FPM___toM_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++
    [(Assert, ((0 <= (21 * 8)) /\ (((21 * 8) + 56) <= 232)))]);
    b_R2 <- (SBArray232_56.get_sub64 b_ctx 21);
    r2 <- (SBArray232_56.get_sub64 ctx 21);
    param <- a;
    b_param <- b_R2;
    param_0 <- r2;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPM___mulmU_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0, b_param, param_1,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___toM_ <- (trace_h__FPM___toM_ ++ tmp__trace);
    trace_h__FPM___toM_ <-
    (trace_h__FPM___toM_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPM___toM_);
  }
  proc h__FPM___ctx_init_ (ctx:BArray232.t, b_ctx:BArray232.t, p:BArray56.t,
                           b_P:BArray56.t) : BArray232.t * BArray232.t *
                                             trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_4:BArray56.t;
    var aux_5:BArray56.t;
    var aux_6:BArray56.t;
    var aux_7:BArray56.t;
    var aux_8:BArray56.t;
    var aux_9:BArray56.t;
    var aux_10:BArray56.t;
    var aux_11:BArray56.t;
    var aux_12:BArray56.t;
    var aux_13:BArray56.t;
    var aux_14:BArray56.t;
    var aux_15:BArray56.t;
    var aux_16:BArray56.t;
    var aux_17:BArray56.t;
    var aux_1:bool;
    var b__x:BArray56.t;
    var b__y:BArray56.t;
    var b_t:BArray56.t;
    var t:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var b_param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:BArray56.t;
    var result_0:bool;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var p0:W64.t;
    var inv:W64.t;
    var j:int;
    var d:W64.t;
    var u0:W64.t;
    var b_x:BArray56.t;
    var x:BArray56.t;
    var _x:BArray56.t;
    var b_param_1:BArray56.t;
    var param_3:BArray56.t;
    var result_2:BArray56.t;
    var b_result_1:BArray56.t;
    var i:W64.t;
    var _i:W64.t;
    var b_y:BArray56.t;
    var y:BArray56.t;
    var _y:BArray56.t;
    var b_param_2:BArray56.t;
    var param_4:BArray56.t;
    var param_5:BArray56.t;
    var param_6:BArray56.t;
    var b_param_3:BArray232.t;
    var param_7:BArray232.t;
    var result_3:BArray56.t;
    var b_result_2:BArray56.t;
    var param_8:BArray56.t;
    var param_9:BArray56.t;
    var param_10:BArray56.t;
    var b_param_4:BArray232.t;
    var param_11:BArray232.t;
    var result_4:BArray56.t;
    var b_result_3:BArray56.t;
    var b_param_5:BArray56.t;
    var param_12:BArray56.t;
    var param_13:BArray56.t;
    var result_5:BArray56.t;
    var b_result_4:BArray56.t;
    var b_param_6:BArray56.t;
    var param_14:BArray56.t;
    var param_15:BArray56.t;
    var param_16:BArray56.t;
    var b_param_7:BArray232.t;
    var param_17:BArray232.t;
    var result_6:BArray56.t;
    var b_result_5:BArray56.t;
    var param_18:BArray56.t;
    var param_19:BArray56.t;
    var param_20:BArray56.t;
    var b_param_8:BArray232.t;
    var param_21:BArray232.t;
    var result_7:BArray56.t;
    var b_result_6:BArray56.t;
    var b_param_9:BArray56.t;
    var param_22:BArray56.t;
    var param_23:BArray56.t;
    var result_8:BArray56.t;
    var b_result_7:BArray56.t;
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
    (trace_h__FPM___ctx_init_ ++ [(Assert, (BArray56.is_init b_P 0 56))]);
    b__x <- (BArray56.init_arr (W8.of_int 0));
    b__y <- (BArray56.init_arr (W8.of_int 0));
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 56) <= 232)))]);
    b_t <- (SBArray232_56.get_sub64 b_ctx 0);
    t <- (SBArray232_56.get_sub64 ctx 0);
    b_param <- b_t;
    param <- t;
    param_0 <- p;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    t <- result;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 0 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 0 t);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_t <- (SBArray232_56.get_sub64 b_ctx 7);
    t <- (SBArray232_56.get_sub64 ctx 7);
    b_param_0 <- b_t;
    param_1 <- t;
    param_2 <- p;
    (aux_1, aux_2, aux_3, tmp__trace) <@ h__BN___neg_ (param_1, b_param_0,
    param_2, (BArray56.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    result_1 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    t <- result_1;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 7 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 7 t);
    p0 <- (BArray56.get64 p 0);
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
    [(Assert, ((0 <= (28 * 8)) /\ (((28 * 8) + 8) <= 232)))]);
    b_ctx <-
    (BArray232.set64d b_ctx (28 * 8) (W64.of_int 18446744073709551615));
    ctx <- (BArray232.set64 ctx 28 u0);
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
    [(Assert, (BArray56.is_init b_result_1 0 56))]);
    x <- result_2;
    x <- (BArray56.set64 x 0 (W64.of_int 1));
    _x <- x;
    i <- (W64.of_int (32 * 7));
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
      param_5, (BArray56.init_arr (W8.of_int 255)), param_6,
      (BArray56.init_arr (W8.of_int 255)), param_7, b_param_3);
      result_3 <- aux_6;
      b_result_2 <- aux_7;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray56.is_init b_result_2 0 56))]);
      y <- result_3;
      b__y <- (BArray56.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_8 <- x;
      param_9 <- y;
      param_10 <- y;
      b_param_4 <- b_ctx;
      param_11 <- ctx;
      (aux_8, aux_9, tmp__trace) <@ h__FPM___addm_ (param_8,
      (BArray56.init_arr (W8.of_int 255)), param_9,
      (BArray56.init_arr (W8.of_int 255)), param_10,
      (BArray56.init_arr (W8.of_int 255)), param_11, b_param_4);
      result_4 <- aux_8;
      b_result_3 <- aux_9;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray56.is_init b_result_3 0 56))]);
      x <- result_4;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 56) <= 232)))]);
    b_t <- (SBArray232_56.get_sub64 b_ctx 14);
    t <- (SBArray232_56.get_sub64 ctx 14);
    b_param_5 <- b_t;
    param_12 <- t;
    param_13 <- x;
    (aux_10, aux_11, tmp__trace) <@ h__BN___mov_ (param_12, b_param_5,
    param_13, (BArray56.init_arr (W8.of_int 255)));
    result_5 <- aux_10;
    b_result_4 <- aux_11;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_4 0 56))]);
    t <- result_5;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 14 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 14 t);
    i <- (W64.of_int (32 * 7));
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
      param_15, (BArray56.init_arr (W8.of_int 255)), param_16,
      (BArray56.init_arr (W8.of_int 255)), param_17, b_param_7);
      result_6 <- aux_12;
      b_result_5 <- aux_13;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray56.is_init b_result_5 0 56))]);
      y <- result_6;
      b__y <- (BArray56.init_arr (W8.of_int 255));
      _y <- y;
      x <- _x;
      y <- _y;
      param_18 <- x;
      param_19 <- y;
      param_20 <- y;
      b_param_8 <- b_ctx;
      param_21 <- ctx;
      (aux_14, aux_15, tmp__trace) <@ h__FPM___addm_ (param_18,
      (BArray56.init_arr (W8.of_int 255)), param_19,
      (BArray56.init_arr (W8.of_int 255)), param_20,
      (BArray56.init_arr (W8.of_int 255)), param_21, b_param_8);
      result_7 <- aux_14;
      b_result_6 <- aux_15;
      trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
      trace_h__FPM___ctx_init_ <-
      (trace_h__FPM___ctx_init_ ++
      [(Assert, (BArray56.is_init b_result_6 0 56))]);
      x <- result_7;
      _x <- x;
      i <- _i;
      i <- (i - (W64.of_int 1));
    }
    x <- _x;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (21 * 8)) /\ (((21 * 8) + 56) <= 232)))]);
    b_t <- (SBArray232_56.get_sub64 b_ctx 21);
    t <- (SBArray232_56.get_sub64 ctx 21);
    b_param_9 <- b_t;
    param_22 <- t;
    param_23 <- x;
    (aux_16, aux_17, tmp__trace) <@ h__BN___mov_ (param_22, b_param_9,
    param_23, (BArray56.init_arr (W8.of_int 255)));
    result_8 <- aux_16;
    b_result_7 <- aux_17;
    trace_h__FPM___ctx_init_ <- (trace_h__FPM___ctx_init_ ++ tmp__trace);
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_7 0 56))]);
    t <- result_8;
    trace_h__FPM___ctx_init_ <-
    (trace_h__FPM___ctx_init_ ++
    [(Assert, ((0 <= (21 * 8)) /\ (((21 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 21 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 21 t);
    return (ctx, b_ctx, trace_h__FPM___ctx_init_);
  }
}.

(* The post and trace are valid. *)

op uTIL____addacc3_spec _a _b_a _b1 _b0 _k =
   hoare [M.uTIL____addacc3 :
   (((_k = k) /\ ((_b0 = b0) /\ ((_b1 = b1) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   (BArray24.is_init _b_a 0 24)) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

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

op h__BN____fill_spec _a _b_a _x =
   hoare [M.h__BN____fill :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__BN___fill__spec _a _b_a _x =
   hoare [M.h__BN___fill_ :
   (((_x = x) /\ ((_b_a = b_a) /\ (_a = a))) /\ true) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__BN___set0__spec _a _b_a =
   hoare [M.h__BN___set0_ :
   (((_b_a = b_a) /\ (_a = a)) /\ true) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

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

op h__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit =
   hoare [M.h__BN___cminusP_ :
   (((_lastbit = lastbit) /\
    ((_b_mP = b_mP) /\ ((_mP = mP) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_mP 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

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
   (((((((0 <= _istart) /\ (_iend <= 7)) /\ (0 <= (_k - (_iend - 1)))) /\
      ((_k - _istart) < 7)) /\
     (BArray24.is_init _b_x 0 24)) /\
    (BArray56.is_init _b_a (8 * _istart) (8 * (_iend - _istart)))) /\
   (BArray56.is_init _b_b 0 (8 * 7))))))))))))) ==>
   ((BArray24.is_init res.`2 0 24) /\ (valid res.`3))].

op h__MUL__UNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__UNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__MUL__LOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__LOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__MUL__XUNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XUNR____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__MUL__XLOOP____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XLOOP____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__MUL__XREG____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL__XREG____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__MUL____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0 =
   hoare [M.h__MUL____mont_redM :
   (((__U0 = _U0) /\
    ((_b__P_mP = b__P_mP) /\
    ((__P_mP = _P_mP) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray112.is_init _b__P_mP 0 (16 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPM__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FPM__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FPM__fun_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__FPM__fun_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FPM___redM_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___redM :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPM___redM__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___redM_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPM___fromM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___fromM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FPM__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPM___addm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___addm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx (8 * 7) (8 * 7)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPM___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPM___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FPM___toM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPM___toM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FPM___ctx_init__spec _ctx _b_ctx _p _b_P =
   hoare [M.h__FPM___ctx_init_ :
   (((_b_P = b_P) /\ ((_p = p) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray56.is_init _b_P 0 (8 * 7))) ==>
   ((BArray232.is_init res.`2 0 (8 * 29)) /\ (valid res.`3))].
