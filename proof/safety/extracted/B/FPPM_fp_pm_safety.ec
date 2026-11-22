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
  proc h__FPPM__fun_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                          b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var trace_h__FPPM__fun_muln:trace;
    trace_h__FPPM__fun_muln <- [];
    trace_h__FPPM__fun_muln <-
    (trace_h__FPPM__fun_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    return (r, b_r, trace_h__FPPM__fun_muln);
  }
  proc h__FPPM__fun_sqrn (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                          b_a:BArray56.t) : BArray112.t * BArray112.t * trace = {
    var trace_h__FPPM__fun_sqrn:trace;
    trace_h__FPPM__fun_sqrn <- [];
    trace_h__FPPM__fun_sqrn <-
    (trace_h__FPPM__fun_sqrn ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    return (r, b_r, trace_h__FPPM__fun_sqrn);
  }
  proc h__FPPM___redPM (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                        b_a:BArray112.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var b__s:BArray56.t;
    var c:W64.t;
    var t:W64.t;
    var i:int;
    var l:W64.t;
    var h:W64.t;
    var cf:bool;
    var x:W64.t;
    var param:bool;
    var result:W64.t;
    var mask:W64.t;
    var j:int;
    var _s:BArray56.t;
    var  _0:bool;
    var  _1:bool;
    var trace_h__FPPM___redPM:trace;
    _s <- witness;
    b__s <- witness;
    trace_h__FPPM___redPM <- [];
    trace_h__FPPM___redPM <-
    (trace_h__FPPM___redPM ++
    [(Assert,
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    b__s <- (BArray56.init_arr (W8.of_int 0));
    trace_h__FPPM___redPM <-
    (trace_h__FPPM___redPM ++
    [(Assert, ((0 <= (28 * 8)) /\ (((28 * 8) + 8) <= 232)))]);
    c <- (BArray232.get64 ctx 28);
    t <- (W64.of_int 0);
    i <- 0;
    while ((i < 7)) {
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++
      [(Assert, ((0 <= ((7 + i) * 8)) /\ ((((7 + i) * 8) + 8) <= 112)))]);
      l <- (BArray112.get64 a (7 + i));
      (h, l) <- (mulu_64 l c);
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      (cf, l) <- (adc_64 l (BArray112.get64 a i) false);
      ( _0, h) <- (adc_64 h (W64.of_int 0) cf);
      (cf, l) <- (adc_64 l t false);
      ( _1, h) <- (adc_64 h (W64.of_int 0) cf);
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i l);
      t <- h;
      i <- (i + 1);
    }
    t <- (t * c);
    trace_h__FPPM___redPM <-
    (trace_h__FPPM___redPM ++ [(Assert, (BArray56.is_init b_r 0 8))]);
    x <- (BArray56.get64 r 0);
    (cf, x) <- (adc_64 x t false);
    b_r <- (BArray56.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r 0 x);
    i <- 1;
    while ((i < 7)) {
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++ [(Assert, (BArray56.is_init b_r (i * 8) 8))]);
      x <- (BArray56.get64 r i);
      (cf, x) <- (adc_64 x (W64.of_int 0) cf);
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i x);
      i <- (i + 1);
    }
    param <- cf;
    (result, tmp__trace) <@ uTIL____cf_mask (param);
    trace_h__FPPM___redPM <- (trace_h__FPPM___redPM ++ tmp__trace);
    mask <- result;
    mask <- (mask `&` c);
    trace_h__FPPM___redPM <-
    (trace_h__FPPM___redPM ++ [(Assert, (BArray56.is_init b_r 0 8))]);
    x <- (BArray56.get64 r 0);
    x <- (x + mask);
    b_r <- (BArray56.set64d b_r 0 (W64.of_int 18446744073709551615));
    r <- (BArray56.set64 r 0 x);
    j <- 0;
    while ((j < 2)) {
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++ [(Assert, (BArray56.is_init b_r 0 8))]);
      x <- (BArray56.get64 r 0);
      trace_h__FPPM___redPM <-
      (trace_h__FPPM___redPM ++
      [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 8) <= 232)))]);
      (cf, x) <- (adc_64 x (BArray232.get64 ctx 7) false);
      b__s <- (BArray56.set64d b__s 0 (W64.of_int 18446744073709551615));
      _s <- (BArray56.set64 _s 0 x);
      i <- 1;
      while ((i < 7)) {
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, (BArray56.is_init b_r (i * 8) 8))]);
        x <- (BArray56.get64 r i);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, ((0 <= ((7 + i) * 8)) /\ ((((7 + i) * 8) + 8) <= 232)))]);
        (cf, x) <- (adc_64 x (BArray232.get64 ctx (7 + i)) cf);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        b__s <-
        (BArray56.set64d b__s (i * 8) (W64.of_int 18446744073709551615));
        _s <- (BArray56.set64 _s i x);
        i <- (i + 1);
      }
      i <- 0;
      while ((i < 7)) {
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, (BArray56.is_init b_r (i * 8) 8))]);
        x <- (BArray56.get64 r i);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, (BArray56.is_init b__s (i * 8) 8))]);
        x <- (cf ? (BArray56.get64 _s i) : x);
        trace_h__FPPM___redPM <-
        (trace_h__FPPM___redPM ++
        [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
        b_r <-
        (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
        r <- (BArray56.set64 r i x);
        i <- (i + 1);
      }
      j <- (j + 1);
    }
    return (r, b_r, trace_h__FPPM___redPM);
  }
  proc h__FPPM___redPM_ (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
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
    var trace_h__FPPM___redPM_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPPM___redPM_ <- [];
    trace_h__FPPM___redPM_ <-
    (trace_h__FPPM___redPM_ ++
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
    (aux, aux_0, tmp__trace) <@ h__FPPM___redPM (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPPM___redPM_ <- (trace_h__FPPM___redPM_ ++ tmp__trace);
    trace_h__FPPM___redPM_ <-
    (trace_h__FPPM___redPM_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    r <- r;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPPM___redPM_);
  }
  proc h__FPPM___fromM_ (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                         b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var trace_h__FPPM___fromM_:trace;
    trace_h__FPPM___fromM_ <- [];
    trace_h__FPPM___fromM_ <-
    (trace_h__FPPM___fromM_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FPPM___fromM_ <-
    (trace_h__FPPM___fromM_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPPM___fromM_);
  }
  proc h__FPPM__fun_red (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
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
    var trace_h__FPPM__fun_red:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__FPPM__fun_red <- [];
    trace_h__FPPM__fun_red <-
    (trace_h__FPPM__fun_red ++
    [(Assert,
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    param_1 <- ctx;
    (aux, aux_0, tmp__trace) <@ h__FPPM___redPM_ (param, b_param, param_0,
    (BArray112.init_arr (W8.of_int 255)), param_1,
    (BArray232.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPPM__fun_red <- (trace_h__FPPM__fun_red ++ tmp__trace);
    trace_h__FPPM__fun_red <-
    (trace_h__FPPM__fun_red ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    r <- result;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPPM__fun_red);
  }
  proc h__FPPM___mulm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
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
    var trace_h__FPPM___mulm_:trace;
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
    trace_h__FPPM___mulm_ <- [];
    trace_h__FPPM___mulm_ <-
    (trace_h__FPPM___mulm_ ++
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
    (aux, aux_0, tmp__trace) <@ h__FPPM__fun_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FPPM___mulm_ <- (trace_h__FPPM___mulm_ ++ tmp__trace);
    trace_h__FPPM___mulm_ <-
    (trace_h__FPPM___mulm_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_2 <- r;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FPPM__fun_red (param_2, b_param_0,
    param_3, (BArray112.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FPPM___mulm_ <- (trace_h__FPPM___mulm_ ++ tmp__trace);
    trace_h__FPPM___mulm_ <-
    (trace_h__FPPM___mulm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FPPM___mulm_);
  }
  proc h__FPPM___toM_ (a:BArray56.t, b_a:BArray56.t, ctx:BArray232.t,
                       b_ctx:BArray232.t) : BArray56.t * BArray56.t * trace = {
    var trace_h__FPPM___toM_:trace;
    trace_h__FPPM___toM_ <- [];
    trace_h__FPPM___toM_ <-
    (trace_h__FPPM___toM_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FPPM___toM_ <-
    (trace_h__FPPM___toM_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FPPM___toM_);
  }
  proc h__FPPM___ctx_init_ (ctx:BArray232.t, b_ctx:BArray232.t, p:BArray56.t,
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
    var aux_1:bool;
    var b__x:BArray56.t;
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
    var b_param_1:BArray56.t;
    var param_3:BArray56.t;
    var result_2:BArray56.t;
    var b_result_1:BArray56.t;
    var b_param_2:BArray56.t;
    var param_4:BArray56.t;
    var result_3:BArray56.t;
    var b_result_2:BArray56.t;
    var b_x:BArray56.t;
    var x:BArray56.t;
    var _x:BArray56.t;
    var b_mP:BArray56.t;
    var mP:BArray56.t;
    var b_param_3:BArray56.t;
    var param_5:BArray56.t;
    var b_param_4:BArray56.t;
    var param_6:BArray56.t;
    var result_4:BArray56.t;
    var b_result_3:BArray56.t;
    var z:W64.t;
    var param_7:BArray56.t;
    var b_param_5:BArray56.t;
    var param_8:BArray56.t;
    var param_9:W64.t;
    var result_5:BArray56.t;
    var b_result_4:BArray56.t;
    var c:W64.t;
    var trace_h__FPPM___ctx_init_:trace;
    _x <- witness;
    b__x <- witness;
    b_mP <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_param_2 <- witness;
    b_param_3 <- witness;
    b_param_4 <- witness;
    b_param_5 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_t <- witness;
    b_x <- witness;
    mP <- witness;
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
    result_1 <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    t <- witness;
    x <- witness;
    trace_h__FPPM___ctx_init_ <- [];
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++ [(Assert, (BArray56.is_init b_P 0 56))]);
    b__x <- (BArray56.init_arr (W8.of_int 0));
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
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
    trace_h__FPPM___ctx_init_ <- (trace_h__FPPM___ctx_init_ ++ tmp__trace);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    t <- result;
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (0 * 8)) /\ (((0 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 0 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 0 t);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
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
    trace_h__FPPM___ctx_init_ <- (trace_h__FPPM___ctx_init_ ++ tmp__trace);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    t <- result_1;
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 7 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 7 t);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 56) <= 232)))]);
    b_t <- (SBArray232_56.get_sub64 b_ctx 14);
    t <- (SBArray232_56.get_sub64 ctx 14);
    b_param_1 <- b_t;
    param_3 <- t;
    (aux_4, aux_5, tmp__trace) <@ h__BN___set0_ (param_3, b_param_1);
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_h__FPPM___ctx_init_ <- (trace_h__FPPM___ctx_init_ ++ tmp__trace);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_1 0 56))]);
    t <- result_2;
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 14 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 14 t);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (14 * 8)) /\ (((14 * 8) + 8) <= 232)))]);
    b_ctx <-
    (BArray232.set64d b_ctx (14 * 8) (W64.of_int 18446744073709551615));
    ctx <- (BArray232.set64 ctx 14 (W64.of_int 1));
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (21 * 8)) /\ (((21 * 8) + 56) <= 232)))]);
    b_t <- (SBArray232_56.get_sub64 b_ctx 21);
    t <- (SBArray232_56.get_sub64 ctx 21);
    b_param_2 <- b_t;
    param_4 <- t;
    (aux_6, aux_7, tmp__trace) <@ h__BN___set0_ (param_4, b_param_2);
    result_3 <- aux_6;
    b_result_2 <- aux_7;
    trace_h__FPPM___ctx_init_ <- (trace_h__FPPM___ctx_init_ ++ tmp__trace);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_2 0 56))]);
    t <- result_3;
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (21 * 8)) /\ (((21 * 8) + 56) <= 232)))]);
    b_ctx <-
    (SBArray232_56.set_sub64 b_ctx 21 (BArray56.init_arr (W8.of_int 255)));
    ctx <- (SBArray232_56.set_sub64 ctx 21 t);
    b_x <- b__x;
    x <- _x;
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_mP <- (SBArray232_56.get_sub64 b_ctx 7);
    mP <- (SBArray232_56.get_sub64 ctx 7);
    b_param_3 <- b_x;
    param_5 <- x;
    b_param_4 <- b_mP;
    param_6 <- mP;
    (aux_8, aux_9, tmp__trace) <@ h__BN___mov_ (param_5, b_param_3, param_6,
    b_param_4);
    result_4 <- aux_8;
    b_result_3 <- aux_9;
    trace_h__FPPM___ctx_init_ <- (trace_h__FPPM___ctx_init_ ++ tmp__trace);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_3 0 56))]);
    x <- result_4;
    z <- (W64.of_int 0);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (7 * 8)) /\ (((7 * 8) + 56) <= 232)))]);
    b_mP <- (SBArray232_56.get_sub64 b_ctx 7);
    mP <- (SBArray232_56.get_sub64 ctx 7);
    param_7 <- x;
    b_param_5 <- b_mP;
    param_8 <- mP;
    param_9 <- z;
    (aux_10, aux_11, tmp__trace) <@ h__BN___cminusP_ (param_7,
    (BArray56.init_arr (W8.of_int 255)), param_8, b_param_5, param_9);
    result_5 <- aux_10;
    b_result_4 <- aux_11;
    trace_h__FPPM___ctx_init_ <- (trace_h__FPPM___ctx_init_ ++ tmp__trace);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, (BArray56.is_init b_result_4 0 56))]);
    x <- result_5;
    c <- (BArray56.get64 x 0);
    trace_h__FPPM___ctx_init_ <-
    (trace_h__FPPM___ctx_init_ ++
    [(Assert, ((0 <= (28 * 8)) /\ (((28 * 8) + 8) <= 232)))]);
    b_ctx <-
    (BArray232.set64d b_ctx (28 * 8) (W64.of_int 18446744073709551615));
    ctx <- (BArray232.set64 ctx 28 c);
    return (ctx, b_ctx, trace_h__FPPM___ctx_init_);
  }
}.

(* The post and trace are valid. *)

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
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

op h__FPPM__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FPPM__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FPPM__fun_sqrn_spec _r _b_r _a _b_a =
   hoare [M.h__FPPM__fun_sqrn :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FPPM___redPM_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPPM___redPM :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPPM___redPM__spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPPM___redPM_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPPM___fromM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPPM___fromM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FPPM__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FPPM__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPPM___mulm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FPPM___mulm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FPPM___toM__spec _a _b_a _ctx _b_ctx =
   hoare [M.h__FPPM___toM_ :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray232.is_init _b_ctx 0 232) /\ (BArray56.is_init _b_a 0 56))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__FPPM___ctx_init__spec _ctx _b_ctx _p _b_P =
   hoare [M.h__FPPM___ctx_init_ :
   (((_b_P = b_P) /\ ((_p = p) /\ ((_b_ctx = b_ctx) /\ (_ctx = ctx)))) /\
   (BArray56.is_init _b_P 0 (8 * 7))) ==>
   ((BArray232.is_init res.`2 0 (8 * 29)) /\ (valid res.`3))].
