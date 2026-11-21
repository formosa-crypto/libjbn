require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import Array11 Array88 BArray88.

module M = {
  var tmp__trace : trace
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
  proc h__BN___store (ap:W64.t, a:BArray88.t, b_a:BArray88.t) : trace = {
    var param:W64.t;
    var param_0:BArray88.t;
    var trace_h__BN___store:trace;
    param_0 <- witness;
    trace_h__BN___store <- [];
    trace_h__BN___store <-
    (trace_h__BN___store ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
     (BArray88.is_init b_a 0 88)))]);
    param <- ap;
    param_0 <- a;
    tmp__trace <@ h__BN____store (param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___store <- (trace_h__BN___store ++ tmp__trace);
    return (trace_h__BN___store);
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
  proc h__BN____eq_zf (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                       b_b:BArray88.t) : bool * trace = {
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    var trace_h__BN____eq_zf:trace;
    trace_h__BN____eq_zf <- [];
    trace_h__BN____eq_zf <-
    (trace_h__BN____eq_zf ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN____eq_zf <-
    (trace_h__BN____eq_zf ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    acc <- (W64.of_int 0);
    i <- 0;
    while ((i < 11)) {
      trace_h__BN____eq_zf <-
      (trace_h__BN____eq_zf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (BArray88.get64 a i);
      trace_h__BN____eq_zf <-
      (trace_h__BN____eq_zf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      t <- (t `^` (BArray88.get64 b i));
      acc <- (acc `|` t);
      i <- (i + 1);
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- (AND_64 acc acc);
    return (zf, trace_h__BN____eq_zf);
  }
  proc h__BN___eq_zf (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                      b_b:BArray88.t) : bool * trace = {
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___eq_zf:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___eq_zf <- [];
    trace_h__BN___eq_zf <-
    (trace_h__BN___eq_zf ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___eq_zf <-
    (trace_h__BN___eq_zf ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- b;
    (result, tmp__trace) <@ h__BN____eq_zf (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___eq_zf <- (trace_h__BN___eq_zf ++ tmp__trace);
    zf <- result;
    return (zf, trace_h__BN___eq_zf);
  }
  proc h__BN___eq_zf_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                       b_b:BArray88.t) : bool * trace = {
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___eq_zf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___eq_zf_ <- [];
    trace_h__BN___eq_zf_ <-
    (trace_h__BN___eq_zf_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___eq_zf_ <-
    (trace_h__BN___eq_zf_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    (result, tmp__trace) <@ h__BN___eq_zf (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___eq_zf_ <- (trace_h__BN___eq_zf_ ++ tmp__trace);
    zf <- result;
    return (zf, trace_h__BN___eq_zf_);
  }
  proc h__BN___eq_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                    b_b:BArray88.t) : W64.t * trace = {
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:bool;
    var zf:bool;
    var res_0:W64.t;
    var are_equal:W64.t;
    var trace_h__BN___eq_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___eq_ <- [];
    trace_h__BN___eq_ <-
    (trace_h__BN___eq_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__BN___eq_ <-
    (trace_h__BN___eq_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    param <- a;
    param_0 <- b;
    (result, tmp__trace) <@ h__BN___eq_zf_ (param,
    (BArray88.init_arr (W8.of_int 255)), param_0,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___eq_ <- (trace_h__BN___eq_ ++ tmp__trace);
    zf <- result;
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0, trace_h__BN___eq_);
  }
  proc h__BN____test0_zf (a:BArray88.t, b_a:BArray88.t) : bool * trace = {
    var acc:W64.t;
    var i:int;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    var trace_h__BN____test0_zf:trace;
    trace_h__BN____test0_zf <- [];
    trace_h__BN____test0_zf <-
    (trace_h__BN____test0_zf ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    acc <- (BArray88.get64 a 0);
    i <- 1;
    while ((i < 11)) {
      trace_h__BN____test0_zf <-
      (trace_h__BN____test0_zf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 88)))]);
      acc <- (acc `|` (BArray88.get64 a i));
      i <- (i + 1);
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- (AND_64 acc acc);
    return (zf, trace_h__BN____test0_zf);
  }
  proc h__BN___test0_zf_ (a:BArray88.t, b_a:BArray88.t) : bool * trace = {
    var param:BArray88.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___test0_zf_:trace;
    param <- witness;
    trace_h__BN___test0_zf_ <- [];
    trace_h__BN___test0_zf_ <-
    (trace_h__BN___test0_zf_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    a <- a;
    param <- a;
    (result, tmp__trace) <@ h__BN____test0_zf (param,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___test0_zf_ <- (trace_h__BN___test0_zf_ ++ tmp__trace);
    zf <- result;
    return (zf, trace_h__BN___test0_zf_);
  }
  proc h__BN___test0_ (a:BArray88.t, b_a:BArray88.t) : W64.t * trace = {
    var res_0:W64.t;
    var is_zero:W64.t;
    var param:BArray88.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___test0_:trace;
    param <- witness;
    trace_h__BN___test0_ <- [];
    trace_h__BN___test0_ <-
    (trace_h__BN___test0_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    param <- a;
    (result, tmp__trace) <@ h__BN___test0_zf_ (param,
    (BArray88.init_arr (W8.of_int 255)));
    trace_h__BN___test0_ <- (trace_h__BN___test0_ ++ tmp__trace);
    zf <- result;
    res_0 <- (zf ? is_zero : res_0);
    return (res_0, trace_h__BN___test0_);
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
  proc bn_eq (ap:W64.t, bp:W64.t) : W64.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
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
    var result_1:W64.t;
    var r:W64.t;
    var trace_bn_eq:trace;
    _a <- witness;
    _b <- witness;
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
    param <- witness;
    param_1 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_bn_eq <- [];
    trace_bn_eq <-
    (trace_bn_eq ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_eq <- (trace_bn_eq ++ tmp__trace);
    trace_bn_eq <-
    (trace_bn_eq ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_bn_eq <- (trace_bn_eq ++ tmp__trace);
    trace_bn_eq <-
    (trace_bn_eq ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    param_3 <- a;
    param_4 <- b;
    (result_1, tmp__trace) <@ h__BN___eq_ (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)));
    trace_bn_eq <- (trace_bn_eq ++ tmp__trace);
    r <- result_1;
    r <- r;
    return (r, trace_bn_eq);
  }
  proc bn_test0 (ap:W64.t) : W64.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b__a:BArray88.t;
    var b_a:BArray88.t;
    var a:BArray88.t;
    var _a:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:W64.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_1:BArray88.t;
    var result_0:W64.t;
    var r:W64.t;
    var trace_bn_test0:trace;
    _a <- witness;
    a <- witness;
    b__a <- witness;
    b_a <- witness;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_1 <- witness;
    result <- witness;
    trace_bn_test0 <- [];
    trace_bn_test0 <-
    (trace_bn_test0 ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_test0 <- (trace_bn_test0 ++ tmp__trace);
    trace_bn_test0 <-
    (trace_bn_test0 ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    a <- result;
    param_1 <- a;
    (result_0, tmp__trace) <@ h__BN___test0_ (param_1,
    (BArray88.init_arr (W8.of_int 255)));
    trace_bn_test0 <- (trace_bn_test0 ++ tmp__trace);
    r <- result_0;
    r <- r;
    return (r, trace_bn_test0);
  }
  proc bn_copy (rp:W64.t, ap:W64.t) : trace = {
    var i:int;
    var t:W64.t;
    var trace_bn_copy:trace;
    trace_bn_copy <- [];
    trace_bn_copy <-
    (trace_bn_copy ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))))]);
    i <- 0;
    while ((i < 11)) {
      trace_bn_copy <-
      (trace_bn_copy ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      trace_bn_copy <-
      (trace_bn_copy ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (rp + (W64.of_int (8 * i)))) 8))]);
      Glob.mem <-
      (storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int (8 * i)))) t);
      i <- (i + 1);
    }
    return (trace_bn_copy);
  }
  proc bn_set0 (rp:W64.t) : trace = {
    var i:int;
    var trace_bn_set0:trace;
    trace_bn_set0 <- [];
    trace_bn_set0 <-
    (trace_bn_set0 ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11)))]);
    i <- 0;
    while ((i < 11)) {
      trace_bn_set0 <-
      (trace_bn_set0 ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (rp + (W64.of_int (8 * i)))) 8))]);
      Glob.mem <-
      (storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int (8 * i))))
      (W64.of_int 0));
      i <- (i + 1);
    }
    return (trace_bn_set0);
  }
  proc bn_addU (rp:W64.t, ap:W64.t, bp:W64.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_3:bool;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
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
    var result_1:bool;
    var result_2:BArray88.t;
    var b_result_1:BArray88.t;
    var param_5:W64.t;
    var param_6:BArray88.t;
    var trace_bn_addU:trace;
    _a <- witness;
    _b <- witness;
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
    param_6 <- witness;
    result <- witness;
    result_0 <- witness;
    result_2 <- witness;
    trace_bn_addU <- [];
    trace_bn_addU <-
    (trace_bn_addU ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_addU <- (trace_bn_addU ++ tmp__trace);
    trace_bn_addU <-
    (trace_bn_addU ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_bn_addU <- (trace_bn_addU ++ tmp__trace);
    trace_bn_addU <-
    (trace_bn_addU ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    param_3 <- a;
    param_4 <- b;
    (aux_3, aux_4, aux_5, tmp__trace) <@ h__BN___addU_ (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_bn_addU <- (trace_bn_addU ++ tmp__trace);
    trace_bn_addU <-
    (trace_bn_addU ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    a <- result_2;
    param_5 <- rp;
    param_6 <- a;
    tmp__trace <@ h__BN___store_ (param_5, param_6,
    (BArray88.init_arr (W8.of_int 255)));
    trace_bn_addU <- (trace_bn_addU ++ tmp__trace);
    return (trace_bn_addU);
  }
  proc bn_subU (rp:W64.t, ap:W64.t, bp:W64.t) : trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_4:BArray88.t;
    var aux_5:BArray88.t;
    var aux_3:bool;
    var b__a:BArray88.t;
    var b__b:BArray88.t;
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
    var result_1:bool;
    var result_2:BArray88.t;
    var b_result_1:BArray88.t;
    var param_5:W64.t;
    var param_6:BArray88.t;
    var trace_bn_subU:trace;
    _a <- witness;
    _b <- witness;
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
    param_6 <- witness;
    result <- witness;
    result_0 <- witness;
    result_2 <- witness;
    trace_bn_subU <- [];
    trace_bn_subU <-
    (trace_bn_subU ++
    [(Assert,
     (((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 11)) /\
      (is_valid ptr_modulus Glob.mem_v (W64.to_uint bp) (8 * 11))) /\
     (is_valid ptr_modulus Glob.mem_v (W64.to_uint rp) (8 * 11))))]);
    b__a <- (BArray88.init_arr (W8.of_int 0));
    b__b <- (BArray88.init_arr (W8.of_int 0));
    b_a <- b__a;
    a <- _a;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ h__BN___load_ (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_bn_subU <- (trace_bn_subU ++ tmp__trace);
    trace_bn_subU <-
    (trace_bn_subU ++ [(Assert, (BArray88.is_init b_result 0 88))]);
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
    trace_bn_subU <- (trace_bn_subU ++ tmp__trace);
    trace_bn_subU <-
    (trace_bn_subU ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    b <- result_0;
    param_3 <- a;
    param_4 <- b;
    (aux_3, aux_4, aux_5, tmp__trace) <@ h__BN___subU_ (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    result_2 <- aux_4;
    b_result_1 <- aux_5;
    trace_bn_subU <- (trace_bn_subU ++ tmp__trace);
    trace_bn_subU <-
    (trace_bn_subU ++ [(Assert, (BArray88.is_init b_result_1 0 88))]);
    a <- result_2;
    param_5 <- rp;
    param_6 <- a;
    tmp__trace <@ h__BN___store (param_5, param_6,
    (BArray88.init_arr (W8.of_int 255)));
    trace_bn_subU <- (trace_bn_subU ++ tmp__trace);
    return (trace_bn_subU);
  }
}.

(* The post and trace are valid. *)

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

op h__BN___store_spec _ap _a _b_a =
   hoare [M.h__BN___store :
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

op h__BN____eq_zf_spec _a _b_a _b _b_b =
   hoare [M.h__BN____eq_zf :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN___eq_zf_spec _a _b_a _b _b_b =
   hoare [M.h__BN___eq_zf :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN___eq_zf__spec _a _b_a _b _b_b =
   hoare [M.h__BN___eq_zf_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN___eq__spec _a _b_a _b _b_b =
   hoare [M.h__BN___eq_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88))) ==>
   (true /\ (valid res.`2))].

op h__BN____test0_zf_spec _a _b_a =
   hoare [M.h__BN____test0_zf :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray88.is_init _b_a 0 88)) ==>
   (true /\ (valid res.`2))].

op h__BN___test0_zf__spec _a _b_a =
   hoare [M.h__BN___test0_zf_ :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray88.is_init _b_a 0 88)) ==>
   (true /\ (valid res.`2))].

op h__BN___test0__spec _a _b_a =
   hoare [M.h__BN___test0_ :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray88.is_init _b_a 0 88)) ==>
   (true /\ (valid res.`2))].

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

op bn_eq_spec _ap _bp =
   hoare [M.bn_eq :
   (((_bp = bp) /\ (_ap = ap)) /\
   (true /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11)))))) ==>
   (true /\ (valid res.`2))].

op bn_test0_spec _ap =
   hoare [M.bn_test0 :
   ((_ap = ap) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)))) ==>
   (true /\ (valid res.`2))].

op bn_copy_spec _rp _ap =
   hoare [M.bn_copy :
   (((_ap = ap) /\ (_rp = rp)) /\
   (true /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11)))))) ==>
   (true /\ (valid res))].

op bn_set0_spec _rp =
   hoare [M.bn_set0 :
   ((_rp = rp) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11)))) ==>
   (true /\ (valid res))].

op bn_addU_spec _rp _ap _bp =
   hoare [M.bn_addU :
   (((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))) /\
   (true /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))))))) ==>
   (true /\ (valid res))].

op bn_subU_spec _rp _ap _bp =
   hoare [M.bn_subU :
   (((_bp = bp) /\ ((_ap = ap) /\ (_rp = rp))) /\
   (true /\
   (true /\
   (true /\
   (((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 11)) /\
    (is_valid ptr_modulus Glob.mem_v (W64.to_uint _bp) (8 * 11))) /\
   (is_valid ptr_modulus Glob.mem_v (W64.to_uint _rp) (8 * 11))))))) ==>
   (true /\ (valid res))].
