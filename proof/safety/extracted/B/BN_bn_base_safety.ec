require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import Array7 Array14 Array56 Array112 BArray56 BArray112.

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
  proc h__BN____store (ap:W64.t, a:BArray56.t, b_a:BArray56.t) : trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____store:trace;
    trace_h__BN____store <- [];
    trace_h__BN____store <-
    (trace_h__BN____store ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)) /\
     (BArray56.is_init b_a 0 56)))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____store <-
      (trace_h__BN____store ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
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
  proc h__BN___store_ (ap:W64.t, a:BArray56.t, b_a:BArray56.t) : trace = {
    var param:W64.t;
    var param_0:BArray56.t;
    var trace_h__BN___store_:trace;
    param_0 <- witness;
    trace_h__BN___store_ <- [];
    trace_h__BN___store_ <-
    (trace_h__BN___store_ ++
    [(Assert,
     ((is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * 7)) /\
     (BArray56.is_init b_a 0 56)))]);
    ap <- ap;
    a <- a;
    param <- ap;
    param_0 <- a;
    tmp__trace <@ h__BN____store (param, param_0,
    (BArray56.init_arr (W8.of_int 255)));
    trace_h__BN___store_ <- (trace_h__BN___store_ ++ tmp__trace);
    return (trace_h__BN___store_);
  }
  proc h__BN____eq_zf (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t) : bool * trace = {
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
    (trace_h__BN____eq_zf ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN____eq_zf <-
    (trace_h__BN____eq_zf ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    acc <- (W64.of_int 0);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____eq_zf <-
      (trace_h__BN____eq_zf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____eq_zf <-
      (trace_h__BN____eq_zf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (t `^` (BArray56.get64 b i));
      acc <- (acc `|` t);
      i <- (i + 1);
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- (AND_64 acc acc);
    return (zf, trace_h__BN____eq_zf);
  }
  proc h__BN___eq_zf (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                      b_b:BArray56.t) : bool * trace = {
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___eq_zf:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___eq_zf <- [];
    trace_h__BN___eq_zf <-
    (trace_h__BN___eq_zf ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___eq_zf <-
    (trace_h__BN___eq_zf ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    param <- a;
    param_0 <- b;
    (result, tmp__trace) <@ h__BN____eq_zf (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)));
    trace_h__BN___eq_zf <- (trace_h__BN___eq_zf ++ tmp__trace);
    zf <- result;
    return (zf, trace_h__BN___eq_zf);
  }
  proc h__BN___eq_zf_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t) : bool * trace = {
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___eq_zf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___eq_zf_ <- [];
    trace_h__BN___eq_zf_ <-
    (trace_h__BN___eq_zf_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___eq_zf_ <-
    (trace_h__BN___eq_zf_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    (result, tmp__trace) <@ h__BN___eq_zf (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)));
    trace_h__BN___eq_zf_ <- (trace_h__BN___eq_zf_ ++ tmp__trace);
    zf <- result;
    return (zf, trace_h__BN___eq_zf_);
  }
  proc h__BN___eq_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                    b_b:BArray56.t) : W64.t * trace = {
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var zf:bool;
    var res_0:W64.t;
    var are_equal:W64.t;
    var trace_h__BN___eq_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___eq_ <- [];
    trace_h__BN___eq_ <-
    (trace_h__BN___eq_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___eq_ <-
    (trace_h__BN___eq_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    param <- a;
    param_0 <- b;
    (result, tmp__trace) <@ h__BN___eq_zf_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)));
    trace_h__BN___eq_ <- (trace_h__BN___eq_ ++ tmp__trace);
    zf <- result;
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    res_0 <- (zf ? are_equal : res_0);
    return (res_0, trace_h__BN___eq_);
  }
  proc h__BN____test0_zf (a:BArray56.t, b_a:BArray56.t) : bool * trace = {
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
    (trace_h__BN____test0_zf ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    acc <- (BArray56.get64 a 0);
    i <- 1;
    while ((i < 7)) {
      trace_h__BN____test0_zf <-
      (trace_h__BN____test0_zf ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      acc <- (acc `|` (BArray56.get64 a i));
      i <- (i + 1);
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- (AND_64 acc acc);
    return (zf, trace_h__BN____test0_zf);
  }
  proc h__BN___test0_zf_ (a:BArray56.t, b_a:BArray56.t) : bool * trace = {
    var param:BArray56.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___test0_zf_:trace;
    param <- witness;
    trace_h__BN___test0_zf_ <- [];
    trace_h__BN___test0_zf_ <-
    (trace_h__BN___test0_zf_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    a <- a;
    param <- a;
    (result, tmp__trace) <@ h__BN____test0_zf (param,
    (BArray56.init_arr (W8.of_int 255)));
    trace_h__BN___test0_zf_ <- (trace_h__BN___test0_zf_ ++ tmp__trace);
    zf <- result;
    return (zf, trace_h__BN___test0_zf_);
  }
  proc h__BN___test0_ (a:BArray56.t, b_a:BArray56.t) : W64.t * trace = {
    var res_0:W64.t;
    var is_zero:W64.t;
    var param:BArray56.t;
    var result:bool;
    var zf:bool;
    var trace_h__BN___test0_:trace;
    param <- witness;
    trace_h__BN___test0_ <- [];
    trace_h__BN___test0_ <-
    (trace_h__BN___test0_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    param <- a;
    (result, tmp__trace) <@ h__BN___test0_zf_ (param,
    (BArray56.init_arr (W8.of_int 255)));
    trace_h__BN___test0_ <- (trace_h__BN___test0_ ++ tmp__trace);
    zf <- result;
    res_0 <- (zf ? is_zero : res_0);
    return (res_0, trace_h__BN___test0_);
  }
  proc h__BN____copy (a:BArray56.t, b_a:BArray56.t) : BArray56.t *
                                                      BArray56.t * trace = {
    var b_r:BArray56.t;
    var i:int;
    var t:W64.t;
    var r:BArray56.t;
    var trace_h__BN____copy:trace;
    b_r <- witness;
    r <- witness;
    trace_h__BN____copy <- [];
    trace_h__BN____copy <-
    (trace_h__BN____copy ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b_r <- (BArray56.init_arr (W8.of_int 0));
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____copy <-
      (trace_h__BN____copy ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      trace_h__BN____copy <-
      (trace_h__BN____copy ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      b_r <- (BArray56.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray56.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__BN____copy);
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
  proc h__BN____cswap_mask (x:BArray56.t, b_x:BArray56.t, y:BArray56.t,
                            b_y:BArray56.t, mask:W64.t) : BArray56.t *
                                                          BArray56.t *
                                                          BArray56.t *
                                                          BArray56.t * trace = {
    var i:int;
    var tmp:W64.t;
    var trace_h__BN____cswap_mask:trace;
    trace_h__BN____cswap_mask <- [];
    trace_h__BN____cswap_mask <-
    (trace_h__BN____cswap_mask ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN____cswap_mask <-
    (trace_h__BN____cswap_mask ++ [(Assert, (BArray56.is_init b_y 0 56))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      tmp <- (BArray56.get64 x i);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      tmp <- (tmp `^` (BArray56.get64 y i));
      tmp <- (tmp `&` mask);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      x <- (BArray56.set64 x i ((BArray56.get64 x i) `^` tmp));
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____cswap_mask <-
      (trace_h__BN____cswap_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      y <- (BArray56.set64 y i ((BArray56.get64 y i) `^` tmp));
      i <- (i + 1);
    }
    b_x <- (BArray56.init_arr (W8.of_int 255));
    b_y <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN____cswap_mask);
  }
  proc h__BN___cswap_mask (x:BArray56.t, b_x:BArray56.t, y:BArray56.t,
                           b_y:BArray56.t, mask:W64.t) : BArray56.t *
                                                         BArray56.t *
                                                         BArray56.t *
                                                         BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__BN___cswap_mask:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__BN___cswap_mask <- [];
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++ [(Assert, (BArray56.is_init b_y 0 56))]);
    param <- x;
    param_0 <- y;
    param_1 <- mask;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ h__BN____cswap_mask (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    b_result <- aux_0;
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__BN___cswap_mask <- (trace_h__BN___cswap_mask ++ tmp__trace);
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    trace_h__BN___cswap_mask <-
    (trace_h__BN___cswap_mask ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    x <- result;
    y <- result_0;
    b_x <- (BArray56.init_arr (W8.of_int 255));
    b_y <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN___cswap_mask);
  }
  proc h__BN___cswap_mask_ (x:BArray56.t, b_x:BArray56.t, y:BArray56.t,
                            b_y:BArray56.t, mask:W64.t) : BArray56.t *
                                                          BArray56.t *
                                                          BArray56.t *
                                                          BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var result_0:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__BN___cswap_mask_:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__BN___cswap_mask_ <- [];
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++ [(Assert, (BArray56.is_init b_y 0 56))]);
    x <- x;
    y <- y;
    param <- x;
    param_0 <- y;
    param_1 <- mask;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ h__BN___cswap_mask (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    b_result <- aux_0;
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__BN___cswap_mask_ <- (trace_h__BN___cswap_mask_ ++ tmp__trace);
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++
    [(Assert, (BArray56.is_init b_result 0 56))]);
    trace_h__BN___cswap_mask_ <-
    (trace_h__BN___cswap_mask_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    x <- result;
    y <- result_0;
    x <- x;
    y <- y;
    b_x <- (BArray56.init_arr (W8.of_int 255));
    b_y <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN___cswap_mask_);
  }
  proc h__BN___cswap_cf_ (x:BArray56.t, b_x:BArray56.t, y:BArray56.t,
                          b_y:BArray56.t, cf:bool) : BArray56.t *
                                                     BArray56.t *
                                                     BArray56.t *
                                                     BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var param:bool;
    var result:W64.t;
    var mask:W64.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:W64.t;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var result_1:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__BN___cswap_cf_:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__BN___cswap_cf_ <- [];
    trace_h__BN___cswap_cf_ <-
    (trace_h__BN___cswap_cf_ ++ [(Assert, (BArray56.is_init b_x 0 56))]);
    trace_h__BN___cswap_cf_ <-
    (trace_h__BN___cswap_cf_ ++ [(Assert, (BArray56.is_init b_y 0 56))]);
    param <- cf;
    (result, tmp__trace) <@ uTIL____cf_mask (param);
    trace_h__BN___cswap_cf_ <- (trace_h__BN___cswap_cf_ ++ tmp__trace);
    mask <- result;
    param_0 <- x;
    param_1 <- y;
    param_2 <- mask;
    (aux, aux_0, aux_1, aux_2, tmp__trace) <@ h__BN___cswap_mask_ (param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)), param_2);
    result_0 <- aux;
    b_result <- aux_0;
    result_1 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__BN___cswap_cf_ <- (trace_h__BN___cswap_cf_ ++ tmp__trace);
    trace_h__BN___cswap_cf_ <-
    (trace_h__BN___cswap_cf_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    trace_h__BN___cswap_cf_ <-
    (trace_h__BN___cswap_cf_ ++
    [(Assert, (BArray56.is_init b_result_0 0 56))]);
    x <- result_0;
    y <- result_1;
    b_x <- (BArray56.init_arr (W8.of_int 255));
    b_y <- (BArray56.init_arr (W8.of_int 255));
    return (x, b_x, y, b_y, trace_h__BN___cswap_cf_);
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
  proc h__BN____cfill (a:BArray56.t, b_a:BArray56.t, b:bool, x:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____cfill:trace;
    trace_h__BN____cfill <- [];
    trace_h__BN____cfill <-
    (trace_h__BN____cfill ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____cfill <-
      (trace_h__BN____cfill ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 a i);
      t <- (b ? x : t);
      trace_h__BN____cfill <-
      (trace_h__BN____cfill ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      a <- (BArray56.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____cfill);
  }
  proc h__BN____or_mask (a:BArray56.t, b_a:BArray56.t, mask:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var i:int;
    var trace_h__BN____or_mask:trace;
    trace_h__BN____or_mask <- [];
    trace_h__BN____or_mask <-
    (trace_h__BN____or_mask ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____or_mask <-
      (trace_h__BN____or_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____or_mask <-
      (trace_h__BN____or_mask ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      a <- (BArray56.set64 a i ((BArray56.get64 a i) `|` mask));
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN____or_mask);
  }
  proc h__BN___or_mask (a:BArray56.t, b_a:BArray56.t, mask:W64.t) : BArray56.t *
                                                                    BArray56.t *
                                                                    trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___or_mask:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___or_mask <- [];
    trace_h__BN___or_mask <-
    (trace_h__BN___or_mask ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    param <- a;
    param_0 <- mask;
    (aux, aux_0, tmp__trace) <@ h__BN____or_mask (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___or_mask <- (trace_h__BN___or_mask ++ tmp__trace);
    trace_h__BN___or_mask <-
    (trace_h__BN___or_mask ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___or_mask);
  }
  proc h__BN___or_mask_ (a:BArray56.t, b_a:BArray56.t, mask:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___or_mask_:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___or_mask_ <- [];
    trace_h__BN___or_mask_ <-
    (trace_h__BN___or_mask_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    a <- a;
    mask <- mask;
    param <- a;
    param_0 <- mask;
    (aux, aux_0, tmp__trace) <@ h__BN___or_mask (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___or_mask_ <- (trace_h__BN___or_mask_ ++ tmp__trace);
    trace_h__BN___or_mask_ <-
    (trace_h__BN___or_mask_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___or_mask_);
  }
  proc h__BN___set_err_ (a:BArray56.t, b_a:BArray56.t, _err:W64.t) : 
  BArray56.t * BArray56.t * trace = {
    var aux:BArray56.t;
    var aux_0:BArray56.t;
    var err:W64.t;
    var param:BArray56.t;
    var param_0:W64.t;
    var result:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___set_err_:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___set_err_ <- [];
    trace_h__BN___set_err_ <-
    (trace_h__BN___set_err_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    err <- _err;
    param <- a;
    param_0 <- err;
    (aux, aux_0, tmp__trace) <@ h__BN___or_mask_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___set_err_ <- (trace_h__BN___set_err_ ++ tmp__trace);
    trace_h__BN___set_err_ <-
    (trace_h__BN___set_err_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    a <- result;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___set_err_);
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
  proc h__BN____carrypropU (a:BArray56.t, b_a:BArray56.t, cf:bool, k:int) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var trace_h__BN____carrypropU:trace;
    trace_h__BN____carrypropU <- [];
    trace_h__BN____carrypropU <-
    (trace_h__BN____carrypropU ++
    [(Assert, ((0 <= k) /\ (BArray56.is_init b_a 0 56)))]);
    i <- k;
    while ((i < 7)) {
      trace_h__BN____carrypropU <-
      (trace_h__BN____carrypropU ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      trace_h__BN____carrypropU <-
      (trace_h__BN____carrypropU ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (aux, aux_0) <- (adc_64 (BArray56.get64 a i) (W64.of_int 0) cf);
      cf <- aux;
      a <- (BArray56.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____carrypropU);
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
  proc h__BN___addcU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                  BArray56.t * trace = {
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___addcU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addcU_ <- [];
    trace_h__BN___addcU_ <-
    (trace_h__BN___addcU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___addcU_ <-
    (trace_h__BN___addcU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    t <- (BArray56.get64 b 0);
    (aux, aux_0) <- (adc_64 (BArray56.get64 a 0) t cf);
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
    trace_h__BN___addcU_ <- (trace_h__BN___addcU_ ++ tmp__trace);
    trace_h__BN___addcU_ <-
    (trace_h__BN___addcU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addcU_);
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
  proc h__BN___addc_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t, cf:bool) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___addc_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___addc_ <- [];
    trace_h__BN___addc_ <-
    (trace_h__BN___addc_ ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    t <- (BArray56.get64 a 0);
    (cf, t) <- (adc_64 t (BArray56.get64 b 0) cf);
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
    trace_h__BN___addc_ <- (trace_h__BN___addc_ ++ tmp__trace);
    trace_h__BN___addc_ <-
    (trace_h__BN___addc_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___addc_);
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
  proc h__BN___subcU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                       b_b:BArray56.t, cf:bool) : bool * BArray56.t *
                                                  BArray56.t * trace = {
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subcU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___subcU_ <- [];
    trace_h__BN___subcU_ <-
    (trace_h__BN___subcU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___subcU_ <-
    (trace_h__BN___subcU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    t <- (BArray56.get64 b 0);
    (aux, aux_0) <- (sbb_64 (BArray56.get64 a 0) t cf);
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
    trace_h__BN___subcU_ <- (trace_h__BN___subcU_ ++ tmp__trace);
    trace_h__BN___subcU_ <-
    (trace_h__BN___subcU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___subcU_);
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
  proc h__BN___subc_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t, cf:bool) : 
  bool * BArray56.t * BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var param_2:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___subc_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result_0 <- witness;
    trace_h__BN___subc_ <- [];
    trace_h__BN___subc_ <-
    (trace_h__BN___subc_ ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    t <- (BArray56.get64 a 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 b 0) cf);
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
    trace_h__BN___subc_ <- (trace_h__BN___subc_ ++ tmp__trace);
    trace_h__BN___subc_ <-
    (trace_h__BN___subc_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___subc_);
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
  proc h__BN___ltc_cf_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
                        b_b:BArray56.t, cf:bool) : bool * trace = {
    var t:W64.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var trace_h__BN___ltc_cf_:trace;
    param <- witness;
    param_0 <- witness;
    trace_h__BN___ltc_cf_ <- [];
    trace_h__BN___ltc_cf_ <-
    (trace_h__BN___ltc_cf_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__BN___ltc_cf_ <-
    (trace_h__BN___ltc_cf_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    t <- (BArray56.get64 a 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 b 0) cf);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (result, tmp__trace) <@ h__BN___ltc1_cf_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1);
    trace_h__BN___ltc_cf_ <- (trace_h__BN___ltc_cf_ ++ tmp__trace);
    cf <- result;
    return (cf, trace_h__BN___ltc_cf_);
  }
  proc h__BN____negc1U (a:BArray56.t, b_a:BArray56.t, cf:bool) : bool *
                                                                 BArray56.t *
                                                                 BArray56.t *
                                                                 trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____negc1U:trace;
    trace_h__BN____negc1U <- [];
    trace_h__BN____negc1U <-
    (trace_h__BN____negc1U ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    i <- 1;
    while ((i < 7)) {
      t <- (W64.of_int 0);
      trace_h__BN____negc1U <-
      (trace_h__BN____negc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      (cf, t) <- (sbb_64 t (BArray56.get64 a i) cf);
      trace_h__BN____negc1U <-
      (trace_h__BN____negc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      a <- (BArray56.set64 a i t);
      i <- (i + 1);
    }
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____negc1U);
  }
  proc h__BN___negc1U (a:BArray56.t, b_a:BArray56.t, cf:bool) : bool *
                                                                BArray56.t *
                                                                BArray56.t *
                                                                trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negc1U:trace;
    b_result <- witness;
    param <- witness;
    result_0 <- witness;
    trace_h__BN___negc1U <- [];
    trace_h__BN___negc1U <-
    (trace_h__BN___negc1U ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    param <- a;
    param_0 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN____negc1U (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1U <- (trace_h__BN___negc1U ++ tmp__trace);
    trace_h__BN___negc1U <-
    (trace_h__BN___negc1U ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___negc1U);
  }
  proc h__BN___negc1U_ (a:BArray56.t, b_a:BArray56.t, cf:bool) : bool *
                                                                 BArray56.t *
                                                                 BArray56.t *
                                                                 trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var param:BArray56.t;
    var param_0:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negc1U_:trace;
    b_result <- witness;
    param <- witness;
    result_0 <- witness;
    trace_h__BN___negc1U_ <- [];
    trace_h__BN___negc1U_ <-
    (trace_h__BN___negc1U_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    a <- a;
    param <- a;
    param_0 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1U (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negc1U_ <- (trace_h__BN___negc1U_ ++ tmp__trace);
    trace_h__BN___negc1U_ <-
    (trace_h__BN___negc1U_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___negc1U_);
  }
  proc h__BN___negU_ (a:BArray56.t, b_a:BArray56.t) : bool * BArray56.t *
                                                      BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var cf:bool;
    var param:BArray56.t;
    var param_0:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negU_:trace;
    b_result <- witness;
    param <- witness;
    result_0 <- witness;
    trace_h__BN___negU_ <- [];
    trace_h__BN___negU_ <-
    (trace_h__BN___negU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 a 0) false);
    a <- (BArray56.set64 a 0 t);
    param <- a;
    param_0 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1U_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negU_ <- (trace_h__BN___negU_ ++ tmp__trace);
    trace_h__BN___negU_ <-
    (trace_h__BN___negU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___negU_);
  }
  proc h__BN___negcU_ (a:BArray56.t, b_a:BArray56.t, cf:bool) : bool *
                                                                BArray56.t *
                                                                BArray56.t *
                                                                trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var param:BArray56.t;
    var param_0:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negcU_:trace;
    b_result <- witness;
    param <- witness;
    result_0 <- witness;
    trace_h__BN___negcU_ <- [];
    trace_h__BN___negcU_ <-
    (trace_h__BN___negcU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 a 0) cf);
    a <- (BArray56.set64 a 0 t);
    param <- a;
    param_0 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___negc1U_ (param,
    (BArray56.init_arr (W8.of_int 255)), param_0);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___negcU_ <- (trace_h__BN___negcU_ ++ tmp__trace);
    trace_h__BN___negcU_ <-
    (trace_h__BN___negcU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___negcU_);
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
  proc h__BN___negc_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
                      b_a:BArray56.t, cf:bool) : bool * BArray56.t *
                                                 BArray56.t * trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux:bool;
    var t:W64.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var param_1:bool;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var trace_h__BN___negc_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___negc_ <- [];
    trace_h__BN___negc_ <-
    (trace_h__BN___negc_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    t <- (W64.of_int 0);
    (cf, t) <- (sbb_64 t (BArray56.get64 a 0) cf);
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
    trace_h__BN___negc_ <- (trace_h__BN___negc_ ++ tmp__trace);
    trace_h__BN___negc_ <-
    (trace_h__BN___negc_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    cf <- result;
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (cf, r, b_r, trace_h__BN___negc_);
  }
  proc h__BN___cnegU_ (a:BArray56.t, b_a:BArray56.t, cond:W64.t) : BArray56.t *
                                                                   BArray56.t *
                                                                   trace = {
    var aux_0:BArray56.t;
    var aux_1:BArray56.t;
    var aux_2:BArray56.t;
    var aux_3:BArray56.t;
    var aux:bool;
    var b__x:BArray56.t;
    var b_x:BArray56.t;
    var x:BArray56.t;
    var _x:BArray56.t;
    var b_param:BArray56.t;
    var param:BArray56.t;
    var param_0:BArray56.t;
    var result:bool;
    var result_0:BArray56.t;
    var b_result:BArray56.t;
    var param_1:W64.t;
    var result_1:bool;
    var cf:bool;
    var param_2:BArray56.t;
    var param_3:bool;
    var param_4:BArray56.t;
    var result_2:BArray56.t;
    var b_result_0:BArray56.t;
    var trace_h__BN___cnegU_:trace;
    _x <- witness;
    b__x <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_x <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_4 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    x <- witness;
    trace_h__BN___cnegU_ <- [];
    trace_h__BN___cnegU_ <-
    (trace_h__BN___cnegU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    b__x <- (BArray56.init_arr (W8.of_int 0));
    b_x <- b__x;
    x <- _x;
    b_param <- b_x;
    param <- x;
    param_0 <- a;
    (aux, aux_0, aux_1, tmp__trace) <@ h__BN___neg_ (param, b_param, 
    param_0, (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___cnegU_ <- (trace_h__BN___cnegU_ ++ tmp__trace);
    trace_h__BN___cnegU_ <-
    (trace_h__BN___cnegU_ ++ [(Assert, (BArray56.is_init b_result 0 56))]);
    x <- result_0;
    param_1 <- cond;
    (result_1, tmp__trace) <@ uTIL____mask_cf (param_1);
    trace_h__BN___cnegU_ <- (trace_h__BN___cnegU_ ++ tmp__trace);
    cf <- result_1;
    param_2 <- a;
    param_3 <- cf;
    param_4 <- x;
    (aux_2, aux_3, tmp__trace) <@ h__BN___cmov_ (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3, param_4,
    (BArray56.init_arr (W8.of_int 255)));
    result_2 <- aux_2;
    b_result_0 <- aux_3;
    trace_h__BN___cnegU_ <- (trace_h__BN___cnegU_ ++ tmp__trace);
    trace_h__BN___cnegU_ <-
    (trace_h__BN___cnegU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_2;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___cnegU_);
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
  proc h__BN____pack2 (r:BArray112.t, b_r:BArray112.t, lo:BArray56.t,
                       b_lo:BArray56.t, hi:BArray56.t, b_hi:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____pack2:trace;
    trace_h__BN____pack2 <- [];
    trace_h__BN____pack2 <-
    (trace_h__BN____pack2 ++
    [(Assert, ((BArray56.is_init b_lo 0 56) /\ (BArray56.is_init b_hi 0 56)))]);
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____pack2 <-
      (trace_h__BN____pack2 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 lo i);
      trace_h__BN____pack2 <-
      (trace_h__BN____pack2 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r i t);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 7)) {
      trace_h__BN____pack2 <-
      (trace_h__BN____pack2 ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 56)))]);
      t <- (BArray56.get64 hi i);
      trace_h__BN____pack2 <-
      (trace_h__BN____pack2 ++
      [(Assert, ((0 <= ((7 + i) * 8)) /\ ((((7 + i) * 8) + 8) <= 112)))]);
      b_r <-
      (BArray112.set64d b_r ((7 + i) * 8) (W64.of_int 18446744073709551615));
      r <- (BArray112.set64 r (7 + i) t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__BN____pack2);
  }
  proc h__BN___pack2_ (r:BArray112.t, b_r:BArray112.t, lo:BArray56.t,
                       b_lo:BArray56.t, hi:BArray56.t, b_hi:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var aux:BArray112.t;
    var aux_0:BArray112.t;
    var b_param:BArray112.t;
    var param:BArray112.t;
    var param_0:BArray56.t;
    var param_1:BArray56.t;
    var result:BArray112.t;
    var b_result:BArray112.t;
    var trace_h__BN___pack2_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    result <- witness;
    trace_h__BN___pack2_ <- [];
    trace_h__BN___pack2_ <-
    (trace_h__BN___pack2_ ++
    [(Assert, ((BArray56.is_init b_lo 0 56) /\ (BArray56.is_init b_hi 0 56)))]);
    b_r <- b_r;
    r <- r;
    lo <- lo;
    hi <- hi;
    b_param <- b_r;
    param <- r;
    param_0 <- lo;
    param_1 <- hi;
    (aux, aux_0, tmp__trace) <@ h__BN____pack2 (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___pack2_ <- (trace_h__BN___pack2_ ++ tmp__trace);
    trace_h__BN___pack2_ <-
    (trace_h__BN___pack2_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    r <- result;
    r <- r;
    b_r <- (BArray112.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___pack2_);
  }
}.

(* The post and trace are valid. *)

op uTIL____mask_cf_spec _mask =
   hoare [M.uTIL____mask_cf :
   ((_mask = mask) /\ true) ==> (true /\ (valid res.`2))].

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

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

op h__BN____store_spec _ap _a _b_a =
   hoare [M.h__BN____store :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)) /\
   (BArray56.is_init _b_a 0 (8 * 7))))) ==> (true /\ (valid res))].

op h__BN___store__spec _ap _a _b_a =
   hoare [M.h__BN___store_ :
   (((_b_a = b_a) /\ ((_a = a) /\ (_ap = ap))) /\
   (true /\
   ((is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * 7)) /\
   (BArray56.is_init _b_a 0 (8 * 7))))) ==> (true /\ (valid res))].

op h__BN____eq_zf_spec _a _b_a _b _b_b =
   hoare [M.h__BN____eq_zf :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___eq_zf_spec _a _b_a _b _b_b =
   hoare [M.h__BN___eq_zf :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___eq_zf__spec _a _b_a _b _b_b =
   hoare [M.h__BN___eq_zf_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN___eq__spec _a _b_a _b _b_b =
   hoare [M.h__BN___eq_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN____test0_zf_spec _a _b_a =
   hoare [M.h__BN____test0_zf :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray56.is_init _b_a 0 56)) ==>
   (true /\ (valid res.`2))].

op h__BN___test0_zf__spec _a _b_a =
   hoare [M.h__BN___test0_zf_ :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray56.is_init _b_a 0 56)) ==>
   (true /\ (valid res.`2))].

op h__BN___test0__spec _a _b_a =
   hoare [M.h__BN___test0_ :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray56.is_init _b_a 0 56)) ==>
   (true /\ (valid res.`2))].

op h__BN____copy_spec _a _b_a =
   hoare [M.h__BN____copy :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

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

op h__BN____cswap_mask_spec _x _b_x _y _b_y _mask =
   hoare [M.h__BN____cswap_mask :
   (((_mask = mask) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_y 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   (((BArray56.is_init res.`4 0 56) /\ (BArray56.is_init res.`2 0 56)) /\
   (valid res.`5))].

op h__BN___cswap_mask_spec _x _b_x _y _b_y _mask =
   hoare [M.h__BN___cswap_mask :
   (((_mask = mask) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_y 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   (((BArray56.is_init res.`4 0 56) /\ (BArray56.is_init res.`2 0 56)) /\
   (valid res.`5))].

op h__BN___cswap_mask__spec _x _b_x _y _b_y _mask =
   hoare [M.h__BN___cswap_mask_ :
   (((_mask = mask) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_y 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   (((BArray56.is_init res.`4 0 56) /\ (BArray56.is_init res.`2 0 56)) /\
   (valid res.`5))].

op h__BN___cswap_cf__spec _x _b_x _y _b_y _cf =
   hoare [M.h__BN___cswap_cf_ :
   (((_cf = cf) /\
    ((_b_y = b_y) /\ ((_y = y) /\ ((_b_x = b_x) /\ (_x = x))))) /\
   ((BArray56.is_init _b_y 0 56) /\ (BArray56.is_init _b_x 0 56))) ==>
   (((BArray56.is_init res.`4 0 56) /\ (BArray56.is_init res.`2 0 56)) /\
   (valid res.`5))].

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

op h__BN____cfill_spec _a _b_a _b _x =
   hoare [M.h__BN____cfill :
   (((_x = x) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN____or_mask_spec _a _b_a _mask =
   hoare [M.h__BN____or_mask :
   (((_mask = mask) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___or_mask_spec _a _b_a _mask =
   hoare [M.h__BN___or_mask :
   (((_mask = mask) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___or_mask__spec _a _b_a _mask =
   hoare [M.h__BN___or_mask_ :
   (((_mask = mask) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

op h__BN___set_err__spec _a _b_a __err =
   hoare [M.h__BN___set_err_ :
   (((__err = _err) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
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

op h__BN____carrypropU_spec _a _b_a _cf _k =
   hoare [M.h__BN____carrypropU :
   (((_k = k) /\ ((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   (true /\ ((0 <= _k) /\ (BArray56.is_init _b_a 0 (8 * 7))))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

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

op h__BN___addcU__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addcU_ :
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

op h__BN___addc__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___addc_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
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

op h__BN___subcU__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subcU_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
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

op h__BN___subc__spec _r _b_r _a _b_a _b _b_b _cf =
   hoare [M.h__BN___subc_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
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

op h__BN___ltc_cf__spec _a _b_a _b _b_b _cf =
   hoare [M.h__BN___ltc_cf_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56))) ==>
   (true /\ (valid res.`2))].

op h__BN____negc1U_spec _a _b_a _cf =
   hoare [M.h__BN____negc1U :
   (((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___negc1U_spec _a _b_a _cf =
   hoare [M.h__BN___negc1U :
   (((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___negc1U__spec _a _b_a _cf =
   hoare [M.h__BN___negc1U_ :
   (((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___negU__spec _a _b_a =
   hoare [M.h__BN___negU_ :
   (((_b_a = b_a) /\ (_a = a)) /\ (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

op h__BN___negcU__spec _a _b_a _cf =
   hoare [M.h__BN___negcU_ :
   (((_cf = cf) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`3 0 56) /\ (valid res.`4))].

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

op h__BN___negc__spec _r _b_r _a _b_a _cf =
   hoare [M.h__BN___negc_ :
   (((_cf = cf) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray56.is_init _b_a 0 (8 * 7))) ==>
   ((BArray56.is_init res.`3 0 (8 * 7)) /\ (valid res.`4))].

op h__BN___cnegU__spec _a _b_a _cond =
   hoare [M.h__BN___cnegU_ :
   (((_cond = cond) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (BArray56.is_init _b_a 0 56)) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].

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

op h__BN____pack2_spec _r _b_r _lo _b_lo _hi _b_hi =
   hoare [M.h__BN____pack2 :
   (((_b_hi = b_hi) /\
    ((_hi = hi) /\
    ((_b_lo = b_lo) /\ ((_lo = lo) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_lo 0 (8 * 7)) /\ (BArray56.is_init _b_hi 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__BN___pack2__spec _r _b_r _lo _b_lo _hi _b_hi =
   hoare [M.h__BN___pack2_ :
   (((_b_hi = b_hi) /\
    ((_hi = hi) /\
    ((_b_lo = b_lo) /\ ((_lo = lo) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_lo 0 (8 * 7)) /\ (BArray56.is_init _b_hi 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].
