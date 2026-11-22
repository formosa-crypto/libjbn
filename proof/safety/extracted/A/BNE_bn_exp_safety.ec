require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array11 Array13 Array45 Array88 Array104 Array176 Array360 Array1408 BArray88
BArray104 BArray360 BArray1408 SBArray360_88 SBArray1408_88.

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
  proc h__EXP__fun_mulU (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                         b_b:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var trace_h__EXP__fun_mulU:trace;
    trace_h__EXP__fun_mulU <- [];
    trace_h__EXP__fun_mulU <-
    (trace_h__EXP__fun_mulU ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP__fun_mulU <-
    (trace_h__EXP__fun_mulU ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__EXP__fun_mulU <-
    (trace_h__EXP__fun_mulU ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__EXP__fun_mulU);
  }
  proc h__EXP__fun_sqrU (a:BArray88.t, b_a:BArray88.t, ctx:BArray360.t,
                         b_ctx:BArray360.t) : BArray88.t * BArray88.t * trace = {
    var trace_h__EXP__fun_sqrU:trace;
    trace_h__EXP__fun_sqrU <- [];
    trace_h__EXP__fun_sqrU <-
    (trace_h__EXP__fun_sqrU ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP__fun_sqrU <-
    (trace_h__EXP__fun_sqrU ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__EXP__fun_sqrU);
  }
  proc h__EXP___exp1mLR_first_noct (r:BArray88.t, b_r:BArray88.t,
                                    x:BArray88.t, b_x:BArray88.t, w:W64.t,
                                    ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var _x:BArray88.t;
    var _ctx:BArray360.t;
    var k:W64.t;
    var cf:bool;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var _k:W64.t;
    var _w:W64.t;
    var param_1:BArray88.t;
    var param_2:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
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
    var trace_h__EXP___exp1mLR_first_noct:trace;
    _ctx <- witness;
    _x <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
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
    trace_h__EXP___exp1mLR_first_noct <- [];
    trace_h__EXP___exp1mLR_first_noct <-
    (trace_h__EXP___exp1mLR_first_noct ++
    [(Assert,
     ((BArray88.is_init b_x 0 88) /\ (BArray360.is_init b_ctx 0 360)))]);
    _x <- x;
    _ctx <- ctx;
    k <- (W64.of_int 64);
    ( _0, cf,  _1,  _2,  _3, w) <- (SHL_64 w (W8.of_int 1));
    while ((! cf)) {
      k <- (k - (W64.of_int 1));
      ( _4, cf,  _5,  _6,  _7, w) <- (SHL_64 w (W8.of_int 1));
    }
    b_param <- b_r;
    param <- r;
    param_0 <- x;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__EXP___exp1mLR_first_noct <-
    (trace_h__EXP___exp1mLR_first_noct ++ tmp__trace);
    trace_h__EXP___exp1mLR_first_noct <-
    (trace_h__EXP___exp1mLR_first_noct ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    k <- (k - (W64.of_int 1));
    while (((W64.of_int 0) \slt k)) {
      _k <- k;
      _w <- w;
      ctx <- _ctx;
      param_1 <- r;
      param_2 <- ctx;
      (aux_1, aux_2, tmp__trace) <@ h__EXP__fun_sqrU (param_1,
      (BArray88.init_arr (W8.of_int 255)), param_2,
      (BArray360.init_arr (W8.of_int 255)));
      result_0 <- aux_1;
      b_result_0 <- aux_2;
      trace_h__EXP___exp1mLR_first_noct <-
      (trace_h__EXP___exp1mLR_first_noct ++ tmp__trace);
      trace_h__EXP___exp1mLR_first_noct <-
      (trace_h__EXP___exp1mLR_first_noct ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      r <- result_0;
      w <- _w;
      ( _8, cf,  _9,  _10,  _11, w) <- (SHL_64 w (W8.of_int 1));
      _w <- w;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_3 <- r;
        param_4 <- x;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__EXP__fun_mulU (param_3,
        (BArray88.init_arr (W8.of_int 255)), param_4,
        (BArray88.init_arr (W8.of_int 255)), param_5,
        (BArray360.init_arr (W8.of_int 255)));
        result_1 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__EXP___exp1mLR_first_noct <-
        (trace_h__EXP___exp1mLR_first_noct ++ tmp__trace);
        trace_h__EXP___exp1mLR_first_noct <-
        (trace_h__EXP___exp1mLR_first_noct ++
        [(Assert, (BArray88.is_init b_result_1 0 88))]);
        r <- result_1;
      } else {
        
      }
      w <- _w;
      k <- _k;
      k <- (k - (W64.of_int 1));
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___exp1mLR_first_noct);
  }
  proc h__EXP___exp1mLR_noct (r:BArray88.t, b_r:BArray88.t, x:BArray88.t,
                              b_x:BArray88.t, w:W64.t, ctx:BArray360.t,
                              b_ctx:BArray360.t) : BArray88.t * BArray88.t *
                                                   trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var _x:BArray88.t;
    var _ctx:BArray360.t;
    var k:W64.t;
    var _k:W64.t;
    var _w:W64.t;
    var param:BArray88.t;
    var param_0:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var cf:bool;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var trace_h__EXP___exp1mLR_noct:trace;
    _ctx <- witness;
    _x <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__EXP___exp1mLR_noct <- [];
    trace_h__EXP___exp1mLR_noct <-
    (trace_h__EXP___exp1mLR_noct ++ [(Assert, (BArray88.is_init b_r 0 88))]);
    trace_h__EXP___exp1mLR_noct <-
    (trace_h__EXP___exp1mLR_noct ++ [(Assert, (BArray88.is_init b_x 0 88))]);
    trace_h__EXP___exp1mLR_noct <-
    (trace_h__EXP___exp1mLR_noct ++
    [(Assert, (BArray360.is_init b_ctx 0 360))]);
    _x <- x;
    _ctx <- ctx;
    k <- (W64.of_int 64);
    while (((W64.of_int 0) \slt k)) {
      _k <- k;
      _w <- w;
      ctx <- _ctx;
      param <- r;
      param_0 <- ctx;
      (aux, aux_0, tmp__trace) <@ h__EXP__fun_sqrU (param,
      (BArray88.init_arr (W8.of_int 255)), param_0,
      (BArray360.init_arr (W8.of_int 255)));
      result <- aux;
      b_result <- aux_0;
      trace_h__EXP___exp1mLR_noct <-
      (trace_h__EXP___exp1mLR_noct ++ tmp__trace);
      trace_h__EXP___exp1mLR_noct <-
      (trace_h__EXP___exp1mLR_noct ++
      [(Assert, (BArray88.is_init b_result 0 88))]);
      r <- result;
      w <- _w;
      ( _0, cf,  _1,  _2,  _3, w) <- (SHL_64 w (W8.of_int 1));
      _w <- w;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_1 <- r;
        param_2 <- x;
        param_3 <- ctx;
        (aux_1, aux_2, tmp__trace) <@ h__EXP__fun_mulU (param_1,
        (BArray88.init_arr (W8.of_int 255)), param_2,
        (BArray88.init_arr (W8.of_int 255)), param_3,
        (BArray360.init_arr (W8.of_int 255)));
        result_0 <- aux_1;
        b_result_0 <- aux_2;
        trace_h__EXP___exp1mLR_noct <-
        (trace_h__EXP___exp1mLR_noct ++ tmp__trace);
        trace_h__EXP___exp1mLR_noct <-
        (trace_h__EXP___exp1mLR_noct ++
        [(Assert, (BArray88.is_init b_result_0 0 88))]);
        r <- result_0;
      } else {
        
      }
      w <- _w;
      k <- _k;
      k <- (k - (W64.of_int 1));
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___exp1mLR_noct);
  }
  proc h__EXP___expmLR_noct (r:BArray88.t, b_r:BArray88.t, x:BArray88.t,
                             b_x:BArray88.t, e:BArray104.t, b_e:BArray104.t,
                             ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                   BArray88.t *
                                                                   trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var aux_3:BArray88.t;
    var aux_4:BArray88.t;
    var _x:BArray88.t;
    var _e:BArray104.t;
    var _ctx:BArray360.t;
    var i:W64.t;
    var w:W64.t;
    var i_s:W64.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:W64.t;
    var param_2:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_exp0:BArray88.t;
    var exp0:BArray88.t;
    var b_param_0:BArray88.t;
    var param_3:BArray88.t;
    var b_param_1:BArray88.t;
    var param_4:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_5:BArray88.t;
    var param_6:BArray88.t;
    var param_7:W64.t;
    var param_8:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var trace_h__EXP___expmLR_noct:trace;
    _ctx <- witness;
    _e <- witness;
    _x <- witness;
    b_exp0 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    exp0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    trace_h__EXP___expmLR_noct <- [];
    trace_h__EXP___expmLR_noct <-
    (trace_h__EXP___expmLR_noct ++
    [(Assert,
     (((BArray88.is_init b_x 0 88) /\ (BArray104.is_init b_e 0 104)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    _x <- x;
    _e <- e;
    _ctx <- ctx;
    i <- (W64.of_int (13 - 1));
    trace_h__EXP___expmLR_noct <-
    (trace_h__EXP___expmLR_noct ++
    [(Assert,
     ((0 <= ((W64.to_uint i) * 8)) /\ ((((W64.to_uint i) * 8) + 8) <= 104)))]);
    w <- (BArray104.get64 e (W64.to_uint i));
    while ((w = (W64.of_int 0))) {
      i <- (i - (W64.of_int 1));
      if (((W64.of_int 0) \sle i)) {
        trace_h__EXP___expmLR_noct <-
        (trace_h__EXP___expmLR_noct ++
        [(Assert,
         ((0 <= ((W64.to_uint i) * 8)) /\
         ((((W64.to_uint i) * 8) + 8) <= 104)))]);
        w <- (BArray104.get64 e (W64.to_uint i));
      } else {
        w <- (W64.of_int 1);
      }
    }
    if (((W64.of_int 0) \sle i)) {
      i_s <- i;
      x <- _x;
      ctx <- _ctx;
      b_param <- b_r;
      param <- r;
      param_0 <- x;
      param_1 <- w;
      param_2 <- ctx;
      (aux_1, aux_2, tmp__trace) <@ h__EXP___exp1mLR_first_noct (param,
      b_param, param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
      param_2, (BArray360.init_arr (W8.of_int 255)));
      result <- aux_1;
      b_result <- aux_2;
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++ tmp__trace);
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++
      [(Assert, (BArray88.is_init b_result 0 88))]);
      r <- result;
      i <- i_s;
      i <- (i - (W64.of_int 1));
    } else {
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++
      [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
      b_exp0 <- (SBArray360_88.get_sub64 b_ctx 22);
      exp0 <- (SBArray360_88.get_sub64 ctx 22);
      b_param_0 <- b_r;
      param_3 <- r;
      b_param_1 <- b_exp0;
      param_4 <- exp0;
      (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param_3, b_param_0, param_4,
      b_param_1);
      result_0 <- aux;
      b_result_0 <- aux_0;
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++ tmp__trace);
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      r <- result_0;
    }
    while (((W64.of_int 0) \sle i)) {
      e <- _e;
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++
      [(Assert,
       ((0 <= ((W64.to_uint i) * 8)) /\ ((((W64.to_uint i) * 8) + 8) <= 104)))]);
      w <- (BArray104.get64 e (W64.to_uint i));
      i_s <- i;
      x <- _x;
      ctx <- _ctx;
      param_5 <- r;
      param_6 <- x;
      param_7 <- w;
      param_8 <- ctx;
      (aux_3, aux_4, tmp__trace) <@ h__EXP___exp1mLR_noct (param_5,
      (BArray88.init_arr (W8.of_int 255)), param_6,
      (BArray88.init_arr (W8.of_int 255)), param_7, param_8,
      (BArray360.init_arr (W8.of_int 255)));
      result_1 <- aux_3;
      b_result_1 <- aux_4;
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++ tmp__trace);
      trace_h__EXP___expmLR_noct <-
      (trace_h__EXP___expmLR_noct ++
      [(Assert, (BArray88.is_init b_result_1 0 88))]);
      r <- result_1;
      i <- i_s;
      i <- (i - (W64.of_int 1));
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___expmLR_noct);
  }
  proc h__EXP___expmLR_noct_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                              b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
                              ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                    BArray88.t *
                                                                    trace = {
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
    var param_3:BArray104.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__EXP___expmLR_noct_:trace;
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
    trace_h__EXP___expmLR_noct_ <- [];
    trace_h__EXP___expmLR_noct_ <-
    (trace_h__EXP___expmLR_noct_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray104.is_init b_b 0 104)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    trace_h__EXP___expmLR_noct_ <-
    (trace_h__EXP___expmLR_noct_ ++
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
    trace_h__EXP___expmLR_noct_ <-
    (trace_h__EXP___expmLR_noct_ ++ tmp__trace);
    trace_h__EXP___expmLR_noct_ <-
    (trace_h__EXP___expmLR_noct_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    a <- a;
    b <- b;
    param_1 <- r;
    param_2 <- a;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__EXP___expmLR_noct (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray104.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__EXP___expmLR_noct_ <-
    (trace_h__EXP___expmLR_noct_ ++ tmp__trace);
    trace_h__EXP___expmLR_noct_ <-
    (trace_h__EXP___expmLR_noct_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___expmLR_noct_);
  }
  proc h__EXP___expm_noct (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                           b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
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
    var b__x:BArray88.t;
    var _b:BArray104.t;
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
    var trace_h__EXP___expm_noct:trace;
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
    trace_h__EXP___expm_noct <- [];
    trace_h__EXP___expm_noct <-
    (trace_h__EXP___expm_noct ++ [(Assert, (BArray88.is_init b_r 0 88))]);
    trace_h__EXP___expm_noct <-
    (trace_h__EXP___expm_noct ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP___expm_noct <-
    (trace_h__EXP___expm_noct ++ [(Assert, (BArray104.is_init b_b 0 104))]);
    trace_h__EXP___expm_noct <-
    (trace_h__EXP___expm_noct ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
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
    trace_h__EXP___expm_noct <- (trace_h__EXP___expm_noct ++ tmp__trace);
    trace_h__EXP___expm_noct <-
    (trace_h__EXP___expm_noct ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    x <- result;
    _x <- x;
    j <- 0;
    while ((j < 13)) {
      b <- _b;
      trace_h__EXP___expm_noct <-
      (trace_h__EXP___expm_noct ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 104)))]);
      t <- (BArray104.get64 b j);
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- (SHR_64 t (W8.of_int 1));
      _t <- t;
      if (cf) {
        x <- _x;
        ctx <- _ctx;
        param_1 <- r;
        param_2 <- x;
        param_3 <- ctx;
        (aux_5, aux_6, tmp__trace) <@ h__EXP__fun_mulU (param_1,
        (BArray88.init_arr (W8.of_int 255)), param_2,
        (BArray88.init_arr (W8.of_int 255)), param_3,
        (BArray360.init_arr (W8.of_int 255)));
        result_0 <- aux_5;
        b_result_0 <- aux_6;
        trace_h__EXP___expm_noct <- (trace_h__EXP___expm_noct ++ tmp__trace);
        trace_h__EXP___expm_noct <-
        (trace_h__EXP___expm_noct ++
        [(Assert, (BArray88.is_init b_result_0 0 88))]);
        r <- result_0;
      } else {
        
      }
      _r <- r;
      x <- _x;
      ctx <- _ctx;
      param_4 <- x;
      param_5 <- ctx;
      (aux_7, aux_8, tmp__trace) <@ h__EXP__fun_sqrU (param_4,
      (BArray88.init_arr (W8.of_int 255)), param_5,
      (BArray360.init_arr (W8.of_int 255)));
      result_1 <- aux_7;
      b_result_1 <- aux_8;
      trace_h__EXP___expm_noct <- (trace_h__EXP___expm_noct ++ tmp__trace);
      trace_h__EXP___expm_noct <-
      (trace_h__EXP___expm_noct ++
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
          (aux_1, aux_2, tmp__trace) <@ h__EXP__fun_mulU (param_1,
          (BArray88.init_arr (W8.of_int 255)), param_2,
          (BArray88.init_arr (W8.of_int 255)), param_3,
          (BArray360.init_arr (W8.of_int 255)));
          result_0 <- aux_1;
          b_result_0 <- aux_2;
          trace_h__EXP___expm_noct <-
          (trace_h__EXP___expm_noct ++ tmp__trace);
          trace_h__EXP___expm_noct <-
          (trace_h__EXP___expm_noct ++
          [(Assert, (BArray88.is_init b_result_0 0 88))]);
          r <- result_0;
        } else {
          
        }
        _r <- r;
        x <- _x;
        ctx <- _ctx;
        param_4 <- x;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__EXP__fun_sqrU (param_4,
        (BArray88.init_arr (W8.of_int 255)), param_5,
        (BArray360.init_arr (W8.of_int 255)));
        result_1 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__EXP___expm_noct <- (trace_h__EXP___expm_noct ++ tmp__trace);
        trace_h__EXP___expm_noct <-
        (trace_h__EXP___expm_noct ++
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
    return (r, b_r, trace_h__EXP___expm_noct);
  }
  proc h__EXP___expm_noct_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                            b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
                            ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                                  BArray88.t *
                                                                  trace = {
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
    var param_3:BArray104.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__EXP___expm_noct_:trace;
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
    trace_h__EXP___expm_noct_ <- [];
    trace_h__EXP___expm_noct_ <-
    (trace_h__EXP___expm_noct_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray104.is_init b_b 0 104)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    trace_h__EXP___expm_noct_ <-
    (trace_h__EXP___expm_noct_ ++
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
    trace_h__EXP___expm_noct_ <- (trace_h__EXP___expm_noct_ ++ tmp__trace);
    trace_h__EXP___expm_noct_ <-
    (trace_h__EXP___expm_noct_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    a <- a;
    b <- b;
    param_1 <- r;
    param_2 <- a;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__EXP___expm_noct (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray104.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__EXP___expm_noct_ <- (trace_h__EXP___expm_noct_ ++ tmp__trace);
    trace_h__EXP___expm_noct_ <-
    (trace_h__EXP___expm_noct_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___expm_noct_);
  }
  proc h__EXP___expmU_noct_ (a:BArray88.t, b_a:BArray88.t, b:BArray104.t,
                             b_b:BArray104.t, ctx:BArray360.t,
                             b_ctx:BArray360.t) : BArray88.t * BArray88.t *
                                                  trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray88.t;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var _tmp:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray104.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__EXP___expmU_noct_:trace;
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
    trace_h__EXP___expmU_noct_ <- [];
    trace_h__EXP___expmU_noct_ <-
    (trace_h__EXP___expmU_noct_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP___expmU_noct_ <-
    (trace_h__EXP___expmU_noct_ ++ [(Assert, (BArray104.is_init b_b 0 104))]);
    trace_h__EXP___expmU_noct_ <-
    (trace_h__EXP___expmU_noct_ ++
    [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__tmp <- (BArray88.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__EXP___expmU_noct_ <- (trace_h__EXP___expmU_noct_ ++ tmp__trace);
    trace_h__EXP___expmU_noct_ <-
    (trace_h__EXP___expmU_noct_ ++
    [(Assert, (BArray88.is_init b_result 0 88))]);
    tmp <- result;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__EXP___expm_noct_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray104.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__EXP___expmU_noct_ <- (trace_h__EXP___expmU_noct_ ++ tmp__trace);
    trace_h__EXP___expmU_noct_ <-
    (trace_h__EXP___expmU_noct_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__EXP___expmU_noct_);
  }
  proc h__EXP___expmML (x0:BArray88.t, b_x0:BArray88.t, x1:BArray88.t,
                        b_x1:BArray88.t, b:BArray104.t, b_b:BArray104.t,
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
    var _b:BArray104.t;
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
    var trace_h__EXP___expmML:trace;
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
    trace_h__EXP___expmML <- [];
    trace_h__EXP___expmML <-
    (trace_h__EXP___expmML ++ [(Assert, (BArray88.is_init b_x0 0 88))]);
    trace_h__EXP___expmML <-
    (trace_h__EXP___expmML ++ [(Assert, (BArray88.is_init b_x1 0 88))]);
    trace_h__EXP___expmML <-
    (trace_h__EXP___expmML ++ [(Assert, (BArray104.is_init b_b 0 104))]);
    trace_h__EXP___expmML <-
    (trace_h__EXP___expmML ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    _b <- b;
    _ctx <- ctx;
    _mask <- (W64.of_int 0);
    j <- (13 - 1);
    while (((-1) < j)) {
      b <- _b;
      trace_h__EXP___expmML <-
      (trace_h__EXP___expmML ++
      [(Assert, ((0 <= (j * 8)) /\ (((j * 8) + 8) <= 104)))]);
      t <- (BArray104.get64 b j);
      _k <- (W64.of_int 64);
      ( _0, cf,  _1,  _2,  _3, t) <- (SHL_64 t (W8.of_int 1));
      _t <- t;
      param <- cf;
      (result, tmp__trace) <@ uTIL____cf_mask (param);
      trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
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
      trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
      trace_h__EXP___expmML <-
      (trace_h__EXP___expmML ++ [(Assert, (BArray88.is_init b_result 0 88))]);
      trace_h__EXP___expmML <-
      (trace_h__EXP___expmML ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      x0 <- result_0;
      x1 <- result_1;
      _x0 <- x0;
      ctx <- _ctx;
      param_3 <- x1;
      param_4 <- x0;
      param_5 <- ctx;
      (aux_11, aux_12, tmp__trace) <@ h__EXP__fun_mulU (param_3,
      (BArray88.init_arr (W8.of_int 255)), param_4,
      (BArray88.init_arr (W8.of_int 255)), param_5,
      (BArray360.init_arr (W8.of_int 255)));
      result_2 <- aux_11;
      b_result_1 <- aux_12;
      trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
      trace_h__EXP___expmML <-
      (trace_h__EXP___expmML ++
      [(Assert, (BArray88.is_init b_result_1 0 88))]);
      x1 <- result_2;
      _x1 <- x1;
      x0 <- _x0;
      ctx <- _ctx;
      param_6 <- x0;
      param_7 <- ctx;
      (aux_13, aux_14, tmp__trace) <@ h__EXP__fun_sqrU (param_6,
      (BArray88.init_arr (W8.of_int 255)), param_7,
      (BArray360.init_arr (W8.of_int 255)));
      result_3 <- aux_13;
      b_result_2 <- aux_14;
      trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
      trace_h__EXP___expmML <-
      (trace_h__EXP___expmML ++
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
        trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
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
        trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
        trace_h__EXP___expmML <-
        (trace_h__EXP___expmML ++
        [(Assert, (BArray88.is_init b_result 0 88))]);
        trace_h__EXP___expmML <-
        (trace_h__EXP___expmML ++
        [(Assert, (BArray88.is_init b_result_0 0 88))]);
        x0 <- result_0;
        x1 <- result_1;
        _x0 <- x0;
        ctx <- _ctx;
        param_3 <- x1;
        param_4 <- x0;
        param_5 <- ctx;
        (aux_3, aux_4, tmp__trace) <@ h__EXP__fun_mulU (param_3,
        (BArray88.init_arr (W8.of_int 255)), param_4,
        (BArray88.init_arr (W8.of_int 255)), param_5,
        (BArray360.init_arr (W8.of_int 255)));
        result_2 <- aux_3;
        b_result_1 <- aux_4;
        trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
        trace_h__EXP___expmML <-
        (trace_h__EXP___expmML ++
        [(Assert, (BArray88.is_init b_result_1 0 88))]);
        x1 <- result_2;
        _x1 <- x1;
        x0 <- _x0;
        ctx <- _ctx;
        param_6 <- x0;
        param_7 <- ctx;
        (aux_5, aux_6, tmp__trace) <@ h__EXP__fun_sqrU (param_6,
        (BArray88.init_arr (W8.of_int 255)), param_7,
        (BArray360.init_arr (W8.of_int 255)));
        result_3 <- aux_5;
        b_result_2 <- aux_6;
        trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
        trace_h__EXP___expmML <-
        (trace_h__EXP___expmML ++
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
    trace_h__EXP___expmML <- (trace_h__EXP___expmML ++ tmp__trace);
    trace_h__EXP___expmML <-
    (trace_h__EXP___expmML ++ [(Assert, (BArray88.is_init b_result_3 0 88))]);
    trace_h__EXP___expmML <-
    (trace_h__EXP___expmML ++ [(Assert, (BArray88.is_init b_result_4 0 88))]);
    x0 <- result_4;
    x1 <- result_5;
    b_x0 <- (BArray88.init_arr (W8.of_int 255));
    b_x1 <- (BArray88.init_arr (W8.of_int 255));
    return (x0, b_x0, x1, b_x1, trace_h__EXP___expmML);
  }
  proc h__EXP___expmML_ (x0:BArray88.t, b_x0:BArray88.t, a:BArray88.t,
                         b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
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
    var param_5:BArray104.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var result_2:BArray88.t;
    var b_result_2:BArray88.t;
    var trace_h__EXP___expmML_:trace;
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
    trace_h__EXP___expmML_ <- [];
    trace_h__EXP___expmML_ <-
    (trace_h__EXP___expmML_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray104.is_init b_b 0 104)) /\
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
    trace_h__EXP___expmML_ <- (trace_h__EXP___expmML_ ++ tmp__trace);
    trace_h__EXP___expmML_ <-
    (trace_h__EXP___expmML_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    x1 <- result;
    trace_h__EXP___expmML_ <-
    (trace_h__EXP___expmML_ ++
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
    trace_h__EXP___expmML_ <- (trace_h__EXP___expmML_ ++ tmp__trace);
    trace_h__EXP___expmML_ <-
    (trace_h__EXP___expmML_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    x0 <- result_0;
    b <- b;
    param_3 <- x0;
    param_4 <- x1;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, aux_5, aux_6, tmp__trace) <@ h__EXP___expmML (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray104.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__EXP___expmML_ <- (trace_h__EXP___expmML_ ++ tmp__trace);
    trace_h__EXP___expmML_ <-
    (trace_h__EXP___expmML_ ++
    [(Assert, (BArray88.is_init b_result_1 0 88))]);
    trace_h__EXP___expmML_ <-
    (trace_h__EXP___expmML_ ++
    [(Assert, (BArray88.is_init b_result_2 0 88))]);
    x0 <- result_1;
    x0 <- x0;
    b_x0 <- (BArray88.init_arr (W8.of_int 255));
    return (x0, b_x0, trace_h__EXP___expmML_);
  }
  proc h__EXP___expmMLU_ (a:BArray88.t, b_a:BArray88.t, b:BArray104.t,
                          b_b:BArray104.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
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
    var param_1:BArray88.t;
    var b_param_0:BArray88.t;
    var param_2:BArray88.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray104.t;
    var param_6:BArray360.t;
    var result_1:BArray88.t;
    var b_result_1:BArray88.t;
    var result_2:BArray88.t;
    var b_result_2:BArray88.t;
    var trace_h__EXP___expmMLU_:trace;
    _x1 <- witness;
    b__x1 <- witness;
    b_exp0 <- witness;
    b_param <- witness;
    b_param_0 <- witness;
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
    trace_h__EXP___expmMLU_ <- [];
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++ [(Assert, (BArray104.is_init b_b 0 104))]);
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
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
    trace_h__EXP___expmMLU_ <- (trace_h__EXP___expmMLU_ ++ tmp__trace);
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    x1 <- result;
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++
    [(Assert, ((0 <= (22 * 8)) /\ (((22 * 8) + 88) <= 360)))]);
    b_exp0 <- (SBArray360_88.get_sub64 b_ctx 22);
    exp0 <- (SBArray360_88.get_sub64 ctx 22);
    param_1 <- a;
    b_param_0 <- b_exp0;
    param_2 <- exp0;
    (aux_1, aux_2, tmp__trace) <@ h__BN___mov_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2, b_param_0);
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__EXP___expmMLU_ <- (trace_h__EXP___expmMLU_ ++ tmp__trace);
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    b <- b;
    param_3 <- a;
    param_4 <- x1;
    param_5 <- b;
    param_6 <- ctx;
    (aux_3, aux_4, aux_5, aux_6, tmp__trace) <@ h__EXP___expmML (param_3,
    (BArray88.init_arr (W8.of_int 255)), param_4,
    (BArray88.init_arr (W8.of_int 255)), param_5,
    (BArray104.init_arr (W8.of_int 255)), param_6,
    (BArray360.init_arr (W8.of_int 255)));
    result_1 <- aux_3;
    b_result_1 <- aux_4;
    result_2 <- aux_5;
    b_result_2 <- aux_6;
    trace_h__EXP___expmMLU_ <- (trace_h__EXP___expmMLU_ ++ tmp__trace);
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++
    [(Assert, (BArray88.is_init b_result_1 0 88))]);
    trace_h__EXP___expmMLU_ <-
    (trace_h__EXP___expmMLU_ ++
    [(Assert, (BArray88.is_init b_result_2 0 88))]);
    a <- result_1;
    a <- a;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__EXP___expmMLU_);
  }
  proc h__EXP____tblsel (r:BArray88.t, b_r:BArray88.t, tbl:BArray1408.t,
                         b_tbl:BArray1408.t, idx:W64.t) : BArray88.t *
                                                          BArray88.t * trace = {
    var k:W64.t;
    var t:W64.t;
    var i:int;
    var zf:bool;
    var trace_h__EXP____tblsel:trace;
    trace_h__EXP____tblsel <- [];
    trace_h__EXP____tblsel <-
    (trace_h__EXP____tblsel ++ [(Assert, (BArray1408.is_init b_tbl 0 1408))]);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 11))) {
      trace_h__EXP____tblsel <-
      (trace_h__EXP____tblsel ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\
       ((((W64.to_uint k) * 8) + 8) <= 1408)))]);
      t <- (BArray1408.get64 tbl (W64.to_uint k));
      i <- 1;
      while ((i < 16)) {
        zf <- (idx = (W64.of_int i));
        trace_h__EXP____tblsel <-
        (trace_h__EXP____tblsel ++
        [(Assert,
         ((0 <= ((W64.to_uint (k + (W64.of_int (i * 11)))) * 8)) /\
         ((((W64.to_uint (k + (W64.of_int (i * 11)))) * 8) + 8) <= 1408)))]);
        t <-
        (zf ? (BArray1408.get64 tbl (W64.to_uint (k + (W64.of_int (i * 11))))
              ) : t);
        i <- (i + 1);
      }
      trace_h__EXP____tblsel <-
      (trace_h__EXP____tblsel ++
      [(Assert,
       ((0 <= ((W64.to_uint k) * 8)) /\ ((((W64.to_uint k) * 8) + 8) <= 88)))]);
      b_r <-
      (BArray88.set64d b_r ((W64.to_uint k) * 8)
      (W64.of_int 18446744073709551615));
      r <- (BArray88.set64 r (W64.to_uint k) t);
      k <- (k + (W64.of_int 1));
    }
    return (r, b_r, trace_h__EXP____tblsel);
  }
  proc h__EXP___expmW (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
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
    var _b:BArray104.t;
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
    var trace_h__EXP___expmW:trace;
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
    trace_h__EXP___expmW <- [];
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray104.is_init b_b 0 104)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b_tbl <- (BArray1408.init_arr (W8.of_int 0));
    b_sel <- (BArray88.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _a <- a;
    _b <- b;
    _ctx <- ctx;
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++
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
    trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    p <- result;
    b_tbl <-
    (SBArray1408_88.set_sub64 b_tbl 0 (BArray88.init_arr (W8.of_int 255)));
    tbl <- (SBArray1408_88.set_sub64 tbl 0 p);
    a <- _a;
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++
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
    trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    p <- result_0;
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++
    [(Assert, ((0 <= (11 * 8)) /\ (((11 * 8) + 88) <= 1408)))]);
    b_tbl <-
    (SBArray1408_88.set_sub64 b_tbl 11 (BArray88.init_arr (W8.of_int 255)));
    tbl <- (SBArray1408_88.set_sub64 tbl 11 p);
    i <- 2;
    while ((i < 16)) {
      a <- _a;
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
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
      trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
      [(Assert, (BArray88.is_init b_result_1 0 88))]);
      p <- result_1;
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
      [(Assert, ((0 <= ((i * 11) * 8)) /\ ((((i * 11) * 8) + 88) <= 1408)))]);
      b_tbl <-
      (SBArray1408_88.set_sub64 b_tbl (i * 11)
      (BArray88.init_arr (W8.of_int 255)));
      tbl <- (SBArray1408_88.set_sub64 tbl (i * 11) p);
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
      [(Assert,
       ((0 <= (((i - 1) * 11) * 8)) /\ (((((i - 1) * 11) * 8) + 88) <= 1408)))]);
      b_q <- (SBArray1408_88.get_sub64 b_tbl ((i - 1) * 11));
      q <- (SBArray1408_88.get_sub64 tbl ((i - 1) * 11));
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
      [(Assert, ((0 <= ((i * 11) * 8)) /\ ((((i * 11) * 8) + 88) <= 1408)))]);
      b_p <- (SBArray1408_88.get_sub64 b_tbl (i * 11));
      p <- (SBArray1408_88.get_sub64 tbl (i * 11));
      ctx <- _ctx;
      b_param_3 <- b_p;
      param_5 <- p;
      b_param_4 <- b_q;
      param_6 <- q;
      param_7 <- ctx;
      (aux_5, aux_6, tmp__trace) <@ h__EXP__fun_mulU (param_5, b_param_3,
      param_6, b_param_4, param_7, (BArray360.init_arr (W8.of_int 255)));
      result_2 <- aux_5;
      b_result_2 <- aux_6;
      trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
      [(Assert, (BArray88.is_init b_result_2 0 88))]);
      p <- result_2;
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
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
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++
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
    trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
    trace_h__EXP___expmW <-
    (trace_h__EXP___expmW ++ [(Assert, (BArray88.is_init b_result_3 0 88))]);
    r <- result_3;
    j <- (W64.of_int 13);
    while ((j <> (W64.of_int 0))) {
      j <- (j - (W64.of_int 1));
      _j <- j;
      b <- _b;
      trace_h__EXP___expmW <-
      (trace_h__EXP___expmW ++
      [(Assert,
       ((0 <= ((W64.to_uint j) * 8)) /\ ((((W64.to_uint j) * 8) + 8) <= 104)))]);
      t <- (BArray104.get64 b (W64.to_uint j));
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
        (aux_9, aux_10, tmp__trace) <@ h__EXP____tblsel (param_10, b_param_7,
        param_11, b_param_8, param_12);
        result_4 <- aux_9;
        b_result_4 <- aux_10;
        trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
        trace_h__EXP___expmW <-
        (trace_h__EXP___expmW ++
        [(Assert, (BArray88.is_init b_result_4 0 88))]);
        psel <- result_4;
        b_sel <- (BArray88.init_arr (W8.of_int 255));
        sel <- psel;
        s <- 0;
        while ((s < 4)) {
          ctx <- _ctx;
          param_13 <- r;
          param_14 <- ctx;
          (aux_11, aux_12, tmp__trace) <@ h__EXP__fun_sqrU (param_13,
          (BArray88.init_arr (W8.of_int 255)), param_14,
          (BArray360.init_arr (W8.of_int 255)));
          result_5 <- aux_11;
          b_result_5 <- aux_12;
          trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
          trace_h__EXP___expmW <-
          (trace_h__EXP___expmW ++
          [(Assert, (BArray88.is_init b_result_5 0 88))]);
          r <- result_5;
          s <- (s + 1);
        }
        psel <- sel;
        ctx <- _ctx;
        param_15 <- r;
        param_16 <- psel;
        param_17 <- ctx;
        (aux_13, aux_14, tmp__trace) <@ h__EXP__fun_mulU (param_15,
        (BArray88.init_arr (W8.of_int 255)), param_16,
        (BArray88.init_arr (W8.of_int 255)), param_17,
        (BArray360.init_arr (W8.of_int 255)));
        result_6 <- aux_13;
        b_result_6 <- aux_14;
        trace_h__EXP___expmW <- (trace_h__EXP___expmW ++ tmp__trace);
        trace_h__EXP___expmW <-
        (trace_h__EXP___expmW ++
        [(Assert, (BArray88.is_init b_result_6 0 88))]);
        r <- result_6;
        k <- _k;
        k <- (k - (W64.of_int 1));
      }
      j <- _j;
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___expmW);
  }
  proc h__EXP___expmW_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                        b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
                        ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                              BArray88.t *
                                                              trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray104.t;
    var param_2:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var trace_h__EXP___expmW_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    trace_h__EXP___expmW_ <- [];
    trace_h__EXP___expmW_ <-
    (trace_h__EXP___expmW_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray104.is_init b_b 0 104)) /\
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
    (aux, aux_0, tmp__trace) <@ h__EXP___expmW (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray104.init_arr (W8.of_int 255)), param_2,
    (BArray360.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__EXP___expmW_ <- (trace_h__EXP___expmW_ ++ tmp__trace);
    trace_h__EXP___expmW_ <-
    (trace_h__EXP___expmW_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    r <- result;
    r <- r;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___expmW_);
  }
  proc h__EXP___expmWU_ (a:BArray88.t, b_a:BArray88.t, b:BArray104.t,
                         b_b:BArray104.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray88.t;
    var b_tmp:BArray88.t;
    var tmp:BArray88.t;
    var _tmp:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_1:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray104.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__EXP___expmWU_:trace;
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
    trace_h__EXP___expmWU_ <- [];
    trace_h__EXP___expmWU_ <-
    (trace_h__EXP___expmWU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP___expmWU_ <-
    (trace_h__EXP___expmWU_ ++ [(Assert, (BArray104.is_init b_b 0 104))]);
    trace_h__EXP___expmWU_ <-
    (trace_h__EXP___expmWU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__tmp <- (BArray88.init_arr (W8.of_int 0));
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ h__BN___mov_ (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__EXP___expmWU_ <- (trace_h__EXP___expmWU_ ++ tmp__trace);
    trace_h__EXP___expmWU_ <-
    (trace_h__EXP___expmWU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
    tmp <- result;
    param_1 <- a;
    param_2 <- tmp;
    param_3 <- b;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__EXP___expmW_ (param_1,
    (BArray88.init_arr (W8.of_int 255)), param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray104.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__EXP___expmWU_ <- (trace_h__EXP___expmWU_ ++ tmp__trace);
    trace_h__EXP___expmWU_ <-
    (trace_h__EXP___expmWU_ ++
    [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__EXP___expmWU_);
  }
  proc h__EXP___expm_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                       b_a:BArray88.t, b:BArray104.t, b_b:BArray104.t,
                       ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                             BArray88.t *
                                                             trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b_param:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray88.t;
    var param_1:BArray104.t;
    var param_2:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var b_param_0:BArray88.t;
    var param_3:BArray88.t;
    var param_4:BArray88.t;
    var param_5:BArray104.t;
    var param_6:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__EXP___expm_:trace;
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
    param_5 <- witness;
    param_6 <- witness;
    result <- witness;
    result_0 <- witness;
    trace_h__EXP___expm_ <- [];
    trace_h__EXP___expm_ <-
    (trace_h__EXP___expm_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray104.is_init b_b 0 104)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    if ((37 = 0)) {
      b_param <- b_r;
      param <- r;
      param_0 <- a;
      param_1 <- b;
      param_2 <- ctx;
      (aux_1, aux_2, tmp__trace) <@ h__EXP___expmML_ (param, b_param,
      param_0, (BArray88.init_arr (W8.of_int 255)), param_1,
      (BArray104.init_arr (W8.of_int 255)), param_2,
      (BArray360.init_arr (W8.of_int 255)));
      result <- aux_1;
      b_result <- aux_2;
      trace_h__EXP___expm_ <- (trace_h__EXP___expm_ ++ tmp__trace);
      trace_h__EXP___expm_ <-
      (trace_h__EXP___expm_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
      r <- result;
    } else {
      b_param_0 <- b_r;
      param_3 <- r;
      param_4 <- a;
      param_5 <- b;
      param_6 <- ctx;
      (aux, aux_0, tmp__trace) <@ h__EXP___expmW_ (param_3, b_param_0,
      param_4, (BArray88.init_arr (W8.of_int 255)), param_5,
      (BArray104.init_arr (W8.of_int 255)), param_6,
      (BArray360.init_arr (W8.of_int 255)));
      result_0 <- aux;
      b_result_0 <- aux_0;
      trace_h__EXP___expm_ <- (trace_h__EXP___expm_ ++ tmp__trace);
      trace_h__EXP___expm_ <-
      (trace_h__EXP___expm_ ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      r <- result_0;
    }
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__EXP___expm_);
  }
  proc h__EXP___expmU_ (a:BArray88.t, b_a:BArray88.t, b:BArray104.t,
                        b_b:BArray104.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray88.t;
    var aux_0:BArray88.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var param:BArray88.t;
    var param_0:BArray104.t;
    var param_1:BArray360.t;
    var result:BArray88.t;
    var b_result:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray104.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__EXP___expmU_:trace;
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
    trace_h__EXP___expmU_ <- [];
    trace_h__EXP___expmU_ <-
    (trace_h__EXP___expmU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__EXP___expmU_ <-
    (trace_h__EXP___expmU_ ++ [(Assert, (BArray104.is_init b_b 0 104))]);
    trace_h__EXP___expmU_ <-
    (trace_h__EXP___expmU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    if ((37 = 0)) {
      param <- a;
      param_0 <- b;
      param_1 <- ctx;
      (aux_1, aux_2, tmp__trace) <@ h__EXP___expmMLU_ (param,
      (BArray88.init_arr (W8.of_int 255)), param_0,
      (BArray104.init_arr (W8.of_int 255)), param_1,
      (BArray360.init_arr (W8.of_int 255)));
      result <- aux_1;
      b_result <- aux_2;
      trace_h__EXP___expmU_ <- (trace_h__EXP___expmU_ ++ tmp__trace);
      trace_h__EXP___expmU_ <-
      (trace_h__EXP___expmU_ ++ [(Assert, (BArray88.is_init b_result 0 88))]);
      a <- result;
    } else {
      param_2 <- a;
      param_3 <- b;
      param_4 <- ctx;
      (aux, aux_0, tmp__trace) <@ h__EXP___expmWU_ (param_2,
      (BArray88.init_arr (W8.of_int 255)), param_3,
      (BArray104.init_arr (W8.of_int 255)), param_4,
      (BArray360.init_arr (W8.of_int 255)));
      result_0 <- aux;
      b_result_0 <- aux_0;
      trace_h__EXP___expmU_ <- (trace_h__EXP___expmU_ ++ tmp__trace);
      trace_h__EXP___expmU_ <-
      (trace_h__EXP___expmU_ ++
      [(Assert, (BArray88.is_init b_result_0 0 88))]);
      a <- result_0;
    }
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__EXP___expmU_);
  }
}.

(* The post and trace are valid. *)

op uTIL____cf_mask_spec _cf =
   hoare [M.uTIL____cf_mask :
   ((_cf = cf) /\ true) ==> (true /\ (valid res.`2))].

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

op h__EXP__fun_mulU_spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP__fun_mulU :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP__fun_sqrU_spec _a _b_a _ctx _b_ctx =
   hoare [M.h__EXP__fun_sqrU :
   (((_b_ctx = b_ctx) /\ ((_ctx = ctx) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((BArray360.is_init _b_ctx 0 360) /\ (BArray88.is_init _b_a 0 88))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP___exp1mLR_first_noct_spec _r _b_r _x _b_x _w _ctx _b_ctx =
   hoare [M.h__EXP___exp1mLR_first_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_w = w) /\ ((_b_x = b_x) /\ ((_x = x) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray88.is_init _b_x 0 (8 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___exp1mLR_noct_spec _r _b_r _x _b_x _w _ctx _b_ctx =
   hoare [M.h__EXP___exp1mLR_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_w = w) /\ ((_b_x = b_x) /\ ((_x = x) /\ ((_b_r = b_r) /\ (_r = r))))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_x 0 88) /\ (BArray88.is_init _b_r 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP___expmLR_noct_spec _r _b_r _x _b_x _e _b_e _ctx _b_ctx =
   hoare [M.h__EXP___expmLR_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_e = b_e) /\
    ((_e = e) /\ ((_b_x = b_x) /\ ((_x = x) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_x 0 (8 * 11)) /\
    (BArray104.is_init _b_e 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmLR_noct__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmLR_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray104.is_init _b_b 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expm_noct_spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expm_noct :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray104.is_init _b_b 0 104) /\
   ((BArray88.is_init _b_a 0 88) /\ (BArray88.is_init _b_r 0 88))))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP___expm_noct__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expm_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray104.is_init _b_b 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmU_noct__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmU_noct_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray104.is_init _b_b 0 104) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP___expmML_spec _x0 _b_x0 _x1 _b_x1 _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmML :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_x1 = b_x1) /\ ((_x1 = x1) /\ ((_b_x0 = b_x0) /\ (_x0 = x0)))))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray104.is_init _b_b 0 104) /\
   ((BArray88.is_init _b_x1 0 88) /\ (BArray88.is_init _b_x0 0 88))))) ==>
   (((BArray88.is_init res.`4 0 88) /\ (BArray88.is_init res.`2 0 88)) /\
   (valid res.`5))].

op h__EXP___expmML__spec _x0 _b_x0 _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmML_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_x0 = b_x0) /\ (_x0 = x0)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray104.is_init _b_b 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmMLU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmMLU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray104.is_init _b_b 0 104) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP____tblsel_spec _r _b_r _tbl _b_tbl _idx =
   hoare [M.h__EXP____tblsel :
   (((_idx = idx) /\
    ((_b_tbl = b_tbl) /\ ((_tbl = tbl) /\ ((_b_r = b_r) /\ (_r = r))))) /\
   (BArray1408.is_init _b_tbl 0 (128 * 11))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmW_spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmW :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray104.is_init _b_b 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmW__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmW_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray104.is_init _b_b 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmWU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmWU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray104.is_init _b_b 0 104) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].

op h__EXP___expm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray104.is_init _b_b 0 (8 * 13))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__EXP___expmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__EXP___expmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray104.is_init _b_b 0 104) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].
