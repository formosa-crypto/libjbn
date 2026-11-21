require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array11 Array22 Array45 Array88 Array176 Array360 BArray88 BArray176
BArray360.

module M = {
  var tmp__trace : trace
  proc h__FP__fun_muln (r:BArray176.t, b_r:BArray176.t, a:BArray88.t,
                        b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t) : 
  BArray176.t * BArray176.t * trace = {
    var trace_h__FP__fun_muln:trace;
    trace_h__FP__fun_muln <- [];
    trace_h__FP__fun_muln <-
    (trace_h__FP__fun_muln ++
    [(Assert, ((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)))]);
    return (r, b_r, trace_h__FP__fun_muln);
  }
  proc h__FP__fun_red (r:BArray88.t, b_r:BArray88.t, a:BArray176.t,
                       b_a:BArray176.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var trace_h__FP__fun_red:trace;
    trace_h__FP__fun_red <- [];
    trace_h__FP__fun_red <-
    (trace_h__FP__fun_red ++
    [(Assert,
     ((BArray176.is_init b_a 0 176) /\ (BArray360.is_init b_ctx 0 360)))]);
    return (r, b_r, trace_h__FP__fun_red);
  }
  proc h__FP___mulm_ (r:BArray88.t, b_r:BArray88.t, a:BArray88.t,
                      b_a:BArray88.t, b:BArray88.t, b_b:BArray88.t,
                      ctx:BArray360.t, b_ctx:BArray360.t) : BArray88.t *
                                                            BArray88.t *
                                                            trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray176.t;
    var b__r:BArray88.t;
    var _r:BArray88.t;
    var _ctx:BArray360.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var b_param_0:BArray88.t;
    var param_2:BArray88.t;
    var param_3:BArray176.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FP___mulm_:trace;
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
    trace_h__FP___mulm_ <- [];
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++
    [(Assert,
     (((BArray88.is_init b_a 0 88) /\ (BArray88.is_init b_b 0 88)) /\
     (BArray360.is_init b_ctx 0 360)))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_muln (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_2 <- r;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_2, b_param_0,
    param_3, (BArray176.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    r <- result_0;
    b_r <- (BArray88.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___mulm_);
  }
  proc h__FP___mulmU_ (a:BArray88.t, b_a:BArray88.t, b:BArray88.t,
                       b_b:BArray88.t, ctx:BArray360.t, b_ctx:BArray360.t) : 
  BArray88.t * BArray88.t * trace = {
    var aux:BArray176.t;
    var aux_0:BArray176.t;
    var aux_1:BArray88.t;
    var aux_2:BArray88.t;
    var b__tmp:BArray176.t;
    var _a:BArray88.t;
    var _ctx:BArray360.t;
    var b_tmp:BArray176.t;
    var tmp:BArray176.t;
    var _tmp:BArray176.t;
    var b_param:BArray176.t;
    var param:BArray176.t;
    var param_0:BArray88.t;
    var param_1:BArray88.t;
    var result:BArray176.t;
    var b_result:BArray176.t;
    var param_2:BArray88.t;
    var param_3:BArray176.t;
    var param_4:BArray360.t;
    var result_0:BArray88.t;
    var b_result_0:BArray88.t;
    var trace_h__FP___mulmU_:trace;
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
    trace_h__FP___mulmU_ <- [];
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray88.is_init b_a 0 88))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray88.is_init b_b 0 88))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray360.is_init b_ctx 0 360))]);
    b__tmp <- (BArray176.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_muln (param, b_param, param_0,
    (BArray88.init_arr (W8.of_int 255)), param_1,
    (BArray88.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray176.is_init b_result 0 176))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_2,
    (BArray88.init_arr (W8.of_int 255)), param_3,
    (BArray176.init_arr (W8.of_int 255)), param_4,
    (BArray360.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray88.is_init b_result_0 0 88))]);
    a <- result_0;
    b_a <- (BArray88.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___mulmU_);
  }
}.

(* The post and trace are valid. *)

op h__FP__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FP__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray88.is_init _b_a 0 (8 * 11)) /\ (BArray88.is_init _b_b 0 (8 * 11)))) ==>
   ((BArray176.is_init res.`2 0 (16 * 11)) /\ (valid res.`3))].

op h__FP__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FP__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray176.is_init _b_a 0 (16 * 11)) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FP___mulm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___mulm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray88.is_init _b_a 0 (8 * 11)) /\
    (BArray88.is_init _b_b 0 (8 * 11))) /\
   (BArray360.is_init _b_ctx 0 (8 * 45)))) ==>
   ((BArray88.is_init res.`2 0 (8 * 11)) /\ (valid res.`3))].

op h__FP___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray360.is_init _b_ctx 0 360) /\
   ((BArray88.is_init _b_b 0 88) /\ (BArray88.is_init _b_a 0 88)))) ==>
   ((BArray88.is_init res.`2 0 88) /\ (valid res.`3))].
