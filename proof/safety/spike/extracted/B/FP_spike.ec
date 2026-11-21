require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array7 Array14 Array29 Array56 Array112 Array232 BArray56 BArray112 BArray232.

module M = {
  var tmp__trace : trace
  proc h__FP__fun_muln (r:BArray112.t, b_r:BArray112.t, a:BArray56.t,
                        b_a:BArray56.t, b:BArray56.t, b_b:BArray56.t) : 
  BArray112.t * BArray112.t * trace = {
    var trace_h__FP__fun_muln:trace;
    trace_h__FP__fun_muln <- [];
    trace_h__FP__fun_muln <-
    (trace_h__FP__fun_muln ++
    [(Assert, ((BArray56.is_init b_a 0 56) /\ (BArray56.is_init b_b 0 56)))]);
    return (r, b_r, trace_h__FP__fun_muln);
  }
  proc h__FP__fun_red (r:BArray56.t, b_r:BArray56.t, a:BArray112.t,
                       b_a:BArray112.t, ctx:BArray232.t, b_ctx:BArray232.t) : 
  BArray56.t * BArray56.t * trace = {
    var trace_h__FP__fun_red:trace;
    trace_h__FP__fun_red <- [];
    trace_h__FP__fun_red <-
    (trace_h__FP__fun_red ++
    [(Assert,
     ((BArray112.is_init b_a 0 112) /\ (BArray232.is_init b_ctx 0 232)))]);
    return (r, b_r, trace_h__FP__fun_red);
  }
  proc h__FP___mulm_ (r:BArray56.t, b_r:BArray56.t, a:BArray56.t,
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
    (aux, aux_0, tmp__trace) <@ h__FP__fun_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_2 <- r;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_2, b_param_0,
    param_3, (BArray112.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    r <- result_0;
    b_r <- (BArray56.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___mulm_);
  }
  proc h__FP___mulmU_ (a:BArray56.t, b_a:BArray56.t, b:BArray56.t,
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
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray56.is_init b_a 0 56))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray56.is_init b_b 0 56))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray232.is_init b_ctx 0 232))]);
    b__tmp <- (BArray112.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ h__FP__fun_muln (param, b_param, param_0,
    (BArray56.init_arr (W8.of_int 255)), param_1,
    (BArray56.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray112.is_init b_result 0 112))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ h__FP__fun_red (param_2,
    (BArray56.init_arr (W8.of_int 255)), param_3,
    (BArray112.init_arr (W8.of_int 255)), param_4,
    (BArray232.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (BArray56.is_init b_result_0 0 56))]);
    a <- result_0;
    b_a <- (BArray56.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___mulmU_);
  }
}.

(* The post and trace are valid. *)

op h__FP__fun_muln_spec _r _b_r _a _b_a _b _b_b =
   hoare [M.h__FP__fun_muln :
   (((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7)))) ==>
   ((BArray112.is_init res.`2 0 (16 * 7)) /\ (valid res.`3))].

op h__FP__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx =
   hoare [M.h__FP__fun_red :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))) /\
   ((BArray112.is_init _b_a 0 (16 * 7)) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___mulm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___mulm_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\
    ((_b = b) /\ ((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))))))) /\
   (((BArray56.is_init _b_a 0 (8 * 7)) /\ (BArray56.is_init _b_b 0 (8 * 7))) /\
   (BArray232.is_init _b_ctx 0 (8 * 29)))) ==>
   ((BArray56.is_init res.`2 0 (8 * 7)) /\ (valid res.`3))].

op h__FP___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx =
   hoare [M.h__FP___mulmU_ :
   (((_b_ctx = b_ctx) /\
    ((_ctx = ctx) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
   ((BArray232.is_init _b_ctx 0 232) /\
   ((BArray56.is_init _b_b 0 56) /\ (BArray56.is_init _b_a 0 56)))) ==>
   ((BArray56.is_init res.`2 0 56) /\ (valid res.`3))].
