(* Spike: safety of fp_base's _mulm_, _mulmU_, a functor over the function
   parameters fun_muln, fun_red; abstracted by hand from the extraction at
   point A. Pre/post conditions are module-free ops (a spec op cannot mention
   the declared module of a section). *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array.

abstract theory FpBaseSafety.

op nlimbs : int.
axiom gt0_nlimbs : 0 < nlimbs.

clone import ByteArray as A with op size <= 8 * nlimbs.
clone import ByteArray as A2 with op size <= 16 * nlimbs.
clone import ByteArray as CTX with op size <= 8 * (4 * nlimbs + 1).

module type MParam = {
  proc fun_muln (r:A2.t, b_r:A2.t, a:A.t,
                        b_a:A.t, b:A.t, b_b:A.t) : 
  A2.t * A2.t * trace
  proc fun_red (r:A.t, b_r:A.t, a:A2.t,
                       b_a:A2.t, ctx:CTX.t, b_ctx:CTX.t) : 
  A.t * A.t * trace
}.

module M(P: MParam) = {
  var tmp__trace : trace
  proc _mulm_ (r:A.t, b_r:A.t, a:A.t,
                      b_a:A.t, b:A.t, b_b:A.t,
                      ctx:CTX.t, b_ctx:CTX.t) : A.t *
                                                            A.t *
                                                            trace = {
    var aux:A2.t;
    var aux_0:A2.t;
    var aux_1:A.t;
    var aux_2:A.t;
    var b__tmp:A2.t;
    var b__r:A.t;
    var _r:A.t;
    var _ctx:CTX.t;
    var b_tmp:A2.t;
    var tmp:A2.t;
    var _tmp:A2.t;
    var b_param:A2.t;
    var param:A2.t;
    var param_0:A.t;
    var param_1:A.t;
    var result:A2.t;
    var b_result:A2.t;
    var b_param_0:A.t;
    var param_2:A.t;
    var param_3:A2.t;
    var param_4:CTX.t;
    var result_0:A.t;
    var b_result_0:A.t;
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
     (((A.is_init b_a 0 (8 * nlimbs)) /\ (A.is_init b_b 0 (8 * nlimbs))) /\
     (CTX.is_init b_ctx 0 (8 * ((4 * nlimbs) + 1)))))]);
    b__tmp <- (A2.init_arr (W8.of_int 0));
    b__r <- b_r;
    _r <- r;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ P.fun_muln (param, b_param, param_0,
    (A.init_arr (W8.of_int 255)), param_1,
    (A.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (A2.is_init b_result 0 (16 * nlimbs)))]);
    tmp <- result;
    b_r <- b__r;
    r <- _r;
    ctx <- _ctx;
    b_param_0 <- b_r;
    param_2 <- r;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ P.fun_red (param_2, b_param_0,
    param_3, (A2.init_arr (W8.of_int 255)), param_4,
    (CTX.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulm_ <- (trace_h__FP___mulm_ ++ tmp__trace);
    trace_h__FP___mulm_ <-
    (trace_h__FP___mulm_ ++ [(Assert, (A.is_init b_result_0 0 (8 * nlimbs)))]);
    r <- result_0;
    b_r <- (A.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__FP___mulm_);
  }
  proc _mulmU_ (a:A.t, b_a:A.t, b:A.t,
                       b_b:A.t, ctx:CTX.t, b_ctx:CTX.t) : 
  A.t * A.t * trace = {
    var aux:A2.t;
    var aux_0:A2.t;
    var aux_1:A.t;
    var aux_2:A.t;
    var b__tmp:A2.t;
    var _a:A.t;
    var _ctx:CTX.t;
    var b_tmp:A2.t;
    var tmp:A2.t;
    var _tmp:A2.t;
    var b_param:A2.t;
    var param:A2.t;
    var param_0:A.t;
    var param_1:A.t;
    var result:A2.t;
    var b_result:A2.t;
    var param_2:A.t;
    var param_3:A2.t;
    var param_4:CTX.t;
    var result_0:A.t;
    var b_result_0:A.t;
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
    (trace_h__FP___mulmU_ ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (A.is_init b_b 0 (8 * nlimbs)))]);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (CTX.is_init b_ctx 0 (8 * ((4 * nlimbs) + 1))))]);
    b__tmp <- (A2.init_arr (W8.of_int 0));
    _a <- a;
    _ctx <- ctx;
    b_tmp <- b__tmp;
    tmp <- _tmp;
    b_param <- b_tmp;
    param <- tmp;
    param_0 <- a;
    param_1 <- b;
    (aux, aux_0, tmp__trace) <@ P.fun_muln (param, b_param, param_0,
    (A.init_arr (W8.of_int 255)), param_1,
    (A.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (A2.is_init b_result 0 (16 * nlimbs)))]);
    tmp <- result;
    a <- _a;
    ctx <- _ctx;
    param_2 <- a;
    param_3 <- tmp;
    param_4 <- ctx;
    (aux_1, aux_2, tmp__trace) <@ P.fun_red (param_2,
    (A.init_arr (W8.of_int 255)), param_3,
    (A2.init_arr (W8.of_int 255)), param_4,
    (CTX.init_arr (W8.of_int 255)));
    result_0 <- aux_1;
    b_result_0 <- aux_2;
    trace_h__FP___mulmU_ <- (trace_h__FP___mulmU_ ++ tmp__trace);
    trace_h__FP___mulmU_ <-
    (trace_h__FP___mulmU_ ++ [(Assert, (A.is_init b_result_0 0 (8 * nlimbs)))]);
    a <- result_0;
    b_a <- (A.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__FP___mulmU_);
  }
}.

op fun_muln_pre (_r : A2.t) (_b_r : A2.t) (_a : A.t) (_b_a : A.t) (_b : A.t) (_b_b : A.t) =
  ((A.is_init _b_a 0 (8 * nlimbs)) /\ (A.is_init _b_b 0 (8 * nlimbs))).
op fun_muln_post (_r : A2.t) (_b_r : A2.t) (_a : A.t) (_b_a : A.t) (_b : A.t) (_b_b : A.t) (_res : A2.t * A2.t * trace) =
  (A2.is_init _res.`2 0 (16 * nlimbs)).

op fun_red_pre (_r : A.t) (_b_r : A.t) (_a : A2.t) (_b_a : A2.t) (_ctx : CTX.t) (_b_ctx : CTX.t) =
  ((A2.is_init _b_a 0 (16 * nlimbs)) /\
   (CTX.is_init _b_ctx 0 (8 * ((4 * nlimbs) + 1)))).
op fun_red_post (_r : A.t) (_b_r : A.t) (_a : A2.t) (_b_a : A2.t) (_ctx : CTX.t) (_b_ctx : CTX.t) (_res : A.t * A.t * trace) =
  (A.is_init _res.`2 0 (8 * nlimbs)).

op _mulm__pre (_r : A.t) (_b_r : A.t) (_a : A.t) (_b_a : A.t) (_b : A.t) (_b_b : A.t) (_ctx : CTX.t) (_b_ctx : CTX.t) =
  (((A.is_init _b_a 0 (8 * nlimbs)) /\
    (A.is_init _b_b 0 (8 * nlimbs))) /\
   (CTX.is_init _b_ctx 0 (8 * ((4 * nlimbs) + 1)))).
op _mulm__post (_r : A.t) (_b_r : A.t) (_a : A.t) (_b_a : A.t) (_b : A.t) (_b_b : A.t) (_ctx : CTX.t) (_b_ctx : CTX.t) (_res : A.t * A.t * trace) =
  (A.is_init _res.`2 0 (8 * nlimbs)).

op _mulmU__pre (_a : A.t) (_b_a : A.t) (_b : A.t) (_b_b : A.t) (_ctx : CTX.t) (_b_ctx : CTX.t) =
  ((CTX.is_init _b_ctx 0 (8 * ((4 * nlimbs) + 1))) /\
   ((A.is_init _b_b 0 (8 * nlimbs)) /\ (A.is_init _b_a 0 (8 * nlimbs)))).
op _mulmU__post (_a : A.t) (_b_a : A.t) (_b : A.t) (_b_b : A.t) (_ctx : CTX.t) (_b_ctx : CTX.t) (_res : A.t * A.t * trace) =
  (A.is_init _res.`2 0 (8 * nlimbs)).

end FpBaseSafety.
