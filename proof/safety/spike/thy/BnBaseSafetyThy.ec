(* Spike: safety of bn_base's _load_, _mov_, _addU_, abstracted by hand from
   the safety extraction at the dummy point A (nlimbs = 11). *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array.

abstract theory BnBaseSafety.

op nlimbs : int.
axiom gt0_nlimbs : 0 < nlimbs.
axiom nlimbs_bnd : 8 * nlimbs < W64.modulus.

clone import ByteArray as A with op size <= 8 * nlimbs.

module M = {
  var tmp__trace : trace
  proc __load (a:A.t, b_a:A.t, ap:W64.t) : A.t *
                                                                A.t *
                                                                trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____load:trace;
    trace_h__BN____load <- [];
    trace_h__BN____load <-
    (trace_h__BN____load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * nlimbs)))]);
    i <- 0;
    while ((i < nlimbs)) {
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert,
       (is_valid ptr_modulus Glob.mem_v
       (W64.to_uint (ap + (W64.of_int (8 * i)))) 8))]);
      t <- (loadW64 Glob.mem (W64.to_uint (ap + (W64.of_int (8 * i)))));
      trace_h__BN____load <-
      (trace_h__BN____load ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= (8 * nlimbs))))]);
      b_a <- (A.set64d b_a (i * 8) (W64.of_int 18446744073709551615));
      a <- (A.set64 a i t);
      i <- (i + 1);
    }
    return (a, b_a, trace_h__BN____load);
  }
  proc _load (a:A.t, b_a:A.t, ap:W64.t) : A.t *
                                                               A.t *
                                                               trace = {
    var aux:A.t;
    var aux_0:A.t;
    var b_param:A.t;
    var param:A.t;
    var param_0:W64.t;
    var result:A.t;
    var b_result:A.t;
    var trace_h__BN___load:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load <- [];
    trace_h__BN___load <-
    (trace_h__BN___load ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * nlimbs)))]);
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ __load (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___load <- (trace_h__BN___load ++ tmp__trace);
    trace_h__BN___load <-
    (trace_h__BN___load ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    a <- result;
    b_a <- (A.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load);
  }
  proc _load_ (a:A.t, b_a:A.t, ap:W64.t) : A.t *
                                                                A.t *
                                                                trace = {
    var aux:A.t;
    var aux_0:A.t;
    var b_param:A.t;
    var param:A.t;
    var param_0:W64.t;
    var result:A.t;
    var b_result:A.t;
    var trace_h__BN___load_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace_h__BN___load_ <- [];
    trace_h__BN___load_ <-
    (trace_h__BN___load_ ++
    [(Assert, (is_valid ptr_modulus Glob.mem_v (W64.to_uint ap) (8 * nlimbs)))]);
    b_a <- b_a;
    a <- a;
    ap <- ap;
    b_param <- b_a;
    param <- a;
    param_0 <- ap;
    (aux, aux_0, tmp__trace) <@ _load (param, b_param, param_0);
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___load_ <- (trace_h__BN___load_ ++ tmp__trace);
    trace_h__BN___load_ <-
    (trace_h__BN___load_ ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    a <- result;
    a <- a;
    b_a <- (A.init_arr (W8.of_int 255));
    return (a, b_a, trace_h__BN___load_);
  }
  proc __mov (r:A.t, b_r:A.t, a:A.t,
                     b_a:A.t) : A.t * A.t * trace = {
    var i:int;
    var t:W64.t;
    var trace_h__BN____mov:trace;
    trace_h__BN____mov <- [];
    trace_h__BN____mov <-
    (trace_h__BN____mov ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    i <- 0;
    while ((i < nlimbs)) {
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= (8 * nlimbs))))]);
      t <- (A.get64 a i);
      trace_h__BN____mov <-
      (trace_h__BN____mov ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= (8 * nlimbs))))]);
      b_r <- (A.set64d b_r (i * 8) (W64.of_int 18446744073709551615));
      r <- (A.set64 r i t);
      i <- (i + 1);
    }
    return (r, b_r, trace_h__BN____mov);
  }
  proc _mov (r:A.t, b_r:A.t, a:A.t,
                    b_a:A.t) : A.t * A.t * trace = {
    var aux:A.t;
    var aux_0:A.t;
    var b_param:A.t;
    var param:A.t;
    var param_0:A.t;
    var result:A.t;
    var b_result:A.t;
    var trace_h__BN___mov:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov <- [];
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ __mov (param, b_param, param_0,
    (A.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov <- (trace_h__BN___mov ++ tmp__trace);
    trace_h__BN___mov <-
    (trace_h__BN___mov ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    r <- result;
    b_r <- (A.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov);
  }
  proc _mov_ (r:A.t, b_r:A.t, a:A.t,
                     b_a:A.t) : A.t * A.t * trace = {
    var aux:A.t;
    var aux_0:A.t;
    var b_param:A.t;
    var param:A.t;
    var param_0:A.t;
    var result:A.t;
    var b_result:A.t;
    var trace_h__BN___mov_:trace;
    b_param <- witness;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result <- witness;
    trace_h__BN___mov_ <- [];
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    b_r <- b_r;
    r <- r;
    a <- a;
    b_param <- b_r;
    param <- r;
    param_0 <- a;
    (aux, aux_0, tmp__trace) <@ _mov (param, b_param, param_0,
    (A.init_arr (W8.of_int 255)));
    result <- aux;
    b_result <- aux_0;
    trace_h__BN___mov_ <- (trace_h__BN___mov_ ++ tmp__trace);
    trace_h__BN___mov_ <-
    (trace_h__BN___mov_ ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    r <- result;
    r <- r;
    b_r <- (A.init_arr (W8.of_int 255));
    return (r, b_r, trace_h__BN___mov_);
  }
  proc __addc1U (a:A.t, b_a:A.t, b:A.t,
                        b_b:A.t, cf:bool) : bool * A.t *
                                                   A.t * trace = {
    var aux_0:W64.t;
    var aux:bool;
    var i:int;
    var t:W64.t;
    var trace_h__BN____addc1U:trace;
    trace_h__BN____addc1U <- [];
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    trace_h__BN____addc1U <-
    (trace_h__BN____addc1U ++ [(Assert, (A.is_init b_b 0 (8 * nlimbs)))]);
    i <- 1;
    while ((i < nlimbs)) {
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= (8 * nlimbs))))]);
      t <- (A.get64 b i);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= (8 * nlimbs))))]);
      trace_h__BN____addc1U <-
      (trace_h__BN____addc1U ++
      [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= (8 * nlimbs))))]);
      (aux, aux_0) <- (adc_64 (A.get64 a i) t cf);
      cf <- aux;
      a <- (A.set64 a i aux_0);
      i <- (i + 1);
    }
    b_a <- (A.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN____addc1U);
  }
  proc _addc1U (a:A.t, b_a:A.t, b:A.t,
                       b_b:A.t, cf:bool) : bool * A.t *
                                                  A.t * trace = {
    var aux_0:A.t;
    var aux_1:A.t;
    var aux:bool;
    var param:A.t;
    var param_0:A.t;
    var param_1:bool;
    var result:bool;
    var result_0:A.t;
    var b_result:A.t;
    var trace_h__BN___addc1U:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U <- [];
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (A.is_init b_b 0 (8 * nlimbs)))]);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ __addc1U (param,
    (A.init_arr (W8.of_int 255)), param_0,
    (A.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U <- (trace_h__BN___addc1U ++ tmp__trace);
    trace_h__BN___addc1U <-
    (trace_h__BN___addc1U ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    cf <- result;
    a <- result_0;
    b_a <- (A.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U);
  }
  proc _addc1U_ (a:A.t, b_a:A.t, b:A.t,
                        b_b:A.t, cf:bool) : bool * A.t *
                                                   A.t * trace = {
    var aux_0:A.t;
    var aux_1:A.t;
    var aux:bool;
    var param:A.t;
    var param_0:A.t;
    var param_1:bool;
    var result:bool;
    var result_0:A.t;
    var b_result:A.t;
    var trace_h__BN___addc1U_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addc1U_ <- [];
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (A.is_init b_b 0 (8 * nlimbs)))]);
    a <- a;
    b <- b;
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux, aux_0, aux_1, tmp__trace) <@ _addc1U (param,
    (A.init_arr (W8.of_int 255)), param_0,
    (A.init_arr (W8.of_int 255)), param_1);
    result <- aux;
    result_0 <- aux_0;
    b_result <- aux_1;
    trace_h__BN___addc1U_ <- (trace_h__BN___addc1U_ ++ tmp__trace);
    trace_h__BN___addc1U_ <-
    (trace_h__BN___addc1U_ ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    cf <- result;
    a <- result_0;
    a <- a;
    b_a <- (A.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addc1U_);
  }
  proc _addU_ (a:A.t, b_a:A.t, b:A.t,
                      b_b:A.t) : bool * A.t * A.t *
                                        trace = {
    var aux_2:A.t;
    var aux_3:A.t;
    var aux_0:W64.t;
    var aux:bool;
    var aux_1:bool;
    var t:W64.t;
    var cf:bool;
    var param:A.t;
    var param_0:A.t;
    var param_1:bool;
    var result:bool;
    var result_0:A.t;
    var b_result:A.t;
    var trace_h__BN___addU_:trace;
    b_result <- witness;
    param <- witness;
    param_0 <- witness;
    result_0 <- witness;
    trace_h__BN___addU_ <- [];
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (A.is_init b_a 0 (8 * nlimbs)))]);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (A.is_init b_b 0 (8 * nlimbs)))]);
    t <- (A.get64 b 0);
    (aux, aux_0) <- (adc_64 (A.get64 a 0) t false);
    cf <- aux;
    a <- (A.set64 a 0 aux_0);
    param <- a;
    param_0 <- b;
    param_1 <- cf;
    (aux_1, aux_2, aux_3, tmp__trace) <@ _addc1U_ (param,
    (A.init_arr (W8.of_int 255)), param_0,
    (A.init_arr (W8.of_int 255)), param_1);
    result <- aux_1;
    result_0 <- aux_2;
    b_result <- aux_3;
    trace_h__BN___addU_ <- (trace_h__BN___addU_ ++ tmp__trace);
    trace_h__BN___addU_ <-
    (trace_h__BN___addU_ ++ [(Assert, (A.is_init b_result 0 (8 * nlimbs)))]);
    cf <- result;
    a <- result_0;
    b_a <- (A.init_arr (W8.of_int 255));
    return (cf, a, b_a, trace_h__BN___addU_);
  }
}.


(* The post and trace are valid. *)

op __load_spec _a _b_a _ap =
   hoare [M.__load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * nlimbs)))) ==>
   ((A.is_init res.`2 0 (8 * nlimbs)) /\ (valid res.`3))].

op _load_spec _a _b_a _ap =
   hoare [M._load :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * nlimbs)))) ==>
   ((A.is_init res.`2 0 (8 * nlimbs)) /\ (valid res.`3))].

op _load__spec _a _b_a _ap =
   hoare [M._load_ :
   (((_ap = ap) /\ ((_b_a = b_a) /\ (_a = a))) /\
   (true /\ (is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * nlimbs)))) ==>
   ((A.is_init res.`2 0 (8 * nlimbs)) /\ (valid res.`3))].

op __mov_spec _r _b_r _a _b_a =
   hoare [M.__mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (A.is_init _b_a 0 (8 * nlimbs))) ==>
   ((A.is_init res.`2 0 (8 * nlimbs)) /\ (valid res.`3))].

op _mov_spec _r _b_r _a _b_a =
   hoare [M._mov :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (A.is_init _b_a 0 (8 * nlimbs))) ==>
   ((A.is_init res.`2 0 (8 * nlimbs)) /\ (valid res.`3))].

op _mov__spec _r _b_r _a _b_a =
   hoare [M._mov_ :
   (((_b_a = b_a) /\ ((_a = a) /\ ((_b_r = b_r) /\ (_r = r)))) /\
   (A.is_init _b_a 0 (8 * nlimbs))) ==>
   ((A.is_init res.`2 0 (8 * nlimbs)) /\ (valid res.`3))].

op __addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M.__addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((A.is_init _b_b 0 (8 * nlimbs)) /\ (A.is_init _b_a 0 (8 * nlimbs)))) ==>
   ((A.is_init res.`3 0 (8 * nlimbs)) /\ (valid res.`4))].

op _addc1U_spec _a _b_a _b _b_b _cf =
   hoare [M._addc1U :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((A.is_init _b_b 0 (8 * nlimbs)) /\ (A.is_init _b_a 0 (8 * nlimbs)))) ==>
   ((A.is_init res.`3 0 (8 * nlimbs)) /\ (valid res.`4))].

op _addc1U__spec _a _b_a _b _b_b _cf =
   hoare [M._addc1U_ :
   (((_cf = cf) /\
    ((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a))))) /\
   ((A.is_init _b_b 0 (8 * nlimbs)) /\ (A.is_init _b_a 0 (8 * nlimbs)))) ==>
   ((A.is_init res.`3 0 (8 * nlimbs)) /\ (valid res.`4))].

op _addU__spec _a _b_a _b _b_b =
   hoare [M._addU_ :
   (((_b_b = b_b) /\ ((_b = b) /\ ((_b_a = b_a) /\ (_a = a)))) /\
   ((A.is_init _b_b 0 (8 * nlimbs)) /\ (A.is_init _b_a 0 (8 * nlimbs)))) ==>
   ((A.is_init res.`3 0 (8 * nlimbs)) /\ (valid res.`4))].

end BnBaseSafety.
