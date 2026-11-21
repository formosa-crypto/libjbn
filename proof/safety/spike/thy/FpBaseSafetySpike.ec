(* Spike: the safety lemmas of fp_base's _mulm_, _mulmU_ over the functor
   theory FpBaseSafety (FpBaseSafetyThy.ec), for any function parameters
   meeting their contracts. *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array.
require import ByteArrayInit FpBaseSafetyThy.

abstract theory FpBaseSafetyProofs.

clone include FpBaseSafety.
clone ByteArrayInit as BI with theory A <- A.
clone ByteArrayInit as BI2 with theory A <- A2.
clone ByteArrayInit as BIC with theory A <- CTX.

section.

declare module P <: MParam.

declare axiom fun_muln_h _r _b_r _a _b_a _b _b_b :
  hoare [P.fun_muln :
    arg = (_r, _b_r, _a, _b_a, _b, _b_b) /\ fun_muln_pre _r _b_r _a _b_a _b _b_b
    ==> fun_muln_post _r _b_r _a _b_a _b _b_b res /\ valid res.`3].

declare axiom fun_red_h _r _b_r _a _b_a _ctx _b_ctx :
  hoare [P.fun_red :
    arg = (_r, _b_r, _a, _b_a, _ctx, _b_ctx) /\ fun_red_pre _r _b_r _a _b_a _ctx _b_ctx
    ==> fun_red_post _r _b_r _a _b_a _ctx _b_ctx res /\ valid res.`3].

lemma _mulm__proof _r _b_r _a _b_a _b _b_b _ctx _b_ctx :
  hoare [M(P)._mulm_ :
    arg = (_r, _b_r, _a, _b_a, _b, _b_b, _ctx, _b_ctx)
    /\ _mulm__pre _r _b_r _a _b_a _b _b_b _ctx _b_ctx
    ==> _mulm__post _r _b_r _a _b_a _b _b_b _ctx _b_ctx res /\ valid res.`3].
proof.
hint +safety.
proc.
wp; ecall (fun_red_h param_2 b_param_0 param_3 (A2.init_arr (W8.of_int 255))
             param_4 (CTX.init_arr (W8.of_int 255))).
wp; ecall (fun_muln_h param b_param param_0 (A.init_arr (W8.of_int 255))
             param_1 (A.init_arr (W8.of_int 255))).
by auto => />.
qed.

lemma _mulmU__proof _a _b_a _b _b_b _ctx _b_ctx :
  hoare [M(P)._mulmU_ :
    arg = (_a, _b_a, _b, _b_b, _ctx, _b_ctx) /\ _mulmU__pre _a _b_a _b _b_b _ctx _b_ctx
    ==> _mulmU__post _a _b_a _b _b_b _ctx _b_ctx res /\ valid res.`3].
proof.
hint +safety.
proc.
wp; ecall (fun_red_h param_2 (A.init_arr (W8.of_int 255)) param_3
             (A2.init_arr (W8.of_int 255)) param_4 (CTX.init_arr (W8.of_int 255))).
wp; ecall (fun_muln_h param b_param param_0 (A.init_arr (W8.of_int 255))
             param_1 (A.init_arr (W8.of_int 255))).
by auto => />.
qed.

end section.

end FpBaseSafetyProofs.
