(* Conditional transfer of the functor spike to the extraction at point B. *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety.
require import BArray56 BArray112 BArray232 FP_spike.
require FpBaseSafetySpike.

clone FpBaseSafetySpike.FpBaseSafetyProofs as T
  with op nlimbs <- 7, theory A <- BArray56, theory A2 <- BArray112,
       theory CTX <- BArray232
  proof gt0_nlimbs by done.

module Stubs = {

  proc fun_muln = M.h__FP__fun_muln
  proc fun_red = M.h__FP__fun_red
}.

lemma stub_fun_muln :
  (forall _r _b_r _a _b_a _b _b_b, h__FP__fun_muln_spec _r _b_r _a _b_a _b _b_b) =>
  forall _r _b_r _a _b_a _b _b_b,
  hoare [Stubs.fun_muln : arg = (_r, _b_r, _a, _b_a, _b, _b_b) /\ T.fun_muln_pre _r _b_r _a _b_a _b _b_b
         ==> T.fun_muln_post _r _b_r _a _b_a _b _b_b res /\ valid res.`3].
proof. move=> h _r _b_r _a _b_a _b _b_b; have := h _r _b_r _a _b_a _b _b_b; rewrite /h__FP__fun_muln_spec => hh; by conseq hh => /> /#. qed.

lemma stub_fun_red :
  (forall _r _b_r _a _b_a _ctx _b_ctx, h__FP__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx) =>
  forall _r _b_r _a _b_a _ctx _b_ctx,
  hoare [Stubs.fun_red : arg = (_r, _b_r, _a, _b_a, _ctx, _b_ctx) /\ T.fun_red_pre _r _b_r _a _b_a _ctx _b_ctx
         ==> T.fun_red_post _r _b_r _a _b_a _ctx _b_ctx res /\ valid res.`3].
proof. move=> h _r _b_r _a _b_a _ctx _b_ctx; have := h _r _b_r _a _b_a _ctx _b_ctx; rewrite /h__FP__fun_red_spec => hh; by conseq hh => /> /#. qed.

equiv eq_mulm_: M.h__FP___mulm_ ~ T.M(Stubs)._mulm_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__FP___mulm__safety :
  (forall _r _b_r _a _b_a _b _b_b, h__FP__fun_muln_spec _r _b_r _a _b_a _b _b_b) => (forall _r _b_r _a _b_a _ctx _b_ctx, h__FP__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx) =>
  forall _r _b_r _a _b_a _b _b_b _ctx _b_ctx, h__FP___mulm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
proof.
move=> h_fun_muln h_fun_red _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
have h := T._mulm__proof Stubs (stub_fun_muln h_fun_muln) (stub_fun_red h_fun_red) _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__FP___mulm__spec.
by conseq eq_mulm_ h => /> /#.
qed.

equiv eq_mulmU_: M.h__FP___mulmU_ ~ T.M(Stubs)._mulmU_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__FP___mulmU__safety :
  (forall _r _b_r _a _b_a _b _b_b, h__FP__fun_muln_spec _r _b_r _a _b_a _b _b_b) => (forall _r _b_r _a _b_a _ctx _b_ctx, h__FP__fun_red_spec _r _b_r _a _b_a _ctx _b_ctx) =>
  forall _a _b_a _b _b_b _ctx _b_ctx, h__FP___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx.
proof.
move=> h_fun_muln h_fun_red _a _b_a _b _b_b _ctx _b_ctx.
have h := T._mulmU__proof Stubs (stub_fun_muln h_fun_muln) (stub_fun_red h_fun_red) _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__FP___mulmU__spec.
by conseq eq_mulmU_ h => /> /#.
qed.
