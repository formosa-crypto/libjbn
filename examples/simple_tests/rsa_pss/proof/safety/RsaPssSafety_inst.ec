(* Safety of the RSA example (../../rsa2048.jazz), the library part: the
   specifications of the library procedures of the extraction
   (extracted/RsaPssXtr_safety.ec, the safety model) established from the
   library's safety theories (proof/safety): clones at the example's sizes,
   binding modules for the function parameters, one equivalence by sim per
   procedure, and the transfer of each lemma by conseq. The multiplication
   selector comes from its theory, cloned at the example's profile (x86_64:
   no MULX/ADX, product scanning up to 64 limbs). *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array JMemory.
require import RsaPssXtr_safety.
require import ByteArrayInit JbnSafetyLib.
require Bn_mulsel_safety Fp_mont_safety Bn_exp_safety.
require import BArray32 BArray128 BArray136 BArray256 SBArray256_128 BArray264 BArray512 SBArray512_256 BArray520 SBArray520_128 SBArray520_256 BArray1032 SBArray1032_256 SBArray1032_512 BArray2048 SBArray2048_128.

clone Fp_mont_safety as F32 with
  op nlimbs <- 32,
  theory BA_8n <- BArray256,
  theory BA_16n <- BArray512,
  theory BA_32n_8 <- BArray1032,
  theory SB_16n__8n <- SBArray512_256,
  theory SB_32n_8__16n <- SBArray1032_512,
  theory SB_32n_8__8n <- SBArray1032_256
  proof gt0_nlimbs by done, nlimbs_bnd by done.

clone Fp_mont_safety as F16 with
  op nlimbs <- 16,
  theory BA_8n <- BArray128,
  theory BA_16n <- BArray256,
  theory BA_32n_8 <- BArray520,
  theory SB_16n__8n <- SBArray256_128,
  theory SB_32n_8__16n <- SBArray520_256,
  theory SB_32n_8__8n <- SBArray520_128,
  theory BA_128n <- BArray2048,
  theory SB_128n__8n <- SBArray2048_128,
  op jbn_exp_window <- 4
  proof gt0_nlimbs by done, nlimbs_bnd by done.

clone Bn_mulsel_safety as S32 with
  op nlimbs <- 32,
  op jbn_features <- 0,
  op jbn_reg_max <- 0,
  op jbn_unroll_max <- 64,
  theory BA_8n <- BArray256,
  theory BA_8n_8 <- BArray264,
  theory BA_16n <- BArray512,
  theory SB_16n__8n <- SBArray512_256
  proof gt0_nlimbs by done, nlimbs_bnd by done.

clone Bn_mulsel_safety as S16 with
  op nlimbs <- 16,
  op jbn_features <- 0,
  op jbn_reg_max <- 0,
  op jbn_unroll_max <- 64,
  theory BA_8n <- BArray128,
  theory BA_8n_8 <- BArray136,
  theory BA_16n <- BArray256,
  theory SB_16n__8n <- SBArray256_128
  proof gt0_nlimbs by done, nlimbs_bnd by done.

clone Bn_exp_safety as E32 with
  op nlimbs <- 32,
  op nlimbsexp <- 4,
  theory BA_8n <- BArray256,
  theory BA_16n <- BArray512,
  theory BA_32n_8 <- BArray1032,
  theory BA_8e <- BArray32,
  theory SB_32n_8__8n <- SBArray1032_256
  proof gt0_nlimbs by done, nlimbs_bnd by done, gt0_nlimbsexp by done, nlimbsexp_bnd by done.

(* the hints of the safety database at the concrete sizes *)
clone ByteArrayLib as BL24 with theory A <- BArray24.
clone ByteArrayLib as BL32 with theory A <- BArray32.
clone ByteArrayLib as BL128 with theory A <- BArray128.
clone ByteArrayLib as BL256 with theory A <- BArray256.
clone ByteArrayLib as BL288 with theory A <- BArray288.
clone ByteArrayLib as BL512 with theory A <- BArray512.
clone ByteArrayLib as BL520 with theory A <- BArray520.
clone ByteArrayLib as BL640 with theory A <- BArray640.
clone ByteArrayLib as BL1032 with theory A <- BArray1032.
clone ByteArrayLib as BL1064 with theory A <- BArray1064.
clone ByteArrayLib as BL1424 with theory A <- BArray1424.

equiv eq_h__BN___mov_: M.h__BN___mov_ ~ F32.BNB.M._mov_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__BN___mov__safety _r _b_r _a _b_a : h__BN___mov__spec _r _b_r _a _b_a.
proof.
have h := F32.BNB._mov__proof _r _b_r _a _b_a.
rewrite /h__BN___mov__spec; rewrite /F32.BNB._mov__spec in h.
by conseq eq_h__BN___mov_ h => /> /#.
qed.

equiv eq_h__BN___addU_: M.h__BN___addU_ ~ F32.BNB.M._addU_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__BN___addU__safety _a _b_a _b _b_b : h__BN___addU__spec _a _b_a _b _b_b.
proof.
have h := F32.BNB._addU__proof _a _b_a _b _b_b.
rewrite /h__BN___addU__spec; rewrite /F32.BNB._addU__spec in h.
by conseq eq_h__BN___addU_ h => /> /#.
qed.

equiv eq_h__H__BN___mov_: M.h__H__BN___mov_ ~ F16.BNB.M._mov_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__BN___mov__safety _r _b_r _a _b_a : h__H__BN___mov__spec _r _b_r _a _b_a.
proof.
have h := F16.BNB._mov__proof _r _b_r _a _b_a.
rewrite /h__H__BN___mov__spec; rewrite /F16.BNB._mov__spec in h.
by conseq eq_h__H__BN___mov_ h => /> /#.
qed.

equiv eq_h__H__BN___set0_: M.h__H__BN___set0_ ~ F16.BNB.M._set0_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__BN___set0__safety _a _b_a : h__H__BN___set0__spec _a _b_a.
proof.
have h := F16.BNB._set0__proof _a _b_a.
rewrite /h__H__BN___set0__spec; rewrite /F16.BNB._set0__spec in h.
by conseq eq_h__H__BN___set0_ h => /> /#.
qed.

equiv eq_h__MUL___muln_: M.h__MUL___muln_ ~ S32.M._muln_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__MUL___muln__safety _r _b_r _a _b_a _b _b_b : h__MUL___muln__spec _r _b_r _a _b_a _b _b_b.
proof.
have h := S32._muln__proof _r _b_r _a _b_a _b _b_b.
rewrite /h__MUL___muln__spec; rewrite /S32._muln__spec in h.
by conseq eq_h__MUL___muln_ h => /> /#.
qed.

equiv eq_h__MUL___sqrn_: M.h__MUL___sqrn_ ~ S32.M._sqrn_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__MUL___sqrn__safety _r _b_r _a _b_a : h__MUL___sqrn__spec _r _b_r _a _b_a.
proof.
have h := S32._sqrn__proof _r _b_r _a _b_a.
rewrite /h__MUL___sqrn__spec; rewrite /S32._sqrn__spec in h.
by conseq eq_h__MUL___sqrn_ h => /> /#.
qed.

equiv eq_h__MUL____mont_redM: M.h__MUL____mont_redM ~ S32.M.__mont_redM : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__MUL____mont_redM_safety _r _b_r _a _b_a __P_mP _b__P_mP __U0 : h__MUL____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0.
proof.
have h := S32.__mont_redM_proof _r _b_r _a _b_a __P_mP _b__P_mP __U0.
rewrite /h__MUL____mont_redM_spec; rewrite /S32.__mont_redM_spec in h.
by conseq eq_h__MUL____mont_redM h => /> /#.
qed.

equiv eq_h__H__MUL___muln_: M.h__H__MUL___muln_ ~ S16.M._muln_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__MUL___muln__safety _r _b_r _a _b_a _b _b_b : h__H__MUL___muln__spec _r _b_r _a _b_a _b _b_b.
proof.
have h := S16._muln__proof _r _b_r _a _b_a _b _b_b.
rewrite /h__H__MUL___muln__spec; rewrite /S16._muln__spec in h.
by conseq eq_h__H__MUL___muln_ h => /> /#.
qed.

equiv eq_h__H__MUL___sqrn_: M.h__H__MUL___sqrn_ ~ S16.M._sqrn_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__MUL___sqrn__safety _r _b_r _a _b_a : h__H__MUL___sqrn__spec _r _b_r _a _b_a.
proof.
have h := S16._sqrn__proof _r _b_r _a _b_a.
rewrite /h__H__MUL___sqrn__spec; rewrite /S16._sqrn__spec in h.
by conseq eq_h__H__MUL___sqrn_ h => /> /#.
qed.

equiv eq_h__H__MUL____mont_redM: M.h__H__MUL____mont_redM ~ S16.M.__mont_redM : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__MUL____mont_redM_safety _r _b_r _a _b_a __P_mP _b__P_mP __U0 : h__H__MUL____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0.
proof.
have h := S16.__mont_redM_proof _r _b_r _a _b_a __P_mP _b__P_mP __U0.
rewrite /h__H__MUL____mont_redM_spec; rewrite /S16.__mont_redM_spec in h.
by conseq eq_h__H__MUL____mont_redM h => /> /#.
qed.

lemma h__FPM__fun_muln_safety _r _b_r _a _b_a _b _b_b : h__FPM__fun_muln_spec _r _b_r _a _b_a _b _b_b.
proof.
hint +safety.
rewrite /h__FPM__fun_muln_spec; proc.
wp; ecall (h__MUL___muln__safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255))) param_1 ((BArray256.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma h__FPM__fun_sqrn_safety _r _b_r _a _b_a : h__FPM__fun_sqrn_spec _r _b_r _a _b_a.
proof.
hint +safety.
rewrite /h__FPM__fun_sqrn_spec; proc.
wp; ecall (h__MUL___sqrn__safety param b_param param_0 ((BArray256.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma h__H__FPM__fun_muln_safety _r _b_r _a _b_a _b _b_b : h__H__FPM__fun_muln_spec _r _b_r _a _b_a _b _b_b.
proof.
hint +safety.
rewrite /h__H__FPM__fun_muln_spec; proc.
wp; ecall (h__H__MUL___muln__safety param b_param param_0 ((BArray128.init_arr (W8.of_int 255))) param_1 ((BArray128.init_arr (W8.of_int 255)))).
by auto => />.
qed.

lemma h__H__FPM__fun_sqrn_safety _r _b_r _a _b_a : h__H__FPM__fun_sqrn_spec _r _b_r _a _b_a.
proof.
hint +safety.
rewrite /h__H__FPM__fun_sqrn_spec; proc.
wp; ecall (h__H__MUL___sqrn__safety param b_param param_0 ((BArray128.init_arr (W8.of_int 255)))).
by auto => />.
qed.

module B32 = {
  proc __mont_redM = M.h__MUL____mont_redM
  proc fun_muln = M.h__FPM__fun_muln
  proc fun_sqrn = M.h__FPM__fun_sqrn
}.

lemma B32___mont_redM_h _r _b_r _a _b_a __P_mP _b__P_mP __U0 :
  hoare [B32.__mont_redM :
    arg = (_r, _b_r, _a, _b_a, __P_mP, _b__P_mP, __U0) /\ F32.__mont_redM_pre _r _b_r _a _b_a __P_mP _b__P_mP __U0
    ==> F32.__mont_redM_post _r _b_r _a _b_a __P_mP _b__P_mP __U0 res /\ valid res.`3].
proof.
have := h__MUL____mont_redM_safety _r _b_r _a _b_a __P_mP _b__P_mP __U0; rewrite /h__MUL____mont_redM_spec => hh.
by conseq hh => /> /#.
qed.

lemma B32_fun_muln_h _r _b_r _a _b_a _b _b_b :
  hoare [B32.fun_muln :
    arg = (_r, _b_r, _a, _b_a, _b, _b_b) /\ F32.fun_muln_pre _r _b_r _a _b_a _b _b_b
    ==> F32.fun_muln_post _r _b_r _a _b_a _b _b_b res /\ valid res.`3].
proof.
have := h__FPM__fun_muln_safety _r _b_r _a _b_a _b _b_b; rewrite /h__FPM__fun_muln_spec => hh.
by conseq hh => /> /#.
qed.

lemma B32_fun_sqrn_h _r _b_r _a _b_a :
  hoare [B32.fun_sqrn :
    arg = (_r, _b_r, _a, _b_a) /\ F32.fun_sqrn_pre _r _b_r _a _b_a
    ==> F32.fun_sqrn_post _r _b_r _a _b_a res /\ valid res.`3].
proof.
have := h__FPM__fun_sqrn_safety _r _b_r _a _b_a; rewrite /h__FPM__fun_sqrn_spec => hh.
by conseq hh => /> /#.
qed.

module B16 = {
  proc __mont_redM = M.h__H__MUL____mont_redM
  proc fun_muln = M.h__H__FPM__fun_muln
  proc fun_sqrn = M.h__H__FPM__fun_sqrn
}.

lemma B16___mont_redM_h _r _b_r _a _b_a __P_mP _b__P_mP __U0 :
  hoare [B16.__mont_redM :
    arg = (_r, _b_r, _a, _b_a, __P_mP, _b__P_mP, __U0) /\ F16.__mont_redM_pre _r _b_r _a _b_a __P_mP _b__P_mP __U0
    ==> F16.__mont_redM_post _r _b_r _a _b_a __P_mP _b__P_mP __U0 res /\ valid res.`3].
proof.
have := h__H__MUL____mont_redM_safety _r _b_r _a _b_a __P_mP _b__P_mP __U0; rewrite /h__H__MUL____mont_redM_spec => hh.
by conseq hh => /> /#.
qed.

lemma B16_fun_muln_h _r _b_r _a _b_a _b _b_b :
  hoare [B16.fun_muln :
    arg = (_r, _b_r, _a, _b_a, _b, _b_b) /\ F16.fun_muln_pre _r _b_r _a _b_a _b _b_b
    ==> F16.fun_muln_post _r _b_r _a _b_a _b _b_b res /\ valid res.`3].
proof.
have := h__H__FPM__fun_muln_safety _r _b_r _a _b_a _b _b_b; rewrite /h__H__FPM__fun_muln_spec => hh.
by conseq hh => /> /#.
qed.

lemma B16_fun_sqrn_h _r _b_r _a _b_a :
  hoare [B16.fun_sqrn :
    arg = (_r, _b_r, _a, _b_a) /\ F16.fun_sqrn_pre _r _b_r _a _b_a
    ==> F16.fun_sqrn_post _r _b_r _a _b_a res /\ valid res.`3].
proof.
have := h__H__FPM__fun_sqrn_safety _r _b_r _a _b_a; rewrite /h__H__FPM__fun_sqrn_spec => hh.
by conseq hh => /> /#.
qed.

equiv eq_h__FPM___toM_: M.h__FPM___toM_ ~ F32.M(B32)._toM_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__FPM___toM__safety _a _b_a _ctx _b_ctx : h__FPM___toM__spec _a _b_a _ctx _b_ctx.
proof.
have h := F32._toM__proof B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h _a _b_a _ctx _b_ctx.
rewrite /h__FPM___toM__spec.
by conseq eq_h__FPM___toM_ h => /> /#.
qed.

equiv eq_h__FPM___fromM_: M.h__FPM___fromM_ ~ F32.M(B32)._fromM_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__FPM___fromM__safety _a _b_a _ctx _b_ctx : h__FPM___fromM__spec _a _b_a _ctx _b_ctx.
proof.
have h := F32._fromM__proof B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h _a _b_a _ctx _b_ctx.
rewrite /h__FPM___fromM__spec.
by conseq eq_h__FPM___fromM_ h => /> /#.
qed.

equiv eq_h__FPM___ctx_init_: M.h__FPM___ctx_init_ ~ F32.M(B32)._ctx_init_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__FPM___ctx_init__safety _ctx _b_ctx _p _b_P : h__FPM___ctx_init__spec _ctx _b_ctx _p _b_P.
proof.
have h := F32._ctx_init__proof B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h _ctx _b_ctx _p _b_P.
rewrite /h__FPM___ctx_init__spec.
by conseq eq_h__FPM___ctx_init_ h => /> /#.
qed.

equiv eq_h__FPM__fun_mulU: M.h__FPM__fun_mulU ~ F32.M(B32).fun_mulU : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__FPM__fun_mulU_safety _a _b_a _b _b_b _ctx _b_ctx : h__FPM__fun_mulU_spec _a _b_a _b _b_b _ctx _b_ctx.
proof.
have h := F32.FPB.fun_mulU_proof (<: F32.M(B32).P_FPB) (F32.P_FPB_muln_h B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h) (F32.P_FPB_sqrn_h B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h) (F32.P_FPB_red_h B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h) _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__FPM__fun_mulU_spec.
by conseq eq_h__FPM__fun_mulU h => /> /#.
qed.

equiv eq_h__FPM__fun_sqrU: M.h__FPM__fun_sqrU ~ F32.M(B32).fun_sqrU : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__FPM__fun_sqrU_safety _a _b_a _ctx _b_ctx : h__FPM__fun_sqrU_spec _a _b_a _ctx _b_ctx.
proof.
have h := F32.FPB.fun_sqrU_proof (<: F32.M(B32).P_FPB) (F32.P_FPB_muln_h B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h) (F32.P_FPB_sqrn_h B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h) (F32.P_FPB_red_h B32 B32___mont_redM_h B32_fun_muln_h B32_fun_sqrn_h) _a _b_a _ctx _b_ctx.
rewrite /h__FPM__fun_sqrU_spec.
by conseq eq_h__FPM__fun_sqrU h => /> /#.
qed.

equiv eq_h__H__FPM___toM_: M.h__H__FPM___toM_ ~ F16.M(B16)._toM_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM___toM__safety _a _b_a _ctx _b_ctx : h__H__FPM___toM__spec _a _b_a _ctx _b_ctx.
proof.
have h := F16._toM__proof B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h _a _b_a _ctx _b_ctx.
rewrite /h__H__FPM___toM__spec.
by conseq eq_h__H__FPM___toM_ h => /> /#.
qed.

equiv eq_h__H__FPM___fromM_: M.h__H__FPM___fromM_ ~ F16.M(B16)._fromM_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM___fromM__safety _a _b_a _ctx _b_ctx : h__H__FPM___fromM__spec _a _b_a _ctx _b_ctx.
proof.
have h := F16._fromM__proof B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h _a _b_a _ctx _b_ctx.
rewrite /h__H__FPM___fromM__spec.
by conseq eq_h__H__FPM___fromM_ h => /> /#.
qed.

equiv eq_h__H__FPM___redM_: M.h__H__FPM___redM_ ~ F16.M(B16)._redM_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM___redM__safety _r _b_r _a _b_a _ctx _b_ctx : h__H__FPM___redM__spec _r _b_r _a _b_a _ctx _b_ctx.
proof.
have h := F16._redM__proof B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h _r _b_r _a _b_a _ctx _b_ctx.
rewrite /h__H__FPM___redM__spec.
by conseq eq_h__H__FPM___redM_ h => /> /#.
qed.

equiv eq_h__H__FPM___ctx_init_: M.h__H__FPM___ctx_init_ ~ F16.M(B16)._ctx_init_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM___ctx_init__safety _ctx _b_ctx _p _b_P : h__H__FPM___ctx_init__spec _ctx _b_ctx _p _b_P.
proof.
have h := F16._ctx_init__proof B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h _ctx _b_ctx _p _b_P.
rewrite /h__H__FPM___ctx_init__spec.
by conseq eq_h__H__FPM___ctx_init_ h => /> /#.
qed.

equiv eq_h__H__FPM___submU_: M.h__H__FPM___submU_ ~ F16.M(B16)._submU_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM___submU__safety _a _b_a _b _b_b _ctx _b_ctx : h__H__FPM___submU__spec _a _b_a _b _b_b _ctx _b_ctx.
proof.
have h := F16.FPB._submU__proof (<: F16.M(B16).P_FPB) (F16.P_FPB_muln_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_sqrn_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_red_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__H__FPM___submU__spec.
by conseq eq_h__H__FPM___submU_ h => /> /#.
qed.

equiv eq_h__H__FPM___mulmU_: M.h__H__FPM___mulmU_ ~ F16.M(B16)._mulmU_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM___mulmU__safety _a _b_a _b _b_b _ctx _b_ctx : h__H__FPM___mulmU__spec _a _b_a _b _b_b _ctx _b_ctx.
proof.
have h := F16.FPB._mulmU__proof (<: F16.M(B16).P_FPB) (F16.P_FPB_muln_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_sqrn_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_red_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__H__FPM___mulmU__spec.
by conseq eq_h__H__FPM___mulmU_ h => /> /#.
qed.

module PE16 = {
  proc fun_mulU = F16.FPB.M(F16.M(B16).P_FPB).P_EXP.fun_mulU
  proc fun_sqrU = F16.FPB.M(F16.M(B16).P_FPB).P_EXP.fun_sqrU
}.

lemma PE16_fun_mulU_h _a _b_a _b _b_b _ctx _b_ctx :
  hoare [PE16.fun_mulU :
    arg = (_a, _b_a, _b, _b_b, _ctx, _b_ctx) /\ F16.FPB.BNE.fun_mulU_pre _a _b_a _b _b_b _ctx _b_ctx
    ==> F16.FPB.BNE.fun_mulU_post _a _b_a _b _b_b _ctx _b_ctx res /\ valid res.`3].
proof.
by conseq (F16.FPB.P_EXP_mulU_h (<: F16.M(B16).P_FPB) (F16.P_FPB_muln_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_sqrn_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_red_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) _a _b_a _b _b_b _ctx _b_ctx).
qed.

lemma PE16_fun_sqrU_h _a _b_a _ctx _b_ctx :
  hoare [PE16.fun_sqrU :
    arg = (_a, _b_a, _ctx, _b_ctx) /\ F16.FPB.BNE.fun_sqrU_pre _a _b_a _ctx _b_ctx
    ==> F16.FPB.BNE.fun_sqrU_post _a _b_a _ctx _b_ctx res /\ valid res.`3].
proof.
by conseq (F16.FPB.P_EXP_sqrU_h (<: F16.M(B16).P_FPB) (F16.P_FPB_muln_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_sqrn_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) (F16.P_FPB_red_h B16 B16___mont_redM_h B16_fun_muln_h B16_fun_sqrn_h) _a _b_a _ctx _b_ctx).
qed.

equiv eq_h__H__FPM__EXP___expm_: M.h__H__FPM__EXP___expm_ ~ F16.FPB.BNE.M(PE16)._expm_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__H__FPM__EXP___expm__safety _r _b_r _a _b_a _b _b_b _ctx _b_ctx : h__H__FPM__EXP___expm__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
proof.
have h := F16.FPB.BNE._expm__proof PE16 PE16_fun_mulU_h PE16_fun_sqrU_h _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__H__FPM__EXP___expm__spec.
by conseq eq_h__H__FPM__EXP___expm_ h => /> /#.
qed.

module BE32 = {
  proc fun_mulU = M.h__FPM__fun_mulU
  proc fun_sqrU = M.h__FPM__fun_sqrU
}.

lemma BE32_fun_mulU_h _a _b_a _b _b_b _ctx _b_ctx :
  hoare [BE32.fun_mulU :
    arg = (_a, _b_a, _b, _b_b, _ctx, _b_ctx) /\ E32.fun_mulU_pre _a _b_a _b _b_b _ctx _b_ctx
    ==> E32.fun_mulU_post _a _b_a _b _b_b _ctx _b_ctx res /\ valid res.`3].
proof.
have := h__FPM__fun_mulU_safety _a _b_a _b _b_b _ctx _b_ctx; rewrite /h__FPM__fun_mulU_spec => hh.
by conseq hh => /> /#.
qed.

lemma BE32_fun_sqrU_h _a _b_a _ctx _b_ctx :
  hoare [BE32.fun_sqrU :
    arg = (_a, _b_a, _ctx, _b_ctx) /\ E32.fun_sqrU_pre _a _b_a _ctx _b_ctx
    ==> E32.fun_sqrU_post _a _b_a _ctx _b_ctx res /\ valid res.`3].
proof.
have := h__FPM__fun_sqrU_safety _a _b_a _ctx _b_ctx; rewrite /h__FPM__fun_sqrU_spec => hh.
by conseq hh => /> /#.
qed.

equiv eq_h__FPM__EXPE___expmLR_noct_: M.h__FPM__EXPE___expmLR_noct_ ~ E32.M(BE32)._expmLR_noct_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof.
by proc; inline *; sim.
qed.

lemma h__FPM__EXPE___expmLR_noct__safety _r _b_r _a _b_a _b _b_b _ctx _b_ctx : h__FPM__EXPE___expmLR_noct__spec _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
proof.
have h := E32._expmLR_noct__proof BE32 BE32_fun_mulU_h BE32_fun_sqrU_h _r _b_r _a _b_a _b _b_b _ctx _b_ctx.
rewrite /h__FPM__EXPE___expmLR_noct__spec.
by conseq eq_h__FPM__EXPE___expmLR_noct_ h => /> /#.
qed.

