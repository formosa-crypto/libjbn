(* The library theories at the sizes of the RSA example (../rsa2048.jazz),
   and the extracted code of the example proved equal to their modules, so
   that the contracts of the library apply to it.

   The example (see its header) has two size scopes:
     H::H  16 limbs (p and q):  BN, MUL (the selector), FPM (fp_mont)
     H     32 limbs (n):        BN, MUL, FPM, and FPM::EXPE (exponents of
                                nlimbsE = 4 limbs, for e)
   with the profile x86_64 (no BMI2/ADX, JBN_UNROLL_MAX = 64), so that the
   selector takes bn_mul at both sizes.

   Each extracted procedure used by the RSA code is related to the
   procedure of the theory instance (equiv eq..., by `inline *; sim`), and
   its contract is carried over (`conseq` with the equivalence). *)

require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel_x86.
import SLH64.

require import RsaPssXtr.
require import Array4 Array16 Array32 Array64 Array65 Array129.
require Bn_exp Fp_mont.

(* -------------------------------------------------------------------- *)
(* the theories at the sizes of the example                              *)

(* the field of p and q: 16 limbs, x86_64 *)
clone Fp_mont as F16
 with op nlimbs <- 16,
      op jbn_features <- 0,
      op jbn_reg_max <- 0,
      op jbn_unroll_max <- 64,
      theory BigN.BN.A <= Array16,
      theory BigN.BN2.A <= Array32,
      theory FPC.CTX <= Array65
 proof gt0_nlimbs by done, nlimbs_bnd by done.

(* the field of n: 32 limbs, x86_64 *)
clone Fp_mont as F32
 with op nlimbs <- 32,
      op jbn_features <- 0,
      op jbn_reg_max <- 0,
      op jbn_unroll_max <- 64,
      theory BigN.BN.A <= Array32,
      theory BigN.BN2.A <= Array64,
      theory FPC.CTX <= Array129
 proof gt0_nlimbs by done, nlimbs_bnd by done.

(* the exponentiation by exponents of 4 limbs over the field of n
   (H::FPM::EXPE): the monoid of representatives of Fp_base, as in its
   own exponentiation (Fp_base.BNE) *)
clone Bn_exp as E32
 with op nlimbs <- 32,
      op nlimbsexp <- 4,
      theory BigN <- F32.BigN,
      theory BNexp.A <= Array4,
      theory BNUTIL <- F32.BNUTIL,
      theory BNB <- F32.BNB,
      theory FPC <- F32.FPC,
      op mok <- (fun c => F32.FPB.ctx_fp (F32.BigN.BN.bn (F32.FPC.ctxP c)) c),
      op mdom <- (fun c x => 0 <= x < F32.BigN.BN.bn (F32.FPC.ctxP c)),
      op mmul <- (fun c x y => F32.FPB.red (F32.BigN.BN.bn (F32.FPC.ctxP c)) (x * y))
 proof gt0_nlimbs by done,
       gt0_nlimbsexp by done,
       nlimbsexp_bnd by done,
       nlimbs_bnd by done,
       mmul_dom by exact F32.FPB.fp_mmul_dom,
       mmulA by smt(F32.FPB.red_assoc),
       mmulC by smt(F32.FPB.redC),
       mone_dom by exact F32.FPB.fp_mone_dom,
       mmul1 by exact F32.FPB.fp_mmul1.

(* -------------------------------------------------------------------- *)
(* the multiplication of each field (fp_mul_sel: the selector's)          *)

module B16 = {
  proc fun_muln (r: W64.t Array32.t, a b: W64.t Array16.t) : W64.t Array32.t = {
    r <@ F16.BNMUL_M._muln_(r, a, b);
    return r;
  }
  proc fun_sqrn (r: W64.t Array32.t, a: W64.t Array16.t) : W64.t Array32.t = {
    r <@ F16.BNMUL_M._sqrn_(r, a);
    return r;
  }
}.

lemma B16_muln_ll: islossless B16.fun_muln.
proof. by proc; call F16.BNMUL._muln__ll. qed.
lemma B16_sqrn_ll: islossless B16.fun_sqrn.
proof. by proc; call F16.BNMUL._sqrn__ll. qed.
hoare B16_muln_h _a _b:
 B16.fun_muln : arg.`2 = _a /\ arg.`3 = _b
   ==> F16.BigN.BN2.bn res = F16.BigN.BN.bn _a * F16.BigN.BN.bn _b.
proof. by proc; ecall (F16.BNMUL._muln__h a b). qed.
hoare B16_sqrn_h _a:
 B16.fun_sqrn : arg.`2 = _a
   ==> F16.BigN.BN2.bn res = F16.BigN.BN.bn _a * F16.BigN.BN.bn _a.
proof. by proc; ecall (F16.BNMUL._sqrn__h a). qed.

module B32 = {
  proc fun_muln (r: W64.t Array64.t, a b: W64.t Array32.t) : W64.t Array64.t = {
    r <@ F32.BNMUL_M._muln_(r, a, b);
    return r;
  }
  proc fun_sqrn (r: W64.t Array64.t, a: W64.t Array32.t) : W64.t Array64.t = {
    r <@ F32.BNMUL_M._sqrn_(r, a);
    return r;
  }
}.

lemma B32_muln_ll: islossless B32.fun_muln.
proof. by proc; call F32.BNMUL._muln__ll. qed.
lemma B32_sqrn_ll: islossless B32.fun_sqrn.
proof. by proc; call F32.BNMUL._sqrn__ll. qed.
hoare B32_muln_h _a _b:
 B32.fun_muln : arg.`2 = _a /\ arg.`3 = _b
   ==> F32.BigN.BN2.bn res = F32.BigN.BN.bn _a * F32.BigN.BN.bn _b.
proof. by proc; ecall (F32.BNMUL._muln__h a b). qed.
hoare B32_sqrn_h _a:
 B32.fun_sqrn : arg.`2 = _a
   ==> F32.BigN.BN2.bn res = F32.BigN.BN.bn _a * F32.BigN.BN.bn _a.
proof. by proc; ecall (F32.BNMUL._sqrn__h a). qed.

(* the field modules of the example, and their exponentiations *)
module FM16 = F16.M(B16).
module FB16 = F16.FPB.M(F16.M(B16).P_FPB).
module EXP16 = F16.FPB.BNE.M(F16.FPB.M(F16.M(B16).P_FPB).P_EXP).
module FM32 = F32.M(B32).
module EXPE32 = E32.M(F32.FPB.M(F32.M(B32).P_FPB).P_EXP).

(* -------------------------------------------------------------------- *)
(* the extracted procedures are those of the theories                    *)

(* 16 limbs *)
equiv eq16_mov: M.h__H__BN___mov_ ~ F16.BNB_M._mov_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_set0: M.h__H__BN___set0_ ~ F16.BNB_M._set0_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_muln: M.h__H__MUL___muln_ ~ F16.BNMUL_M._muln_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_redM: M.h__H__FPM___redM_ ~ FM16._redM_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_toM: M.h__H__FPM___toM_ ~ FM16._toM_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_fromM: M.h__H__FPM___fromM_ ~ FM16._fromM_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_submU: M.h__H__FPM___submU_ ~ FM16._submU_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_mulmU: M.h__H__FPM___mulmU_ ~ FM16._mulmU_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_expm: M.h__H__FPM__EXP___expm_ ~ EXP16._expm_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq16_ctx_init: M.h__H__FPM___ctx_init_ ~ FM16._ctx_init_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.

(* 32 limbs *)
equiv eq32_mov: M.h__BN___mov_ ~ F32.BNB_M._mov_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq32_addU: M.h__BN___addU_ ~ F32.BNB_M._addU_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq32_toM: M.h__FPM___toM_ ~ FM32._toM_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq32_fromM: M.h__FPM___fromM_ ~ FM32._fromM_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq32_expmLR_noct: M.h__FPM__EXPE___expmLR_noct_ ~ EXPE32._expmLR_noct_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.
equiv eq32_ctx_init: M.h__FPM___ctx_init_ ~ FM32._ctx_init_ : ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof. by proc; inline *; sim. qed.

(* -------------------------------------------------------------------- *)
(* the contracts of the extracted procedures                             *)

(* the parameters of the nested modules (fun_muln/fun_sqrn/fun_red of
   Fp_base in Fp_mont, fun_mulU/fun_sqrU of the exponentiations), from
   those of the bindings *)
lemma P16_muln_ll: islossless F16.M(B16).P_FPB.fun_muln.
proof. exact (F16.P_FPB_muln_ll B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h). qed.
lemma P16_sqrn_ll: islossless F16.M(B16).P_FPB.fun_sqrn.
proof. exact (F16.P_FPB_sqrn_ll B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h). qed.
lemma P16_red_ll: islossless F16.M(B16).P_FPB.fun_red.
proof. exact (F16.P_FPB_red_ll B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h). qed.

lemma P32_muln_ll: islossless F32.M(B32).P_FPB.fun_muln.
proof. exact (F32.P_FPB_muln_ll B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h). qed.
lemma P32_sqrn_ll: islossless F32.M(B32).P_FPB.fun_sqrn.
proof. exact (F32.P_FPB_sqrn_ll B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h). qed.
lemma P32_red_ll: islossless F32.M(B32).P_FPB.fun_red.
proof. exact (F32.P_FPB_red_ll B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h). qed.

(* 16 limbs *)
hoare mov16_h _a: M.h__H__BN___mov_ : a = _a ==> res = _a.
proof.
conseq eq16_mov (F16.BNB._mov__h _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare set016_h: M.h__H__BN___set0_ : true ==> F16.BigN.BN.bn res = 0.
proof.
conseq eq16_set0 F16.BNB._set0__h.
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare muln16_h _a _b:
 M.h__H__MUL___muln_ : a = _a /\ b = _b
   ==> F16.BigN.BN2.bn res = F16.BigN.BN.bn _a * F16.BigN.BN.bn _b.
proof.
conseq eq16_muln (F16.BNMUL._muln__h _a _b).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare redM16_h p _a:
 M.h__H__FPM___redM_
 : F16.FPC.ctx_mod p ctx /\ F16.mont_ctx p ctx /\ a = _a
   /\ F16.BigN.BN2.bn _a < p * F16.BigN.BN.bn_modulus
   ==> F16.BigN.BN.bn res = F16.FPB.red p (F16.BigN.BN2.bn _a).
proof.
conseq eq16_redM (F16._redM__h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h p _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare toM16_h p _a:
 M.h__H__FPM___toM_ : F16.FPC.ctx_mont p ctx /\ a = _a
   ==> F16.BigN.BN.bn res = F16.BigN.BN.bn _a * F16.BigN.BN.bn_modulus %% p.
proof.
conseq eq16_toM (F16._toM__any_h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h p _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare fromM16_h p _a:
 M.h__H__FPM___fromM_
 : F16.FPC.ctx_mod p ctx /\ F16.mont_ctx p ctx /\ a = _a /\ F16.BigN.BN.bn _a < p
   ==> F16.BigN.BN.bn res = F16.FPB.red p (F16.BigN.BN.bn _a).
proof.
conseq eq16_fromM (F16._fromM__h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h p _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare submU16_h p _a _b:
 M.h__H__FPM___submU_
 : F16.FPC.ctx_mod p ctx /\ a = _a /\ b = _b
   /\ F16.BigN.BN.bn _a < p /\ F16.BigN.BN.bn _b < p
   ==> F16.BigN.BN.bn res = (F16.BigN.BN.bn _a - F16.BigN.BN.bn _b) %% p.
proof.
conseq eq16_submU (F16._submU__h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h p _a _b).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare mulmU16_h p _a _b:
 M.h__H__FPM___mulmU_
 : F16.FPC.ctx_mod p ctx /\ F16.mont_ctx p ctx /\ a = _a /\ b = _b
   /\ F16.BigN.BN.bn _a < p /\ F16.BigN.BN.bn _b < p
   ==> F16.BigN.BN.bn res = F16.FPB.red p (F16.BigN.BN.bn _a * F16.BigN.BN.bn _b).
proof.
conseq eq16_mulmU (F16._mulmU__h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h p _a _b).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare expm16_h _c _a _b:
 M.h__H__FPM__EXP___expm_
 : ctx = _c /\ a = _a /\ b = _b
   /\ F16.FPB.ctx_fp (F16.BigN.BN.bn (F16.FPC.ctxP _c)) _c
   /\ 0 <= F16.BigN.BN.bn _a < F16.BigN.BN.bn (F16.FPC.ctxP _c)
   ==> F16.BigN.BN.bn res = F16.FPB.BNE.mexp _c (F16.BigN.BN.bn _a) (F16.BigN.BN.bn _b).
proof.
have PMh := F16.P_FPB_muln_h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h.
have PSh := F16.P_FPB_sqrn_h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h.
have PRh := F16.P_FPB_red_h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h.
have EMl := F16.FPB.P_EXP_mulU_ll (<: F16.M(B16).P_FPB) P16_muln_ll P16_sqrn_ll P16_red_ll PMh PSh PRh.
have ESl := F16.FPB.P_EXP_sqrU_ll (<: F16.M(B16).P_FPB) P16_muln_ll P16_sqrn_ll P16_red_ll PMh PSh PRh.
have EMh := F16.FPB.P_EXP_mulU_h (<: F16.M(B16).P_FPB) P16_muln_ll P16_sqrn_ll P16_red_ll PMh PSh PRh.
have ESh := F16.FPB.P_EXP_sqrU_h (<: F16.M(B16).P_FPB) P16_muln_ll P16_sqrn_ll P16_red_ll PMh PSh PRh.
conseq eq16_expm (F16.FPB.BNE._expm__h (<: F16.FPB.M(F16.M(B16).P_FPB).P_EXP) EMl ESl EMh ESh _c _a _b).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare ctx_init16_h _p:
 M.h__H__FPM___ctx_init_
 : F16.BigN.BN.bn p = _p /\ 1 < _p /\ _p %% 2 = 1 ==> F16.FPC.ctx_mont _p res.
proof.
conseq eq16_ctx_init (F16._ctx_init__h B16 B16_muln_ll B16_sqrn_ll B16_muln_h B16_sqrn_h _p).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

(* 32 limbs *)
hoare mov32_h _a: M.h__BN___mov_ : a = _a ==> res = _a.
proof.
conseq eq32_mov (F32.BNB._mov__h _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare addU32_h _a _b:
 M.h__BN___addU_ : a = _a /\ b = _b
   ==> F32.BigN.BN.bn_withcarry res = F32.BigN.BN.bn _a + F32.BigN.BN.bn _b.
proof.
conseq eq32_addU (F32.BNB._addU__h _a _b).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare toM32_h p _a:
 M.h__FPM___toM_ : F32.FPC.ctx_mont p ctx /\ a = _a
   ==> F32.BigN.BN.bn res = F32.BigN.BN.bn _a * F32.BigN.BN.bn_modulus %% p.
proof.
conseq eq32_toM (F32._toM__any_h B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h p _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare fromM32_h p _a:
 M.h__FPM___fromM_
 : F32.FPC.ctx_mod p ctx /\ F32.mont_ctx p ctx /\ a = _a /\ F32.BigN.BN.bn _a < p
   ==> F32.BigN.BN.bn res = F32.FPB.red p (F32.BigN.BN.bn _a).
proof.
conseq eq32_fromM (F32._fromM__h B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h p _a).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare expmLR_noct32_h _c _a _b:
 M.h__FPM__EXPE___expmLR_noct_
 : ctx = _c /\ a = _a /\ b = _b
   /\ F32.FPB.ctx_fp (F32.BigN.BN.bn (F32.FPC.ctxP _c)) _c
   /\ 0 <= F32.BigN.BN.bn _a < F32.BigN.BN.bn (F32.FPC.ctxP _c)
   ==> F32.BigN.BN.bn res = E32.mexp _c (F32.BigN.BN.bn _a) (E32.BNexp.bn _b).
proof.
have PMh := F32.P_FPB_muln_h B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h.
have PSh := F32.P_FPB_sqrn_h B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h.
have PRh := F32.P_FPB_red_h B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h.
have EMl := F32.FPB.P_EXP_mulU_ll (<: F32.M(B32).P_FPB) P32_muln_ll P32_sqrn_ll P32_red_ll PMh PSh PRh.
have ESl := F32.FPB.P_EXP_sqrU_ll (<: F32.M(B32).P_FPB) P32_muln_ll P32_sqrn_ll P32_red_ll PMh PSh PRh.
have EMh := F32.FPB.P_EXP_mulU_h (<: F32.M(B32).P_FPB) P32_muln_ll P32_sqrn_ll P32_red_ll PMh PSh PRh.
have ESh := F32.FPB.P_EXP_sqrU_h (<: F32.M(B32).P_FPB) P32_muln_ll P32_sqrn_ll P32_red_ll PMh PSh PRh.
conseq eq32_expmLR_noct (E32._expmLR_noct__h (<: F32.FPB.M(F32.M(B32).P_FPB).P_EXP) EMl ESl EMh ESh _c _a _b).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.

hoare ctx_init32_h _p:
 M.h__FPM___ctx_init_
 : F32.BigN.BN.bn p = _p /\ 1 < _p /\ _p %% 2 = 1 ==> F32.FPC.ctx_mont _p res.
proof.
conseq eq32_ctx_init (F32._ctx_init__h B32 B32_muln_ll B32_sqrn_ll B32_muln_h B32_sqrn_h _p).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
qed.
