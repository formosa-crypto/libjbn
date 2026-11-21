(* Correctness of the RSA code of the example (../rsa2048@libjbn.jinc and
   the entry points of ../rsa2048.jazz):

     rsa_init   the expanded keys of the example key pair are well formed
                (the contexts of n, p and q are Montgomery contexts);
     rsa_enc    RSAVP1: c = m^e mod n, for any well-formed PK of (n, e);
     rsa_dec    RSASP1 by the CRT, for any well-formed SK of
                (p, q, dP, dQ, qInv) with qInv * q = 1 (mod p): for c < p*q,
                a result below p*q, congruent to c^dP modulo p and to c^dQ
                modulo q.

   The library procedures they call have the contracts of the library
   theories (RsaPss_inst.ec); the formats of the keys and the example key
   pair are in RsaPss_keys.ec. *)

require import AllCore IntDiv CoreMap List StdOrder.
from Jasmin require import JModel_x86.
import SLH64.

require import RsaPssXtr RsaPss_inst RsaPss_keys.
require import Array4 Array16 Array32 Array36 Array65 Array80 Array129 Array133 Array178.

(* a 32-word number is the same seen as a double of 16 limbs or as 32 limbs *)
lemma bn2_16_bn32 (x: W64.t Array32.t): F16.BigN.BN2.bn x = bn32 x.
proof. by rewrite /F16.BigN.BN2.bnk /F32.BigN.BN.bnk /F16.BigN.BN2.dig /F32.BigN.BN.dig. qed.

lemma bn2_16_bn32' (x: W64.t Array32.t): F16.BigN.BN2.bnk 32 x = bn32 x.
proof. exact (bn2_16_bn32 x). qed.

(* -------------------------------------------------------------------- *)
(* Montgomery arithmetic modulo an odd X                                 *)

(* from Montgomery form, then back: x * R^-1 * R = x *)
lemma red16_toM X c: 1 < X => X %% 2 = 1 =>
  F16.FPB.red X c * R16 %% X = c %% X.
proof.
move=> H1 Hodd; have HR := F16.Rinv_R X H1 Hodd.
rewrite /F16.FPB.red modzMml.
have ->: c * F16.Rinv X * R16 = c * (F16.Rinv X * R16) by ring.
by rewrite -modzMmr HR.
qed.

(* into Montgomery form, then out: x * R * R^-1 = x *)
lemma red16_R X x: 1 < X => X %% 2 = 1 =>
  F16.FPB.red X (x * R16 %% X) = x %% X.
proof.
move=> H1 Hodd; have HR := F16.Rinv_R X H1 Hodd.
rewrite /F16.FPB.red modzMml.
have ->: x * R16 * F16.Rinv X = x * (F16.Rinv X * R16) by ring.
by rewrite -modzMmr HR.
qed.

lemma red32_R X x: 1 < X => X %% 2 = 1 =>
  F32.FPB.red X (x * R32 %% X) = x %% X.
proof.
move=> H1 Hodd; have HR := F32.Rinv_R X H1 Hodd.
rewrite /F32.FPB.red modzMml.
have ->: x * R32 * F32.Rinv X = x * (F32.Rinv X * R32) by ring.
by rewrite -modzMmr HR.
qed.

(* the value of a power in the monoid of representatives of EXPE (as
   Fp_base.red_mexp for the field's own exponentiation) *)
lemma red_mexp32 p c x n: F32.FPB.ctx_fp p c => 0 <= x < p => 0 <= n =>
  F32.FPB.red p (E32.mexp c x n) = (F32.FPB.red p x) ^ n %% p.
proof.
move=> Hc Hx; have [HP H1] := F32.FPB.ctx_fp_p _ _ Hc.
elim/natind: n => [n Hn H0|n Hn IH _].
- rewrite (_: n = 0) 1:/# E32.mexp0 expr0 modz_small 1:/#.
  by have [_ [_ [_ ->]]] := Hc.
- rewrite E32.mexpS //= HP F32.FPB.red_mul IH // modzMmr exprS //.
qed.

(* -------------------------------------------------------------------- *)
(* the expansion of the keys                                             *)

hoare ctx_init_N_h _p:
 M.h__RSA___ctx_init_N : bn32 n = _p /\ 1 < _p /\ _p %% 2 = 1
   ==> F32.FPC.ctx_mont _p res.
proof. by proc; ecall (ctx_init32_h _p). qed.

hoare ctx_init_P_h _p:
 M.h__RSA___ctx_init_P : bn16 p = _p /\ 1 < _p /\ _p %% 2 = 1
   ==> F16.FPC.ctx_mont _p res.
proof. by proc; ecall (ctx_init16_h _p). qed.

(* PK = (ctx_n, e) from pk = (n, e) *)
hoare expand_pk_h _k N:
 M.h__RSA____RSA_expand_pk
 : pk = _k /\ bn32 (pub_n _k) = N /\ 1 < N /\ N %% 2 = 1
   ==> F32.FPC.ctx_mont N (pk_ctxn res) /\ pk_e res = pub_e _k.
proof.
proc.
unroll for ^while.
wp; ecall (ctx_init_N_h N); wp; skip => &hr [-> [Hn [H1 Hodd]]].
split; first done.
move=> _ c Hc.
split.
- have ->: pk_ctxn (Array133.init (fun i_0 => if 0 <= i_0 < 0 + 129 then c.[i_0 - 0] else pK{hr}.[i_0])).[(4 * 32 + 1) + 0 <- _k.[32 + 0]].[(4 * 32 + 1) + 1 <- _k.[32 + 1]].[(4 * 32 + 1) + 2 <- _k.[32 + 2]].[(4 * 32 + 1) + 3 <- _k.[32 + 3]] = c; last done.
  apply Array129.tP => i Hi.
  rewrite /pk_ctxn Array129.initiE //= !Array133.get_setE 1..4:/#.
  by rewrite Array133.initiE 1:/# /= /#.
apply Array4.tP => i Hi.
rewrite /pk_e /pub_e !Array4.initiE //= !Array133.get_setE 1..4:/#.
smt().
qed.

(* the parts of an expanded private key, from its words *)
lemma sk_ctxpE (k: W64.t Array178.t) c:
  (forall i, 0 <= i < 65 => k.[i] = c.[i]) => sk_ctxp k = c.
proof. by move=> H; apply Array65.tP => i Hi; rewrite /sk_ctxp Array65.initiE //= H. qed.

lemma sk_ctxqE (k: W64.t Array178.t) c:
  (forall i, 0 <= i < 65 => k.[65 + i] = c.[i]) => sk_ctxq k = c.
proof. by move=> H; apply Array65.tP => i Hi; rewrite /sk_ctxq Array65.initiE //= H. qed.

lemma sk_dpE (k: W64.t Array178.t) c:
  (forall i, 0 <= i < 16 => k.[130 + i] = c.[i]) => sk_dp k = c.
proof. by move=> H; apply Array16.tP => i Hi; rewrite /sk_dp Array16.initiE //= H. qed.

lemma sk_dqE (k: W64.t Array178.t) c:
  (forall i, 0 <= i < 16 => k.[146 + i] = c.[i]) => sk_dq k = c.
proof. by move=> H; apply Array16.tP => i Hi; rewrite /sk_dq Array16.initiE //= H. qed.

lemma sk_qinvE (k: W64.t Array178.t) c:
  (forall i, 0 <= i < 16 => k.[162 + i] = c.[i]) => sk_qinv k = c.
proof. by move=> H; apply Array16.tP => i Hi; rewrite /sk_qinv Array16.initiE //= H. qed.

(* SK = (ctx_p, ctx_q, dP, dQ, qInv) from sk = (p, q, dP, dQ, qInv) *)
hoare expand_sk_h _k P Q:
 M.h__RSA____RSA_expand_sk
 : sk = _k /\ bn16 (priv_p _k) = P /\ 1 < P /\ P %% 2 = 1
   /\ bn16 (priv_q _k) = Q /\ 1 < Q /\ Q %% 2 = 1
   ==> F16.FPC.ctx_mont P (sk_ctxp res) /\ F16.FPC.ctx_mont Q (sk_ctxq res)
    /\ sk_dp res = priv_dp _k /\ sk_dq res = priv_dq _k
    /\ sk_qinv res = priv_qinv _k.
proof.
proc.
wp; ecall (mov16_h y); wp.
ecall (mov16_h y); wp.
ecall (mov16_h y); wp.
ecall (ctx_init_P_h Q); wp.
ecall (ctx_init_P_h P); wp.
skip => &hr [-> [Hp [Hp1 [Hpodd [Hq [Hq1 Hqodd]]]]]].
split; first done.
move=> _ cp Hcp.
split; first done.
move=> _ cq Hcq /=.
move=> d1 -> d2 -> d3 ->.
rewrite (sk_ctxpE _ cp).
- by move=> i Hi; do (rewrite Array178.initiE 1:/# /=); smt().
rewrite (sk_ctxqE _ cq).
- by move=> i Hi; do (rewrite Array178.initiE 1:/# /=); smt().
rewrite (sk_dpE _ (priv_dp _k)).
- move=> i Hi; do (rewrite Array178.initiE 1:/# /=).
  by rewrite (_: (162 <= 130 + i < 178) = false) 1:/# (_: (146 <= 130 + i < 162) = false) 1:/# (_: (130 <= 130 + i < 146) = true) 1:/# /= /priv_dp !Array16.initiE.
rewrite (sk_dqE _ (priv_dq _k)).
- move=> i Hi; do (rewrite Array178.initiE 1:/# /=).
  by rewrite (_: (162 <= 146 + i < 178) = false) 1:/# (_: (146 <= 146 + i < 162) = true) 1:/# /= /priv_dq !Array16.initiE.
rewrite (sk_qinvE _ (priv_qinv _k)).
- move=> i Hi; do (rewrite Array178.initiE 1:/# /=).
  by rewrite (_: (162 <= 162 + i < 178) = true) 1:/# /= /priv_qinv !Array16.initiE.
done.
qed.

(* rsa_init: the expanded keys of the example key pair are well formed *)
hoare rsa_init_h:
 M.rsa_init : true
   ==> wf_pk n_val e_val res.`1 /\ wf_sk p_val q_val dP_val dQ_val qInv_val res.`2.
proof.
proc.
wp; ecall (expand_sk_h skT p_val q_val); wp.
ecall (expand_pk_h pkT n_val); wp.
skip; rewrite -/pkT -/skT => &hr _.
have [Hn1 Hnodd] := n_odd; have [Hp1 Hpodd] := p_odd; have [Hq1 Hqodd] := q_odd.
split; first by rewrite pkT_n.
move=> _ PK [HPK HPKe].
split; first by rewrite skT_p skT_q.
move=> _ SK [HSKp [HSKq [HSKdp [HSKdq HSKqi]]]].
split; first by split => //; rewrite HPKe pkT_e.
by rewrite /wf_sk /= HSKp HSKq HSKdp HSKdq HSKqi skT_dp skT_dq skT_qinv.
qed.

(* -------------------------------------------------------------------- *)
(* RSAVP1 (rsa_enc): y = s^e mod n                                       *)

hoare RSAVP1_h N E _s:
 M.h__RSA____RSAVP1 : s = _s /\ wf_pk N E pk
   ==> bn32 res = (bn32 _s %% N) ^ E %% N.
proof.
proc.
ecall (fromM32_h N y); wp.
ecall (expmLR_noct32_h ctx_n x e); wp.
ecall (toM32_h N x); wp.
ecall (mov32_h s); wp.
skip => &hr [-> [Hc He]] /=.
rewrite -/(pk_ctxn pk{hr}) -/(pk_e pk{hr}).
move: Hc He => /= Hc He.
have Hfp := F32.ctx_mont_fp _ _ Hc.
have [[H1 [Hodd [HP HmP]]] [Hone [HR2 HU0]]] := Hc.
move=> m1 ->; split; first done.
move=> _ m2 Hm2.
have Hm2b: 0 <= bn32 m2 < N by rewrite Hm2; smt(modz_ge0 ltz_pmod).
split; first by rewrite HP.
move=> _ r1 Hr1.
have Hr1b: 0 <= bn32 r1 < N.
- rewrite Hr1; have := E32.mexp_dom (pk_ctxn pk{hr}) (bn32 m2) (bn4 (pk_e pk{hr})) _ _ _ => //=.
  + by rewrite HP.
  + by rewrite HP.
  + smt(E32.BNexp.bnk_cmp).
  by rewrite HP.
split; first by do !split => //; smt().
move=> _ r2 ->.
rewrite Hr1 red_mexp32 //; first smt(E32.BNexp.bnk_cmp).
by rewrite Hm2 red32_R // He.
qed.

(* rsa_enc(c, m, PK): c = m^e mod n *)
hoare rsa_enc_h N E _m:
 M.rsa_enc : m = _m /\ wf_pk N E pk ==> bn32 res = (bn32 _m %% N) ^ E %% N.
proof. by proc; ecall (RSAVP1_h N E m). qed.

(* -------------------------------------------------------------------- *)
(* RSASP1 by the CRT (rsa_dec)                                          *)

(* x = (x * R^-1) * R in Montgomery form, for 0 <= x < X *)
lemma red16_inv X x: 1 < X => X %% 2 = 1 => 0 <= x < X =>
  x = F16.FPB.red X x * R16 %% X.
proof. by move=> H1 Hodd Hx; rewrite red16_toM // modz_small /#. qed.

(* the half of the CRT, in Montgomery form: r = (c mod X)^dX * R mod X *)
hoare crt_exp_h X _c _d _ctx:
 M.h__RSA___crt_exp
 : ctxX = _ctx /\ c = _c /\ dX = _d /\ F16.FPC.ctx_mont X _ctx
   /\ F16.BigN.BN2.bn _c < X * R16
   ==> bn16 res = (F16.BigN.BN2.bn _c %% X) ^ bn16 _d * R16 %% X.
proof.
proc.
ecall (expm16_h ctxX cX dX).
ecall (toM16_h X cX).
ecall (toM16_h X cX).
ecall (redM16_h X c).
wp; skip => &hr [-> [-> [-> [Hc Hb]]]].
have Hfp := F16.ctx_mont_fp _ _ Hc.
have [[H1 [Hodd [HP HmP]]] [Hone [HR2 HU0]]] := Hc.
split; first by do !split => //.
move=> _ c1 Hc1; split; first done.
move=> _ c2 Hc2; split; first done.
move=> _ c3 Hc3.
have Hc3b: 0 <= bn16 c3 < X by rewrite Hc3; smt(modz_ge0 ltz_pmod).
split; first by rewrite HP.
move=> _ r1 Hr1.
have Hr1b: 0 <= bn16 r1 < X.
- rewrite Hr1; have := F16.FPB.BNE.mexp_dom _ctx (bn16 c3) (bn16 _d) _ _ _ => //=.
  + by rewrite HP.
  + by rewrite HP.
  + smt(F16.BigN.BN.bnk_cmp).
  by rewrite HP.
have Hred: F16.FPB.red X (bn16 r1) = (F16.BigN.BN2.bn _c %% X) ^ bn16 _d %% X.
- rewrite Hr1 F16.FPB.red_mexp //; first smt(F16.BigN.BN.bnk_cmp).
  by rewrite Hc3 red16_R // Hc2 modz_mod Hc1 red16_toM.
by rewrite {1}(red16_inv X (bn16 r1)) // Hred modzMml.
qed.

(* the zeroing sets every word *)
hoare set016_w_h:
 M.h__H__BN___set0_ : true ==> forall k, 0 <= k < 16 => res.[k] = W64.zero.
proof.
conseq eq16_set0 (_: true ==> forall k, 0 <= k < 16 => res.[k] = W64.zero).
- by move=> &1 H; exists Glob.mem{1} arg{1}.
- by move=> &1 &2 [-> _].
by proc; ecall (F16.BNB._fill__h t); auto.
qed.

require import StdBigop.
import Bigint BIA.

(* a number of 32 words whose upper 16 are zero is its lower 16 *)
lemma bn32_low (w: W64.t Array32.t) (x: W64.t Array16.t):
  (forall i, 0 <= i < 16 => w.[i] = x.[i]) =>
  (forall i, 16 <= i < 32 => w.[i] = W64.zero) =>
  bn32 w = bn16 x.
proof.
move=> Hlo Hhi.
rewrite (F32.BigN.BN.bn_k_kup 16 w) //.
have ->: F32.BigN.BN.bnkup 16 w = 0.
- rewrite /F32.BigN.BN.bnkup big1_seq //= => i Hi.
  by rewrite Hhi; smt(mem_range).
rewrite /F32.BigN.BN.bnk /F16.BigN.BN.bnk /=.
by apply eq_big_int => i Hi /=; rewrite /F32.BigN.BN.dig /F16.BigN.BN.dig Hlo.
qed.

(* Garner's step: from mp * R and mq * R (Montgomery form), the product by
   the plain qInv and one reduction give (mp - mq) * qInv mod X *)
lemma garner_plain X a b c: 1 < X => X %% 2 = 1 =>
  F16.FPB.red X (((a * R16 %% X - b * R16 %% X) %% X) * c) = (a - b) * c %% X.
proof.
move=> H1 Hodd; have HR := F16.Rinv_R X H1 Hodd.
rewrite modzBm -mulrBl /F16.FPB.red.
have ->: (a - b) * R16 %% X * c * F16.Rinv X
         = ((a - b) * R16 %% X) * (c * F16.Rinv X) by ring.
rewrite modzMml.
have ->: (a - b) * R16 * (c * F16.Rinv X) = (a - b) * c * (F16.Rinv X * R16) by ring.
by rewrite -modzMmr HR.
qed.

(* the CRT recombination: m = mq + ((mp - mq) * qInv mod p) * q *)
lemma crt_comb p q mp mq qi: 1 < p => 1 < q => 0 <= mq < q => qi * q %% p = 1 =>
  (mq + ((mp - mq) * qi %% p) * q) %% p = mp %% p
  /\ (mq + ((mp - mq) * qi %% p) * q) %% q = mq
  /\ 0 <= mq + ((mp - mq) * qi %% p) * q < p * q.
proof.
move=> Hp Hq Hmq Hqi.
have Hh: 0 <= (mp - mq) * qi %% p < p by smt(modz_ge0 ltz_pmod).
split.
- have Hhq: ((mp - mq) * qi %% p * q) %% p = (mp - mq) %% p.
  + have ->: (mp - mq) * qi %% p * q %% p = (mp - mq) * qi * q %% p by rewrite modzMml.
    have ->: (mp - mq) * qi * q = (mp - mq) * (qi * q) by ring.
    by rewrite -modzMmr Hqi.
  rewrite -modzDm Hhq modzDm.
  by rewrite (_: mq + (mp - mq) = mp) 1:/#.
split; first by rewrite modzMDr modz_small /#.
have: (mp - mq) * qi %% p * q <= (p - 1) * q.
- by apply StdOrder.IntOrder.ler_wpmul2r; smt().
smt().
qed.

(* a sum below R has no carry *)
lemma withcarry_small (r: bool * W64.t Array32.t) s:
  F32.BigN.BN.bn_withcarry r = s => 0 <= s < R32 => bn32 r.`2 = s.
proof.
move=> <- [_ Hs].
have [H0 _] := F32.BigN.BN.bnk_cmp 32 r.`2.
move: Hs; rewrite /F32.BigN.BN.bnk_withcarry -F32.BigN.BN.bn_modulusE.
by case: (r.`1); rewrite ?b2i1 ?b2i0 => Hs; smt().
qed.

(* the context of p in SK, as the simplifier writes it *)
lemma sk_ctxp0 (k: W64.t Array178.t): Array65.init (fun i => k.[i]) = sk_ctxp k.
proof. by rewrite /sk_ctxp. qed.

lemma sk_ctxp_eta (k: W64.t Array178.t): Array65.init ("_.[_]" k) = sk_ctxp k.
proof. by rewrite /sk_ctxp. qed.

(* the modulus q, read from its context in SK (the first words) *)
lemma sk_q (k: W64.t Array178.t):
  Array16.init (fun i => k.[65 + i]) = F16.FPC.ctxP (sk_ctxq k).
proof.
apply Array16.tP => i Hi.
by rewrite /F16.FPC.ctxP /sk_ctxq Array16.initiE // F16.BigN.BN.A.initiE //= Array65.initiE /#.
qed.

hoare RSASP1_h P Q DP DQ QI _c:
 M.h__RSA____RSASP1_crt
 : s = _c /\ wf_sk P Q DP DQ QI sk /\ QI < P /\ QI * Q %% P = 1 /\ bn32 _c < P * Q
   ==> bn32 res %% P = (bn32 _c %% P) ^ DP %% P
    /\ bn32 res %% Q = (bn32 _c %% Q) ^ DQ %% Q
    /\ bn32 res < P * Q.
proof.
proc.
ecall (addU32_h s tmp); wp.
ecall (set016_w_h); wp.
ecall (muln16_h x y); wp.
ecall (mulmU16_h P x y); wp.
ecall (submU16_h P x y); wp.
ecall (toM16_h P y); wp.
ecall (mov16_h x); wp.
ecall (fromM16_h Q x); wp.
ecall (crt_exp_h Q s y ctx); wp.
ecall (crt_exp_h P s y ctx); wp.
skip => &hr [-> [[HcP [HcQ [Hdp [Hdq Hqi]]]] [HQI [Hinv Hc]]]] /=.
rewrite sk_q -/(sk_ctxq sk{hr}) -/(sk_dp sk{hr}) -/(sk_dq sk{hr}) -/(sk_qinv sk{hr}).
rewrite !sk_ctxp0 !sk_ctxp_eta !bn2_16_bn32'.
move: HcP HcQ Hdp Hdq Hqi => /= HcP HcQ Hdp Hdq Hqi.
rewrite Hdp Hdq Hqi.
have [[Hp1 [Hpodd [HPp HMPp]]] [_ [_ HUp]]] := HcP.
have [[Hq1 [Hqodd [HPq HMPq]]] [_ [_ HUq]]] := HcQ.
have Hpm: F16.FPC.ctx_mod P (sk_ctxp sk{hr}) by case: HcP.
have Hqm: F16.FPC.ctx_mod Q (sk_ctxq sk{hr}) by case: HcQ.
have [_ HpR] := F16.FPC.ctx_mod_bnd _ _ Hpm.
have [_ HqR] := F16.FPC.ctx_mod_bnd _ _ Hqm.
have Hc0 := F32.BigN.BN.bnk_cmp 32 _c.
have Hcp: bn32 _c < P * R16.
- have: P * Q <= P * R16 by apply StdOrder.IntOrder.ler_wpmul2l; smt().
  smt().
have Hcq: bn32 _c < Q * R16.
- have: Q * P <= Q * R16 by apply StdOrder.IntOrder.ler_wpmul2l; smt().
  smt().
have HmontP: F16.mont_ctx P (sk_ctxp sk{hr}) by rewrite /F16.mont_ctx HUp.
have HmontQ: F16.mont_ctx Q (sk_ctxq sk{hr}) by rewrite /F16.mont_ctx HUq.
split; first by split.
move=> _ mp Hmp; split; first by split.
move=> _ mq Hmq.
have Hmqb: bn16 mq < Q by rewrite Hmq; smt(ltz_pmod).
split; first by do !split.
move=> _ mq1 Hmq1 y1 Ey1.
(* s_2 = c^dQ mod q *)
have Emq1: bn16 mq1 = (bn32 _c %% Q) ^ DQ %% Q by rewrite Hmq1 Hmq red16_R.
have Hmq1b: 0 <= bn16 mq1 < Q by rewrite Emq1; smt(modz_ge0 ltz_pmod).
have Ey1': y1 = mq1.
- rewrite Ey1; apply Array16.tP => i Hi.
  by rewrite Array16.initiE //= Array32.initiE 1:/# /= Hi.
split; first done.
move=> _ y2 Hy2.
have Hmpb: bn16 mp < P by rewrite Hmp; smt(ltz_pmod).
have Hy2b: bn16 y2 < P by rewrite Hy2; smt(ltz_pmod).
split; first by do !split.
move=> _ x4 Hx4.
have Hx4b: bn16 x4 < P by rewrite Hx4; smt(ltz_pmod).
split; first by do !split.
move=> _ x5 Hx5 s6 Hs6 z7 Hz7 r8 Hr8.
(* h = (s_1 - s_2) * qInv mod p *)
have Eh: bn16 x5 = ((bn32 _c %% P) ^ DP - bn16 mq1) * QI %% P.
- by rewrite Hx5 Hx4 Hmp Hy2 Ey1' garner_plain.
(* h * q, as a number of 32 words *)
have Ehq: bn32 s6 = bn16 x5 * Q by rewrite -bn2_16_bn32' Hs6 HPq.
(* s_2 || 0 *)
have Ew: bn32 (Array32.init (fun i => if 16 <= i < 32 then z7.[i - 16]
               else (Array32.init (fun i0 => if 0 <= i0 < 16 then mq1.[i0]
                     else witness<:W64.t Array32.t>.[i0])).[i])) = bn16 mq1.
- apply bn32_low => i Hi.
  + by rewrite Array32.initiE 1:/# /= (_: !(16 <= i < 32)) 1:/# /= Array32.initiE 1:/# /= Hi.
  + by rewrite Array32.initiE 1:/# /= Hi /= Hz7 /#.
have [Cp [Cq Cb]] := crt_comb P Q ((bn32 _c %% P) ^ DP) (bn16 mq1) QI Hp1 Hq1 Hmq1b Hinv.
have HR32: R32 = R16 * R16.
- by rewrite F32.BigN.BN.bn_modulusE F16.BigN.BN.bn_modulusE -exprD_nneg.
have Em: bn32 r8.`2 = bn16 mq1 + ((bn32 _c %% P) ^ DP - bn16 mq1) * QI %% P * Q.
- apply (withcarry_small r8); first by rewrite Hr8 Ehq Ew Eh; ring.
  have: P * Q < R16 * R16 by apply StdOrder.IntOrder.ltr_pmul; smt().
  smt().
rewrite Em Cp Cq.
split; first done.
split; first exact Emq1.
by case: Cb.
qed.

(* rsa_dec(m, c, SK): m = c^d mod n, by the CRT *)
hoare rsa_dec_h P Q DP DQ QI _c:
 M.rsa_dec
 : c = _c /\ wf_sk P Q DP DQ QI sk /\ QI < P /\ QI * Q %% P = 1 /\ bn32 _c < P * Q
   ==> bn32 res %% P = (bn32 _c %% P) ^ DP %% P
    /\ bn32 res %% Q = (bn32 _c %% Q) ^ DQ %% Q
    /\ bn32 res < P * Q.
proof.
proc.
ecall (RSASP1_h P Q DP DQ QI m).
ecall (mov32_h c).
by skip => &hr [-> H] /= m1 ->.
qed.

(* -------------------------------------------------------------------- *)
(* the example key pair                                                  *)

(* with the expanded keys of rsa_init: c = m^e mod n, and RSASP1 by the
   CRT for c < n (the key meets the hypotheses of rsa_dec_h) *)
hoare rsa_enc_test_h _m:
 M.rsa_enc : m = _m /\ wf_pk n_val e_val pk
   ==> bn32 res = (bn32 _m %% n_val) ^ e_val %% n_val.
proof. exact (rsa_enc_h n_val e_val _m). qed.

hoare rsa_dec_test_h _c:
 M.rsa_dec
 : c = _c /\ wf_sk p_val q_val dP_val dQ_val qInv_val sk /\ bn32 _c < n_val
   ==> bn32 res %% p_val = (bn32 _c %% p_val) ^ dP_val %% p_val
    /\ bn32 res %% q_val = (bn32 _c %% q_val) ^ dQ_val %% q_val
    /\ bn32 res < n_val.
proof.
conseq (rsa_dec_h p_val q_val dP_val dQ_val qInv_val _c).
- by move=> &hr [-> [Hk Hc]]; rewrite Hk qInv_bnd qInv_inv -n_pq Hc.
- by move=> &hr r; rewrite n_pq.
qed.
