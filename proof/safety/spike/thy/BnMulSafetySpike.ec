(* Spike: the safety lemmas of bn_mul's __mont_redM and its callees over
   the abstract theory BnMulSafety (BnMulSafetyThy.ec). *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array.
require import BArray24 ByteArrayInit BnMulSafetyThy.

abstract theory BnMulSafetyProofs.

clone include BnMulSafety.
clone ByteArrayInit as BI with theory A <- A.
clone ByteArrayInit as BI2 with theory A <- A2.
clone ByteArrayInit as BI24 with theory A <- BArray24.
clone SubByteArrayInit as SBI with theory SB <- SA.

abbrev m1 = W64.of_int 18446744073709551615.

(* writing the next word extends an initialised prefix *)
lemma is_init_ext64 (t : A.t) i :
  0 <= i => 8 * (i + 1) <= 8 * nlimbs => A.is_init t 0 (8 * i) =>
  A.is_init (A.set64d t (i * 8) m1) 0 (8 * (i + 1)).
proof.
move=> h0 h1 h; rewrite BI.is_init_set64d_in 1,2:/#; split.
- by rewrite (_: i * 8 = 8 * i) 1:/#.
by rewrite BI.is_init_le0 /#.
qed.

(* a word write keeps what was initialised *)
lemma is_init_mono64 (t : A.t) i k l :
  A.is_init t k l => A.is_init (A.set64d t i m1) k l.
proof. by move=> h j *; rewrite A.is_init_cell_set64d; right; apply h. qed.

lemma is_init_mono64_24 (t : BArray24.t) i k l :
  BArray24.is_init t k l => BArray24.is_init (BArray24.set64d t i m1) k l.
proof. by move=> h j *; rewrite BArray24.is_init_cell_set64d; right; apply h. qed.

lemma mod3_bnd k : 0 <= k %% 3 < 3.
proof. smt(). qed.

(* ------------------------------------------------------------------ *)
(* bn_util                                                            *)

lemma __addacc3_proof _a _b_a _b1 _b0 _k : __addacc3_spec _a _b_a _b1 _b0 _k.
proof.
hint +safety.
rewrite /__addacc3_spec; proc.
by auto => />; smt(mod3_bnd).
qed.

(* ------------------------------------------------------------------ *)
(* bn_base                                                            *)

lemma __mov_proof _r _b_r _a _b_a : __mov_spec _r _b_r _a _b_a.
proof.
hint +safety.
rewrite /__mov_spec; proc.
while (valid trace_h__BN____mov /\ 0 <= i <= nlimbs /\ A.is_init b_r 0 (8 * i)).
- auto => /> &hr hv hi0 _ hb hin.
  have -> /= := is_init_ext64 b_r{hr} i{hr} _ _ hb; 1,2: smt().
  smt().
auto => /> &hr *; split; first smt(gt0_nlimbs).
by move=> b i r tr *; smt().
qed.

lemma _mov_proof _r _b_r _a _b_a : _mov_spec _r _b_r _a _b_a.
proof.
hint +safety.
rewrite /_mov_spec; proc.
wp; ecall (__mov_proof param b_param param_0 (A.init_arr (W8.of_int 255))).
by auto.
qed.

lemma _mov__proof _r _b_r _a _b_a : _mov__spec _r _b_r _a _b_a.
proof.
hint +safety.
rewrite /_mov__spec; proc.
wp; ecall (_mov_proof param b_param param_0 (A.init_arr (W8.of_int 255))).
by auto.
qed.

lemma __cmov_proof _a _b_a _cond _b _b_b : __cmov_spec _a _b_a _cond _b _b_b.
proof.
hint +safety.
rewrite /__cmov_spec; proc.
wp; while (valid trace_h__BN____cmov /\ 0 <= i <= nlimbs).
- by auto => /> &hr *; smt().
by auto => /> &hr *; smt(gt0_nlimbs).
qed.

lemma _cmov_proof _a _b_a _cond _b _b_b : _cmov_spec _a _b_a _cond _b _b_b.
proof.
hint +safety.
rewrite /_cmov_spec; proc.
wp; ecall (__cmov_proof param (A.init_arr (W8.of_int 255)) param_0 param_1
             (A.init_arr (W8.of_int 255))).
by auto.
qed.

lemma _cmov__proof _a _b_a _cond _b _b_b : _cmov__spec _a _b_a _cond _b _b_b.
proof.
hint +safety.
rewrite /_cmov__spec; proc.
wp; ecall (_cmov_proof param (A.init_arr (W8.of_int 255)) param_0 param_1
             (A.init_arr (W8.of_int 255))).
by auto.
qed.

lemma __addc1U_proof _a _b_a _b _b_b _cf : __addc1U_spec _a _b_a _b _b_b _cf.
proof.
hint +safety.
rewrite /__addc1U_spec; proc.
wp; while (valid trace_h__BN____addc1U /\ 1 <= i <= nlimbs).
- by auto => /> &hr *; smt().
by auto => /> &hr *; smt(gt0_nlimbs).
qed.

lemma _addc1U_proof _a _b_a _b _b_b _cf : _addc1U_spec _a _b_a _b _b_b _cf.
proof.
hint +safety.
rewrite /_addc1U_spec; proc.
wp; ecall (__addc1U_proof param (A.init_arr (W8.of_int 255)) param_0
             (A.init_arr (W8.of_int 255)) param_1).
by auto.
qed.

lemma _addc1U__proof _a _b_a _b _b_b _cf : _addc1U__spec _a _b_a _b _b_b _cf.
proof.
hint +safety.
rewrite /_addc1U__spec; proc.
wp; ecall (_addc1U_proof param (A.init_arr (W8.of_int 255)) param_0
             (A.init_arr (W8.of_int 255)) param_1).
by auto.
qed.

lemma _addU__proof _a _b_a _b _b_b : _addU__spec _a _b_a _b _b_b.
proof.
hint +safety.
rewrite /_addU__spec; proc.
wp; ecall (_addc1U__proof param (A.init_arr (W8.of_int 255)) param_0
             (A.init_arr (W8.of_int 255)) param_1).
by auto.
qed.

lemma _cminusP__proof _x _b_x _mP _b_mP _lastbit :
  _cminusP__spec _x _b_x _mP _b_mP _lastbit.
proof.
hint +safety.
rewrite /_cminusP__spec; proc.
wp; ecall (_cmov__proof param_3 (A.init_arr (W8.of_int 255)) param_4 param_5
             (A.init_arr (W8.of_int 255))).
wp; ecall (_addU__proof param_1 (A.init_arr (W8.of_int 255)) param_2
             (A.init_arr (W8.of_int 255))).
wp; ecall (_mov__proof param b_param param_0 (A.init_arr (W8.of_int 255))).
by auto.
qed.

(* ------------------------------------------------------------------ *)
(* bn_mul                                                             *)

(* the inner loop reads a only on [istart, iend): in __mont_redM, a is the
   output, written on a prefix *)
lemma __muln_innerloop_proof _x _b_x _k _istart _iend _a _b_a _b _b_b :
  __muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b.
proof.
hint +safety.
rewrite /__muln_innerloop_spec; proc.
wp; while (valid trace_h__MUL__UNR____muln_innerloop /\ inc = iend
           /\ istart <= i /\ (istart <= iend => i <= iend)
           /\ 0 <= istart /\ iend <= nlimbs /\ 0 <= k - (iend - 1) /\ k - istart < nlimbs
           /\ A.is_init b_a (8 * istart) (8 * (iend - istart))).
- wp; ecall (__addacc3_proof param (BArray24.init_arr (W8.of_int 255))
               param_0 param_1 param_2).
  auto => /> &hr hv hi hie h0 hn hk1 hk2 ha hin r hr hvr.
  have hsub: A.is_init b_a{hr} (i{hr} * 8) 8.
  - by apply (BI.is_init_sub _ _ _ _ _ ha); smt().
  smt().
by auto => /> &hr *; smt().
qed.

lemma __mont_redM_proof _r _b_r _a _b_a __P_mP _b__P_mP __U0 :
  __mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0.
proof.
hint +safety.
rewrite /__mont_redM_spec; proc.
wp; ecall (_cminusP__proof param_23 b_param_5 param_24 b_param_6 param_25).
wp.
while (valid trace_h__MUL__UNR____mont_redM /\ inc = 2 * nlimbs - 1
       /\ nlimbs <= k <= 2 * nlimbs - 1
       /\ A.is_init b_r 0 (8 * nlimbs) /\ BArray24.is_init b_x 0 24
       /\ A.is_init b_P 0 (8 * nlimbs) /\ A2.is_init b__P_mP 0 (16 * nlimbs)).
- wp; ecall (__addacc3_proof param_19 (BArray24.init_arr (W8.of_int 255))
               param_20 param_21 param_22).
  wp; ecall (__muln_innerloop_proof param_13 b_param_2 param_14 param_15 param_16
               param_17 b_param_3 param_18 b_param_4).
  auto => /> &hr hv hk0 hk1 hr hx hp hpm hin.
  have hsub: A.is_init b_r{hr} (8 * (k{hr} - nlimbs + 1))
                                (8 * (nlimbs - (k{hr} - nlimbs + 1))).
  - by apply (BI.is_init_sub _ _ _ _ _ hr); smt().
  split; first smt().
  move=> *; split; first smt(mod3_bnd).
  split; first smt().
  by apply is_init_mono64.
wp.
while (valid trace_h__MUL__UNR____mont_redM /\ 0 <= k <= nlimbs
       /\ A.is_init b_r 0 (8 * k) /\ BArray24.is_init b_x 0 24
       /\ A.is_init b_P 0 (8 * nlimbs) /\ A2.is_init b__P_mP 0 (16 * nlimbs)).
- wp; ecall (__addacc3_proof param_9 (BArray24.init_arr (W8.of_int 255))
               param_10 param_11 param_12).
  wp; ecall (__addacc3_proof param_5 (BArray24.init_arr (W8.of_int 255))
               param_6 param_7 param_8).
  wp; ecall (__muln_innerloop_proof param b_param param_0 param_1 param_2
               param_3 b_param_0 param_4 b_param_1).
  auto => /> &hr hv hk0 hk1 hr hx hp hpm hin.
  split; first smt().
  move=> *; split.
  - split; first smt(mod3_bnd).
    by apply (BI.is_init_sub _ _ _ _ _ hp); smt().
  split; first smt().
  by apply is_init_ext64 => /#.
auto => /> ha hpm.
have hP: A.is_init (SA.get_sub _b__P_mP 0) 0 (8 * nlimbs).
- rewrite SBI.is_init_get_sub; 1..4: smt(gt0_nlimbs).
  by apply (BI2.is_init_sub _ _ _ _ _ hpm); smt(gt0_nlimbs).
have hmP: A.is_init (SA.get_sub _b__P_mP (8 * nlimbs)) 0 (8 * nlimbs).
- rewrite SBI.is_init_get_sub; 1..4: smt(gt0_nlimbs).
  by apply (BI2.is_init_sub _ _ _ _ _ hpm); smt(gt0_nlimbs).
split; first smt(gt0_nlimbs).
move=> b_r0 b_x0 k0 tr0 hk hv0 hk0 hk1 hr0 hx0 _.
split; first smt(gt0_nlimbs).
move=> b_r1 b_x1 k1 tr1 hk' hv1 hk2 hk3 hr1 hx1.
split; first by split; [done | apply is_init_mono64].
move=> _ _ r0 _ _.
have hx2 := BI24.is_init_sub _ _ _ (2 * nlimbs %% 3 * 8) 8 hx1 _ _; 1,2: smt(mod3_bnd).
have hx3 := BI24.is_init_sub _ _ _ ((2 * nlimbs - 1) %% 3 * 8) 8 hx1 _ _; 1,2: smt(mod3_bnd).
smt(mod3_bnd gt0_nlimbs).
qed.

end BnMulSafetyProofs.
