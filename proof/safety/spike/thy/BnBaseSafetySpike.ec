(* Spike: the safety lemmas of bn_base's _load_, _mov_, _addU_ over the
   abstract theory BnBaseSafety (BnBaseSafetyThy.ec). *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety JByte_array JMemory.
require import ByteArrayInit BnBaseSafetyThy.

(* a sub-range of a valid memory region is valid *)
lemma is_valid_sub md mv p l p' l' :
  is_valid md mv p l => p <= p' => p' + l' <= p + l => is_valid md mv p' l'.
proof. by rewrite /is_valid => /> h *; split; [move=> j *; apply h | ]; smt(). qed.

(* the address of the i-th word of a valid region of n words, n * 8 < 2^64 *)
lemma to_uint_addr (ap : W64.t) i n :
  0 <= i < n => W64.to_uint ap + 8 * n < W64.modulus =>
  W64.to_uint (ap + W64.of_int (8 * i)) = W64.to_uint ap + 8 * i.
proof.
move=> *; rewrite W64.to_uintD_small W64.of_uintK modz_small //;
  smt(W64.to_uint_cmp pow2_64).
qed.

abstract theory BnBaseSafetyProofs.

clone include BnBaseSafety.
clone ByteArrayInit as BI with theory A <- A.

(* writing the next word extends an initialised prefix *)
lemma is_init_ext64 (t : A.t) i :
  0 <= i => 8 * (i + 1) <= 8 * nlimbs => A.is_init t 0 (8 * i) =>
  A.is_init (A.set64d t (i * 8) (W64.of_int 18446744073709551615)) 0 (8 * (i + 1)).
proof.
move=> h0 h1 h; rewrite BI.is_init_set64d_in 1,2:/#; split.
- by rewrite (_: i * 8 = 8 * i) 1:/#.
by rewrite BI.is_init_le0 /#.
qed.

lemma __load_proof _a _b_a _ap : __load_spec _a _b_a _ap.
proof.
hint +safety.
rewrite /__load_spec; proc.
while (valid trace_h__BN____load /\ 0 <= i <= nlimbs /\ A.is_init b_a 0 (8 * i)
       /\ ap = _ap /\ is_valid ptr_modulus Glob.mem_v (W64.to_uint _ap) (8 * nlimbs)).
- auto => /> &hr hv hi0 _ hb hval h0 hlt hin.
  rewrite (to_uint_addr _ap i{hr} nlimbs) 1,2:/#.
  have -> /= := is_init_ext64 b_a{hr} i{hr} _ _ hb; 1,2: smt().
  split; last smt().
  split; last smt().
  by split; [move=> i0 *; apply hval | ]; smt().
auto => /> &hr *; split; first smt(gt0_nlimbs).
by move=> b i tr *; smt().
qed.

lemma _load_proof _a _b_a _ap : _load_spec _a _b_a _ap.
proof.
hint +safety.
rewrite /_load_spec; proc.
wp; ecall (__load_proof param b_param param_0).
by auto.
qed.

lemma _load__proof _a _b_a _ap : _load__spec _a _b_a _ap.
proof.
hint +safety.
rewrite /_load__spec; proc.
wp; ecall (_load_proof param b_param param_0).
by auto.
qed.

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

end BnBaseSafetyProofs.
