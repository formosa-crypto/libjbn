(* Lemmas of the safety proofs of libjbn, besides ByteArrayInit (the hint
   database `safety`): memory regions, addresses of words, and the
   initialisation witnesses of byte arrays under word writes (ByteArrayLib,
   cloned once per byte-array theory of a proof). *)
require import AllCore IntDiv List.
from Jasmin require import JModel_x86 JByte_array JMemory Jcheck.
require import ByteArrayInit.

(* a sub-range of a valid memory region is valid *)
lemma is_valid_sub md mv p l p' l' :
  is_valid md mv p l => p <= p' => p' + l' <= p + l => is_valid md mv p' l'.
proof. by rewrite /is_valid => /> h *; split; [move=> j *; apply h | ]; smt(). qed.

(* the address of the i-th word of a region of n words that does not wrap *)
lemma to_uint_addr (ap : W64.t) i n :
  0 <= i < n => W64.to_uint ap + 8 * n < W64.modulus =>
  W64.to_uint (ap + W64.of_int (8 * i)) = W64.to_uint ap + 8 * i.
proof.
move=> *; rewrite W64.to_uintD_small W64.of_uintK modz_small //;
  smt(W64.to_uint_cmp pow2_64).
qed.

(* the indices of the 3-word accumulators of the product-scanning
   multiplications (x[k % 3]) *)
lemma mod3_bnd k : 0 <= k %% 3 < 3.
proof. smt(). qed.

(* signed run-time indices (the exponent scanning of bn_exp): comparison with
   0, decrement, and the unsigned value of a non-negative index (as in
   proof/Bn_exp.eca) *)
lemma sle0E (i : W64.t) : (W64.zero \sle i) = (0 <= W64.to_sint i).
proof. by rewrite W64.sleE (W64.to_sintK_small 0). qed.

lemma sle0E_of_int (i : W64.t) : (W64.of_int 0 \sle i) = (0 <= W64.to_sint i).
proof. by rewrite W64.sleE (W64.to_sintK_small 0). qed.

lemma to_sint_small (k : W64.t) : W64.to_uint k < 2^63 => W64.to_sint k = W64.to_uint k.
proof. by move=> H; rewrite W64.to_sintE /W64.smod /=; move: H => /= H; smt(). qed.

lemma to_sint_dec (i : W64.t) : 0 <= W64.to_sint i =>
  W64.to_sint (i - W64.one) = W64.to_sint i - 1.
proof.
move=> H; have Hc := W64.to_sint_cmp i; move: Hc => /= Hc.
rewrite W64.to_sintB_small (to_sint_small W64.one) //=; smt().
qed.

lemma one_neq_zero64 : W64.one <> W64.zero.
proof. by rewrite W64.to_uint_eq /=. qed.

lemma to_uint_sint (i : W64.t) : 0 <= W64.to_sint i => W64.to_uint i = W64.to_sint i.
proof.
rewrite W64.to_sintE /W64.smod /=.
have /= := W64.to_uint_cmp i.
smt().
qed.

lemma to_sint_of_int k : 0 <= k < 9223372036854775808 => W64.to_sint (W64.of_int k) = k.
proof.
move=> hk; have hu : W64.to_uint (W64.of_int k) = k.
- by rewrite W64.of_uintK modz_small //; smt(pow2_64).
by rewrite to_sint_small hu //; smt().
qed.

(* unsigned run-time counters (the row loops of bn_mul_loop, bn_mulx_loop):
   comparison with a bound, increment, offset *)
lemma ult_of_intE (k : W64.t) n :
  0 <= n < W64.modulus => (k \ult W64.of_int n) = (W64.to_uint k < n).
proof. by move=> hn; rewrite W64.ultE W64.of_uintK modz_small //; smt(). qed.

lemma to_uint_inc (k : W64.t) n :
  W64.to_uint k < n => n < W64.modulus => W64.to_uint (k + W64.one) = W64.to_uint k + 1.
proof.
move=> h1 h2; have h0 := W64.to_uint_cmp k.
by rewrite W64.to_uintD_small /=; move: h0 h1 h2; smt().
qed.

lemma to_uint_add_of_int (k : W64.t) i :
  0 <= i => W64.to_uint k + i < W64.modulus =>
  W64.to_uint (k + W64.of_int i) = W64.to_uint k + i.
proof.
move=> h1 h2; have h0 := W64.to_uint_cmp k.
by rewrite W64.to_uintD_small W64.of_uintK modz_small //; move: h0 h1 h2; smt().
qed.

abstract theory ByteArrayLib.

clone import ByteArray as A.
clone include ByteArrayInit with theory A <- A.

abbrev m1_64 = W64.of_int 18446744073709551615.

(* writing the next word extends an initialised prefix *)
lemma is_init_ext64 (t : A.t) i :
  0 <= i => A.is_init t 0 (8 * i) =>
  A.is_init (A.set64d t (i * 8) m1_64) 0 (8 * (i + 1)).
proof.
move=> h0 h; rewrite is_init_set64d_in 1,2:/#; split.
- by rewrite (_: i * 8 = 8 * i) 1:/#.
by rewrite is_init_le0 /#.
qed.

(* writing the word just after an initialised range extends it (the rows of
   the squarings, whose ranges start at word 1) *)
lemma is_init_ext64_at (t : A.t) o l :
  A.is_init t o l => A.is_init (A.set64d t (o + l) m1_64) o (l + 8).
proof.
move=> h j hj0 hj1; rewrite A.is_init_cell_set64d.
by case: (j < o + l) => c; [right; apply h | left]; smt().
qed.

(* writing the word just before an initialised range extends it (loops
   that count down: bn_rnd's __bnd_mask) *)
lemma is_init_ext64_below (t : A.t) o l :
  A.is_init t o l => A.is_init (A.set64d t (o - 8) m1_64) (o - 8) (l + 8).
proof.
move=> h j hj0 hj1; rewrite A.is_init_cell_set64d.
by case: (j < o) => c; [left | right; apply h]; smt().
qed.

(* the word at index i of an initialised prefix *)
lemma is_init_word (t : A.t) i l :
  0 <= i => 8 * (i + 1) <= l => A.is_init t 0 l => A.is_init t (i * 8) 8.
proof. by move=> h0 h1 h; apply (is_init_sub _ 0 l) => /#. qed.

(* two adjacent initialised ranges *)
lemma is_init_cat (t : A.t) k l1 l2 :
  0 <= l1 => A.is_init t k l1 => A.is_init t (k + l1) l2 => A.is_init t k (l1 + l2).
proof. by move=> h0 h1 h2 j *; case: (j < k + l1) => c; [apply h1 | apply h2]; smt(). qed.

(* a word write keeps what was initialised *)
lemma is_init_mono64 (t : A.t) i k l :
  A.is_init t k l => A.is_init (A.set64d t i m1_64) k l.
proof. by move=> h j *; rewrite A.is_init_cell_set64d; right; apply h. qed.

end ByteArrayLib.

(* a sub-array write of an initialised small array (a part of a context, a
   half of a double-size number) *)
abstract theory SubByteArrayLib.

clone import SubByteArray as SB.

(* it extends an initialised prefix that ends where it starts *)
lemma is_init_ext_sub (t : Abig.t) o :
  0 <= o => Abig.is_init t 0 o =>
  Abig.is_init (set_sub t o (Asmall.init_arr (W8.of_int 255))) 0 (o + Asmall.size).
proof.
move=> h0 h j hj0 hj1; rewrite is_init_cell_set.
case: (o <= j < Asmall.size + o /\ 0 <= j < Abig.size) => /= c.
- by apply (Asmall.init_arrP witness).
case: (j < o) => hjo; first by apply h.
by rewrite /Abig.is_init_cell; smt().
qed.

(* it keeps what was initialised *)
lemma is_init_mono_sub (t : Abig.t) o k l :
  Abig.is_init t k l => Abig.is_init (set_sub t o (Asmall.init_arr (W8.of_int 255))) k l.
proof.
move=> h j hj0 hj1; rewrite is_init_cell_set.
by case: (o <= j < Asmall.size + o /\ 0 <= j < Abig.size) => /= c;
  [apply (Asmall.init_arrP witness) | apply h].
qed.

end SubByteArrayLib.
