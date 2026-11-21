(* From formosa-libjade, proofs/safety/common/ByteArrayInit.ec (commit 912d6e24,
   licence CC0-1.0 OR Apache-2.0), unchanged below this comment. *)
(* Computing with the initialisation witnesses of the safety model.

   The safety extraction pairs every byte array with a witness array whose
   cells hold 255 once initialised, and asserts `is_init w k l` on reads.
   After unrolling the constant-bound loops of a procedure, the witnesses
   are closed terms built from `init_arr`, word writes and `set_sub`, so the
   assertions reduce by simplification alone: the hints below rewrite
   `is_init` on such terms into `is_init` facts on the symbolic inputs.
   They live in the simplify database `safety`, which every safety proof
   activates first (`hint +safety`). *)
require import AllCore IntDiv List.
from Jasmin require import JModel_x86 JByte_array Jcheck.

lemma all_cat_hint ['a] (p : 'a -> bool) s1 s2 :
  all p (s1 ++ s2) = (all p s1 /\ all p s2).
proof. by rewrite all_cat. qed.

lemma valid_cat (t1 t2 : trace) : valid (t1 ++ t2) = (valid t1 /\ valid t2).
proof. by rewrite /valid all_cat. qed.

lemma valid_nil : valid<:kind> [] = true.
proof. by rewrite /valid. qed.

lemma valid_cons k b (t : trace) : valid ((k, b) :: t) = (b /\ valid t).
proof. by rewrite /valid. qed.

hint simplify in safety : all_cat_hint, valid_cat, valid_nil, valid_cons.

abstract theory ByteArrayInit.

clone import ByteArray as A.

lemma is_init_le0 t k l : l <= 0 => is_init t k l = true.
proof. by move=> le0_l; rewrite eqT /is_init /#. qed.

lemma is_init_cell_init_arr k :
  is_init_cell (init_arr (W8.of_int 255)) k = true.
proof. by rewrite eqT; apply (init_arrP witness). qed.

lemma is_init_init_arr k l : is_init (init_arr (W8.of_int 255)) k l = true.
proof. by rewrite eqT /is_init => i _ _; apply (init_arrP witness). qed.

hint simplify in safety : is_init_le0, is_init_cell_init_arr, is_init_init_arr.

(* the conditional initialisation of the contracts, `is_arr_init(a, k,
   (c ? l : 0))`, as the disjunction the proofs state (not a simplify
   hint: its left-hand side is not first order) *)
lemma is_init_if t k l (c : bool) :
  is_init t k (if c then l else 0) = (!c \/ is_init t k l).
proof.
case: c => /=.
- done.
by rewrite is_init_le0.
qed.

(* a fully initialised witness is the constant array *)
lemma is_init_full t l : l = A.size =>
  is_init t 0 l = (t = init_arr (W8.of_int 255)).
proof.
move=> ->; apply eq_iff; split=> [h|->]; last by rewrite is_init_init_arr.
apply ext_eq => i hi; rewrite initE hi /=.
by have := h i _ _; 1,2:smt(); rewrite /is_init_cell hi.
qed.

lemma is_init_sub t k l k' l' :
  is_init t k l => k <= k' => k' + l' <= k + l => is_init t k' l'.
proof. by rewrite /is_init => h ?? i ??; apply h => /#. qed.

(* cell-wise form *)
lemma is_initE t k l : is_init t k l <=> all (is_init_cell t) (iota_ k l).
proof. by rewrite /is_init allP; smt(mem_iota). qed.

(* `is_init (set t i m_one) k l` for a word write of r initialised bytes at
   i, by position of [i, i + r) relative to [k, k + l) *)
abstract theory WordInit.

type B.
op r : int.
op m_one : B.
op set : t -> int -> B -> t.

axiom gt0_r : 0 < r.
axiom is_init_cell_w t i j :
  is_init_cell (set t i m_one) j = (i <= j < i + r \/ is_init_cell t j).

lemma is_init_set_in t i k l :
  k <= i => i + r <= k + l =>
  is_init (set t i m_one) k l = (is_init t k (i - k) /\ is_init t (i + r) (k + l - (i + r))).
proof.
move=> *; have ? := gt0_r; rewrite /is_init; apply eq_iff; split.
+ move=> h; split.
  + by move=> j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_w /#.
  by move=> j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_w /#.
by move=> h j ??; rewrite is_init_cell_w /#.
qed.

lemma is_init_set_out t i k l :
  k + l <= i \/ i + r <= k => is_init (set t i m_one) k l = is_init t k l.
proof.
move=> *; have ? := gt0_r; rewrite /is_init; apply eq_iff; split.
+ by move=> h j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_w /#.
by move=> h j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_w /#.
qed.

lemma is_init_set_sub t i k l :
  i <= k => k + l <= i + r => is_init (set t i m_one) k l = true.
proof. by move=> *; rewrite eqT /is_init => j ??; rewrite is_init_cell_w /#. qed.

lemma is_init_set_left t i k l :
  k < i => i < k + l => k + l < i + r => is_init (set t i m_one) k l = is_init t k (i - k).
proof.
move=> *; have ? := gt0_r; rewrite /is_init; apply eq_iff; split.
+ by move=> h j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_w /#.
by move=> h j ??; rewrite is_init_cell_w /#.
qed.

lemma is_init_set_right t i k l :
  i < k => k < i + r => i + r < k + l =>
  is_init (set t i m_one) k l = is_init t (i + r) (k + l - (i + r)).
proof.
move=> *; have ? := gt0_r; rewrite /is_init; apply eq_iff; split.
+ by move=> h j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_w /#.
by move=> h j ??; rewrite is_init_cell_w /#.
qed.

hint simplify in safety : is_init_set_in, is_init_set_out, is_init_set_sub,
              is_init_set_left, is_init_set_right.

end WordInit.

lemma gt0_r1 : 0 < 1 by done.

lemma is_init_cell_set8 t i j :
  is_init_cell t.[i <- W8.of_int 255] j = (i <= j < i + 1 \/ is_init_cell t j).
proof. by rewrite /is_init_cell get_set_if /#. qed.

hint simplify in safety : is_init_cell_set8.

clone include WordInit with
  type B <- W8.t, op r <- 1, op m_one <- W8.of_int 255, op set <- A."_.[_<-_]",
  axiom gt0_r <- gt0_r1, axiom is_init_cell_w <- is_init_cell_set8
  rename [lemma] "_set" as "_set8".

clone include WordInit with
  type B <- W16.t, op r <- 2, op m_one <- W16.of_int 65535, op set <- set16d,
  axiom gt0_r <- W2u8.gt0_r, axiom is_init_cell_w <- is_init_cell_set16d
  rename [lemma] "_set" as "_set16d".

clone include WordInit with
  type B <- W32.t, op r <- 4, op m_one <- W32.of_int 4294967295, op set <- set32d,
  axiom gt0_r <- W4u8.gt0_r, axiom is_init_cell_w <- is_init_cell_set32d
  rename [lemma] "_set" as "_set32d".

clone include WordInit with
  type B <- W64.t, op r <- 8, op m_one <- W64.of_int 18446744073709551615, op set <- set64d,
  axiom gt0_r <- W8u8.gt0_r, axiom is_init_cell_w <- is_init_cell_set64d
  rename [lemma] "_set" as "_set64d".

clone include WordInit with
  type B <- W128.t, op r <- 16,
  op m_one <- W128.of_int 340282366920938463463374607431768211455, op set <- set128d,
  axiom gt0_r <- W16u8.gt0_r, axiom is_init_cell_w <- is_init_cell_set128d
  rename [lemma] "_set" as "_set128d".

clone include WordInit with
  type B <- W256.t, op r <- 32,
  op m_one <- W256.of_int 115792089237316195423570985008687907853269984665640564039457584007913129639935,
  op set <- set256d,
  axiom gt0_r <- W32u8.gt0_r, axiom is_init_cell_w <- is_init_cell_set256d
  rename [lemma] "_set" as "_set256d".

end ByteArrayInit.

abstract theory SubByteArrayInit.

clone import SubByteArray as SB.
import Asmall Abig.

(* `is_init (set_sub t i s) k l` by position of the written chunk
   [i, i + size) relative to the queried range [k, k + l): the chunk is
   inside the range, outside, covers it, or overlaps one of its ends. *)

lemma is_init_set_sub_in t i s k l :
  0 <= Asmall.size => 0 <= Abig.size =>
  0 <= i => i + Asmall.size <= Abig.size => k <= i => i + Asmall.size <= k + l =>
  Abig.is_init (set_sub t i s) k l =
    (Asmall.is_init s 0 Asmall.size /\
     Abig.is_init t k (i - k) /\
     Abig.is_init t (i + Asmall.size) (k + l - (i + Asmall.size))).
proof.
move=> *.
rewrite /is_init; apply eq_iff; split.
+ move=> h; do! split.
  + by move=> j ??; have := h (i + j) _ _; 1,2:smt(); rewrite is_init_cell_set /#.
  + by move=> j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_set /#.
  by move=> j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_set /#.
by move=> h j ??; rewrite is_init_cell_set /#.
qed.

lemma is_init_set_sub_out t i s k l :
  0 <= Asmall.size => 0 <= Abig.size =>
  k + l <= i \/ i + Asmall.size <= k =>
  Abig.is_init (set_sub t i s) k l = Abig.is_init t k l.
proof.
move=> *.
rewrite /is_init; apply eq_iff; split.
+ by move=> h j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_set /#.
by move=> h j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_set /#.
qed.

lemma is_init_set_sub_sub t i s k l :
  0 <= Asmall.size => 0 <= Abig.size =>
  0 <= i => i + Asmall.size <= Abig.size => i <= k => k + l <= i + Asmall.size =>
  Abig.is_init (set_sub t i s) k l = Asmall.is_init s (k - i) l.
proof.
move=> *.
rewrite /is_init; apply eq_iff; split.
+ by move=> h j ??; have := h (i + j) _ _; 1,2:smt(); rewrite is_init_cell_set /#.
by move=> h j ??; have := h (j - i) _ _; 1,2:smt(); rewrite is_init_cell_set /#.
qed.

lemma is_init_set_sub_left t i s k l :
  0 <= Asmall.size => 0 <= Abig.size =>
  0 <= i => i + Asmall.size <= Abig.size =>
  k < i => i < k + l => k + l < i + Asmall.size =>
  Abig.is_init (set_sub t i s) k l =
    (Abig.is_init t k (i - k) /\ Asmall.is_init s 0 (k + l - i)).
proof.
move=> *.
rewrite /is_init; apply eq_iff; split.
+ move=> h; split.
  + by move=> j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_set /#.
  by move=> j ??; have := h (i + j) _ _; 1,2:smt(); rewrite is_init_cell_set /#.
by move=> h j ??; rewrite is_init_cell_set /#.
qed.

lemma is_init_set_sub_right t i s k l :
  0 <= Asmall.size => 0 <= Abig.size =>
  0 <= i => i + Asmall.size <= Abig.size =>
  i < k => k < i + Asmall.size => i + Asmall.size < k + l =>
  Abig.is_init (set_sub t i s) k l =
    (Asmall.is_init s (k - i) (i + Asmall.size - k) /\
     Abig.is_init t (i + Asmall.size) (k + l - (i + Asmall.size))).
proof.
move=> *.
rewrite /is_init; apply eq_iff; split.
+ move=> h; split.
  + by move=> j ??; have := h (i + j) _ _; 1,2:smt(); rewrite is_init_cell_set /#.
  by move=> j ??; have := h j _ _; 1,2:smt(); rewrite is_init_cell_set /#.
by move=> h j ??; rewrite is_init_cell_set /#.
qed.

hint simplify in safety : is_init_set_sub_in, is_init_set_sub_out, is_init_set_sub_sub,
              is_init_set_sub_left, is_init_set_sub_right.

(* a range of a sub-array is a range of the array *)
lemma is_init_get_sub t i k l :
  0 <= k => k + l <= Asmall.size => 0 <= i + k => i + k + l <= Abig.size =>
  Asmall.is_init (get_sub t i) k l = Abig.is_init t (i + k) l.
proof.
move=> *; rewrite /is_init; apply eq_iff; split=> h j ??.
+ by have := h (j - i) _ _; 1,2:smt(); rewrite is_init_cell_get 1,2:/# /#.
by rewrite is_init_cell_get 1,2:/#; apply h => /#.
qed.

hint simplify in safety : is_init_get_sub.

(* sub-arrays of the constant array *)
lemma get_sub_init_arr b i :
  0 <= i => i + Asmall.size <= Abig.size =>
  get_sub (Abig.init_arr b) i = Asmall.init_arr b.
proof.
move=> ??; apply Asmall.ext_eq => k hk.
by rewrite get8_get_sub hk /= Abig.initE Asmall.initE hk /#.
qed.

lemma set_sub_init_arr b i :
  set_sub (Abig.init_arr b) i (Asmall.init_arr b) = Abig.init_arr b.
proof.
apply Abig.ext_eq => k hk.
by rewrite get8_set_sub Abig.initE hk /= Asmall.initE /#.
qed.

hint simplify in safety : get_sub_init_arr, set_sub_init_arr.

end SubByteArrayInit.
