require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

from Jasmin require import JWord JUtils JArray JWord_array.


(** TO BE MOVED ELSEWHERE... *)

lemma lex_lt x1 x2 m y1 y2:
 0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
 (y1*m + x1 < y2*m + x2) = (y1 < y2 \/ y1=y2 /\ x1 < x2)
by smt().
(*proof. by move=> /> *; rewrite (divzU (y1 * m + x1) m y1 x1) /#. qed.*)

lemma lex_le x1 x2 m y1 y2:
 0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
 (y1*m + x1 <= y2*m + x2) = (y1 < y2 \/ y1=y2 /\ x1 <= x2)
by smt().
(*proof. by move=> /> *; rewrite (divzU (y1 * m + x1) m y1 x1) /#. qed.*)

lemma lex_eq x1 x2 m y1 y2:
 0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
 (y1*m + x1 = y2*m + x2) = (y1 = y2 /\ x1 = x2)
by smt().

lemma modz_pow (a b d: int):
 0 <= b => a ^ b %% d = (a %% d) ^ b %% d.
proof.
elim/natind: b.
 by move => n *; rewrite (_:n=0) 1:/# !expr0.
move=> n Hn IH H.
rewrite !exprS 1..2://.
by rewrite eq_sym -modzMmr -IH 1:// modzMmr modzMml.
qed.

require import Distr DBool Dexcepted.

(* ? [Jasmin/eclib] JWord.ec ? *)
lemma W8_dword1E x: mu1 W8.dword x = inv (W8.modulus%r).
proof.
rewrite /W8.dword duniform1E W8.all_wordsP all_wordsE undup_id.
rewrite map_inj_in_uniq.
  move => a b; rewrite !mem_iota /= => Ha Hb E. 
  have ->: a = a %% W8.modulus by smt().
  have ->: b = b %% W8.modulus by smt().
  by rewrite -(W8.of_uintK a) -(W8.of_uintK b) E.
 by apply  iota_uniq.
by rewrite size_map size_iota /max /=.
qed.

lemma W64_dword1E x: mu1 W64.dword x = inv (W64.modulus%r).
proof.
rewrite /W64.dword duniform1E W64.all_wordsP all_wordsE undup_id.
rewrite map_inj_in_uniq.
  move => a b; rewrite !mem_iota /= => Ha Hb E. 
  have ->: a = a %% W64.modulus by smt().
  have ->: b = b %% W64.modulus by smt().
  by rewrite -(W64.of_uintK a) -(W64.of_uintK b) E.
 by apply  iota_uniq.
by rewrite size_map size_iota /max /=.
qed.

lemma W64_orw_eq0 w1 w2:
 W64.orw w1 w2 = W64.zero <=> w1=W64.zero /\ w2=W64.zero.
proof.
split.
 case: (w1=W64.zero) => [E|/negP E].
  by rewrite E or0w.
 move=> H /=; apply E.
 rewrite to_uint_eq /=.
 have:= W64.ule_orw w1 w2; rewrite H uleE to_uint0.
 move: (W64.to_uint_cmp w1); smt().
by move=> [-> ->]; rewrite or0w.
qed.

lemma W64_xorw_eq0 (w1 w2: W64.t):
 w1 +^ w2 = W64.zero <=> w1=w2.
proof.
split => H.
 move/W64.wordP: H => H.
 apply W64.wordP => i Hi.
 move: (H i Hi).
 by rewrite xorE /map2 initiE 1:/# /= /#.
by rewrite H xorwK.
qed.


(* ? DBool.ec (Biased theory) ? *)
import Biased.
lemma dbiased_supp p b:
 b \in dbiased p => if b then 0%r < p else p < 1%r.
proof. by move=> /supportP; case: (b) => Hb; rewrite dbiased1E /= /#. qed.

lemma dbiased_dcond_ll ['a] b (d: 'a distr) P:
 b \in dbiased (mu d P)
 => is_lossless d => is_lossless (if b then dcond d P else dcond d (predC P)).
proof.
move=> /dbiased_supp; case: (b).
 by move=> *; rewrite dcond_ll.
by move=> *; rewrite dcond_ll mu_not /#.
qed.

(* ? Dexcepted.ec ? *)
lemma dexcepted_dcond ['a] (d: 'a distr) P:
 d \ P = dcond d (predC P).
proof.
apply eq_distr => x.
rewrite dexcepted1E dcond1E mu_not /#.
qed.

(* ? Logic.ec ? *)
lemma predCK ['a]: involutive (predC <:'a>).
proof.
move=> p; rewrite /predC; apply fun_ext => x.
by rewrite negbK.
qed.

(* END: *)


abstract theory BN.

(*
(* Words *)
op wsize : int.
axiom gt0_wsize: 0 < wsize.
clone import WordExt as Word with
  op size <- wsize
  proof gt0_size by apply gt0_wsize.
*)
import W64.

(** Number of limbs *)
op nlimbs : int.
axiom gt0_nlimbs: 0 < nlimbs.
clone export PolyArray as A with
  op size <- nlimbs
  proof ge0_size by (apply ltrW; apply gt0_nlimbs).

(*
clone export WArray as Abytes with
  op size <- 8*nlimbs
  proof ge0_size by (apply ltrW; smt(gt0_nlimbs)).
*)

(* BigInt view of an array... *)
type t = W64.t A.t.

op bn_modulus : int = W64.modulus ^ nlimbs.
lemma bn_modulusE: bn_modulus = W64.modulus ^ nlimbs by rewrite /bn_modulus.


(* digits *)
op dig (x: t) (i:int): int = to_uint x.[i]*W64.modulus^i.
lemma digE (x: t) (i:int): dig x i = to_uint x.[i]*W64.modulus^i by rewrite /dig.
hint simplify digE.

(* BigInt value for a prefix of an array *)
op bnk (k:int) (x:t): int = bigi predT (dig x) 0 k.
abbrev [-printing] bn (x:t): int = bnk nlimbs x.

lemma bnkN k x: k <= 0 => bnk k x = 0.
proof. by move => ?; rewrite /bnk big_geq. qed.

lemma bnk0 x: bnk 0 x = 0.
proof. by rewrite bnkN. qed.

lemma bnkS k x: 0 <= k => bnk (k+1) x = dig x k + bnk k x.
proof. 
case: (k=0) => E.
 by rewrite E /= /bnk rangeS range_geq 1:// big_cons /#.
move=> ?; rewrite /bnk (range_cat k) // 1:/# big_cat rangeS addzC; congr.
by rewrite big_cons big_nil /#.
qed.

lemma bnk1 x: bnk 1 x = dig x 0.
proof. by rewrite -(add0z 1) bnkS 1:/# digE expr0 bnk0. qed.

require import StdOrder.
lemma bnk_cmp k x: 0 <= bnk k x < W64.modulus^k.
proof.
case: (k <= 0).
 by move=> *; rewrite bnkN // expr_gt0.
elim/natind: k => // k Hk IH H.
rewrite bnkS // exprS // digE. 
case: (k=0) => E.
  rewrite E bnk0 !expr0 !mulr1 !addr0.
  move: to_uint_cmp; smt().
  (* ??? falha com "smt(to_uint_cmp)." ??? *)
move: (IH _); first smt().
move=> /> ??; split; first smt(@IntOrder to_uint_cmp).
move=> H2; rewrite ltzE -addzA.
apply (lez_trans (to_uint x.[k] * W64.modulus ^ k + W64.modulus^k)).
 smt().
rewrite (_:to_uint x.[k] * W64.modulus ^ k + W64.modulus ^ k=(to_uint x.[k]+1)*W64.modulus^k) 1:/#.
rewrite ler_pmul2r 1:/# -ltzE.
by move: (to_uint_cmp x.[k]) => /#.
qed.

lemma bnk_ltb k x y b:
 0 <= k =>
 bnk (k+1) x < bnk (k+1) y + b2i b
 = (to_uint x.[k] < to_uint y.[k] \/ x.[k]=y.[k] /\ bnk k x < bnk k y + b2i b).
proof.
move=> ?; rewrite !bnkS // !digE.
move: (to_uint_cmp x.[k]) (to_uint_cmp y.[k]) =>  *.
case: b => E; rewrite ?b2i1 ?b2i0 => *.
 rewrite !ltzS lex_le ?expr_gt0 //; move: bnk_cmp to_uint_eq; smt().
by rewrite /= lex_lt ?expr_gt0 //; move: bnk_cmp to_uint_eq; smt().
qed.

lemma bnk_setO k (x: t) i y:
 0 <= k <= i < nlimbs =>
 bnk k x.[i <- y] = bnk k x.
proof.
elim/natind: k => /=.
 by move=> k *; rewrite (_:k=0) 1:/# !bnk0.
by move=> k Hk IH H; rewrite !bnkS // !digE !get_setE 1:/# IH /#.
qed.

lemma bnkS_eq0 k x:
 0 <= k => bnk (k+1) x = 0 =>
 to_uint x.[k] = 0 /\ bnk k x = 0.
proof. 
move=> Hk; rewrite bnkS 1:/# /=.
move: (to_uint_cmp x.[k]) (bnk_cmp k x); smt(). 
qed.

lemma bnkS_eq k x y:
 0 <= k => bnk (k+1) x = bnk (k+1) y =>
 x.[k] = y.[k] /\ bnk k x = bnk k y.
proof. 
move=> Hk; rewrite !bnkS 1..2:/# /=.
have /= ?:= bnk_cmp.
have /= ?:= to_uint_cmp.
by rewrite lex_eq; smt(expr_gt0 to_uint_eq).
qed.


(* upper part of a bigint (useful in decreasing loops...) *)

op bnkup k (x: t): int =
 bigi predT (fun i => to_uint x.[i] * W64.modulus^(i-k)) k nlimbs.

lemma bnkup0 x: bnkup 0 x = bn x by done.

lemma bnkup_nlimbs x: bnkup nlimbs x = 0.
proof. by rewrite /bnkup range_geq 1:// big_nil. qed.

lemma bnkupP k x:
 0 < k <= nlimbs =>
 bnkup (k-1) x = to_uint x.[k-1] + bnkup (k) x * W64.modulus.
proof.
move=> *; rewrite /bnkup (range_cat k) 1..2:/# big_cat.
rewrite rangeS big_cons big_nil /predT /=; congr => //.
rewrite mulr_suml; apply eq_big_int => i * /=.
rewrite mulzA; congr.
by rewrite (_:i-(k-1)=i-k+1) 1:/# exprS /#.
qed.

lemma bnkup_setO k (x: t) y:
 0 < k <= nlimbs =>
 bnkup k x.[k - 1 <- y] = bnkup k x.
proof.
move=> H; apply eq_big_seq => x0; rewrite mem_range => * /=.
by rewrite get_setE 1:/# (_:x0 <> k - 1) 1:/#.
qed.

lemma bn_k_kup k x:
 0 <= k <= nlimbs =>
 bn x = bnk k x + bnkup k x * W64.modulus^k.
proof.
elim/natind: k=> [k Hk H|k Hk IH H].
 by rewrite (_:k=0) 1:/# bnk0 bnkup0 expr0.
rewrite bnkS 1:// exprS 1:/# IH 1:/#.
move: (bnkupP (k+1) x _); first smt().
by move=> /= ->; ring.
qed.

lemma bn_mod k x:
 0 <= k <= nlimbs =>
 bn x %% W64.modulus^k = bnk k x.
proof.
by move=> H; rewrite (bn_k_kup k x _) 1:/# modzMDr modz_small; move:bnk_cmp; smt().
qed.

lemma bn_div_kup k x:
 0 <= k <= nlimbs =>
 bn x %/ W64.modulus^k = bnkup k x.
proof.
move=> H; rewrite (bn_k_kup k x _) 1:/# divzMDr; first smt(expr_gt0).
rewrite divz_small; move: bnk_cmp; smt().
qed.

lemma bn_inj x y:
 bn x = bn y => x = y.
proof.
move=> E.
have HH: forall k, 0 <= k <= nlimbs => bnk k x = bnk k y.
 by move=> k Hk; rewrite -!(bn_mod k) 1..2:/# E.
apply A.ext_eq => k Hk; rewrite to_uint_eq.
move: (HH (k+1) _); first smt(). 
rewrite !bnkS 1..2:/# !digE (HH k _) 1:/# => /addIz.
move: (mulIf (W64.modulus ^ k) _); first smt(expr_gt0).
by move => I /I.
qed.

(* BigNum of an integer *)

op bn_ofint x = A.init (fun i => JWord.W64.of_int (x %/ W64.modulus^i)).

lemma bn_ofintE x i:
 0 <= i < nlimbs =>
 (bn_ofint x).[i] = W64.of_int (x %/ W64.modulus^i).
proof. by move=> Hi; rewrite /bn_ofint initiE 1:/#. qed.

lemma bnk_ofintK x k:
 0 <= k <= nlimbs =>
 bnk k (bn_ofint x) = x %% W64.modulus ^ k.
proof.
elim/natind: k x.
 move=> k Hk0 x Hk.
 by rewrite (_:k=0) 1:/# bnk0 expr0 modz1.
move=> k Hk0 IH /= x Hk.
case: (k=0) => [->/=|Ek].
 rewrite bnk1 digE expr0 bn_ofintE; first smt(gt0_nlimbs).
 by rewrite expr0 divz1 W64.of_uintK.
rewrite bnkS 1:/# /= IH 1:/# bn_ofintE 1:/# of_uintK.
rewrite exprS 1:/#.
have ->: x %/ W64.modulus ^ k %% W64.modulus 
         = (x %% W64.modulus ^ (k+1)) %/ W64.modulus ^ k.
 rewrite -divz_mod_mul /=; first 2 smt(StdOrder.IntOrder.expr_gt0).
 rewrite exprS; smt(StdOrder.IntOrder.expr_gt0).
have ->: x %% W64.modulus ^ k = (x %% W64.modulus ^ (k+1)) %% W64.modulus ^ k.
 by rewrite modz_dvd_pow 1:/#.
by rewrite /= -divz_eq exprS /#.
qed.

lemma bn_ofintK x:
 bn (bn_ofint x) = x %% bn_modulus.
proof. by rewrite bnk_ofintK /bn_modulus; smt(gt0_nlimbs). qed.

lemma bnK x:
 bn_ofint (bn x) = x.
proof.
apply bn_inj.
rewrite bnk_ofintK; first smt(gt0_nlimbs).
rewrite modz_small; move: bnk_cmp; smt().
qed.



(** SAMPLING *)
op bn_rnd: t distr = 
 Distr.dmap (DList.dlist W64.dword nlimbs) (A.of_list W64.zero).

require import DList List. 

lemma bn_rnd_uni: is_uniform bn_rnd.
proof.
have Hlimbs:= gt0_nlimbs; rewrite /bn_rnd.
apply (dmap_uni_in_inj _).
 move=> l1 l2; rewrite !supp_dlist 1..2:/#; move => [l1_sz ?] [l2_sz ?] Hl.
 by rewrite -(A.of_listK W64.zero l1) // -(A.of_listK W64.zero l2) // Hl.
by apply dlist_uni; apply duniform_uni.
qed.

lemma bn_rnd_fu: is_full bn_rnd.
proof.
have Hlimbs:= gt0_nlimbs; move => a; rewrite /bn_rnd supp_dmap.
exists (A.to_list a); split.
 by rewrite supp_dlist 1:/# size_to_list /=; apply/List.allP => *; apply W64.dword_fu.
by rewrite to_listK.
qed.

lemma bn_rnd_ll: is_lossless bn_rnd.
proof. by rewrite /bn_rnd dmap_ll dlist_ll W64.dword_ll. qed.

lemma bn_rnd1E x: mu1 bn_rnd x = inv (bn_modulus%r).
proof.
have Hlimbs:= gt0_nlimbs; rewrite /bn_rnd (dmap1E_can _ _ (A.to_list)).
  by move=> y; rewrite to_listK.
 by move=> a; rewrite supp_dlist 1:/#; move => [H _]; rewrite of_listK.
rewrite dlist1E 1:/# A.size_to_list /=.
rewrite (StdBigop.Bigreal.BRM.eq_bigr _ _ (fun _ => inv W64.modulus%r)).
 by move=> i _ /=; rewrite W64_dword1E.
rewrite StdBigop.Bigreal.BRM.big_const count_predT size_to_list.
rewrite /bn_modulus.
rewrite eq_sym -RField.fromintXn 1:/#.
by rewrite -RField.exprVn 1:/# /RField.exp ifF 1:/# RField.MulMonoid.iteropE.
qed.

(*
lemma bn_rnd_dinter: dmap bn_rnd (bnk nlimbs) = [0..bn_modulus-1].
proof.
apply (dmap_bij _ _ _ bn_ofint).
+ smt(supp_dinter bnk_cmp).
+ move => x /supp_dinter Hx.
  rewrite bn_rnd1E duniform1E ifT /range /= ?mem_iota 1:/# undup_id .
   by apply iota_uniq.
  rewrite size_iota /max /= bn_modulusE /= ifT //.
  smt(StdOrder.IntOrder.expr_gt0).
+ smt(bnK).
+ move => x /supp_dinter Hx.
  by rewrite bn_ofintK modz_small /#.
qed.
*)

require import DInterval.
lemma bn_rndE: bn_rnd = dmap [0..bn_modulus-1] bn_ofint.
proof.
rewrite eq_sym.
apply (dmap_bij _ _ _ bn).
+ smt(bn_rnd_fu).
+ move=> x _; rewrite bn_rnd1E duniform1E ifT /range /=. 
   by rewrite mem_iota /=; smt(bnk_cmp).
  rewrite undup_id; first by apply iota_uniq.
  rewrite size_iota /max bn_modulusE /= ifT //.
  smt(StdOrder.IntOrder.expr_gt0).
+ move => x /supp_dinter Hx /=.
  by rewrite bn_ofintK modz_small /#.
+ by move=> a _ /=; rewrite bnK.
qed.

op bn_rnd_bnd (bnd: BN.t): BN.t distr =
 dmap [0..bn bnd-1] bn_ofint.

lemma bn_rnd_bndE bnd:
 bn_rnd_bnd bnd = dcond bn_rnd (fun x=> bn x < bn bnd).
proof.
apply eq_distr => x.
rewrite dmap1E dcond1E /=.
case: (bn bnd = 0) => ?.
 by rewrite dinterE range_geq 1:/# /= ifF; smt(bnk_cmp).
rewrite (mu_eq_support _ _ (pred1 (bn x))).
 move=> i; rewrite supp_dinter /(\o) /pred1 /= => Hi.
 rewrite eq_iff => *; split.
  by move=> <-; rewrite bn_ofintK; smt(bnk_cmp).
 by move=> ->; rewrite bnK.
rewrite dinter1E.
case: (bn x < bn bnd) => C.
 rewrite ifT /=; first smt(bnk_cmp).
 rewrite bn_rnd1E bn_rndE dmapE /(\o) /=; congr.
 rewrite dinterE /pred1 /(\o) /max ifT /=.
  smt(StdOrder.IntOrder.expr_gt0).
 rewrite (range_cat (bn bnd)); first 2 smt(bnk_cmp).
 rewrite filter_cat size_cat /= eq_in_filter_predT.
  move=> y; rewrite mem_range => Hy /=.
  by rewrite bn_ofintK modz_small; smt(bnk_cmp).
 rewrite eq_in_filter_pred0.
  move=> y; rewrite mem_range => Hy /=.
  rewrite bn_ofintK modz_small; smt(bnk_cmp).
 by rewrite /= size_range /= lez_maxr; smt(bnk_cmp).
by rewrite ifF //; smt(bnk_cmp).
qed.

lemma bn_rnd_excepted bnd:
 bn_rnd \ (fun x=>! bn x < bn bnd)
 = bn_rnd_bnd bnd.
proof.
rewrite dexcepted_dcond /predC bn_rnd_bndE; congr.
apply fun_ext => x; smt(negbK).
qed.


(* to prove by simplification... *)
op bn_seq (x: W64.t list) : int = foldr (fun w r => W64.to_uint w + W64.modulus * r) 0 x.

lemma bn2seq x:
 bn x = bn_seq (to_list x).
proof.
have ->: bn x = bigi predT (fun i => to_uint (nth W64.zero (to_list x) i) * W64.modulus ^ i) 0 (size (to_list x)).
 rewrite size_to_list; apply eq_big_seq => y; rewrite mem_range => /> *; congr.
 rewrite -get_to_list; congr.
 by rewrite !nth_mkseq.
elim: (to_list x) => //=.
 by rewrite /bn_seq big1_eq.
move=> y ys IH; rewrite /bn_seq /= -/(bn_seq ys).
rewrite (range_cat 1) //; first smt(size_ge0).
rewrite big_cat rangeS big_cons big_nil /predT /=; congr.
rewrite -(add0z 1) big_addn /= -IH.
rewrite big_distrr // 1:/#.
apply eq_big_seq => z; rewrite mem_range => /> *.
by rewrite (_:! z+1=0) 1:/# /= exprS // /#.
qed.



(* carry and borrow *)

(* bnk with carry *)
op bnk_withcarry k (x: bool * t): int =
 b2i x.`1 * W64.modulus ^ k + bnk k x.`2. 

abbrev bn_withcarry x = bnk_withcarry nlimbs x.

op bnk_addc k cf (a:t) x = 
 ((addc a.[k] x cf).`1, a.[k <- (addc a.[k] x cf).`2]).

op to_uint_withcarry (cw:bool*W64.t) =
 W64.to_uint cw.`2 + b2i cw.`1 * W64.modulus.

lemma to_uint_withcarry_addc x y cf:
 to_uint_withcarry (W64.addc x y cf)
 = to_uint x + to_uint y + b2i cf.
proof.
move: (W64.addcP x y cf) => /=.
by rewrite /to_uint_withcarry mulrC addcE /=.
qed.

lemma bnk_withcarryS k cf a x:
 0 <= k < nlimbs =>
 bnk_withcarry (k+1) (bnk_addc k cf a x)
 = (to_uint a.[k] + to_uint x) * W64.modulus ^ k
   + bnk_withcarry k (cf,a).
proof.
move=> Hk; rewrite /bnk_withcarry /bnk_addc /= bnkS 1:/# addcE /= bnk_setO 1:/# get_setE 1:/# /=.
move: (W64.addcP a.[k] x cf); rewrite addcE /= => E.
rewrite exprS 1:/#; ring E.
qed.

(* bn with borrow *)
op bnk_withborrow k (x: bool * t): int =
 bnk k x.`2 - b2i x.`1 * W64.modulus ^ k.

abbrev bn_withborrow x = bnk_withborrow nlimbs x.
(*
op bnb (x: bool * t): int = bn x.`2 - b2i x.`1 * bn_modulus. 
*)
op bnk_subc k cf (a:t) x = 
 ((subc a.[k] x cf).`1, a.[k <- (subc a.[k] x cf).`2]).

op to_uint_withborrow (cw:bool*W64.t) =
 W64.to_uint cw.`2 - b2i cw.`1 * W64.modulus.

lemma to_uint_withborrow_subc x y cf:
 to_uint_withborrow (W64.subc x y cf)
 = to_uint x - (to_uint y + b2i cf).
proof.
move: (W64.subcP x y cf) => /=.
by rewrite /to_uint_withborrow mulrC subcE /=.
qed.

lemma bnk_withborrowS k cf a x:
 0 <= k < nlimbs =>
 bnk_withborrow (k+1) (bnk_subc k cf a x)
 = (to_uint a.[k] - to_uint x) * W64.modulus ^ k
   + bnk_withborrow k (cf,a).
proof.
move=> Hk; rewrite /bnk_withborrow /bnk_subc /= bnkS 1:/# subcE /= bnk_setO 1:/# get_setE 1:/# /=.
move: (W64.subcP a.[k] x cf); rewrite subcE /= => E.
rewrite exprS 1:/#; ring E.
qed.




end BN.

abstract theory BigN.

op nlimbs: int.
axiom gt0_nlimbs: 0 < nlimbs.

clone BN as BN2
 with op nlimbs <- 2*nlimbs
      proof gt0_nlimbs by smt(gt0_nlimbs).

clone export BN
 with op nlimbs <- nlimbs
      proof gt0_nlimbs by exact gt0_nlimbs.

end BigN.
