(* The keys of the RSA example: their formats (../rsa2048_params.jinc), the
   well-formed expanded keys, and the example key pair (../rsa_keys.jinc,
   pk_test and sk_test in xtr/RsaPssXtr.ec).

   The facts about the example key are closed computations: the value of a
   part of a key given by a list of words is rewritten into bn_seq of a
   sublist (drop, take), which the simplifier reduces with the word
   conversions and the integer arithmetic on the literals. *)

require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel_x86.
import SLH64.
require import RsaPssXtr RsaPss_inst.
require import Array4 Array16 Array32 Array36 Array65 Array80 Array129 Array133 Array178.

(* values of the big numbers of each size *)
abbrev bn16 (x: W64.t Array16.t) = F16.BigN.BN.bn x.
abbrev bn32 (x: W64.t Array32.t) = F32.BigN.BN.bn x.
abbrev bn4 (x: W64.t Array4.t) = E32.BNexp.bn x.
abbrev R16 = F16.BigN.BN.bn_modulus.
abbrev R32 = F32.BigN.BN.bn_modulus.

(* -------------------------------------------------------------------- *)
(* the formats                                                           *)

(* the key pair: pk = (n, e) (RSA_pubkey), sk = (p, q, dP, dQ, qInv)
   (RSA_privkey) *)
op pub_n (k: W64.t Array36.t) : W64.t Array32.t = Array32.init (fun i => k.[0 + i]).
op pub_e (k: W64.t Array36.t) : W64.t Array4.t = Array4.init (fun i => k.[32 + i]).
op priv_p (k: W64.t Array80.t) : W64.t Array16.t = Array16.init (fun i => k.[0 + i]).
op priv_q (k: W64.t Array80.t) : W64.t Array16.t = Array16.init (fun i => k.[16 + i]).
op priv_dp (k: W64.t Array80.t) : W64.t Array16.t = Array16.init (fun i => k.[32 + i]).
op priv_dq (k: W64.t Array80.t) : W64.t Array16.t = Array16.init (fun i => k.[48 + i]).
op priv_qinv (k: W64.t Array80.t) : W64.t Array16.t = Array16.init (fun i => k.[64 + i]).

(* the expanded keys: PK = (ctx_n, e) (RSA_PK), SK = (ctx_p, ctx_q, dP, dQ,
   qInv) (RSA_SK); a context starts with its modulus *)
op pk_ctxn (k: W64.t Array133.t) : W64.t Array129.t = Array129.init (fun i => k.[0 + i]).
op pk_e (k: W64.t Array133.t) : W64.t Array4.t = Array4.init (fun i => k.[129 + i]).
op sk_ctxp (k: W64.t Array178.t) : W64.t Array65.t = Array65.init (fun i => k.[0 + i]).
op sk_ctxq (k: W64.t Array178.t) : W64.t Array65.t = Array65.init (fun i => k.[65 + i]).
op sk_dp (k: W64.t Array178.t) : W64.t Array16.t = Array16.init (fun i => k.[130 + i]).
op sk_dq (k: W64.t Array178.t) : W64.t Array16.t = Array16.init (fun i => k.[146 + i]).
op sk_qinv (k: W64.t Array178.t) : W64.t Array16.t = Array16.init (fun i => k.[162 + i]).

(* PK is an expanded public key of (n, e): its context is a Montgomery
   context of n *)
pred wf_pk (n e: int) (k: W64.t Array133.t) =
  F32.FPC.ctx_mont n (pk_ctxn k) /\ bn4 (pk_e k) = e.

(* SK is an expanded private key of (p, q, dP, dQ, qInv) *)
pred wf_sk (p q dp dq qi: int) (k: W64.t Array178.t) =
  F16.FPC.ctx_mont p (sk_ctxp k) /\ F16.FPC.ctx_mont q (sk_ctxq k)
  /\ bn16 (sk_dp k) = dp /\ bn16 (sk_dq k) = dq /\ bn16 (sk_qinv k) = qi.

(* -------------------------------------------------------------------- *)
(* the example key pair                                                  *)

(* The values of the parts of the key are opaque: they are unfolded by
   name only (rewrite /p_val), so that no simplification evaluates, e.g.,
   x ^ dP_val by unrolling the power. *)

(* the globals, under names that simplification does not unfold (the
   extraction makes them abbreviations of literal arrays) *)
op pkT : W64.t Array36.t = pk_test.
op skT : W64.t Array80.t = sk_test.

op [opaque] n_val : int =
  29371081152817474224266586408243284112097480749397847536704623974146421651875378974624502482600682233384586661723730351571473381008840255266249761900776376089872641678422605504091161472148619334092687542516850442834119705967316692975149221902191696873903893909771882895663317155459232454946233308284017961767276445345771619611904439797581721436851955544084762465568078570068452694692715317647425907853618296875494949800699191462096330683257337584751543739104196828147241421543970972205968626121077866506477634979168234130681119557001656791850500896355932717904998771555150750274702633266754420572411197276542091804529.

op [opaque] e_val : int = 65537.

op [opaque] p_val : int =
  166903302825020570534582231459842875312983571366225473153971908505474440749668381584735215945095806226193048683324332285062125940241308105711880128355487796127944015194633953069342220562002200409708458423855078358021176477025467148449201757954968268110113113001064925326938656007136613767980591339858871960863.

op [opaque] q_val : int =
  175976632311523307273209184846041449201189209649284560308566574852731116446230316190803091132771349344735631515027301274999504679204212573358705816750832897685724956097163716768090229952049113840006370890125335575639561365001759954672962305389811625646724447988745009722265384266961482994153015857145886038383.

op [opaque] dP_val : int =
  40637746664919865786049539457172479078524785209741975908539141920165031219653910996042233255045146710276065090556576747070148826287906883788462566308627473988946742305274486002220025535313931243995267880273059269709384211115787712098568937419891491130705936252162793741580483298074048947856421502511985899255.

op [opaque] dQ_val : int =
  123831032123998967934427696988646009320097697199994752090424717830895538354682141260223479160932241599877521378435296899448436109233878133658596459268781920786312736321969255934724157875683186336871901465430369115793668484516931867947159660003691696903275880310312550366384068941810926823647018207790970389735.

op [opaque] qInv_val : int =
  88800123902782924503229615203330188974210535863748606984663706858776926771781835925440729072902528098089345114543157540075906958304612552543810057218573980150331292430563672478246686315060862852500228681244097533040383522722823297645733714658529550438776847427329497685329157492076962427322611856710955348128.

(* the private exponent: d = e^-1 mod lcm(p-1, q-1); it is not part of the
   key, whose dP and dQ are its residues modulo p-1 and q-1 *)
op [opaque] d_val : int =
  11653960271264561998990315592107639349542745157809201326647039715331851452391280572136893091803838149395498596998090911428118372823807650608718110509602039822406399044901375307511582204277777395421612934000765657803354575796482952898756128085579029945053891042154936033367851737347786452819351678420092513813377793230360781076177567549730638696754988830292092104375733775040256138722663829335315396960078012092160783599179789976418059118656064311996698452402776614694145566570906732911048945030824091198633748852061340561870668570672979685150245983270854906986111419801655897571201999056731846809625989172960142030801.

(* a part of a key given by a list of words *)
lemma slice16E (l: W64.t list) o:
  0 <= o => o + 16 <= 80 =>
  Array16.init (fun i => (Array80.of_list witness l).[o + i])
  = Array16.of_list witness (drop o l).
proof.
move=> H0 H1; apply Array16.tP => i Hi.
by rewrite Array16.initiE //= Array80.get_of_list 1:/# Array16.get_of_list // nth_drop /#.
qed.

lemma slice32E (l: W64.t list):
  Array32.init (fun i => (Array36.of_list witness l).[0 + i])
  = Array32.of_list witness l.
proof.
apply Array32.tP => i Hi.
by rewrite Array32.initiE //= Array36.get_of_list 1:/# Array32.get_of_list.
qed.

lemma slice4E (l: W64.t list):
  Array4.init (fun i => (Array36.of_list witness l).[32 + i])
  = Array4.of_list witness (drop 32 l).
proof.
apply Array4.tP => i Hi.
by rewrite Array4.initiE //= Array36.get_of_list 1:/# Array4.get_of_list // nth_drop /#.
qed.

(* the value of an array given by a list *)
lemma bn16E (l: W64.t list):
  16 <= size l => bn16 (Array16.of_list witness l) = JBigNumber.bn_seq (take 16 l).
proof.
move=> Hl; rewrite F16.BigN.BN.bn2seq; congr.
rewrite -(Array16.of_listK witness (take 16 l)) 1:size_take //= 1:/#; congr.
by apply Array16.tP => i Hi; rewrite !Array16.get_of_list // nth_take /#.
qed.

lemma bn32E (l: W64.t list):
  32 <= size l => bn32 (Array32.of_list witness l) = JBigNumber.bn_seq (take 32 l).
proof.
move=> Hl; rewrite F32.BigN.BN.bn2seq; congr.
rewrite -(Array32.of_listK witness (take 32 l)) 1:size_take //= 1:/#; congr.
by apply Array32.tP => i Hi; rewrite !Array32.get_of_list // nth_take /#.
qed.

lemma bn4E (l: W64.t list):
  4 <= size l => bn4 (Array4.of_list witness l) = JBigNumber.bn_seq (take 4 l).
proof.
move=> Hl; rewrite E32.BNexp.bn2seq; congr.
rewrite -(Array4.of_listK witness (take 4 l)) 1:size_take //= 1:/#; congr.
by apply Array4.tP => i Hi; rewrite !Array4.get_of_list // nth_take /#.
qed.

(* the values of the parts of the example keys *)
lemma pkT_n: bn32 (pub_n pkT) = n_val.
proof. by rewrite /pub_n /pkT slice32E bn32E //= /n_val. qed.

lemma pkT_e: bn4 (pub_e pkT) = e_val.
proof. by rewrite /pub_e /pkT slice4E bn4E //= /e_val. qed.

lemma skT_p: bn16 (priv_p skT) = p_val.
proof. by rewrite /priv_p /skT slice16E // bn16E //= /p_val. qed.

lemma skT_q: bn16 (priv_q skT) = q_val.
proof. by rewrite /priv_q /skT slice16E // bn16E //= /q_val. qed.

lemma skT_dp: bn16 (priv_dp skT) = dP_val.
proof. by rewrite /priv_dp /skT slice16E // bn16E //= /dP_val. qed.

lemma skT_dq: bn16 (priv_dq skT) = dQ_val.
proof. by rewrite /priv_dq /skT slice16E // bn16E //= /dQ_val. qed.

lemma skT_qinv: bn16 (priv_qinv skT) = qInv_val.
proof. by rewrite /priv_qinv /skT slice16E // bn16E //= /qInv_val. qed.

(* the facts of the key pair *)
lemma n_pq: n_val = p_val * q_val.
proof. by rewrite /n_val /p_val /q_val. qed.

lemma n_odd: 1 < n_val /\ n_val %% 2 = 1.
proof. by rewrite /n_val. qed.

lemma p_odd: 1 < p_val /\ p_val %% 2 = 1.
proof. by rewrite /p_val. qed.

lemma q_odd: 1 < q_val /\ q_val %% 2 = 1.
proof. by rewrite /q_val. qed.

lemma qInv_bnd: qInv_val < p_val.
proof. by rewrite /qInv_val /p_val. qed.

lemma qInv_inv: qInv_val * q_val %% p_val = 1.
proof. by rewrite /qInv_val /q_val /p_val. qed.

lemma pq_ne: p_val <> q_val.
proof. by rewrite /p_val /q_val. qed.

lemma d_pos: 0 < d_val.
proof. by rewrite /d_val. qed.

lemma dP_pos: 0 < dP_val.
proof. by rewrite /dP_val. qed.

lemma dQ_pos: 0 < dQ_val.
proof. by rewrite /dQ_val. qed.

lemma d_dP: dP_val %% (p_val - 1) = d_val %% (p_val - 1).
proof. by rewrite /dP_val /d_val /p_val. qed.

lemma d_dQ: dQ_val %% (q_val - 1) = d_val %% (q_val - 1).
proof. by rewrite /dQ_val /d_val /q_val. qed.

(* d is the inverse of e modulo lcm(p-1, q-1) = (p-1)(q-1)/2 *)
lemma ed_inv: e_val * d_val %% ((p_val - 1) * (q_val - 1) %/ 2) = 1.
proof. by rewrite /e_val /d_val /p_val /q_val. qed.
