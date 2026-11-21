(* Transfer of the __mont_redM spike to the extraction at point B. *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety.
require import BArray24 BArray56 BArray112 SBArray112_56 MUL_spike.
require BnMulSafetySpike.

clone BnMulSafetySpike.BnMulSafetyProofs as T
  with op nlimbs <- 7, theory A <- BArray56, theory A2 <- BArray112,
       theory SA <- SBArray112_56
  proof gt0_nlimbs by done, nlimbs_bnd by done.

equiv eq__addacc3: M.uTIL____addacc3 ~ T.M.__addacc3 : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma uTIL____addacc3_safety _a _b_a _b1 _b0 _k : uTIL____addacc3_spec _a _b_a _b1 _b0 _k.
proof.
have h := T.__addacc3_proof _a _b_a _b1 _b0 _k.
rewrite /uTIL____addacc3_spec; rewrite /T.__addacc3_spec in h.
by conseq eq__addacc3 h => /> /#.
qed.

equiv eq__mov: M.h__BN____mov ~ T.M.__mov : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN____mov_safety _r _b_r _a _b_a : h__BN____mov_spec _r _b_r _a _b_a.
proof.
have h := T.__mov_proof _r _b_r _a _b_a.
rewrite /h__BN____mov_spec; rewrite /T.__mov_spec in h.
by conseq eq__mov h => /> /#.
qed.

equiv eq_mov: M.h__BN___mov ~ T.M._mov : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___mov_safety _r _b_r _a _b_a : h__BN___mov_spec _r _b_r _a _b_a.
proof.
have h := T._mov_proof _r _b_r _a _b_a.
rewrite /h__BN___mov_spec; rewrite /T._mov_spec in h.
by conseq eq_mov h => /> /#.
qed.

equiv eq_mov_: M.h__BN___mov_ ~ T.M._mov_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___mov__safety _r _b_r _a _b_a : h__BN___mov__spec _r _b_r _a _b_a.
proof.
have h := T._mov__proof _r _b_r _a _b_a.
rewrite /h__BN___mov__spec; rewrite /T._mov__spec in h.
by conseq eq_mov_ h => /> /#.
qed.

equiv eq__cmov: M.h__BN____cmov ~ T.M.__cmov : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN____cmov_safety _a _b_a _cond _b _b_b : h__BN____cmov_spec _a _b_a _cond _b _b_b.
proof.
have h := T.__cmov_proof _a _b_a _cond _b _b_b.
rewrite /h__BN____cmov_spec; rewrite /T.__cmov_spec in h.
by conseq eq__cmov h => /> /#.
qed.

equiv eq_cmov: M.h__BN___cmov ~ T.M._cmov : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___cmov_safety _a _b_a _cond _b _b_b : h__BN___cmov_spec _a _b_a _cond _b _b_b.
proof.
have h := T._cmov_proof _a _b_a _cond _b _b_b.
rewrite /h__BN___cmov_spec; rewrite /T._cmov_spec in h.
by conseq eq_cmov h => /> /#.
qed.

equiv eq_cmov_: M.h__BN___cmov_ ~ T.M._cmov_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___cmov__safety _a _b_a _cond _b _b_b : h__BN___cmov__spec _a _b_a _cond _b _b_b.
proof.
have h := T._cmov__proof _a _b_a _cond _b _b_b.
rewrite /h__BN___cmov__spec; rewrite /T._cmov__spec in h.
by conseq eq_cmov_ h => /> /#.
qed.

equiv eq__addc1U: M.h__BN____addc1U ~ T.M.__addc1U : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN____addc1U_safety _a _b_a _b _b_b _cf : h__BN____addc1U_spec _a _b_a _b _b_b _cf.
proof.
have h := T.__addc1U_proof _a _b_a _b _b_b _cf.
rewrite /h__BN____addc1U_spec; rewrite /T.__addc1U_spec in h.
by conseq eq__addc1U h => /> /#.
qed.

equiv eq_addc1U: M.h__BN___addc1U ~ T.M._addc1U : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___addc1U_safety _a _b_a _b _b_b _cf : h__BN___addc1U_spec _a _b_a _b _b_b _cf.
proof.
have h := T._addc1U_proof _a _b_a _b _b_b _cf.
rewrite /h__BN___addc1U_spec; rewrite /T._addc1U_spec in h.
by conseq eq_addc1U h => /> /#.
qed.

equiv eq_addc1U_: M.h__BN___addc1U_ ~ T.M._addc1U_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___addc1U__safety _a _b_a _b _b_b _cf : h__BN___addc1U__spec _a _b_a _b _b_b _cf.
proof.
have h := T._addc1U__proof _a _b_a _b _b_b _cf.
rewrite /h__BN___addc1U__spec; rewrite /T._addc1U__spec in h.
by conseq eq_addc1U_ h => /> /#.
qed.

equiv eq_addU_: M.h__BN___addU_ ~ T.M._addU_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___addU__safety _a _b_a _b _b_b : h__BN___addU__spec _a _b_a _b _b_b.
proof.
have h := T._addU__proof _a _b_a _b _b_b.
rewrite /h__BN___addU__spec; rewrite /T._addU__spec in h.
by conseq eq_addU_ h => /> /#.
qed.

equiv eq_cminusP_: M.h__BN___cminusP_ ~ T.M._cminusP_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___cminusP__safety _x _b_x _mP _b_mP _lastbit : h__BN___cminusP__spec _x _b_x _mP _b_mP _lastbit.
proof.
have h := T._cminusP__proof _x _b_x _mP _b_mP _lastbit.
rewrite /h__BN___cminusP__spec; rewrite /T._cminusP__spec in h.
by conseq eq_cminusP_ h => /> /#.
qed.

equiv eq__muln_innerloop: M.h__MUL__UNR____muln_innerloop ~ T.M.__muln_innerloop : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__MUL__UNR____muln_innerloop_safety _x _b_x _k _istart _iend _a _b_a _b _b_b : h__MUL__UNR____muln_innerloop_spec _x _b_x _k _istart _iend _a _b_a _b _b_b.
proof.
have h := T.__muln_innerloop_proof _x _b_x _k _istart _iend _a _b_a _b _b_b.
rewrite /h__MUL__UNR____muln_innerloop_spec; rewrite /T.__muln_innerloop_spec in h.
by conseq eq__muln_innerloop h => /> /#.
qed.

equiv eq__mont_redM: M.h__MUL__UNR____mont_redM ~ T.M.__mont_redM : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__MUL__UNR____mont_redM_safety _r _b_r _a _b_a __P_mP _b__P_mP __U0 : h__MUL__UNR____mont_redM_spec _r _b_r _a _b_a __P_mP _b__P_mP __U0.
proof.
have h := T.__mont_redM_proof _r _b_r _a _b_a __P_mP _b__P_mP __U0.
rewrite /h__MUL__UNR____mont_redM_spec; rewrite /T.__mont_redM_spec in h.
by conseq eq__mont_redM h => /> /#.
qed.
