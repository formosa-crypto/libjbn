(* Transfer of the spike lemmas to the extraction at point B (nlimbs = 7). *)
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
from Jasmin require import Jcheck JSafety.
require import BArray56 BN_spike.
require BnBaseSafetySpike.

clone BnBaseSafetySpike.BnBaseSafetyProofs as T
  with op nlimbs <- 7, theory A <- BArray56
  proof gt0_nlimbs by done, nlimbs_bnd by done.

equiv eq__load: M.h__BN____load ~ T.M.__load : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN____load_safety _a _b_a _ap : h__BN____load_spec _a _b_a _ap.
proof.
have h := T.__load_proof _a _b_a _ap.
rewrite /h__BN____load_spec; rewrite /T.__load_spec in h.
by conseq eq__load h => /> /#.
qed.

equiv eq_load: M.h__BN___load ~ T.M._load : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___load_safety _a _b_a _ap : h__BN___load_spec _a _b_a _ap.
proof.
have h := T._load_proof _a _b_a _ap.
rewrite /h__BN___load_spec; rewrite /T._load_spec in h.
by conseq eq_load h => /> /#.
qed.

equiv eq_load_: M.h__BN___load_ ~ T.M._load_ : ={arg, Glob.mem, Glob.mem_v} ==> ={res}.
proof. by proc; inline *; sim. qed.

lemma h__BN___load__safety _a _b_a _ap : h__BN___load__spec _a _b_a _ap.
proof.
have h := T._load__proof _a _b_a _ap.
rewrite /h__BN___load__spec; rewrite /T._load__spec in h.
by conseq eq_load_ h => /> /#.
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
