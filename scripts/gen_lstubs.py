import os
from string import Template


BN_UTIL_FNS = "__mask_zf __mask_cf __cf_mask __addacc3 __addacc3x2"

BN_BASE_FNS = "_load_ _store_ _eq_ _test0_ __copy _mov_ _cmov_ _cswap_cf_ _set0_ __cfill _or_mask_ _and_mask_ _set_err_ __carrypropU _addcU_ _addU_ _addc_ _add_ _subcU_ _subU_ _subc_ _sub_ _lt_cf_ _ltc_cf_ _negU_ _negcU_ _neg_ _negc_ _cnegU_ _caddU_ _muln_ _sqrn_ _cminusP_ __mont_redM _pack2_"

BN_RND_FNS = "_rnd_ _rsample_"

BN_EXP_FNS = "_expmU_noct _expmU"

FP_BASE_FNS = "_chk_bnds_ _addm_ _addmU_ _subm_ _submU_ _mulm_ _mulmU_ _sqrm_ _sqrmU_ _invmU_"

FP_MONT_FNS = "_redM_ _fromM_ _toM_"


ll_lemma = """
lemma ${fn}_ll: islossless M.${fn}.
admitted."""

ll_base_lemma = """
lemma ${fn}_ll: islossless M.${fn}.
proof.
have ?:= gt0_nlimbs.
proc; inline*.
wp; while (0 <= i <= nlimbs) (nlimbs - i).
 by move=> z; auto => /> &m /#.
by auto => /> /#.
qed."""


h_lemma = """
hoare ${fn}_h:
 M.${fn} :  true  ==>  true.
admitted."""

ph_lemma = """
phoare ${fn}_ph:
 [ M.${fn}
 : true ==> true
 ] = 1%r.
proof. by conseq ${fn}_ll (${fn}_h). qed."""

ct_lemma = """
equiv $fn}_ct:
 MLeak.${fn} ~ MLeak.${fn}
 : ={glob LEAK} ==> ={glob LEAK}.
admitted."""

proj_lemma = """
equiv ${fn}_lproj:
 M.${fn} ~ MLeak.${fn}
 : ={arg} ==> ={res}.
proof. by proc; sim. qed."""


def gen_lemmas(tstring, fns):
    t = Template(tstring)
    for f in fns.split():
        print(t.substitute(fn = f))
