# Extraction of the libjbn modules to EasyCrypt (old array model, which
# the proofs rely on). Every module is instantiated once, with dummy
# parameters and stub function parameters, in libjbn_abs.jazz; each .ec file
# below collects the listed procedures of one module (and their callees).

SRCDIR = $(abspath ..)
JASMIN2EC = jasmin2ec --array-model=old -I Libjbn=$(SRCDIR)

LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc)
HARNESS = libjbn_abs.jazz preamb@n.jinc

MJAZZ_EC = BNUTIL_bn_util.ec BN_bn_base.ec BNRND_bn_rnd.ec BNMUL_bn_mul.ec BNMULL_bn_mul_loop.ec BNMULX_bn_mulx.ec BNMULXL_bn_mulx_loop.ec BNMULXR_bn_mulxr.ec BNMULSEL_bn_mulsel.ec BNMULREG_bn_mulreg.ec BNKAR_bn_karatsuba.ec BNE_bn_exp.ec FP_fp_base.ec FPM_fp_mont.ec

all: $(MJAZZ_EC)

# module = namespace path in libjbn_abs.jazz + procedures to extract
BN_UTIL_NS  = UTIL::
BN_UTIL_FNS = __mask_zf __mask_cf __cf_mask __ncf_mask __addacc3 __addacc3x2

BN_BASE_NS  = H::BN::
BN_BASE_FNS = _load_ _store_ _eq_ _test0_ __copy _mov_ _cmov_ _cswap_cf_ _set0_ __cfill _or_mask_ _and_mask_ _set_err_ __carrypropU _addcU_ _addU_ _addc_ _add_ _subcU_ _subU_ _subc_ _sub_ _lt_cf_ _ltc_cf_ _negU_ _negcU_ _neg_ _negc_ _cnegU_ _caddU_ _cminusP_ _pack2_

BN_RND_NS  = H::RND::
BN_RND_FNS = _rnd_ _rsample_

# the five multiplication modules, instantiated by the selector (MUL)
BN_MUL_NS  = H::MUL::UNR::
BN_MUL_FNS = _os_muln_ _ps_muln_ _ps_sqrn_ _ps_ksqrn_ __mont_redM

BN_MULL_NS  = H::MUL::LOOP::
BN_MULL_FNS = _os_muln_ _os_sqrn_ __mont_redM

BN_MULX_NS  = H::MUL::XUNR::
BN_MULX_FNS = _os_muln_ _os_sqrn_ __mont_redM

BN_MULXL_NS  = H::MUL::XLOOP::
BN_MULXL_FNS = _os_muln_ _os_sqrn_ __mont_redM

BN_MULXR_NS  = H::MUL::XREG::
BN_MULXR_FNS = _os_muln_ _os_sqrn_ __mont_redM

BN_MULSEL_NS  = H::MUL::
BN_MULSEL_FNS = _muln_ _sqrn_ __mont_redM

BN_MULREG_NS  = H::MULREG::
BN_MULREG_FNS = _osreg_muln_

BN_KAR_NS  = KAR::
BN_KAR_FNS = _kar_muln_

BN_EXP_NS  = H::EXP::
BN_EXP_FNS = _expm_noct_ _expmU_noct_ _expm_ _expmU_ _expmLR_noct_

FP_BASE_NS  = H::FP::
FP_BASE_FNS = _chk_bnds_ _addm_ _addmU_ _subm_ _submU_ _mulm_ _mulmU_ _sqrm_ _sqrmU_ _invm_ _invmU_

FP_MONT_NS  = H::FPM::
FP_MONT_FNS = fun_muln fun_sqrn _redM_ _fromM_ _toM_ _ctx_init_

xtr = $(JASMIN2EC) $(foreach fn, $(2), -f '$(1)$(fn)') -o $@ libjbn_abs.jazz

BNUTIL_bn_util.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_UTIL_NS),$(BN_UTIL_FNS))

BN_bn_base.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_BASE_NS),$(BN_BASE_FNS))

BNRND_bn_rnd.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_RND_NS),$(BN_RND_FNS))

BNMUL_bn_mul.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MUL_NS),$(BN_MUL_FNS))

BNMULL_bn_mul_loop.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MULL_NS),$(BN_MULL_FNS))

BNMULX_bn_mulx.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MULX_NS),$(BN_MULX_FNS))

BNMULXL_bn_mulx_loop.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MULXL_NS),$(BN_MULXL_FNS))

BNMULXR_bn_mulxr.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MULXR_NS),$(BN_MULXR_FNS))

BNMULSEL_bn_mulsel.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MULSEL_NS),$(BN_MULSEL_FNS))

BNMULREG_bn_mulreg.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_MULREG_NS),$(BN_MULREG_FNS))

BNKAR_bn_karatsuba.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_KAR_NS),$(BN_KAR_FNS))

BNE_bn_exp.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(BN_EXP_NS),$(BN_EXP_FNS))

FP_fp_base.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(FP_BASE_NS),$(FP_BASE_FNS))

FPM_fp_mont.ec: $(HARNESS) $(LIBJBN_SRC)
	$(call xtr,$(FP_MONT_NS),$(FP_MONT_FNS))

clean:
	rm -f Array*.ec WArray*.ec *~

realclean: clean
	rm -f $(MJAZZ_EC)
