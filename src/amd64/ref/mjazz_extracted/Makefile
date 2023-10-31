
PWD = $(shell pwd)
SRCDIR = $(PWD)/..


JASMINC = jasminc -I MJazz:.
JASMINC_OPT = -I Libjbn:$(SRCDIR)

MJAZZ_EC = BNUTIL_bn_util.ec BN_bn_base.ec BNRND_bn_rnd.ec BNE_bn_exp.ec FP_fp_base.ec FPM_fp_mont.ec

MJAZZ_EC_CT = BNUTIL_bn_util_CT.ec BN_bn_base_CT.ec BNRND_bn_rnd_CT.ec BNE_bn_exp_CT.ec FP_fp_base_CT.ec FPM_fp_mont_CT.ec


all: $(MJAZZ_EC) $(MJAZZ_EC_CT)

BN_UTIL_FNS = __mask_zf __mask_cf __cf_mask __addacc3 __addacc3x2

BN_BASE_FNS = _load_ _store_ _eq_ _test0_ __copy _mov_ _cmov_ _cswap_cf_ _set0_ __cfill _or_mask_ _and_mask_ _set_err_ __carrypropU _addcU_ _addU_ _addc_ _add_ _subcU_ _subU_ _subc_ _sub_ _lt_cf_ _ltc_cf_ _negU_ _negcU_ _neg_ _negc_ _cnegU_ _caddU_ _muln_ _sqrn_ _cminusP_ __mont_redM _pack2_

BN_RND_FNS = _rnd_ _rsample_

BN_EXP_FNS =  _expm_noct_ _expmU_noct_ _expm_ _expmU_

FP_BASE_FNS = _chk_bnds_ _addm_ _addmU_ _subm_ _submU_ _mulm_ _mulmU_ _sqrm_ _sqrmU_ _invmU_

FP_MONT_FNS = _redM_ _fromM_ _toM_

%.pjinc: %.jinc
	cat preamb.jinc $< > $@

BNUTIL_bn_util.ec: BNUTIL_bn_util.pjinc
	$(JASMINC) $(foreach fn, $(BN_UTIL_FNS), -ec BNUTIL$(fn)) -oec $@  $<

BNUTIL_bn_util_CT.ec: BNUTIL_bn_util.pjinc
	$(JASMINC) -CT $(foreach fn, $(BN_UTIL_FNS), -ec BNUTIL$(fn)) -oec $@  $<

BN_bn_base.ec: BN_bn_base.pjinc
	$(JASMINC) $(foreach fn, $(BN_BASE_FNS), -ec BN$(fn)) -oec $@  $<

BN_bn_base_CT.ec: BN_bn_base.pjinc
	$(JASMINC) -CT $(foreach fn, $(BN_BASE_FNS), -ec BN$(fn)) -oec $@  $<

BNRND_bn_rnd.ec: BNRND_bn_rnd.pjinc
	$(JASMINC) $(foreach fn, $(BN_RND_FNS), -ec BNRND$(fn)) -oec $@  $<

BNRND_bn_rnd_CT.ec: BNRND_bn_rnd.pjinc
	$(JASMINC) -CT $(foreach fn, $(BN_RND_FNS), -ec BNRND$(fn)) -oec $@  $<

BNE_bn_exp.ec: BNE_bn_exp.pjinc
	$(JASMINC) $(foreach fn, $(BN_EXP_FNS), -ec BNE$(fn)) -oec $@  $<

BNE_bn_exp_CT.ec: BNE_bn_exp.pjinc
	$(JASMINC) -CT $(foreach fn, $(BN_EXP_FNS), -ec BNE$(fn)) -oec $@  $<

FP_fp_base.ec: FP_fp_base.pjinc
	$(JASMINC) $(foreach fn, $(FP_BASE_FNS), -ec FP$(fn)) -oec $@  $<

FP_fp_base_CT.ec: FP_fp_base.pjinc
	$(JASMINC) -CT $(foreach fn, $(FP_BASE_FNS), -ec FP$(fn)) -oec $@  $<

FPM_fp_mont.ec: FPM_fp_mont.pjinc
	$(JASMINC) $(foreach fn, $(FP_MONT_FNS), -ec FPM$(fn)) -oec $@  $<

FPM_fp_mont_CT.ec: FPM_fp_mont.pjinc
	$(JASMINC) -CT $(foreach fn, $(FP_MONT_FNS), -ec FPM$(fn)) -oec $@  $<

clean:
	rm -f *.pjinc Array*.ec WArray*.ec *~

realclean: clean
	rm -f $(MJAZZ_EC)
