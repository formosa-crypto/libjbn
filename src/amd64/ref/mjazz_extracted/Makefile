
PWD = $(shell pwd)
SRCDIR = $(PWD)/..


JASMINC = jasminc -I MJazz:.
JASMINC_OPT = -I Libjbn:$(SRCDIR)

MJAZZ_EC = BN_bn_base.ec BNE_bn_exp.ec FP_fp_base.ec FPM_fp_mont.ec


all: $(MJAZZ_EC)

BN_BASE_FNS = BNUTIL__cf_mask BN__cswap_mask BN__load BN__store BN_eq_ BN_test0 BN__copy BN__copy2 BN__cmov BN__set0 BN__cfill BN__set_err BN__carrypropU BN_addU BN_add BN__lt_cf BN__negU BN__neg BN_subU BN_sub BN__rnd BN__rsample BN__subU_signabs BN__cnegU BN__caddU BN_muln BN_sqrn BN__cminusP BN__mont_redM BN__pack2

FP_BASE_FNS = FP__chk_bnds FP_addmU FP_submU FP_mulm FP_mulmU FP_sqrm FP_sqrmU FP__invm

FP_MONT_FNS = FPM_redM FPM__fromM FPM__toM

BN_EXP_FNS = BNE_expm_noct BNE_expm

%.pjinc: %.jinc
	cat preamb.jinc $< > $@

BN_bn_base.ec: BN_bn_base.pjinc
	$(JASMINC) $(foreach fn, $(BN_BASE_FNS), -ec $(fn)) -oec $@  $<

BNE_bn_exp.ec: BNE_bn_exp.pjinc
	$(JASMINC) $(foreach fn, $(BN_EXP_FNS), -ec $(fn)) -oec $@  $<

FP_fp_base.ec: FP_fp_base.pjinc
	$(JASMINC) $(foreach fn, $(FP_BASE_FNS), -ec $(fn)) -oec $@  $<

FPM_fp_mont.ec: FPM_fp_mont.pjinc
	$(JASMINC) $(foreach fn, $(FP_MONT_FNS), -ec $(fn)) -oec $@  $<

%.ec: %.jinc
	$(JASMINC) 

clean:
	rm -f *.pjinc Array*.ec WArray*.ec

realclean: clean
	rm -f $(MJAZZ_EC)
