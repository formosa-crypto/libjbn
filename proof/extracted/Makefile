
PWD = $(shell pwd)
SRCDIR = $(PWD)/../../src/amd64/ref


JASMINC = jasminc -lazy-regalloc -I MJazz:.
JASMINC_OPT = -I Libjbn:$(SRCDIR)

MJAZZ_EC = FPM_fp_mont.ec

MJAZZ_EC_CT = FPM_fp_mont_CT.ec


all: $(MJAZZ_EC) $(MJAZZ_EC_CT)

BN_BASE_FNS = _load_ _store_ _eq_ _pack2_

BN_RND_FNS = _rnd_ _rsample_

BN_EXP_FNS =  _expm_noct_ _expmU_noct_ _expm_ _expmU_

FP_BASE_FNS = _chk_bnds_ _rnd_ _addm_ _addmU_ _subm_ _submU_ _mulm_ _mulmU_ _sqrm_ _sqrmU_ _invmU_

FP_MONT_FNS = _redM_ _fromM_ _toM_

ALL_BN_FNS = $(BN_BASE_FNS) $(BN_RND_FNS)

ALL_FPM_FNS = $(BN_EXP_FNS) $(FP_BASE_FNS) $(FP_MONT_FNS)

ALL_EC = $(foreach fn, $(ALL_BN_FNS), -ec BN$(fn)) $(foreach fn, $(ALL_FPM_FNS), -ec FPM$(fn))


%.pjinc: %.jinc
	echo $(ALL_BN_FNS)
	echo $(ALL_FPM_FNS)
	cat preamb.jinc $< > $@

FPM_fp_mont.ec: FPM_fp_mont.pjinc
	$(JASMINC) $(ALL_EC) -oec $@  $<

FPM_fp_mont_CT.ec: FPM_fp_mont.pjinc
	$(JASMINC) -CT $(ALL_EC) -oec $@  $<

clean:
	rm -f *.pjinc Array*.ec WArray*.ec *~

realclean: clean
	rm -f $(MJAZZ_EC)
