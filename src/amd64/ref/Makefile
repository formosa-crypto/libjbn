
PWD = $(shell pwd)
SRCDIR = $(PWD)

PROCMJAZZ = $(PWD)/../../../scripts/mjazz_proc.py
MJAZZDIR = $(PWD)/mjazz_extracted

GCC ?= arch -x86_64 gcc
JASMINC = jasminc
JASMINC_OPT = -I Libjbn:$(SRCDIR)

MJAZZ_FILES = $(MJAZZDIR)/BNUTIL_bn_util.jinc $(MJAZZDIR)/BN_bn_base.jinc $(MJAZZDIR)/BNRND_bn_rnd.jinc $(MJAZZDIR)/BNE_bn_exp.jinc $(MJAZZDIR)/FP_fp_base.jinc $(MJAZZDIR)/FPM_fp_mont.jinc


all: $(MJAZZ_FILES)

$(MJAZZ_FILES): extracted.keys
	python3 $(PROCMJAZZ) `basename $< .keys`

extract: $(MJAZZ_FILES)
	(cd $(MJAZZDIR); make; make clean)

clean:
	rm -f $(MJAZZ_FILES)

realclean: clean
	(cd $(MJAZZDIR); make realclean)
