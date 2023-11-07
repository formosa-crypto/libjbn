PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

PROCMJAZZ = $(PWD)/../../../scripts/mjazz_proc.py
MJAZZDIR = $(PWD)/bn_modp2048

GCC ?= arch -x86_64 gcc

JASMINC = jasminc
JASMINC_OPT = -lazy-regalloc -I Libjbn:$(SRCDIR)

all: test_schnorr

MJAZZ_FILES = $(MJAZZDIR)/BN_bn_base.jinc $(MJAZZDIR)/FPM_bn_exp.jinc $(MJAZZDIR)/FPM_fp_base.jinc $(MJAZZDIR)/FPM_fp_mont.jinc $(MJAZZDIR)/FQM_bn_exp.jinc $(MJAZZDIR)/FQM_fp_base.jinc $(MJAZZDIR)/FQM_fp_mont.jinc

mjazz: $(MJAZZ_FILES)
$(MJAZZ_FILES): bn_modp2048.jinc
	python3 $(PROCMJAZZ) `basename $< .jinc`

schnorr.s: schnorr.jazz bn_modp2048.jinc $(MJAZZ_FILES)
	$(JASMINC) $(JASMINC_OPT) -I MJazz:$(MJAZZDIR) schnorr.jazz -o schnorr.s



test_schnorr : test_schnorr.c schnorr.s schnorr_protocol.h
	$(GCC) -o test_schnorr test_schnorr.c schnorr.s ./syscalls/jasmin_syscall.c

clean:
	rm -f schnorr.s test_schnorr

realclean: clean
	rm -rf $(MJAZZDIR)
