PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

PROCMJAZZ = $(PWD)/../../../scripts/mjazz_proc.py
MJAZZDIRPREFIX = $(PWD)/mjazz_

JASMINC ?= jasminc -I Libjbn:$(SRCDIR)
GCC ?= arch -x86_64 gcc

.DEFAULT_GOAL := all

PROGS = test_bn_sike751 test_bn_sike610 test_bn_sike503 test_bn_sike434

all: $(PROGS)

test_bn_sike751: test_bn_sike751.c bn_sike751.s
	$(GCC) -o $@ $^

test_bn_sike610: test_bn_sike610.c bn_sike610.s
	$(GCC) -o $@ $^

test_bn_sike503: test_bn_sike503.c bn_sike503.s
	$(GCC) -o $@ $^

test_bn_sike434: test_bn_sike434.c bn_sike434.s
	$(GCC) -o $@ $^


%.s: %.jinc
	python3 $(PROCMJAZZ) `basename $< .jinc`
	$(JASMINC) $(JFLAGS) -I MJazz:$(MJAZZDIRPREFIX)`basename $< .jinc` -o $@ $<

clean:
	rm -f $(PROGS) bn_sike???.s

realclean: clean
	rm -rf mjazz_bn_sike???
