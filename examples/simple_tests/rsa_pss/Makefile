PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

PROCMJAZZ = $(PWD)/../../../scripts/mjazz_proc.py
MJAZZDIRPREFIX = $(PWD)/

JASMINC ?= jasminc -lazy-regalloc -I Libjbn:$(SRCDIR)
GCC ?= arch -x86_64 gcc

.DEFAULT_GOAL := all

PROGS = test_rsapss

all: $(PROGS)

test_rsapss: test_rsapss.c rsapss.s
	$(GCC) -o $@ $^


%.s: %.jinc rsa_keys.jinc
	python3 $(PROCMJAZZ) `basename $< .jinc`
	$(JASMINC) $(JFLAGS) -I MJazz:$(MJAZZDIRPREFIX)`basename $< .jinc` -o $@ $<

clean:
	rm -f $(PROGS) rsapss.s

realclean: clean
	rm -rf rsapss/
