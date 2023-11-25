PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

PROCMJAZZ = $(PWD)/../../../scripts/mjazz_proc.py
MJAZZDIRPREFIX = $(PWD)/

JASMINC ?= jasminc -lazy-regalloc -I Libjbn:$(SRCDIR)
GCC ?= arch -x86_64 gcc

.DEFAULT_GOAL := all

PROGS = testmul_ps_32 testmul_os_32 testmul_kar_32_ps_16

all: $(PROGS)

testmul_ps_32: testmul_ps_32.c muln32.s
	$(GCC) -o $@ $^

testmul_os_32: testmul_os_32.c muln32.s
	$(GCC) -o $@ $^

testmul_kar_32_ps_16: testmul_kar_32_ps_16.c kar_32_ps_16.s
	$(GCC) -o $@ $^

%.s: %.jinc
	python3 $(PROCMJAZZ) `basename $< .jinc`
	$(JASMINC) $(JFLAGS) -I MJazz:$(MJAZZDIRPREFIX)`basename $< .jinc` -o $@ $<

clean:
	rm -f $(PROGS) *.s

realclean: clean
	rm -rf muln32/ kar_32_ps_16/
