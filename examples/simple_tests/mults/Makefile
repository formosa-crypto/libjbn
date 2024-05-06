PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

PROCMJAZZ = $(PWD)/../../../scripts/mjazz_proc.py
MJAZZDIRPREFIX = $(PWD)/

JASMINC ?= jasminc -lazy-regalloc -I Libjbn:$(SRCDIR)
GCC ?= arch -x86_64 gcc

.DEFAULT_GOAL := all

PROGS = testmul_ps_32 testmul_os_32 testmul_kar_32_ps_16 testmul_kar_32_ps_8 testmul_kar_32_ps_4 testmul_kar_32_os_16 testmul_kar_32_os_8 testmul_kar_32_os_4 testmul_kar_32_osreg_4

all: $(PROGS)

run: $(PROGS)
	for p in $(PROGS); do time ./$$p; done

testmul_ps_32: testmul_ps_32.c muln32.s
	$(GCC) -o $@ $^

testmul_os_32: testmul_os_32.c muln32.s
	$(GCC) -o $@ $^

testmul_kar_32_ps_16: testmul_kar_32_ps_16.c kar_32_ps_16.s
	$(GCC) -o $@ $^

testmul_kar_32_ps_8: testmul_kar_32_ps_8.c kar_32_ps_8.s
	$(GCC) -o $@ $^

testmul_kar_32_ps_4: testmul_kar_32_ps_4.c kar_32_ps_4.s
	$(GCC) -o $@ $^

testmul_kar_32_os_16: testmul_kar_32_os_16.c kar_32_os_16.s
	$(GCC) -o $@ $^

testmul_kar_32_os_8: testmul_kar_32_os_8.c kar_32_os_8.s
	$(GCC) -o $@ $^

testmul_kar_32_os_4: testmul_kar_32_os_4.c kar_32_os_4.s
	$(GCC) -o $@ $^

testmul_kar_32_osreg_4: testmul_kar_32_osreg_4.c kar_32_osreg_4.s
	$(GCC) -o $@ $^

%.s: %.jinc
	python3 $(PROCMJAZZ) `basename $< .jinc`
	$(JASMINC) $(JFLAGS) -I MJazz:$(MJAZZDIRPREFIX)`basename $< .jinc` -o $@ $<

clean:
	rm -f $(PROGS)

realclean: clean
	rm -rf *.s *~ muln32/ kar_32_ps_16/ kar_32_ps_8/ kar_32_ps_4/ kar_32_os_16/ kar_32_os_8/ kar_32_os_4/ kar_32_osreg_4/
