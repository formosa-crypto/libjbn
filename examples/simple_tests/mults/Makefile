PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

# libjbn library modules (rebuild instances when they change)
LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc $(SRCDIR)/params/*/*.jinc)

JASMINC ?= jasminc -lazy-regalloc -I Libjbn=$(SRCDIR)
# x86-64 C compiler (on macOS/Apple Silicon: cross-compile, run under Rosetta)
ifeq ($(shell uname -s),Darwin)
GCC ?= gcc -arch x86_64
else
GCC ?= gcc
endif

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

%.s: %.jinc $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

clean:
	rm -f $(PROGS)

realclean: clean
	rm -f *.s *~
