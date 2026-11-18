PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

# libjbn library modules (rebuild when they change)
LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc $(SRCDIR)/params/*/*.jinc)

# x86-64 C compiler (on macOS/Apple Silicon: cross-compile, run under Rosetta)
ifeq ($(shell uname -s),Darwin)
GCC ?= gcc -arch x86_64
else
GCC ?= gcc
endif

JASMINC = jasminc
JASMINC_OPT = -lazy-regalloc -I Libjbn=$(SRCDIR)

all: test_schnorr

schnorr.s: schnorr.jazz bn_modp2048.jinc $(LIBJBN_SRC)
	$(JASMINC) $(JASMINC_OPT) schnorr.jazz -o schnorr.s



test_schnorr : test_schnorr.c schnorr.s schnorr_protocol.h
	$(GCC) -o test_schnorr test_schnorr.c schnorr.s ./syscalls/jasmin_syscall.c

clean:
	rm -f schnorr.s test_schnorr

realclean: clean
