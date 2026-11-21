PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

# libjbn library modules (rebuild instances when they change)
LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc $(SRCDIR)/params/*/*.jinc $(SRCDIR)/profiles/*.jinc)

# the example's own sources: sizes and key layout, the key pair, the RSA code
EXAMPLE_SRC = rsa2048_params.jinc rsa_keys.jinc rsa2048@libjbn.jinc

JASMINC ?= jasminc -lazy-regalloc -I Libjbn=$(SRCDIR)
# x86-64 C compiler (on macOS/Apple Silicon: cross-compile, run under Rosetta)
ifeq ($(shell uname -s),Darwin)
GCC ?= gcc -arch x86_64
else
GCC ?= gcc
endif

.DEFAULT_GOAL := all

PROGS = test_rsa2048

all: $(PROGS)

test_rsa2048: test_rsa2048.c rsa2048.s
	$(GCC) -o $@ $^

run: test_rsa2048
	./test_rsa2048

%.s: %.jazz $(EXAMPLE_SRC) $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

clean:
	rm -f $(PROGS) rsa2048.s test_rsapss rsapss.s

realclean: clean

.PHONY: all run clean realclean
