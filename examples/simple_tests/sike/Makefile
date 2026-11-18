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


%.s: %.jinc $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

clean:
	rm -f $(PROGS) bn_sike???.s

realclean: clean
