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

PROGS = test_rsapss

all: $(PROGS)

test_rsapss: test_rsapss.c rsapss.s
	$(GCC) -o $@ $^


%.s: %.jazz rsa_keys.jinc rsa_key_p@fp.jinc rsa_key_q@fp.jinc rsa_key_n@fp.jinc rsa_crt@fp.jinc $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

clean:
	rm -f $(PROGS) rsapss.s

realclean: clean
