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

SIZES = 7 16
PROGS = $(addprefix test_fp_ctx, $(SIZES))

all: $(PROGS)

test_fp_ctx%: test_fp_ctx.c fp_ctx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

vectors%.txt: gen_vectors.py
	python3 gen_vectors.py $* > $@

run: $(PROGS) $(addprefix vectors, $(addsuffix .txt, $(SIZES)))
	for n in $(SIZES); do ./test_fp_ctx$$n < vectors$$n.txt || exit 1; done

%.s: %.jazz $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

.PRECIOUS: fp_ctx%.s

clean:
	rm -f $(PROGS) fp_ctx*.s vectors*.txt

realclean: clean
