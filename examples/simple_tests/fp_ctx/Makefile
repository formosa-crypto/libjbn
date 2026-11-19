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
# the same instances with row-looped multiplication and reduction
# (bn_mul_loop in the place of bn_mul): same entry points, same vectors
PROGS = $(addprefix test_fp_ctx, $(SIZES)) $(addprefix test_fp_ctx_loop, $(SIZES))
# and with the MULX/ADCX/ADOX modules, bn_mulx_loop (looped rows) and bn_mulx
# (unrolled): these only run on a CPU with BMI2 and ADX (not under Rosetta),
# hence the separate target run-mulx
MULX_PROGS = $(addprefix test_fp_ctx_mulx_loop, $(SIZES)) $(addprefix test_fp_ctx_mulx, $(SIZES))

all: $(PROGS) $(MULX_PROGS)

# (the more specific patterns first: make 3.81 takes the first match)
test_fp_ctx_mulx_loop%: test_fp_ctx.c fp_ctx_mulx_loop%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_mulx%: test_fp_ctx.c fp_ctx_mulx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_loop%: test_fp_ctx.c fp_ctx_loop%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx%: test_fp_ctx.c fp_ctx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

vectors%.txt: gen_vectors.py
	python3 gen_vectors.py $* > $@

run: $(PROGS) $(addprefix vectors, $(addsuffix .txt, $(SIZES)))
	for n in $(SIZES); do ./test_fp_ctx$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_loop$$n < vectors$$n.txt || exit 1; done

run-mulx: $(MULX_PROGS) $(addprefix vectors, $(addsuffix .txt, $(SIZES)))
	for n in $(SIZES); do ./test_fp_ctx_mulx_loop$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_mulx$$n < vectors$$n.txt || exit 1; done

%.s: %.jazz $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

# Timing of the multiplication modules: bn_mul (unr), bn_mul_loop (loop),
# bn_mulx (mulx_unr) and bn_mulx_loop (mulx); the last two need BMI2 and ADX,
# so they do not run under Rosetta.
# The instances (tmpbench_<variant>_<size>.*) are generated from fp_ctx7.jazz.
BENCH_SIZES    ?= 4 8 16 32 64
BENCH_VARIANTS ?= unr loop mulx_unr mulx

bench: bench_fp_ctx.c fp_ctx7.jazz $(LIBJBN_SRC)
	@for n in $(BENCH_SIZES); do for v in $(BENCH_VARIANTS); do \
	  case $$v in \
	    unr)      m=bn_mul;       s=fp_mul_ps;; \
	    loop)     m=bn_mul_loop;  s=fp_mul_os;; \
	    mulx_unr) m=bn_mulx;      s=fp_mul_os;; \
	    mulx)     m=bn_mulx_loop; s=fp_mul_os;; \
	    *) echo "unknown variant $$v"; exit 1;; \
	  esac; \
	  f=tmpbench_$${v}_$$n; \
	  sed -e "s/param int nlimbs = 7;/param int nlimbs = $$n;/" \
	      -e "s/bn_mul@n.jinc/$$m@n.jinc/" -e "s/fp_mul_ps@fp.jinc/$$s@fp.jinc/" \
	      fp_ctx7.jazz > $$f.jazz; \
	  $(JASMINC) $(JFLAGS) -o $$f.s $$f.jazz 2> $$f.log || { cat $$f.log; exit 1; }; \
	  $(GCC) -O2 -DNLIMBS=$$n -DVARIANT=\"$$v\" -o $$f bench_fp_ctx.c $$f.s || exit 1; \
	  ./$$f || echo "$$v n=$$n: did not run (the mulx variants need a CPU with BMI2 and ADX)"; \
	done; done

.PRECIOUS: fp_ctx%.s

clean:
	rm -f $(PROGS) $(MULX_PROGS) fp_ctx*.s vectors*.txt tmpbench_*

realclean: clean
