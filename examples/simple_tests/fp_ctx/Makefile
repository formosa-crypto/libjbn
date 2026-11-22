PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64/ref

# libjbn library modules (rebuild instances when they change)
LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc $(SRCDIR)/params/*/*.jinc $(SRCDIR)/profiles/*.jinc)

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
# the selector bn_mulsel, with a profile (fp_ctx_sel*: x86_64, in `run`;
# fp_ctx_selx*: x86_64_adx, in `run-mulx`); the 16-limb instances shadow
# the threshold, so that the four modules are selected once each
PROGS += $(addprefix test_fp_ctx_sel, $(SIZES))
MULX_PROGS += $(addprefix test_fp_ctx_selx, $(SIZES))
# bn_mulxr (MULX/ADCX/ADOX rows with the accumulator in registers), which
# fits the registers of a field up to 6 limbs, hence sizes of its own
XR_SIZES = 4 5 6
MULX_PROGS += $(addprefix test_fp_ctx_mulxr, $(XR_SIZES))
# pseudo-Mersenne fields (fp_pm: 2^255-19 at 4 limbs, R - c, R/2 - c), over
# bn_mul (fp_ctx_pm*, in `run`) and over bn_mulxr (fp_ctx_pmxr*, in
# `run-mulx`), with vectors of their own (vectors_pm*.txt)
PM_SIZES = 4 6
PROGS += $(addprefix test_fp_ctx_pm, $(PM_SIZES))
MULX_PROGS += $(addprefix test_fp_ctx_pmxr, $(PM_SIZES))

all: $(PROGS) $(MULX_PROGS)

# (the more specific patterns first: make 3.81 takes the first match)
test_fp_ctx_pmxr%: test_fp_ctx.c fp_ctx_pmxr%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_pm%: test_fp_ctx.c fp_ctx_pm%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_mulxr%: test_fp_ctx.c fp_ctx_mulxr%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_selx%: test_fp_ctx.c fp_ctx_selx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_sel%: test_fp_ctx.c fp_ctx_sel%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_mulx_loop%: test_fp_ctx.c fp_ctx_mulx_loop%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_mulx%: test_fp_ctx.c fp_ctx_mulx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_loop%: test_fp_ctx.c fp_ctx_loop%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx%: test_fp_ctx.c fp_ctx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

vectors_pm%.txt: gen_vectors.py
	python3 gen_vectors.py $* 1 pm > $@

vectors%.txt: gen_vectors.py
	python3 gen_vectors.py $* > $@

PM_VECTORS = $(addprefix vectors_pm, $(addsuffix .txt, $(PM_SIZES)))

run: $(PROGS) $(addprefix vectors, $(addsuffix .txt, $(SIZES))) $(PM_VECTORS)
	for n in $(SIZES); do ./test_fp_ctx$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_loop$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_sel$$n < vectors$$n.txt || exit 1; done
	for n in $(PM_SIZES); do ./test_fp_ctx_pm$$n < vectors_pm$$n.txt || exit 1; done

run-mulx: $(MULX_PROGS) $(addprefix vectors, $(addsuffix .txt, $(SIZES) $(XR_SIZES))) $(PM_VECTORS)
	for n in $(SIZES); do ./test_fp_ctx_mulx_loop$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_mulx$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_selx$$n < vectors$$n.txt || exit 1; done
	for n in $(XR_SIZES); do ./test_fp_ctx_mulxr$$n < vectors$$n.txt || exit 1; done
	for n in $(PM_SIZES); do ./test_fp_ctx_pmxr$$n < vectors_pm$$n.txt || exit 1; done

# The same operations run by the interpreter of jasminc (gen_exec_test.py):
# on any host, MULX/ADCX/ADOX included (e.g. on Apple Silicon, where Rosetta
# does not run them). Each test prints the OR of the differences (0X0 when
# correct) and the number of words checked.
#   module:binding:size:f    f = 1 with the (Montgomery) field, pm with the
#                            pseudo-Mersenne field, 0 for the products only
EXEC_TESTS ?= $(foreach n,1 2 3 4 5 6,bn_mulxr:fp_mul_os:$(n):1) \
              bn_mulxr:fp_mul_os:7:0 bn_mulxr:fp_mul_os:8:0 \
              bn_mulx:fp_mul_os:4:1 bn_mulx_loop:fp_mul_os:4:1 \
              bn_mul_loop:fp_mul_os:4:1 bn_mul:fp_mul_ps:4:1 \
              bn_mulxr:fp_mul_os:4:pm bn_mulxr:fp_mul_os:6:pm bn_mul:fp_mul_ps:4:pm
JASMINC_EXEC ?= jasminc -I Libjbn=$(SRCDIR)

exec: gen_exec_test.py $(LIBJBN_SRC)
	@for t in $(EXEC_TESTS); do \
	  set -- $$(echo $$t | tr ':' ' '); \
	  f=""; [ "$$4" = 1 ] && f=--field; [ "$$4" = pm ] && f="--field --pm"; \
	  j=tmpexec_$$1_$$3_$$4.jazz; \
	  python3 gen_exec_test.py $$3 $$1@n.jinc $$2@fp.jinc $$f --seed $$3 > $$j || exit 1; \
	  res=$$($(JASMINC_EXEC) -o /dev/null $$j 2>&1 | awk '/Evaluation/{getline a; getline b; print a, b}'); \
	  echo "$$1 n=$$3 $${f:-(products)}: $$res"; \
	  case "$$res" in "0X0 "*) ;; *) echo "FAILED"; exit 1;; esac; \
	done

%.s: %.jazz $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

# Timing of the multiplication modules: bn_mul (unr), bn_mul_loop (loop),
# bn_mulx (mulx_unr), bn_mulx_loop (mulx) and bn_mulxr (mulxr, up to 6
# limbs); and of the pseudo-Mersenne field fp_pm, modulus 2^(64n-1)-19
# (2^255-19 at 4 limbs), over bn_mul (pm_unr, to be compared with unr) and
# over bn_mulxr (pm_mulxr, up to 6 limbs, to be compared with mulxr). The
# variants over bn_mulx, bn_mulx_loop and bn_mulxr need BMI2 and ADX, so
# they do not run under Rosetta. The instances
# (tmpbench_<variant>_<size>.*) are generated from fp_ctx7.jazz, with the
# profile of their module (x86_64 or x86_64_adx).
# fpc_mul and fpc_sqr are timed on the same arguments at each call, so that
# consecutive calls may overlap (throughput); with BENCH_CHAINED=1, each
# call takes the result of the previous one (latency, as in fpc_exp), and
# the lines end with "(chained)". The two constant-time exponentiations are
# timed on the same operands: fpc_exp (the one of the profile: the fixed
# window) and fpc_exp_ladder.
BENCH_SIZES    ?= 4 5 6 8 16 32 64
BENCH_VARIANTS ?= unr loop mulx_unr mulx mulxr pm_unr pm_mulxr
BENCH_CHAINED  ?=

bench: bench_fp_ctx.c fp_ctx7.jazz $(LIBJBN_SRC)
	@for n in $(BENCH_SIZES); do for v in $(BENCH_VARIANTS); do \
	  k=fp_mont; p=x86_64; \
	  case $$v in \
	    unr)      m=bn_mul;       s=fp_mul_ps;; \
	    loop)     m=bn_mul_loop;  s=fp_mul_os;; \
	    mulx_unr) m=bn_mulx;      s=fp_mul_os; p=x86_64_adx;; \
	    mulx)     m=bn_mulx_loop; s=fp_mul_os; p=x86_64_adx;; \
	    mulxr)    m=bn_mulxr;     s=fp_mul_os; p=x86_64_adx; [ $$n -le 6 ] || continue;; \
	    pm_unr)   m=bn_mul;       s=fp_mul_ps; k=fp_pm;; \
	    pm_mulxr) m=bn_mulxr;     s=fp_mul_os; k=fp_pm; p=x86_64_adx; [ $$n -le 6 ] || continue;; \
	    *) echo "unknown variant $$v"; exit 1;; \
	  esac; \
	  f=tmpbench_$${v}_$$n; \
	  sed -e "s/param int nlimbs = 7;/param int nlimbs = $$n;/" \
	      -e "s/bn_mul@n.jinc/$$m@n.jinc/" -e "s/fp_mul_ps@fp.jinc/$$s@fp.jinc/" \
	      -e "s/fp_mont@fp.jinc/$$k@fp.jinc/" \
	      -e "s|profiles/x86_64.jinc|profiles/$$p.jinc|" \
	      fp_ctx7.jazz > $$f.jazz; \
	  $(JASMINC) $(JFLAGS) -o $$f.s $$f.jazz 2> $$f.log || { cat $$f.log; exit 1; }; \
	  pm=; [ $$k = fp_pm ] && pm=-DPM; \
	  $(GCC) -O2 -DNLIMBS=$$n -DVARIANT=\"$$v\" $$pm $(if $(BENCH_CHAINED),-DCHAINED) -o $$f bench_fp_ctx.c $$f.s || exit 1; \
	  ./$$f || echo "$$v n=$$n: did not run (the variants over bn_mulx, bn_mulx_loop and bn_mulxr need a CPU with BMI2 and ADX)"; \
	done; done

# GMP's exponentiations at the same sizes and on the same operands, as a
# reference for fpc_exp (bench_gmp.c: mpz_powm_sec, its core mpn_sec_powm,
# mpz_powm, and the products mpn_sec_mul/mpn_sec_sqr alone). It needs the
# GMP of the host (no Jasmin code is linked, so that it is a native program
# on any host); where GMP is not on the default paths, e.g.
#   make bench-gmp GMP_FLAGS="-I/opt/homebrew/include -L/opt/homebrew/lib"
GMP_CC    ?= cc
GMP_FLAGS ?=
bench-gmp: bench_gmp.c
	$(GMP_CC) -O2 $(GMP_FLAGS) -o tmpbench_gmp bench_gmp.c -lgmp
	./tmpbench_gmp $(BENCH_SIZES)

.PRECIOUS: fp_ctx%.s

clean:
	rm -f $(PROGS) $(MULX_PROGS) fp_ctx*.s vectors*.txt tmpbench_* tmpexec_*

realclean: clean
