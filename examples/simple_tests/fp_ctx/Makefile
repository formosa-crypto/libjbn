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
# bn_mulx_loop with the squaring of bn_mulx (fp_ctx_mulx_sqru7.jazz: an
# experiment, see its header and the bench variant mulx_sqru), in `run-mulx`
MULX_PROGS += test_fp_ctx_mulx_sqru7
# bn_mulx_loop with the looped squaring of bn_sqrx_loop, a prototype
# (fp_ctx_mulx_sqrl7.jazz: see its header and the bench variants
# mulx_sqrl<G>, mulx_sqrl<G>s), in `run-mulx`
MULX_PROGS += test_fp_ctx_mulx_sqrl7
# the squaring that the binding fp_mul_ksqr selects, between the one of the
# selector and the squaring over the half size (bn_ksqr): fp_ctx_ksqr16
# (profile x86_64, in `run`), fp_ctx_ksqrx16 and, with two levels of half
# scopes, fp_ctx_ksqrx2_16 (x86_64_adx, in `run-mulx`). They shadow the
# threshold of the profile, so that the tests run bn_ksqr at 16 limbs; see
# their headers and the bench variants ksqr, ksqrx, ksqrx2
PROGS += test_fp_ctx_ksqr16
MULX_PROGS += test_fp_ctx_ksqrx16 test_fp_ctx_ksqrx2_16

all: $(PROGS) $(MULX_PROGS)

# (the more specific patterns first: make 3.81 takes the first match)
test_fp_ctx_mulx_sqru%: test_fp_ctx.c fp_ctx_mulx_sqru%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_mulx_sqrl%: test_fp_ctx.c fp_ctx_mulx_sqrl%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_ksqrx2_%: test_fp_ctx.c fp_ctx_ksqrx2_%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_ksqrx%: test_fp_ctx.c fp_ctx_ksqrx%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

test_fp_ctx_ksqr%: test_fp_ctx.c fp_ctx_ksqr%.s
	$(GCC) -DNLIMBS=$* -o $@ $^

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
	./test_fp_ctx_ksqr16 < vectors16.txt

run-mulx: $(MULX_PROGS) $(addprefix vectors, $(addsuffix .txt, $(SIZES) $(XR_SIZES))) $(PM_VECTORS)
	for n in $(SIZES); do ./test_fp_ctx_mulx_loop$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_mulx$$n < vectors$$n.txt || exit 1; done
	for n in $(SIZES); do ./test_fp_ctx_selx$$n < vectors$$n.txt || exit 1; done
	for n in $(XR_SIZES); do ./test_fp_ctx_mulxr$$n < vectors$$n.txt || exit 1; done
	for n in $(PM_SIZES); do ./test_fp_ctx_pmxr$$n < vectors_pm$$n.txt || exit 1; done
	./test_fp_ctx_mulx_sqru7 < vectors7.txt
	./test_fp_ctx_mulx_sqrl7 < vectors7.txt
	./test_fp_ctx_ksqrx16 < vectors16.txt
	./test_fp_ctx_ksqrx2_16 < vectors16.txt

# The same operations run by the interpreter of jasminc (gen_exec_test.py):
# on any host, MULX/ADCX/ADOX included (e.g. on Apple Silicon, where Rosetta
# does not run them). Each test prints the OR of the differences (0X0 when
# correct) and the number of words checked.
#   module:binding:size:f    f = 1 with the (Montgomery) field, pm with the
#                            pseudo-Mersenne field, 0 for the products only
#   module:binding:size:f:levels:profile[:max]
#                            the same with the squaring over the half size
#                            (bn_ksqr, with 1 or 2 levels of half scopes,
#                            over the selector bn_mulsel and the binding
#                            fp_mul_ksqr), under a profile of
#                            src/amd64/ref/profiles; max, if given, shadows
#                            JBN_SQR_UNROLL_MAX in the size scope, so that
#                            the binding (and, with 2 levels, the half
#                            scope) takes bn_ksqr at a small size
# (the last entries: the field at 4 limbs, since at 8 it takes the
# interpreter 5 minutes; at 48 limbs the multiplication is the looped one
# and the half squaring the unrolled one, which is what the profile selects
# there)
EXEC_TESTS ?= $(foreach n,1 2 3 4 5 6,bn_mulxr:fp_mul_os:$(n):1) \
              bn_mulxr:fp_mul_os:7:0 bn_mulxr:fp_mul_os:8:0 \
              bn_mulx:fp_mul_os:4:1 bn_mulx_loop:fp_mul_os:4:1 \
              bn_mul_loop:fp_mul_os:4:1 bn_mul:fp_mul_ps:4:1 \
              bn_mulxr:fp_mul_os:4:pm bn_mulxr:fp_mul_os:6:pm bn_mul:fp_mul_ps:4:pm \
              bn_mulsel:fp_mul_ksqr:4:1:1:x86_64_adx:2 \
              bn_mulsel:fp_mul_ksqr:16:0:1:x86_64_adx \
              bn_mulsel:fp_mul_ksqr:16:0:2:x86_64_adx:4 \
              bn_mulsel:fp_mul_ksqr:48:0:1:x86_64_adx
# The looped squaring of bn_sqrx_loop (a prototype), next to bn_mulx_loop:
#   size:f:group:tail        f as above; group: the products per group of a
#                            row; tail: 1 for groups of group/2, .., 1
#                            products, 0 for single products
# (the products at the sizes around one and two groups, so that every length
# of the tail is run; the field at 4 limbs)
EXEC_SQRL_TESTS ?= $(foreach n,1 2 3 4 5 6 7 8 9 13 16 17 32 33,$(n):0:4:1) \
                   9:0:4:0 17:0:8:1 17:0:8:0 33:0:16:1 33:0:16:0 4:1:4:1
JASMINC_EXEC ?= jasminc -I Libjbn=$(SRCDIR)

exec: gen_exec_test.py $(LIBJBN_SRC)
	@for t in $(EXEC_TESTS); do \
	  set -- $$(echo $$t | tr ':' ' '); \
	  f=""; [ "$$4" = 1 ] && f=--field; [ "$$4" = pm ] && f="--field --pm"; \
	  k=""; [ -n "$$5" ] && k="--ksqr $$5 --profile $$6.jinc $${7:+--sqr-unroll-max $$7}"; \
	  j=tmpexec_$$1_$$3_$$4$${5:+_ksqr$$5}.jazz; \
	  python3 gen_exec_test.py $$3 $$1@n.jinc $$2@fp.jinc $$f $$k --seed $$3 > $$j || exit 1; \
	  res=$$($(JASMINC_EXEC) -o /dev/null $$j 2>&1 | awk '/Evaluation/{getline a; getline b; print a, b}'); \
	  echo "$$1 n=$$3 $${f:-(products)}$${5:+, bn_ksqr ($$5 level(s), $$6$${7:+, JBN_SQR_UNROLL_MAX = $$7})}: $$res"; \
	  case "$$res" in "0X0 "*) ;; *) echo "FAILED"; exit 1;; esac; \
	done
	@for t in $(EXEC_SQRL_TESTS); do \
	  set -- $$(echo $$t | tr ':' ' '); \
	  f=""; [ "$$2" = 1 ] && f=--field; \
	  j=tmpexec_sqrl_$$1_$$2_$$3_$$4.jazz; \
	  python3 gen_exec_test.py $$1 bn_mulx_loop@n.jinc fp_mul_os@fp.jinc $$f --sqrl $$3:$$4 --seed $$1 > $$j || exit 1; \
	  res=$$($(JASMINC_EXEC) -o /dev/null $$j 2>&1 | awk '/Evaluation/{getline a; getline b; print a, b}'); \
	  echo "bn_sqrx_loop n=$$1 $${f:-(products)}, groups of $$3, tail $$4: $$res"; \
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
# The variants above wire a module directly. Two more are what the selector
# bn_mulsel takes at each size, from a profile: sel (x86_64, generated from
# fp_ctx_sel7.jazz) and selx (x86_64_adx, from fp_ctx_selx7.jazz, which
# needs BMI2 and ADX); each should equal the best direct variant of its
# instruction set.
# One more variant, not in the default list: mulx_sqru, bn_mulx_loop with
# the unrolled squaring of bn_mulx (generated from fp_ctx_mulx_sqru7.jazz;
# see its header), to be compared with mulx and mulx_unr, e.g.
#   make bench BENCH_VARIANTS="mulx_unr mulx mulx_sqru" BENCH_SIZES="24 32 40 48"
# The looped squaring of bn_sqrx_loop, a prototype, in the same place
# (generated from fp_ctx_mulx_sqrl7.jazz; see its header): mulx_sqrl<G>,
# with rows cut into groups of G products (1, 2, 4, 8, 16, 32) and their
# tail by groups of G/2, .., 1, and mulx_sqrl<G>s, with the tail by single
# products; not in the default list. To be compared with mulx and
# mulx_sqru, e.g.
#   make bench BENCH_VARIANTS="mulx mulx_sqru mulx_sqrl4 mulx_sqrl8 mulx_sqrl16" BENCH_SIZES="8 16 24 32 48 64"
# Three more, not in the default list either: the selector with the
# squaring that fp_mul_ksqr selects from the profile, which is the one of
# the selector up to JBN_SQR_UNROLL_MAX and the squaring over the half size
# of bn_ksqr above: ksqr (x86_64, generated from fp_ctx_ksqr16.jazz), ksqrx
# (x86_64_adx, from fp_ctx_ksqrx16.jazz) and, with two levels of half
# scopes, the second of which is taken where the half size is itself above
# the threshold, ksqrx2 (x86_64_adx, from fp_ctx_ksqrx2_16.jazz). The
# instances do not shadow the threshold, as the test wirings do; a size
# that the levels do not divide is skipped. Up to the threshold they are
# sel and selx; above, they are to be compared with them, e.g.
#   make bench BENCH_VARIANTS="mulx selx ksqrx ksqrx2" BENCH_SIZES="24 32 40 48 64 96 128"
BENCH_SIZES    ?= 4 5 6 8 16 32 64
BENCH_VARIANTS ?= unr loop mulx_unr mulx mulxr pm_unr pm_mulxr sel selx
BENCH_CHAINED  ?=

bench: bench_fp_ctx.c fp_ctx7.jazz fp_ctx_sel7.jazz fp_ctx_selx7.jazz fp_ctx_mulx_sqru7.jazz \
       fp_ctx_mulx_sqrl7.jazz \
       fp_ctx_ksqr16.jazz fp_ctx_ksqrx16.jazz fp_ctx_ksqrx2_16.jazz $(LIBJBN_SRC)
	@for n in $(BENCH_SIZES); do for v in $(BENCH_VARIANTS); do \
	  k=fp_mont; p=x86_64; t=fp_ctx7.jazz; m=bn_mul; s=fp_mul_ps; d=1; sg=4; st=1; \
	  case $$v in \
	    sel)       t=fp_ctx_sel7.jazz;; \
	    selx)      t=fp_ctx_selx7.jazz;; \
	    mulx_sqru) t=fp_ctx_mulx_sqru7.jazz;; \
	    mulx_sqrl*) t=fp_ctx_mulx_sqrl7.jazz; sg=$${v#mulx_sqrl}; \
	               case $$sg in *s) st=0; sg=$${sg%s};; esac;; \
	    ksqr)      t=fp_ctx_ksqr16.jazz;    d=2;; \
	    ksqrx)     t=fp_ctx_ksqrx16.jazz;   d=2;; \
	    ksqrx2)    t=fp_ctx_ksqrx2_16.jazz; d=4;; \
	    unr)      m=bn_mul;       s=fp_mul_ps;; \
	    loop)     m=bn_mul_loop;  s=fp_mul_os;; \
	    mulx_unr) m=bn_mulx;      s=fp_mul_os; p=x86_64_adx;; \
	    mulx)     m=bn_mulx_loop; s=fp_mul_os; p=x86_64_adx;; \
	    mulxr)    m=bn_mulxr;     s=fp_mul_os; p=x86_64_adx; [ $$n -le 6 ] || continue;; \
	    pm_unr)   m=bn_mul;       s=fp_mul_ps; k=fp_pm;; \
	    pm_mulxr) m=bn_mulxr;     s=fp_mul_os; k=fp_pm; p=x86_64_adx; [ $$n -le 6 ] || continue;; \
	    *) echo "unknown variant $$v"; exit 1;; \
	  esac; \
	  [ $$((n % d)) -eq 0 ] || continue; \
	  f=tmpbench_$${v}_$$n; \
	  if [ $$d -gt 1 ]; then \
	    sed -e "/param int JBN_SQR_UNROLL_MAX = /d" \
	        -e "s/param int nlimbs = 16;/param int nlimbs = SIZE1;/" \
	        -e "s/param int nlimbs = 8;/param int nlimbs = SIZE2;/" \
	        -e "s/param int nlimbs = 4;/param int nlimbs = SIZE4;/" \
	        -e "s/= SIZE1;/= $$n;/" -e "s/= SIZE2;/= $$((n/2));/" -e "s/= SIZE4;/= $$((n/4));/" \
	        $$t > $$f.jazz; \
	  else \
	  sed -e "s/param int nlimbs = 7;/param int nlimbs = $$n;/" \
	      -e "s/param int JBN_SQRL_GROUP = 4;/param int JBN_SQRL_GROUP = $$sg;/" \
	      -e "s/param int JBN_SQRL_TAIL = 1;/param int JBN_SQRL_TAIL = $$st;/" \
	      -e "s/bn_mul@n.jinc/$$m@n.jinc/" -e "s/fp_mul_ps@fp.jinc/$$s@fp.jinc/" \
	      -e "s/fp_mont@fp.jinc/$$k@fp.jinc/" \
	      -e "s|profiles/x86_64.jinc|profiles/$$p.jinc|" \
	      $$t > $$f.jazz; \
	  fi; \
	  $(JASMINC) $(JFLAGS) -o $$f.s $$f.jazz 2> $$f.log || { cat $$f.log; exit 1; }; \
	  pm=; [ $$k = fp_pm ] && pm=-DPM; \
	  $(GCC) -O2 -DNLIMBS=$$n -DVARIANT=\"$$v\" $$pm $(if $(BENCH_CHAINED),-DCHAINED) -o $$f bench_fp_ctx.c $$f.s || exit 1; \
	  ./$$f || echo "$$v n=$$n: did not run (selx, ksqrx, ksqrx2 and the variants over bn_mulx, bn_mulx_loop and bn_mulxr need a CPU with BMI2 and ADX)"; \
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
