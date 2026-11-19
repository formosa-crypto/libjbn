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
# row-looped operand scanning (bn_mul_loop: MUL/ADC rows; bn_mulx_loop:
# MULX/ADCX/ADOX rows, which, as the other `os` programs, need BMI2 and ADX)
PROGS += testmul_os_loop_32 testmul_os_mulx_loop_32

all: $(PROGS)

run: $(PROGS)
	for p in $(PROGS); do time ./$$p; done

testmul_ps_32: testmul_ps_32.c muln32.s
	$(GCC) -o $@ $^

testmul_os_32: testmul_os_32.c muln32.s
	$(GCC) -o $@ $^

testmul_os_loop_32: testmul_os_loop.c muln32_loop.s
	$(GCC) -DNLIMBS=32 -o $@ $^

testmul_os_mulx_loop_32: testmul_os_loop.c muln32_mulx_loop.s
	$(GCC) -DNLIMBS=32 -o $@ $^

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

%.s: %.jazz $(LIBJBN_SRC)
	$(JASMINC) $(JFLAGS) -o $@ $<

# Timing of the schoolbook multiplications alone, which separates the loop
# kind from the instructions (the instances, tmpbench_<variant>_<size>.*,
# are generated from muln32.jazz):
#   ps        bn_mul        product scanning,  MUL/ADC,        unrolled
#   loop      bn_mul_loop   operand scanning,  MUL/ADC,        looped rows
#   mulx_unr  bn_mul        operand scanning,  MULX/ADCX/ADOX, unrolled
#   mulx      bn_mulx_loop  operand scanning,  MULX/ADCX/ADOX, looped rows
# (the last two need BMI2 and ADX, so they do not run under Rosetta)
BENCH_SIZES    ?= 4 8 16 32 64
BENCH_VARIANTS ?= ps loop mulx_unr mulx

bench: bench_mul.c muln32.jazz $(LIBJBN_SRC)
	@for n in $(BENCH_SIZES); do for v in $(BENCH_VARIANTS); do \
	  case $$v in \
	    ps)       m=bn_mul;       x=bn_mul_export;      fn=bn_ps_muln;; \
	    loop)     m=bn_mul_loop;  x=bn_mul_loop_export; fn=bn_os_muln;; \
	    mulx_unr) m=bn_mul;       x=bn_mul_export;      fn=bn_os_muln;; \
	    mulx)     m=bn_mulx_loop; x=bn_mul_loop_export; fn=bn_os_muln;; \
	    *) echo "unknown variant $$v"; exit 1;; \
	  esac; \
	  f=tmpbench_$${v}_$$n; \
	  sed -e "s/param int nlimbs = 64;/param int nlimbs = TOP;/" \
	      -e "s/param int nlimbs = 32;/param int nlimbs = $$n;/" \
	      -e "s/param int nlimbs = TOP;/param int nlimbs = $$((2*n));/" \
	      -e "s/bn_mul@n.jinc/$$m@n.jinc/" -e "s/bn_mul_export@2n.jinc/$$x@2n.jinc/" \
	      muln32.jazz > $$f.jazz; \
	  $(JASMINC) $(JFLAGS) -o $$f.s $$f.jazz 2> $$f.log || { cat $$f.log; exit 1; }; \
	  $(GCC) -O2 -DNLIMBS=$$n -DFN=$$fn -DVARIANT=\"$$v\" -o $$f bench_mul.c $$f.s || exit 1; \
	  ./$$f || echo "$$v n=$$n: did not run (the mulx variants need a CPU with BMI2 and ADX)"; \
	done; done

# The same for Karatsuba (bn_karatsuba, one or two levels: kar1, kar2) over
# each of the four schoolbook multiplications above, as its base case; the
# instances are generated from kar_32_os_16.jazz and kar_32_os_8.jazz.
# To be compared with the lines of `bench` for the same size.
BENCH_KAR_SIZES ?= 16 32 64
BENCH_KAR_BASES ?= ps loop mulx_unr mulx

bench-kar: bench_mul.c kar_32_os_16.jazz kar_32_os_8.jazz $(LIBJBN_SRC)
	@for n in $(BENCH_KAR_SIZES); do for b in $(BENCH_KAR_BASES); do for l in 1 2; do \
	  case $$b in \
	    ps)       m=bn_mul;       fn=_ps_muln_;; \
	    loop)     m=bn_mul_loop;  fn=_os_muln_;; \
	    mulx_unr) m=bn_mul;       fn=_os_muln_;; \
	    mulx)     m=bn_mulx_loop; fn=_os_muln_;; \
	    *) echo "unknown base $$b"; exit 1;; \
	  esac; \
	  case $$l in \
	    1) t=kar_32_os_16.jazz; nl=$$((n/2));; \
	    2) t=kar_32_os_8.jazz;  nl=$$((n/4));; \
	  esac; \
	  f=tmpbench_kar$${l}_$${b}_$$n; \
	  sed -e "s/param int nlimbsL = [0-9]*;/param int nlimbsL = $$nl;/" \
	      -e "s/bn_mul@n.jinc/$$m@n.jinc/" -e "s/_os_muln_/$$fn/" \
	      $$t > $$f.jazz; \
	  $(JASMINC) $(JFLAGS) -o $$f.s $$f.jazz 2> $$f.log || { cat $$f.log; exit 1; }; \
	  $(GCC) -O2 -DNLIMBS=$$n -DFN=bn_kar_muln -DVARIANT=\"kar$$l/$$b\" -o $$f bench_mul.c $$f.s || exit 1; \
	  ./$$f || echo "kar$$l/$$b n=$$n: did not run (the mulx bases need a CPU with BMI2 and ADX)"; \
	done; done; done

clean:
	rm -f $(PROGS) tmpbench_*

realclean: clean
	rm -f *.s *~
