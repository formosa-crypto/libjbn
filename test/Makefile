#--
CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe

#--
MIN_NLIMBS  ?= 1
MAX_NLIMBS  ?= 16
MAX_TESTS   ?= 10

#--
LIST_NLIMBS := $(shell seq $(MIN_NLIMBS) $(MAX_NLIMBS))
LIST_TESTS  := $(shell seq 1 $(MAX_TESTS))

export MIN_NLIMBS
export MAX_NLIMBS
export MAX_TESTS

#--
INCLUDE   ?= -Icommon/
RANDOMLIB ?= common/notrandombytes.c common/notrandombytes1.c
BIN       ?= bin

TARGETS := $(foreach L,$(addprefix d_, $(LIST_NLIMBS)),$(foreach T,$(LIST_TESTS),$(L)_$(T)))

GMP_EXPM := $(addprefix $(BIN)/gmp_expm_,$(TARGETS))
GMP_EXPM_CHECKSUMS := $(addsuffix .out, $(GMP_EXPM))

LIBJBN_EXPM := $(addprefix $(BIN)/libjbn_expm_,$(TARGETS))
LIBJBN_EXPM_CHECKSUMS := $(addsuffix .out, $(LIBJBN_EXPM))

GET_LIMBS = $(firstword $(subst _, ,$*))

##--

.PHONY: __phony

bin/params:
	$(MAKE) -C misc default

defaults: default-gmp default-libjbn
all: all-gmp all-libjbn
run-all: run-all-gmp run-all-libjbn

#-- GMP

default-gmp: $(BIN)/gmp_expm_d_16_1

all-gmp: $(GMP_EXPM)
run-all-gmp: $(GMP_EXPM_CHECKSUMS)

$(GMP_TARGETS):
$(BIN)/gmp_expm_d_%: __phony bin/params | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$(GET_LIMBS) $(INCLUDE) common/params/try-expm.c common/params/gmp-expm.c bin/params/libjbn_d_$*.c -lgmp

$(BIN)/gmp_expm_d_%.out: $(BIN)/gmp_expm_d_%
	(./$< > $@ 2>&1 || true)

#-- LIBJBN

default-libjbn: $(BIN)/libjbn_expm_16_1

all-libjbn: $(LIBJBN_EXPM)
run-all-libjbn: $(LIBJBN_EXPM_CHECKSUMS)

$(LIBJBN_EXPM):
$(BIN)/libjbn_expm_d_%: __phony bin/params | $(BIN)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$(GET_LIMBS) $(INCLUDE) common/params/try-expm.c common/params/libjbn-expm.c bin/params/libjbn_d_$*.c bin/params/libjbn_d_$*.s -lgmp

$(BIN)/libjbn_expm_d_%.out: $(BIN)/libjbn_expm_d_%
	(./$< > $@ 2>&1 || true)

#-- ------------------------------------------------------------------------------------------------
#-- ------------------------------------------------------------------------------------------------
#-- ------------------------------------------------------------------------------------------------
#-- LIBJBN / GMP rfc :: to be refactored (requires different names of non-random instantiations like sike and rfc3526)
$(BIN)/libjbn_expm_rfc3526_modp2048: __phony
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=32 $(INCLUDE) common/params/try-expm.c common/params/libjbn-expm.c bin/params/libjbn_rfc3526_modp2048.c bin/params/libjbn_rfc3526_modp2048.s -lgmp

$(BIN)/libjbn_expm_rfc3526_modp2048.out: $(BIN)/libjbn_expm_rfc3526_modp2048
	(./$< > $@ 2>&1 || true)

# --

$(BIN)/gmp_expm_rfc3526_modp2048: __phony
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=32 $(INCLUDE) common/params/try-expm.c common/params/gmp-expm.c bin/params/libjbn_rfc3526_modp2048.c -lgmp

$(BIN)/gmp_expm_rfc3526_modp2048.out: $(BIN)/gmp_expm_rfc3526_modp2048
	(./$< > $@ 2>&1 || true)

#-- ------------------------------------------------------------------------------------------------
#-- ------------------------------------------------------------------------------------------------
#-- ------------------------------------------------------------------------------------------------

#-- CHECK
check: __phony
	for nlimbs in $(LIST_NLIMBS); do \
		for test in $(LIST_TESTS); do \
		  libjbn=$$(cat $(BIN)/libjbn_expm_d_$${nlimbs}_$${test}.out); \
		  gmp=$$(cat $(BIN)/gmp_expm_d_$${nlimbs}_$${test}.out); \
		  if [ "$$libjbn" = "$$gmp" ] ; then echo -n "OK  "; else echo -n "FAIL"; fi; \
		  echo " - $${nlimbs} - $${test} - $$libjbn/$$gmp"; \
		done; \
	done

#--
$(BIN): ; mkdir -p $@

#--

.PHONY: clean
clean:
	rm -fr $(BIN)

