#--
TOP = $(abspath $(dir $(firstword $(MAKEFILE_LIST)))../../)
TEST = $(TOP)/test
SRC = $(TOP)/src

#--
CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe

JASMIN ?= jasminc
JINCLUDE ?= -I Libjbn:$(SRC)/

BUILD ?= $(TEST)/bin/globals

MIN_NLIMBS ?= 1
MAX_NLIMBS ?= 16
MAX_TESTS  ?= 10

#--
default: globals

#--
gen: gen.c
	$(CC) $(CFLAGS) -D_MAIN_GEN -o $@ $< -lgmp

primes-det: primes.c gen.c ../common/notrandombytes.c
	$(CC) $(CFLAGS) -D_MAIN_PRIMES -o $@ -I../common $^ -lgmp

primes-rnd: primes.c gen.c ../common/randombytes.c
	$(CC) $(CFLAGS) -D_MAIN_PRIMES -o $@ -I../common $^ -lgmp

#--
JAZZ = $(shell find $(BUILD) -name '*.jazz')
ASM  = $(JAZZ:%.jazz=%.s)

.PHONY: globals
globals: gen primes-det
	./sike $(BUILD)
	./det $(BUILD) $(MIN_NLIMBS) $(MAX_NLIMBS) $(MAX_TESTS)
	$(MAKE) asm

#--
.PHONY: asm
asm: $(ASM)

%.s: %.jazz
	$(JASMIN) -o $@ $(JINCLUDE) $<

#--
.PHONY: clean
clean:
	rm -f gen primes-det primes-rnd

distclean: clean
	rm -fr $(BUILD)
