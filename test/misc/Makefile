#--
CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe

#--
TOP  = $(abspath $(dir $(firstword $(MAKEFILE_LIST)))../../)
TEST = $(TOP)/test
SRC  = $(TOP)/src

JASMIN   ?= jasminc
JINCLUDE ?= -I Libjbn:$(SRC)/

PARAMS_DIR ?= $(TEST)/bin/params
MIN_NLIMBS ?= 1
MAX_NLIMBS ?= 16
MAX_TESTS  ?= 10

#--
default: $(PARAMS_DIR)

#--
params: params.c
	$(CC) $(CFLAGS) -D_MAIN_PARAMS -o $@ $< -lgmp

primes-det: primes.c params.c ../common/notrandombytes.c
	$(CC) $(CFLAGS) -D_MAIN_PRIMES -o $@ -I../common $^ -lgmp

primes-rnd: primes.c params.c ../common/randombytes.c
	$(CC) $(CFLAGS) -D_MAIN_PRIMES -o $@ -I../common $^ -lgmp

#--
.PHONY: $(PARAMS_DIR)
$(PARAMS_DIR): params primes-det
	./sike.sh $(PARAMS_DIR)
	./rfc3526.sh $(PARAMS_DIR)
	./gen.sh det $(PARAMS_DIR) $(MIN_NLIMBS) $(MAX_NLIMBS) $(MAX_TESTS)
	$(MAKE) compile

#--
.PHONY: compile
compile: JAZZ := $(shell find $(PARAMS_DIR) -name '*.jazz')
compile: ASM  := $(JAZZ:%.jazz=%.s)
compile:
	$(MAKE) $(ASM)

%.s: %.jazz
	$(JASMIN) -o $@ $(JINCLUDE) $<

#--
.PHONY: clean
clean:
	rm -f params primes-det primes-rnd

distclean: clean
	rm -fr $(PARAMS_DIR)
