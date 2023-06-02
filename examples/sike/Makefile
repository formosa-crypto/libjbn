#include ../Makefile.common
#--
#TOP         = $(abspath $(dir $(firstword $(MAKEFILE_LIST)))../)
TOP         = ../..
TEST        = $(TOP)/test
SRC         = $(TOP)/src
BIN        ?= bin
PARAMS_DIR ?= $(TEST)/$(BIN)/params



GFLAGS ?=
JFLAGS ?=
JASMINC ?= jasminc -I Libjbn:$(SRC)

.DEFAULT_GOAL := all

EC_TARGETS ?= bn_sike751.ec
ASM_TARGETS ?= bn_sike751.s

%.s: %.jazz
	@$(JASMINC) $(JFLAGS) -o $@ $< || (rm -f $@ && touch fail && echo "\033[1;31m FAIL \033[0m")

%.ec: %.jazz
	@$(JASMINC) $(JFLAGS) -ec toEC -oec $@ $< || (rm -f $@ && touch fail && echo "\033[1;31m FAIL \033[0m")

all: test751 test610 test503 test434

test751: test_bn_sike751.c $(SRC)/sike/sike751/amd64/ref/bn_sike751.s
	gcc -o $@ $^

test610: test_bn_sike610.c $(SRC)/sike/sike610/amd64/ref/bn_sike610.s
	gcc -o $@ $^

test503: test_bn_sike503.c $(SRC)/sike/sike503/amd64/ref/bn_sike503.s
	gcc -o $@ $^

test434: test_bn_sike434.c $(SRC)/sike/sike434/amd64/ref/bn_sike434.s
	gcc -o $@ $^

sfiles: asm-clean $(ASM_TARGETS)

ecfiles: $(EC_TARGETS)

asm-clean:
	@rm -f fail *.japp $(ASM_TARGETS)
ec-clean:
	@rm -f fail Array*.ec WArray*.ec $(EC_TARGETS)

clean: asm-clean ec-clean
