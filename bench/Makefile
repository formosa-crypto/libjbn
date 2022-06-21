# -*- Makefile -*-

# --------------------------------------------------------------------
AS      ?= as
CC      ?= gcc
CFLAGS  ?= -Wall -Wno-unused-function -Wno-unused-variable -Ofast
CI      ?= 0
export CI
EXCLUDE ?=

# --------------------------------------------------------------------
SRC      := ../src
BIN      ?= bin
COMMON   := common

JAZZ    ?= $(filter-out $(addprefix $(SRC)/,$(EXCLUDE)), $(sort $(dir $(shell find $(SRC) -name '*.jazz'))))
BENCH   := $(subst $(SRC),$(BIN), $(JAZZ))
BENCHS  := $(addsuffix bench, $(BENCH))

# --------------------------------------------------------------------

RDIR       = $(subst $(BIN)/,,$(@D))
OPERATION  = $(subst crypto_,,$(word 1, $(subst /, ,$(RDIR))))
NAMESPACE  = libjbn_$(subst -,_,$(subst /,_,$(RDIR)))
NAMESPACE1 = $(shell echo $(NAMESPACE) | tr a-z A-Z)
IDIR       = $(subst $(BIN),$(SRC),$(@D))
ASM        = $(IDIR)/*.s

MAIN       = $(COMMON)/$(OPERATION).c
DEFINES    = -DLIBJBN_NAMESPACE=$(NAMESPACE1) -DLIBJBN_NAMESPACE_LC=$(NAMESPACE)
INCLUDES   = -I$(IDIR)/include/ -I$(COMMON)/
COMPILE    = $(CC) $(CFLAGS) -o $@ $(DEFINES) $(INCLUDES) $(MAIN) $(ASM)

# --------------------------------------------------------------------
.PHONY: __phony benchs

default: benchs

benchs: $(BENCHS)

%/bench: __phony | %/
	$(MAKE) -C $(IDIR) || true
	$(COMPILE) || true

$(BENCH): ; @mkdir -p $@

run: benchs
	for d in $(BENCH); do (cd $$d && ./bench); done

# --------------------------------------------------------------------
clean:
	rm -fr $(BIN)

