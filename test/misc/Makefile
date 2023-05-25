#--
CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe

#--
JASMIN   ?= jasminc
JINCLUDE ?= -I Libjbn:$(SRC)/

#--
TOP  = $(abspath $(dir $(firstword $(MAKEFILE_LIST)))../../)
TEST = $(TOP)/test
SRC  = $(TOP)/src
BIN ?= bin

#--
PARAMS_DIR ?= $(TEST)/$(BIN)/params
MIN_NLIMBS ?= 1
MAX_NLIMBS ?= 16
MAX_TESTS  ?= 10

# --------------------------------------------------------------------

default: $(PARAMS_DIR)

# --------------------------------------------------------------------
# CI   - 0 or 1 depending if in CI or not : example : $ make ... CI=1 ...
# CID  - CI DIRNAME
# CIDR - CI DIRNAME to be used in RULES
# CIC  - CI CLEAR logs and errors
# CIL  - CI LOG stderr
# CILA - CI LOG stderr in append (>>)

CI      ?= 0
export CI

CID  =
CIC  = true
CIL  =
CICL ?= "1"

ifeq ($(CI),1)
CID  = .ci
CIDR = $(@D)/$(CID)

CIC  = (rm -f $(CIDR)/$(@F).*)

CIL  = 2> $(CIDR)/$(@F).log || \
       (echo $$? | cat - $(CIDR)/$(@F).log > $(CIDR)/$(@F).error && \
        rm -f $(CIDR)/$(@F).log)

CILA = 2>> $(CIDR)/$(@F).log || \
       (echo $$? | cat - $(CIDR)/$(@F).log >> $(CIDR)/$(@F).error && \
        rm -f $(CIDR)/$(@F).log)
endif

# --------------------------------------------------------------------
exec: $(BIN)/params $(BIN)/primes-det $(BIN)/primes-rnd

$(BIN)/params: params.c | $(BIN) $(BIN)/$(CID)
	$(CC) $(CFLAGS) -D_MAIN_PARAMS -o $@ $< -lgmp $(CIL)

$(BIN)/primes-det: primes.c params.c ../common/notrandombytes.c | $(BIN) $(BIN)/$(CID)
	$(CC) $(CFLAGS) -D_MAIN_PRIMES -o $@ -I../common $^ -lgmp $(CIL)

$(BIN)/primes-rnd: primes.c params.c ../common/randombytes.c | $(BIN) $(BIN)/$(CID)
	$(CC) $(CFLAGS) -D_MAIN_PRIMES -o $@ -I../common $^ -lgmp $(CIL)


# --------------------------------------------------------------------
.PHONY: $(PARAMS_DIR)
$(PARAMS_DIR): exec | $(dir $(PARAMS_DIR))$(CID)
	mkdir -p $@
	./sike.sh $(PARAMS_DIR) $(CIL)
	./rfc3526.sh $(PARAMS_DIR) $(CILA)
	./gen.sh det $(PARAMS_DIR) $(MIN_NLIMBS) $(MAX_NLIMBS) $(MAX_TESTS) $(CILA)
	$(MAKE) compile $(CILA)


# --------------------------------------------------------------------
.PHONY: compile
compile: JAZZ := $(shell test -d $(PARAMS_DIR) && find $(PARAMS_DIR) -name '*.jazz')
compile: ASM  := $(JAZZ:%.jazz=%.s)
compile:
	mkdir -p $(PARAMS_DIR)/$(CID)
	$(MAKE) $(ASM)

%.s: %.jazz
	$(JASMIN) -o $@ $(JINCLUDE) $< $(CIL)

$(BIN): ; mkdir -p $@


# --------------------------------------------------------------------
ifeq ($(CI),1)

CI_TAR_NAME := libjbn-test-misc.tar.gz

.PRECIOUS: %/$(CID)
%/$(CID): ; mkdir -p $@

.PRECIOUS: $(CID)
$(CID): ; mkdir -p $@

.PHONY: ci_reporter

ci_reporter: ci_reporter_params
	$(MAKE) $(CI_TAR_NAME)

ci_reporter_params:
	./../../scripts/ci/reporter/jlog "Status: $(TEST)/misc/$(BIN)/*" $(TEST)/misc/$(BIN)/$(CID)/ "*" $(CICL);
	./../../scripts/ci/reporter/jlog "Status: $(PARAMS_DIR)/libjbn*" $(PARAMS_DIR)/$(CID)/ "libjbn*" $(CICL);
	./../../scripts/ci/reporter/jlog "Status: $(PARAMS_DIR)" $(dir $(PARAMS_DIR))$(CID)/ "$(notdir $(PARAMS_DIR))" $(CICL);

CI_ERR := \
  $(shell test -d $(TEST)/misc/$(BIN)/$(CID)/ && find $(TEST)/misc/$(BIN)/$(CID)/ -name '*.error') \
  $(shell test -d $(PARAMS_DIR)/$(CID)/ && find $(PARAMS_DIR)/$(CID)/ -name 'libjbn*.error') \
  $(shell test -d $(dir $(PARAMS_DIR))$(CID)/ && find $(dir $(PARAMS_DIR))$(CID)/ -name "$(notdir $(PARAMS_DIR)).error")

# the following variable, by default (CICL="1"), will only contain non-empty logs
CI_WARNINGS := \
  $(shell test -d $(TEST)/misc/$(BIN)/$(CID)/ && find $(TEST)/misc/$(BIN)/$(CID)/ -name '*.log') \
  $(shell test -d $(PARAMS_DIR)/$(CID)/ && find $(PARAMS_DIR)/$(CID)/ -name 'libjbn*.log') \
  $(shell test -d $(dir $(PARAMS_DIR))$(CID)/ && find $(dir $(PARAMS_DIR))$(CID)/ -name "$(notdir $(PARAMS_DIR)).log")

CI_FILES_TO_TAR := $(CI_ERR) $(CI_WARNINGS)

$(CI_TAR_NAME):
	@$(JASMIN) -version > notes
ifeq ($(words $(CI_FILES_TO_TAR)),0)
	@echo "good job." >> notes
	@tar -zcvf $@ notes
else
	@tar -zcvf $@ notes $(CI_FILES_TO_TAR)
endif
	@rm notes

ci_err:
ifneq ($(words $(CI_ERR)),0)
	$(error $(CI_ERR))
endif

endif


# --------------------------------------------------------------------
.PHONY: clean
clean:
	rm -fr $(BIN) $(CID) $(CI_TAR_NAME)

distclean: clean
	rm -fr $(PARAMS_DIR)


