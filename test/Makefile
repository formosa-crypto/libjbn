include Makefile.compiler_flags

INCLUDE := -Icommon/

#--
TOP         = $(abspath $(dir $(firstword $(MAKEFILE_LIST)))../)
TEST        = $(TOP)/test
SRC         = $(TOP)/src
BIN        ?= bin
PARAMS_DIR ?= $(TEST)/$(BIN)/params

#--
JASMIN   ?= jasminc

#--
MIN_NLIMBS  ?= 1
MAX_NLIMBS  ?= 4
MAX_TESTS   ?= 1

export MIN_NLIMBS
export MAX_NLIMBS
export MAX_TESTS

# -----------------------------------------------------------------------------
TESTS_FP_LIBS      := libjbn gmp
TESTS_FP_DEFINED   := exp
TESTS_FP_BASE_NAME := $(patsubst %.s, %, $(subst libjbn_,, $(notdir $(shell test -d $(PARAMS_DIR) && find $(PARAMS_DIR) -name '*.s'))))

TESTS_FP     := $(addprefix $(BIN)/fp/, $(foreach LB, $(TESTS_FP_LIBS), $(foreach TD, $(TESTS_FP_DEFINED), $(foreach BN,$(TESTS_FP_BASE_NAME),$(LB)_$(TD)_$(BN)))))
TESTS_FP_BIN := $(addsuffix .bin, $(TESTS_FP))
TESTS_FP_OUT := $(addsuffix .out, $(TESTS_FP))


# -----------------------------------------------------------------------------
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


# -----------------------------------------------------------------------------
default: all

all:
	$(MAKE) -C misc/ default
	$(MAKE) all-out

all-out: $(TESTS_FP_OUT)
all-bin: $(TESTS_FP_BIN)

# -----------------------------------------------------------------------------
# expm or mul or ...
GET_TEST        = $(word 1, $(subst _, ,$*))

# d(eterministic) or r(andom)
GET_TYPE        = $(word 2, $(subst _, ,$*))

# number of limbs
GET_LIMBS       = $(word 3, $(subst _, ,$*))

# test number
GET_TEST_NUMBER = $(word 4, $(subst _, ,$*))

#--
$(TESTS_FP_BIN):
$(BIN)/fp/gmp_%.bin: $(BIN)/fp/$(CID)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$(GET_LIMBS) $(INCLUDE) common/fp/try-$(GET_TEST).c \
   common/fp/gmp-$(GET_TEST).c $(PARAMS_DIR)/libjbn_$(GET_TYPE)_$(GET_LIMBS)_$(GET_TEST_NUMBER).c -lgmp $(CIL)

$(BIN)/fp/libjbn_%.bin: | $(BIN)/fp/$(CID)
	$(CC) $(CFLAGS) -o $@ -DNLIMBS=$(GET_LIMBS) $(INCLUDE) common/fp/try-$(GET_TEST).c \
   common/fp/libjbn-$(GET_TEST).c $(PARAMS_DIR)/libjbn_$(GET_TYPE)_$(GET_LIMBS)_$(GET_TEST_NUMBER).c \
   $(PARAMS_DIR)/libjbn_$(GET_TYPE)_$(GET_LIMBS)_$(GET_TEST_NUMBER).s -lgmp $(CIL)

#--
$(TESTS_FP_OUT):
$(BIN)/fp/%.out: $(BIN)/fp/%.bin | $(BIN)/fp/$(CID)
	./$< > $@ $(CIL)

#--
$(BIN)/fp/: ; mkdir -p $@


# -----------------------------------------------------------------------------
ifeq ($(CI),1)

CI_TAR_NAME := libjbn-test.tar.gz

.PRECIOUS: %/$(CID)
%/$(CID): ; mkdir -p $@

.PRECIOUS: $(CID)
$(CID): ; mkdir -p $@

.PHONY: ci_reporter

ci_reporter:
	$(MAKE) ci_reporter_fp_compile
	$(MAKE) ci_reporter_fp_run
	$(MAKE) ci_reporter_fp_checksums
	$(MAKE) $(CI_TAR_NAME)

ci_reporter_fp_compile:
	./../scripts/ci/reporter/jlog "Status: fp: $(TEST)/$(BIN)/fp/*.bin" $(TEST)/$(BIN)/fp/$(CID)/ "*.bin" $(CICL)

ci_reporter_fp_run:
	./../scripts/ci/reporter/jlog "Status: fp $(TEST)/$(BIN)/fp/*.out" $(TEST)/$(BIN)/fp/$(CID)/ "*.out" $(CICL)

ci_reporter_fp_checksums:
	./scripts/checksum-compare.sh $(BIN)/ libjbn gmp
	./../scripts/ci/reporter/jlog "Status: $(TEST)/$(BIN)/fp/*.checksum*" $(TEST)/$(BIN)/fp/ "*checksum_match_with*" $(CICL)

CI_ERR := $(shell test -d $(TEST)/$(BIN)/ && find $(TEST)/$(BIN)/ -name '*.error')
CI_WARNINGS := $(shell test -d $(TEST)/$(BIN)/ && find $(TEST)/$(BIN)/ -name '*.log')

CI_FILES_TO_TAR := $(CI_ERR) $(CI_WARNINGS)

.PHONY: $(CI_TAR_NAME)
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


# -----------------------------------------------------------------------------
.PHONY: clean-out clean-bin clean distclean

clean-out:
	rm -f $(BIN)/*.out

clean-bin:
	rm -f $(BIN)/*.bin

clean:
	rm -fr $(BIN) $(CI_TAR_NAME)

distclean: clean

