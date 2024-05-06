# 1. how to run benchmarks:
#
#   $ make CI=1 distclean && make -j8 CI=1 default && make CI=1 reporter 
#
# 2. how to set the number of tests, set MIN_LIMBS, MAX_LIMBS, and MAX_TESTS:
#
#   $ make CI=1 distclean && make -j8 CI=1 MIN_LIMBS=1 MAX_LIMBS=8 MAX_TESTS=100 default && make CI=1 reporter 
#
# 3. to just consider 'd'eterministic parameters (and ignore rfc* sike*);
#    useful to speed up benchmarkings in settings where one is only focused on
#    understanding limb-by-limb performance.
#
#   $ make CI=1 distclean && make -j8 CI=1 BENCH_FP_BASE_NAME_FILTER=d_% default && make CI=1 reporter
#
# 4. to generate the parameters:
#
#   $ make CI=1 distclean && make -j8 CI=1 params && make CI=1 reporter
#

# notes: this Makefile is going to be refactored; this is a first working draft


CC      ?= clang
CFLAGS  ?= -g -O3 -Wall -Wno-unused-function

INCLUDE := -Icommon/

#--
TOP        ?= $(abspath $(dir $(firstword $(MAKEFILE_LIST)))../)
export TOP

SRC         = $(TOP)/src
TEST        = $(TOP)/test
BENCH       = $(TOP)/bench

BIN        ?= bin
PARAMS_DIR ?= $(BENCH)/$(BIN)/params

export PARAMS_DIR

#--
JASMIN ?= jasminc
override JFLAGS +=
export JFLAGS

#--
MIN_NLIMBS  ?= 1
MAX_NLIMBS  ?= 8
MAX_TESTS   ?= 1

export MIN_NLIMBS
export MAX_NLIMBS
export MAX_TESTS

# -----------------------------------------------------------------------------
BENCH_FP_LIBS      := libjbn gmp
BENCH_FP_DEFINED   := exp

BENCH_FP_BASE_NAME_FILTER ?= %
BENCH_FP_BASE_NAME :=  $(filter $(BENCH_FP_BASE_NAME_FILTER), $(patsubst %.s, %, $(subst libjbn_,, $(notdir $(shell test -d $(PARAMS_DIR) && find $(PARAMS_DIR) -name '*.s')))))

BENCH_FP        := $(addprefix $(BIN)/fp/, $(foreach LB, $(BENCH_FP_LIBS), $(foreach TD, $(BENCH_FP_DEFINED), $(foreach BN,$(BENCH_FP_BASE_NAME),$(LB)_$(TD)_$(BN)))))
BENCH_FP_BIN    := $(addsuffix .bin, $(BENCH_FP))
BENCH_FP_OUT    := $(addsuffix .out, $(BENCH_FP))
BENCH_FP_STDOUT := $(addsuffix .stdout, $(BENCH_FP))

ddd:
	echo $(BENCH_FP_BASE_NAME)

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
default:
	$(MAKE) params
	$(MAKE) run

params:
	$(MAKE) -C $(TEST)/misc/ default

exec: $(BENCH_FP_BIN)

run: $(BENCH_FP_OUT)

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
$(BENCH_FP_BIN):

$(BIN)/fp/gmp_%.bin: $(BIN)/fp/$(CID)
	$(CC) $(CFLAGS) -o $@ -DST_ON -DRUNS=10 -DNLIMBS=$(GET_LIMBS) $(INCLUDE) common/fp/bench-$(GET_TEST).c \
   common/fp/gmp-$(GET_TEST).c $(PARAMS_DIR)/libjbn_$(GET_TYPE)_$(GET_LIMBS)_$(GET_TEST_NUMBER).c -lgmp -lgsl $(CIL)

$(BIN)/fp/libjbn_%.bin: | $(BIN)/fp/$(CID)
	$(CC) $(CFLAGS) -o $@ -DST_ON -DRUNS=10 -DNLIMBS=$(GET_LIMBS) $(INCLUDE) common/fp/bench-$(GET_TEST).c \
   common/fp/libjbn-$(GET_TEST).c $(PARAMS_DIR)/libjbn_$(GET_TYPE)_$(GET_LIMBS)_$(GET_TEST_NUMBER).c \
   $(PARAMS_DIR)/libjbn_$(GET_TYPE)_$(GET_LIMBS)_$(GET_TEST_NUMBER).s -lgmp -lgsl $(CIL)

#--
$(BENCH_FP_OUT):

$(BIN)/fp/%.out: $(BIN)/fp/%.bin | $(BIN)/fp/$(CID)
	./$< - > $@ $(CIL)

$(BENCH_FP_STDOUT):
$(BIN)/fp/%.stdout: $(BIN)/fp/%.bin | $(BIN)/fp/$(CID)
	./$< $(CIL)

#--
$(BIN)/fp/: ; mkdir -p $@


# -----------------------------------------------------------------------------
ifeq ($(CI),1)

CI_TAR_NAME := libjbn-test.tar.gz

.PRECIOUS: %/$(CID)
%/$(CID): ; mkdir -p $@

.PRECIOUS: $(CID)
$(CID): ; mkdir -p $@

.PHONY: reporter

reporter:
	$(MAKE) reporter_fp_compile
	$(MAKE) reporter_fp_run
	$(MAKE) $(CI_TAR_NAME)

reporter_fp_compile:
	./../scripts/ci/reporter/jlog "Status: fp: $(BENCH)/$(BIN)/fp/*.bin" $(BENCH)/$(BIN)/fp/$(CID)/ "*.bin" $(CICL)

reporter_fp_run:
	./../scripts/ci/reporter/jlog "Status: fp $(BENCH)/$(BIN)/fp/*.out" $(BENCH)/$(BIN)/fp/$(CID)/ "*.out" $(CICL)

CI_ERR := $(shell test -d $(BENCH)/$(BIN)/ && find $(BENCH)/$(BIN)/ -name '*.error')
CI_WARNINGS := $(shell test -d $(BENCH)/$(BIN)/ && find $(BENCH)/$(BIN)/ -name '*.log')

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

