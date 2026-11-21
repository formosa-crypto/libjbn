# Safety proofs of libjbn (see README, "Safety proofs").
#
# Every module of the abstract instantiation (src/amd64/ref/extracted/
# libjbn_abs.jazz, the module lists of modules.mk) and every export template
# (its harness in extracted/exports/, the lists of exports/exports.mk) is
# extracted with Jasmin's safety model at the two dummy points A and B
# (dummyA/, dummyB/), into extracted/{A,B}/<QUAL>_<module>_safety.ec
# (committed, with the byte-array theories they require). scripts/xtr_safety.py abstracts each pair into a
# theory over the module parameters (theories/), checks that the theory at
# each point is the extraction, and writes the glue that transfers the
# lemmas to the extractions (checkxtr/).
#
#   make extract            re-extracts extracted/ (needs the safety jasmin2ec)
#   make check-extraction   re-extracts and fails if extracted/ changed
#   make align              checks that the extractions at A and B align
#                           (only parameters, sizes and array theories differ)
#   make lint               no call passes a fresh array where the callee
#                           requires it initialised (scripts/xtr_safety.py lint)
#   make gen                writes theories/<Name>_xtr.eca (committed),
#                           theories/<Name>_skeleton.ec and checkxtr/
#   make check-gen          fails if theories/ is not what gen writes
#   make check              checks the proofs <Name>.eca (no admit allowed)
#   make checkxtr           checks, at A and B, that each proved theory is the
#                           extraction and transfers its lemmas to it
#
# Only the theories with a proof file (<Name>.eca) are checked.
#
# The safety jasmin2ec: Jasmin's safety-assert2 line with
# --safety-symbolic-params (the parameters stay symbolic through the
# simplification of the safety model, so that the shape of the extraction does
# not depend on them) and the fix of the flags of shifts (branch
# safety-shift-flags); point JASMIN2EC_SAFETY to it, e.g.
#   make extract JASMIN2EC_SAFETY=/Users/jba/src/jasmin/safety-shift-flags/compiler/jasmin2ec

EC               ?= easycrypt
JASMIN2EC_SAFETY ?= jasmin2ec-safety
PYTHON           ?= python3

SRC     := $(abspath ../../src/amd64/ref)
XTR     := $(SRC)/extracted
XFLAGS  := -m safety --safety-symbolic-params -I Libjbn=$(SRC)
XDIR    := extracted
SYNC    := $(PYTHON) ../../scripts/xtr_safety.py

include $(XTR)/modules.mk
include $(XTR)/exports/exports.mk

POINTS := A B

# the theories (keys of scripts/xtr_safety.py), in dependency order
THEORIES := bn_util bn_base bn_rnd bn_mul bn_mul_loop bn_mulx bn_mulx_loop \
            bn_mulxr bn_mulsel bn_mulreg bn_karatsuba bn_exp fp_base fp_mont fp_pm \
            bn_base_export bn_mul_export bn_mul_loop_export bn_karatsuba_export \
            fp_mont_ctx_export fp_mont_export
NAMES    := Bn_util_safety Bn_base_safety Bn_rnd_safety Bn_mul_safety \
            Bn_mul_loop_safety Bn_mulx_safety Bn_mulx_loop_safety Bn_mulxr_safety \
            Bn_mulsel_safety Bn_mulreg_safety Bn_karatsuba_safety Bn_exp_safety \
            Fp_base_safety Fp_mont_safety Fp_pm_safety \
            Bn_base_export_safety Bn_mul_export_safety Bn_mul_loop_export_safety \
            Bn_karatsuba_export_safety Fp_mont_ctx_export_safety Fp_mont_export_safety
PROVED   := $(foreach n,$(NAMES),$(if $(wildcard $(n).eca),$(n)))
# their extractions (lint)
MODULES  := $(XTR_MODULES) $(EXPORT_MODULES)

all: align lint check-gen check checkxtr

# one module at one point: $(call xtr,module,point)
xtr = (cd $(XTR) && $(JASMIN2EC_SAFETY) $(XFLAGS) -I Dummy=dummy$(2) \
         $(foreach fn,$($(1)_FNS),-f '$($(1)_NS)$(fn)') \
         -o $(CURDIR)/$(XDIR)/$(2)/$(1)_safety.ec libjbn_abs.jazz)

# one export template at one point: $(call xtr_exp,module,point)
xtr_exp = (cd $(XTR) && $(JASMIN2EC_SAFETY) $(XFLAGS) -I Dummy=dummy$(2) \
             $(foreach fn,$($(1)_FNS),-f '$(fn)') \
             -o $(CURDIR)/$(XDIR)/$(2)/$(1)_safety.ec \
             exports/$(subst $(firstword $(subst _, ,$(1)))_,,$(1)).jazz)

extract:
	rm -rf $(addprefix $(XDIR)/,$(POINTS))
	mkdir -p $(addprefix $(XDIR)/,$(POINTS))
	$(foreach p,$(POINTS),$(foreach m,$(XTR_MODULES),$(call xtr,$(m),$(p)) &&)) true
	$(foreach p,$(POINTS),$(foreach m,$(EXPORT_MODULES),$(call xtr_exp,$(m),$(p)) &&)) true

check-extraction: extract
	git diff --exit-code --stat -- $(XDIR)
	test -z "$$(git status --porcelain -- $(XDIR))"

align:
	$(SYNC) align $(XTR_MODULES) $(EXPORT_MODULES)

lint:
	$(SYNC) lint $(MODULES)

gen:
	$(SYNC) gen $(THEORIES)

check-gen: gen
	git diff --exit-code --stat -- theories
	test -z "$$(git status --porcelain -- theories)"

# the common libraries are checked on their own: EasyCrypt trusts the proofs
# of the files a proof requires
check:
	@! grep -l 'admit' $(addsuffix .eca,$(PROVED)) common/*.ec /dev/null
	for f in common/*.ec; do $(EC) compile -no-eco $$f || exit 1; done
	for n in $(PROVED); do $(EC) compile -no-eco $$n.eca || exit 1; done

checkxtr: gen
	for p in $(POINTS); do for n in $(PROVED); do \
	  $(EC) compile -no-eco -I $(XDIR)/$$p checkxtr/$$p/$${n}_checkxtr.ec || exit 1; \
	done; done

.PHONY: all extract check-extraction align lint gen check-gen check checkxtr
