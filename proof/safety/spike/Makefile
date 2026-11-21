# Spike of the safety proofs: three slices of the library, abstracted by hand
# from the safety extraction at the dummy point A (nlimbs = 11), proved with a
# symbolic nlimbs (thy/), and transferred by sim + conseq to the extractions at
# both dummy points (chk/). Kept as the reference of the generator of the
# safety theories (scripts/xtr_safety.py), which supersedes it.
#
#   thy/BnBaseSafety*   bn_base's _load_, _mov_, _addU_ chains (memory,
#                       output-only arguments, in-place loops)
#   thy/BnMulSafety*    bn_mul's __mont_redM: its output is read on a growing
#                       prefix by the inner loop it calls
#   thy/FpBaseSafety*   fp_base's _mulm_, _mulmU_: a functor over the function
#                       parameters (module type MParam, module M(P), pre/post
#                       ops, lemmas in a section with the parameters'
#                       contracts as declared axioms)
#   chk/{A,B}           clone at the point, `equiv ... by proc; inline *; sim`
#                       per procedure, transfer of each lemma to the
#                       extractor's own spec by conseq (for the functor: under
#                       the hypothesis that the stubs meet their specs)
#
#   make extract   re-extracts extracted/{A,B} (needs the safety jasmin2ec)
#   make check     checks thy/ and chk/ (EasyCrypt and the released eclib)
#
# The safety jasmin2ec: Jasmin's safety-assert2 line with --safety-symbolic-params
# and the fix of the flags of shifts (branch safety-shift-flags), e.g.
#   make extract JASMIN2EC_SAFETY=/Users/jba/src/jasmin/safety-shift-flags/compiler/jasmin2ec

EC               ?= easycrypt
JASMIN2EC_SAFETY ?= jasmin2ec-safety

SRC     := $(abspath ../../../src/amd64/ref)
XFLAGS  := -m safety --safety-symbolic-params -I Libjbn=$(SRC)
ECFLAGS := -I Jasmin:$(abspath ../eclib) -I $(abspath ../common)

BN_FNS  := H::BN::_load_ H::BN::_mov_ H::BN::_addU_
FP_FNS  := H::FP::_mulm_ H::FP::_mulmU_
MUL_FNS := H::MUL::UNR::__mont_redM

THY := BnBaseSafetyThy BnBaseSafetySpike FpBaseSafetyThy FpBaseSafetySpike \
       BnMulSafetyThy BnMulSafetySpike

# extract a slice: $(call xtr,point,functions,output)
xtr = (cd $(SRC)/extracted && $(JASMIN2EC_SAFETY) $(XFLAGS) -I Dummy=dummy$(1) \
         $(addprefix -f ,$(2)) -o $(CURDIR)/extracted/$(1)/$(3) libjbn_abs.jazz)

all: check

extract:
	$(call xtr,A,$(BN_FNS),BN_spike.ec)
	$(call xtr,A,$(FP_FNS),FP_spike.ec)
	$(call xtr,A,$(MUL_FNS),MUL_spike.ec)
	$(call xtr,B,$(BN_FNS),BN_spike.ec)
	$(call xtr,B,$(FP_FNS),FP_spike.ec)
	$(call xtr,B,$(MUL_FNS),MUL_spike.ec)

check:
	cd thy && for f in $(THY); do \
	  $(EC) compile -no-eco $(ECFLAGS) -I ../extracted/A $$f.ec || exit 1; done
	for p in A B; do (cd chk/$$p && for f in ChkBN$$p ChkMUL$$p ChkFP$$p; do \
	  $(EC) compile -no-eco $(ECFLAGS) -I ../../extracted/$$p -I ../../thy $$f.ec \
	  || exit 1; done) || exit 1; done

.PHONY: all extract check
