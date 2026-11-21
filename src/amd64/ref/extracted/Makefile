# Extraction of the libjbn modules to EasyCrypt (old array model, which
# the proofs rely on). Every module is instantiated once, with dummy
# parameters and stub function parameters, in libjbn_abs.jazz; each .ec file
# below collects the listed procedures of one module (and their callees).

SRCDIR = $(abspath ..)
JASMIN2EC = jasmin2ec --array-model=old -I Libjbn=$(SRCDIR) -I Dummy=dummyA

LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc)
HARNESS = libjbn_abs.jazz preamb@n.jinc dummyA/dummy.jinc

include modules.mk

MJAZZ_EC = $(addsuffix .ec,$(XTR_MODULES))

all: $(MJAZZ_EC)

xtr = $(JASMIN2EC) $(foreach fn, $(2), -f '$(1)$(fn)') -o $@ libjbn_abs.jazz

$(MJAZZ_EC): %.ec: $(HARNESS) $(LIBJBN_SRC) modules.mk
	$(call xtr,$($*_NS),$($*_FNS))

clean:
	rm -f Array*.ec WArray*.ec *~

realclean: clean
	rm -f $(MJAZZ_EC)
