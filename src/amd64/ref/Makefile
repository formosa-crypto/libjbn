SRCDIR = $(abspath .)

JASMINC = jasminc
JASMINC_OPT = -I Libjbn=$(SRCDIR)

# Library modules are plain .jinc files, instantiated by requiring them
# inside namespaces (see README); there is no generation step.

all: check

# typecheck every module, through the abstract instantiation used for
# the extraction (it has no export functions, so no code is produced)
check:
	$(JASMINC) $(JASMINC_OPT) -I Dummy=extracted/dummyA -o /dev/null extracted/libjbn_abs.jazz
	$(JASMINC) $(JASMINC_OPT) -I Dummy=extracted/dummyB -o /dev/null extracted/libjbn_abs.jazz

# extraction to EasyCrypt (proofs); the generated Array*.ec/WArray*.ec are
# kept, since the sanity checks of proof/ load them (see proof/Makefile)
extract:
	(cd extracted; $(MAKE))

clean:
	(cd extracted; $(MAKE) clean)

realclean:
	(cd extracted; $(MAKE) realclean)

.PHONY: all check extract clean realclean
