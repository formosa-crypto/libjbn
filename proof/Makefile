# EasyCrypt proofs of libjbn.
#
# The module M of each theory below is generated from the extraction of
# the corresponding Jasmin module (scripts/xtr_sync.py), between the
# markers "BEGIN generated" / "END generated":
#
#   make update      re-extract and regenerate the modules M
#   make check-sync  fail if a module M is out of date (e.g. in CI)
#   make checkxtr    sanity checks: each theory, cloned at the dummy sizes
#                    of the extraction, has the extracted code as its
#                    module M (equiv ... by sim, for every procedure)
#   make check       compile the theories
#   make             check-sync, checkxtr and check

ROOT    = ..
XTRDIR  = $(ROOT)/src/amd64/ref/extracted
SYNC    = python3 $(ROOT)/scripts/xtr_sync.py
EC     ?= easycrypt
ECFLAGS = -I . -I $(XTRDIR)

# theory keys of scripts/xtr_sync.py, and their files (in dependency order)
THEORIES = bn_util bn_base bn_mul
FILES    = Bn_util.ec Bn_base.eca Bn_mul.eca

CHECKDIR = checkxtr

all: check-sync checkxtr check

extract:
	$(MAKE) -C $(ROOT)/src/amd64/ref extract

update: extract
	$(SYNC) update $(THEORIES)

check-sync: extract
	$(SYNC) check $(THEORIES)

checkxtr: extract
	mkdir -p $(CHECKDIR)
	for t in $(THEORIES); do \
	  $(SYNC) checkxtr $$t -o $(CHECKDIR)/$${t}_checkXtr.ec || exit 1; \
	done
	for t in $(THEORIES); do \
	  $(EC) compile -no-eco $(ECFLAGS) $(CHECKDIR)/$${t}_checkXtr.ec || exit 1; \
	done

check: extract
	for f in $(FILES); do \
	  $(EC) compile -no-eco $(ECFLAGS) $$f || exit 1; \
	done

clean:
	rm -rf $(CHECKDIR) *.eco

.PHONY: all extract update check-sync checkxtr check clean
