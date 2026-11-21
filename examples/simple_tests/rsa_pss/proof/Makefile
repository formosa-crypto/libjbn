# Correctness of the RSA example (../rsa2048.jazz) in EasyCrypt, from the
# contracts of the library (proof/):
#
#   xtr/RsaPssXtr.ec  the extraction of rsa2048.jazz (rsa_init, rsa_enc,
#                     rsa_dec and their callees; old array model, as the
#                     library)
#   RsaPss_inst.ec    the library theories at the sizes of the example
#                     (16 and 32 limbs, exponents of 4), and the extracted
#                     procedures proved equal to theirs, so that their
#                     contracts apply to the extracted code
#   RsaPss_keys.ec    the formats of the keys (rsa2048_params.jinc) and the
#                     example key pair (rsa_keys.jinc): n = p*q, qInv * q = 1
#                     (mod p), the values of its parts
#   RsaPss.ec         the contracts of the RSA code: the expansion of the
#                     keys (rsa_init), RSAVP1 (rsa_enc) and RSASP1 by the CRT
#                     (rsa_dec), for any well-formed expanded key
#
#   make              extract, then check the three files
#   make safety       check the safety proofs (safety/, see its Makefile)

ROOT     = $(abspath ../../../..)
SRCDIR   = $(ROOT)/src/amd64/ref
PROOFDIR = $(ROOT)/proof
JASMIN2EC = jasmin2ec --array-model=old -I Libjbn=$(SRCDIR)
EC      ?= easycrypt
ECFLAGS  = -I $(PROOFDIR) -I xtr -I .

FILES = RsaPss_inst.ec RsaPss_keys.ec RsaPss.ec

LIBJBN_SRC = $(wildcard $(SRCDIR)/*.jinc $(SRCDIR)/profiles/*.jinc)
EXAMPLE_SRC = ../rsa2048.jazz $(wildcard ../*.jinc)

all: check

xtr/RsaPssXtr.ec: $(EXAMPLE_SRC) $(LIBJBN_SRC)
	mkdir -p xtr
	cd xtr && $(JASMIN2EC) -f rsa_init -f rsa_enc -f rsa_dec -o RsaPssXtr.ec ../../rsa2048.jazz

extract: xtr/RsaPssXtr.ec

check: xtr/RsaPssXtr.ec
	for f in $(FILES); do \
	  $(EC) compile -no-eco $(ECFLAGS) $$f || exit 1; \
	done

safety:
	$(MAKE) -C safety check

clean:
	rm -rf xtr

.PHONY: all extract check safety clean
