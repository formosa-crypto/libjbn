# Safety of the RSA example (../../rsa2048.jazz) in EasyCrypt, from the safety
# theories of the library (proof/safety):
#
#   extracted/RsaPssXtr_safety.ec
#                         the extraction of rsa2048.jazz with Jasmin's safety
#                         model (rsa_init, rsa_enc, rsa_dec and their callees;
#                         committed, with the array theories it requires)
#   BArray136.ec, BArray264.ec
#                         the arrays u64[nlimbs+1] of bn_mul at 16 and 32
#                         limbs, which the theory takes but the example does
#                         not use
#   RsaPssSafety_inst.ec  the library theories at the sizes of the example (16
#                         and 32 limbs, exponents of 4 limbs), binding modules
#                         for their function parameters, and the extracted
#                         library procedures proved equal to theirs (sim), so
#                         that their lemmas apply to the extracted code
#                         (conseq); the multiplication selector, proved at the
#                         example's profile (x86_64: product scanning)
#   RsaPssSafety.ec       the RSA procedures and the three exports: rsa_init,
#                         rsa_enc and rsa_dec are safe
#
#   make extract   re-extracts extracted/ (needs the safety jasmin2ec, see
#                  proof/safety/Makefile)
#   make check     checks the two proof files (no admit allowed)

ROOT             = $(abspath ../../../../..)
SRCDIR           = $(ROOT)/src/amd64/ref
EC              ?= easycrypt
JASMIN2EC_SAFETY ?= jasmin2ec-safety
XFLAGS           = -m safety --safety-symbolic-params -I Libjbn=$(SRCDIR)

FILES = RsaPssSafety_inst.ec RsaPssSafety.ec

all: check

extract:
	rm -rf extracted
	mkdir -p extracted
	$(JASMIN2EC_SAFETY) $(XFLAGS) -f rsa_init -f rsa_enc -f rsa_dec \
	  -o extracted/RsaPssXtr_safety.ec ../../rsa2048.jazz

check:
	@! grep -l 'admit' $(FILES) /dev/null
	for f in $(FILES); do $(EC) compile -no-eco $$f || exit 1; done

.PHONY: all extract check
