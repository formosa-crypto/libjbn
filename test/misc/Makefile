#--
CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe

JASMIN ?= jasminc
JINCLUDE ?= -I Libjbn:../../src/

#--
default: asm

#--
gen: gen.c
	$(CC) $(CFLAGS) -D_MAIN -o $@ $< -lgmp

#--
JAZZ := sike434.jazz sike503.jazz sike610.jazz sike751.jazz
ASM  := $(JAZZ:%.jazz=%.s)

.PHONY: jazz
jazz: $(JAZZ)

sike434.jazz: gen
	./gen j 7 0x0002341f271773446cfc5fd681c520567bc65c783158aea3fdc1767ae2ffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

sike503.jazz: gen
	./gen j 8 0x004066f541811e1e6045c6bdda77a4d01b9bf6c87b7e7daf13085bda2211e7a0abffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

sike610.jazz: gen
	./gen j 10 0x000000027bf6a768819010c251e7d88cb255b2fa10c4252a9ae7bf45048ff9abb1784de8aa5ab02e6e01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

sike751.jazz: gen
	./gen j 12 0x00006fe5d541f71c0e12909f97badc668562b5045cb25748084e9867d6ebe876da959b1a13f7cc76e3ec968549f878a8eeafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

#--
sike434.c: gen
	./gen c 7 0x0002341f271773446cfc5fd681c520567bc65c783158aea3fdc1767ae2ffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

sike503.c: gen
	./gen c 8 0x004066f541811e1e6045c6bdda77a4d01b9bf6c87b7e7daf13085bda2211e7a0abffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

sike610.c: gen
	./gen c 10 0x000000027bf6a768819010c251e7d88cb255b2fa10c4252a9ae7bf45048ff9abb1784de8aa5ab02e6e01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

sike751.c: gen
	./gen c 12 0x00006fe5d541f71c0e12909f97badc668562b5045cb25748084e9867d6ebe876da959b1a13f7cc76e3ec968549f878a8eeafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff > $@

#--
.PHONY: asm
asm: $(ASM)

%.s: %.jazz
	$(JASMIN) -o $@ $(JINCLUDE) $<

#--
.PHONY: clean
clean:
	rm -f gen sike*
