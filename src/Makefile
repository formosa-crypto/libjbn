# -*- Makefile -*-

# --------------------------------------------------------------------
AS      ?= as
CC      ?= gcc
CFLAGS  ?= -Wall -Ofast
CI      ?= 0
export CI
EXCLUDE ?=

# --------------------------------------------------------------------
SRC    := .
BUILD  := .build

ECMK   := $(filter-out $(addprefix ./,$(EXCLUDE)), $(dir $(shell find $(SRC) -name 'Ec.mk'))) # just for cleaning .deps and .ci
JAZZ   := $(filter-out $(addprefix ./,$(EXCLUDE)), $(sort $(dir $(shell find $(SRC) -name '*.jazz'))))
API    := $(shell find $(SRC) -name 'api.h')
ASM    := $(shell find $(SRC) -name '*.s')
OBJ    := $(ASM:%.s=$(BUILD)/%.o)

# --------------------------------------------------------------------
.PHONY: default source $(JAZZ) clean-ci clean distclean check.tar.gz report err

default: source
ifeq ($(CI),1)
	$(MAKE) check.tar.gz
	$(MAKE) report
	$(MAKE) err
endif

source: $(JAZZ)
$(JAZZ):
	$(MAKE) -C $@ || true

# --------------------------------------------------------------------

clean-ci:
	for i in $(JAZZ); do $(MAKE) -C $$i clean-ci; done
	for i in $(ECMK); do $(MAKE) -C $$i -f Ec.mk clean-ci; done

clean:
	for i in $(JAZZ); do $(MAKE) -C $$i clean; done
	for i in $(ECMK); do $(MAKE) -C $$i -f Ec.mk clean; done

distclean: clean
	rm -fr $(BUILD) check.tar.gz

# --------------------------------------------------------------------
ifeq ($(CI),1)

ERR := $(shell find $(SRC) -name '*.s.error')
CIL := $(shell find $(SRC) -name '.ci')

check.tar.gz:
	@tar -zcvf $@ $(CIL)

report:
	./../scripts/ci/jsrc

err:
ifneq ($(words $(ERR)),0)
	$(error $(ERR))
endif

endif

