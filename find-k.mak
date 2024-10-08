MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ifneq (,${K_HOME})
else ifneq (,$(wildcard ${MAKEFILE_PATH}/../../../include/kframework/ktest.mak))
export K_HOME?=${MAKEFILE_PATH}/../../../
else ifneq (,$(wildcard ${MAKEFILE_PATH}/../include/kframework/ktest.mak))
export K_HOME?=${MAKEFILE_PATH}/..
else ifneq (,$(wildcard /usr/include/kframework/ktest.mak))
export K_HOME?=/usr
else ifneq (,$(wildcard /usr/local/include/kframework/ktest.mak))
export K_HOME?=/usr/local
else ifneq (,$(shell which kompile))
export K_HOME?=$(abspath $(dir $(shell which kompile))/..)
else
$(error "Could not find installation of K. Please set K_HOME environment variable to your K installation.")
endif
