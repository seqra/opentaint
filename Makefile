MAKE ?= make
GRADLEW := $(CURDIR)/core/gradlew
INSTALL ?= install
APT_GET ?= apt-get

PREFIX ?= /usr/local
BINDIR ?= $(PREFIX)/bin
LIBDIR ?= $(PREFIX)/lib

CORE_DIR := core
CLI_DIR := cli

CLI_BINARY_NAME := opentaint
CLI_DEV_BINARY_NAME := opentaint-dev
ANALYZER_TASK := :projectAnalyzerJar
AUTOBUILDER_TASK := opentaint-jvm-autobuilder:projectAutoBuilderJar
GO_SERVER_TASK := :opentaint-ir:go:buildGoServer

ANALYZER_JAR := $(CORE_DIR)/build/libs/opentaint-project-analyzer.jar
AUTOBUILDER_JAR := $(CORE_DIR)/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder.jar
GO_SERVER_BINARY := $(CORE_DIR)/opentaint-ir/go/go-ssa-server/go-ssa-server
RULES_SRC := rules/ruleset
INSTALLED_ANALYZER_JAR := $(LIBDIR)/$(notdir $(ANALYZER_JAR))
INSTALLED_AUTOBUILDER_JAR := $(LIBDIR)/$(notdir $(AUTOBUILDER_JAR))
INSTALLED_RULES_DIR := $(LIBDIR)/rules
INSTALLED_CLI_BINARY := $(BINDIR)/$(CLI_BINARY_NAME)
INSTALLED_DEV_BINARY := $(BINDIR)/$(CLI_DEV_BINARY_NAME)
INSTALLED_GO_SERVER := $(LIBDIR)/$(notdir $(GO_SERVER_BINARY))

.PHONY: all core projectAnalyzerJar core/autobuilder go-server cli install install-deps clean

all: core go-server cli

install-deps:
	$(APT_GET) update
	$(APT_GET) install -y protobuf-compiler

core:
	cd $(CORE_DIR) && $(GRADLEW) $(ANALYZER_TASK) $(AUTOBUILDER_TASK)

projectAnalyzerJar:
	cd $(CORE_DIR) && $(GRADLEW) $(ANALYZER_TASK)

core/autobuilder:
	cd $(CORE_DIR) && $(GRADLEW) $(AUTOBUILDER_TASK)

go-server:
	cd $(CORE_DIR) && $(GRADLEW) $(GO_SERVER_TASK)

cli:
	$(MAKE) -C $(CLI_DIR) build

install: core go-server
	mkdir -p $(BINDIR) $(LIBDIR)
	$(MAKE) -C $(CLI_DIR) install PREFIX=$(PREFIX) BINDIR=$(abspath $(BINDIR))
	$(INSTALL) -m 0644 $(ANALYZER_JAR) $(INSTALLED_ANALYZER_JAR)
	$(INSTALL) -m 0644 $(AUTOBUILDER_JAR) $(INSTALLED_AUTOBUILDER_JAR)
	$(INSTALL) -m 0755 $(GO_SERVER_BINARY) $(INSTALLED_GO_SERVER)
	rm -rf $(INSTALLED_RULES_DIR)
	mkdir -p $(INSTALLED_RULES_DIR)
	cp -R $(RULES_SRC)/. $(INSTALLED_RULES_DIR)/
	printf '%s\n' \
		'#!/bin/sh' \
		'set -eu' \
		'if command -v realpath >/dev/null 2>&1; then SELF=$$(realpath "$$0"); else SELF=$$0; fi' \
		'BIN_DIR=$$(CDPATH= cd -- "$$(dirname -- "$$SELF")" && pwd -P)' \
		'PREFIX_DIR=$$(CDPATH= cd -- "$$BIN_DIR/.." && pwd)' \
		'LIB_DIR="$$PREFIX_DIR/lib"' \
		'exec "$$BIN_DIR/$(CLI_BINARY_NAME)" --experimental --analyzer-jar "$$LIB_DIR/$(notdir $(ANALYZER_JAR))" --autobuilder-jar "$$LIB_DIR/$(notdir $(AUTOBUILDER_JAR))" --go-server-binary "$$LIB_DIR/$(notdir $(GO_SERVER_BINARY))" "$$@"' \
		> $(INSTALLED_DEV_BINARY)
	chmod 0755 $(INSTALLED_DEV_BINARY)
	$(INSTALLED_CLI_BINARY) pull

clean:
	$(MAKE) -C $(CLI_DIR) clean
	cd $(CORE_DIR) && $(GRADLEW) clean
