
# Path to leon.
LEON ?= leon

# Path to leon library path.
LEON_LIBRARY_DIR ?= /usr/local/lib/leon/library
LEON_LIBRARY = $(shell find $(LEON_LIBRARY_DIR) -name *.scala)

# Functions to be verified.
FUNS ?=

# Verify files containing the specified functions.
VF ?= no

# Timeout for each verification condition.
TIMEOUT ?= 5

# Path to scaladoc.
SCALADOC ?= scaladoc

# Output directory of API documentation.
DOCDIR ?= doc
APIDIR = $(DOCDIR)/api

# Resolving dependencies.
RD ?= yes
RESOLVE_DEPENDENCY ?= $(RD)

# Include files in the same package when resolving dependencies.
ISP ?= no
INCLUDE_SAME_PACKAGE ?= $(ISP)

# We need bash.
SHELL = /bin/bash

# Source files.
SRC := $(shell find . -name *.scala)

LEON_FLAGS = --timeout=$(TIMEOUT) -feature

# Some temporary files used in resolving dependencies.
SOURCE = .source
DEPEND = .depend
PROCESSED = .processed
ERROR = .error

EMPTY :=
SPACE := $(EMPTY) $(EMPTY)
COMMA := ,

define find_sources
	rm -f $(SOURCE) $(ERROR); \
	targets=`echo ${1} | tr "," "\n"`; \
	for target in $${targets}; do \
		found=no; \
		object=`echo "$${target}" | cut -d "." -f 1`; \
		method=`echo "$${target}" | cut -d "." -f 2`; \
		for file in $(SRC); do \
			c1=`grep -E "(object|class)[ ]*$${object}[ ]*\b" $${file}`; \
			c2=`grep "def[ ]*$${method}[ ]*\b" $${file}`; \
			if [[ ($${target} != *.* || -n "$${c1}") && -n "$${c2}" ]]; then \
				found=yes; \
				echo $${file} >> $(SOURCE); \
			fi \
		done; \
		if [[ "$${found}" == "no" ]]; then \
			touch $(ERROR); \
			echo "ERROR: Failed to find $${target}."; \
		fi \
	done;
endef

define find_imports
	function resolve_path { \
		file="$${1}"; \
		path="$${2}"; \
		if [[ -z "`grep -l \"^$${path}$$\" $(PROCESSED) 2> /dev/null`" ]]; then \
			echo "$${path}" >> $(PROCESSED); \
			dn=`dirname "$${path}"`; \
			bn=`basename "$${path}"`; \
			if [[ $${dn} != .* && $${dn} != /* ]]; then \
				dn="./$${dn}"; \
			fi; \
			if [[ "$${dn}" == "." && "$${bn}" == "." ]]; then \
				:; \
			elif [[ -d "$${dn}" && "$${bn}" == "_" ]]; then \
				ls $${dn}/*.scala >> $(DEPEND); \
			elif [[ $${bn} == {*} ]]; then \
				bn=`echo $${bn} | sed "s/[{},]/ /g"`; \
				for bn_i in $${bn}; do \
					resolve_path "$${file}" "$${dn}/$${bn_i}"; \
				done \
			elif [[ -f "$${dn}/$${bn}.scala" ]]; then \
				if [[ "$(INCLUDE_SAME_PACKAGE)" == "yes" ]]; then \
					ls $${dn}/*.scala >> $(DEPEND); \
					resolved="yes"; \
				else \
					echo $${dn}/$${bn}.scala >> $(DEPEND); \
					resolved="yes"; \
				fi \
			elif [[ -d "$${dn}" ]]; then \
				lines=`grep -E -l "(class|object|def)[ ]*$${bn}[ ]*\b" $${dn}/*.scala 2> /dev/null`; \
				if [[ -z "$${lines}" ]]; then \
					resolve_path "$${file}" "$${dn}"; \
				else \
					if [[ "$(INCLUDE_SAME_PACKAGE)" == "yes" ]]; then \
						ls $${dn}/*.scala >> $(DEPEND); \
						resolved="yes"; \
					else \
						for line in $${lines}; do \
							echo $${line} >> $(DEPEND); \
						done; \
						resolved="yes"; \
					fi \
				fi \
			else \
				resolve_path "$${file}" "$${dn}"; \
				if [[ "$${resolved}" != "yes" && "$${bn}" != "" && "$${bn}" != "." && "$${bn}" != "_" ]]; then \
					basedir=`dirname $${file}`; \
					lines=`grep -E -l "(class|object|def)[ ]*$${bn}[ ]*\b" $${basedir}/*.scala 2> /dev/null`; \
					if [[ -z "$${lines}" ]]; then \
						resolve_path "$${file}" "$${dn}"; \
					else \
						for line in $${lines}; do \
							echo $${line} >> $(DEPEND); \
						done; \
						resolved="yes"; \
					fi \
				fi \
			fi \
		fi \
	}; \
	sources="${1}"; \
	prev=-1; \
	curr=0; \
	rm -f $(PROCESSED); \
	while [[ "$${prev}" != "$${curr}" ]]; do \
		prev=$${curr}; \
		rm -f $(DEPEND); \
		for source in $${sources}; do \
			echo $${source} >> $(DEPEND); \
			if [[ "$(INCLUDE_SAME_PACKAGE)" == "yes" ]]; then \
				ls `dirname $${source}`/*.scala >> $(DEPEND); \
			fi; \
			IFS=$$'\n'; \
			depends=`grep "import" $${source} | cut -d " " -f 2- | grep -v "^leon[.]" | grep -v "^scala[.]" | sed "s/[.]/\//g"`; \
			for depend in $${depends}; do \
				resolved="no"; \
				IFS=$$' ' resolve_path "$${source}" "$${depend}"; \
			done; \
			IFS=$$' '; \
		done; \
		sort -u $(DEPEND) -o $(DEPEND); \
		sources=`cat $(DEPEND) | xargs`; \
		curr=`wc -l < $(DEPEND) | bc`; \
	done
endef


ifneq ($(FUNS),)
all: $(FUNS)
else
all:
	$(LEON) $(LEON_FLAGS) $(SRC)
endif

ifeq ($(RESOLVE_DEPENDENCY),yes)
%:
	@echo Find source files to be included...
	@$(call find_sources, $@)
	@if [[ -f "$(ERROR)" ]]; then exit -1; else cat $(SOURCE) | sed 's/^/  /g';	fi
	@echo Resolving dependencies...
	@$(call find_imports, `cat $(SOURCE) | xargs`)
	@cat $(DEPEND) | sed 's/^/  /g'
ifeq ($(VF),yes)
	$(LEON) $(LEON_FLAGS) `cat $(DEPEND) | xargs`
else
	$(LEON) $(LEON_FLAGS) --functions=$@ `cat $(DEPEND) | xargs`
endif
	@rm -f $(SOURCE) $(DEPEND) $(PROCESSED) $(ERROR)
else
%:
	$(LEON) $(LEON_FLAGS) --functions=$@ $(SRC)
endif

doc:
	$(SCALADOC) -d $(APIDIR) $(LEON_LIBRARY) $(SRC)

.PHONY: all doc
