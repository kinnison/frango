# Makefile
#
# Build system for Frango
#
# This file is part of the Frango suite of lexer/parser tools for Lua
#
# Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
#
# Please see the COPYING file for licence details.
#

all: check

.PHONY: all check


check: lunit/lunit
	lunit/lunit -p "lib/?.lua" tests/*.lua
