-- tests/frango-util-fa.lua
--
-- Tests for frango.util.fa
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

require "lunit"

module("frango-util-fa-basics", package.seeall, lunit.testcase)

function test_01_load_module()
   local ok, fa = pcall(require, "frango.util.fa")
   assert(ok, "Unable to load frango.util.fa")
end

function test_02_instantiate()
   local ok, fa = pcall(require, "frango.util.fa")
   assert(ok, "Unable to load frango.util.fa")
   local mymemo = fa.new()
   assert(mymemo, "Unable to instantiate a fa")
end

module("frango-util-fa-main", package.seeall, lunit.testcase)

local famod, memoiser

function setup()
   local ok, _fa = pcall(require, "frango.util.fa")
   assert(ok, "Unable to load frango.util.fa")
   famod = _fa
   local ok, _mem = pcall(require, "frango.util.memoset")
   assert(ok, "Unable to load frango.util.memoset")
   memoiser = _mem.new()
end

function teardown()
   famod = nil
   memoiser = nil
end

local function new_fa(...)
   return assert(famod.new(...), "Unable to allocate a FA")
end

local function new_state(fa)
   return assert(fa:newstate(), "Unable to allocate a new state")
end

function test_newstate()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   local st2 = new_state(nfa)
   assert(st1 ~= st2, "Unable to allocate independent states")
end

function test_onestate()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   local all = nfa:allstates()
   assert(next(all) == st1, "Newly allocated state not first in newly allocated FA")
   assert(next(all, st1) == nil, "Newly allocated state not only in newly allocated FA")
end

function test_all_states_returned()
   local nfa = new_fa()
   local sts = {}
   sts[new_state(nfa)] = true
   sts[new_state(nfa)] = true
   sts[new_state(nfa)] = true
   sts[new_state(nfa)] = true
   local sts1 = memoiser(sts)
   local sts2 = memoiser(nfa:allstates())
   assert(sts1 == sts2, "All states are returned in the :allstates() set")
end

function test_mark_start()
   local nfa = new_fa()
   local st = new_state(nfa)
   assert(nfa:statetype(st) == "mid", "New state is not a mid-state")
   nfa:markstart(st)
   assert(nfa:statetype(st) == "start", "Marked-as-start state is not a start-state")
end

function test_unmark_start()
   local nfa = new_fa()
   local st = new_state(nfa)
   nfa:markstart(st)
   nfa:unmarkstart(st)
   assert(nfa:statetype(st) == "mid", "Un-marked-as-start state is not a mid-state")
end

function test_startstates()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   nfa:markstart(st1)
   local st2 = new_state(nfa)
   local sts = nfa:startstates()
   assert(sts[st1], "Start state not in :startstates() set")
   assert(not(sts[st2]), "Non-start state in :startstates() set")
end

function test_midstates()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   nfa:markstart(st1)
   local st2 = new_state(nfa)
   local sts = nfa:midstates()
   assert(sts[st2], "Mid state not in :midstates() set")
   assert(not(sts[st1]), "Start state in :midstates() set")
end

function test_mark_accepting_plain()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   nfa:markaccepting(st1)
   assert(nfa:statetype(st1) == "accepting", "marked-as-accepting state doesn't accept")
end

function test_unmark_accepting_plain()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   nfa:markaccepting(st1)
   nfa:unmarkaccepting(st1)
   assert(nfa:statetype(st1) == "mid", "unmarked-as-accepting state isn't a mid-state")
end

function test_acceptingstates()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   local st2 = new_state(nfa)
   nfa:markaccepting(st1)
   local sts = nfa:acceptingstates()
   assert(sts[st1], "accepting state not in :acceptingstates()")
   assert(not(sts[st2]), "mid-state in :acceptingstates()")
   sts = nfa:midstates()
   assert(not(sts[st1]), "accepting state in :midstates()")
end

function test_mark_accepting_tagged()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   nfa:markaccepting(st1, "moose")
   local t, as = nfa:statetype(st1)
   assert(t == "accepting", "marked-as-accepting state with tag doesn't accept")
   assert(as.moose, "tag missing from accepting state")
end

function test_unmark_accepting_tagged()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   nfa:markaccepting(st1, "moose")
   local t, as = nfa:statetype(st1)
   assert(t == "accepting", "marked-as-accepting state with tag doesn't accept")
   assert(as.moose, "tag missing from accepting state")
   nfa:unmarkaccepting(st1, "moose")
   assert(nfa:statetype(st1) == "mid", "unmarked-as-accepting state with tag isn't mid-state")
end

function test_newarc()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   local st2 = new_state(nfa)
   nfa:newarc(st1, "a", st2)
   local arcs = nfa:allarcs()
   local arc = arcs[1]
   assert(arc, "No arc was created")
   assert(not arc[2], "More than one arc was created")
   assert(arc[1] == st1, "Source state on arc was wrong")
   assert(arc[2] == "a", "Token on arc was wrong")
   assert(arc[3] == st2, "Goal state on arc was wrong")
end

function test_arcsinto()
   local nfa = new_fa()
   local st1 = new_state(nfa)
   local st2 = new_state(nfa)
   nfa:newarc(st1, "a", st2)
   local arcs = nfa:allarcs()
   local arc = arcs[1]
   assert(arc, "No arc was created")
   assert(not arc[2], "More than one arc was created")
   arcs = nfa:arcsinto(st2)
   local arc = arcs[1]
   assert(arc, "No arc was created")
   assert(not arc[2], "More than one arc was created")
   assert(arc[1] == st1, "Source state on arc was wrong")
   assert(arc[2] == "a", "Token on arc was wrong")
   assert(arc[3] == st2, "Goal state on arc was wrong")
   arcs = nfa:arcsoutof(st1)
   local arc = arcs[1]
   assert(arc, "No arc was created")
   assert(not arc[2], "More than one arc was created")
   assert(arc[1] == st1, "Source state on arc was wrong")
   assert(arc[2] == "a", "Token on arc was wrong")
   assert(arc[3] == st2, "Goal state on arc was wrong")
end