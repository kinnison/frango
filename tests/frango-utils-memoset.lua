-- tests/frango-util-memoset.lua
--
-- Tests for frango.util.memoset
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

require "lunit"

local function Set(_t)
   local t = {}
   for _, v in ipairs(_t) do
      t[v] = "Harry"
   end
   return t
end

module("frango-util-memoset-basics", package.seeall, lunit.testcase)

function test_01_load_module()
   local ok, memoset = pcall(require, "frango.util.memoset")
   assert(ok, "Unable to load frango.util.memoset")
end

function test_02_instantiate()
   local ok, memoset = pcall(require, "frango.util.memoset")
   assert(ok, "Unable to load frango.util.memoset")
   local mymemo = memoset.new()
   assert(mymemo, "Unable to instantiate a memoset")
end

module("frango-util-memoset-main", package.seeall, lunit.testcase)

local memoset

function setup()
   local ok, ms = pcall(require, "frango.util.memoset")
   assert(ok, "Unable to load frango.util.memoset")
   assert_table(ms, "frango.util.memoset didn't give us a table")
   assert_function(ms.new, "frango.util.memoset.new isn't a function!")
   memoset = ms.new()
end

function teardown()
   memoset = nil
end

function test_00_set_memoise_empty_ok()
   local s = memoset:memoise({})
   assert_table(s, "Returned set wasn't a table")
   assert(next(s) == nil, "Returned set wasn't empty")
end

function test_01_set_basic_memoise_unchanged()
   local s = memoset:memoise(Set{1})
   assert_table(s, "Returned set wasn't a table")
   assert_boolean(s[1], "Returned single element set wasn't boolean")
   assert(s[1] == true, "Returned single element set wasn't true")
end

function test_02_set_basic_memoise_works()
   local a = memoset:memoise(Set{1})
   local b = memoset:memoise(Set{1})
   assert(a == b, "Memoisation failed to work")
end

function test_03_set_memoise_memoize_same()
   local a = memoset:memoise(Set{1})
   local b = memoset:memoize(Set{1})
   assert(a == b, "Memoisation failed to work")
end

function test_04_set_memoise_by_call_ok()
   local a = memoset(Set{1})
   local b = memoset(Set{1})
   assert(a == b, "Memoisation failed to work")
end

function test_05_set_ordering_ignored()
   local a = memoset(Set{1,2,3})
   local b = memoset(Set{3,1,2})
   local c = memoset(Set{2,1,3})
   assert(a == b, "Memoisation failed to work")
   assert(a == c, "Memoisation failed to work")
end

function test_06_set_types_ok()
   local a = memoset(Set{"a"})
   local b = memoset(Set{"a"})
   assert(a == b, "Memoisation failed to work")
end

function test_07_set_types_matter()
   local a = memoset(Set{ 1 })
   local b = memoset(Set{ "1" })
   assert(a ~= b, "Memoisation over-zealous")
end
