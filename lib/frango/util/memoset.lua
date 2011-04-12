-- lib/frango/util/memoset.lua
--
-- Memoisation of sets
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

--[[
Sets are tables whose keys are the elements of the set and whose
values are irrelevant so long as they are non-nil.  Only the keys
are taken into account when memoising.  The returned set is normalised
so that all the values will be true.
]]

module(..., package.seeall)

local tsort = table.sort
local tconcat = table.concat

local methods = {}

local function key_for_set(s)
   local key, ns = {}, {}
   for k in pairs(s) do
      key[#key + 1] = ("<%s %q>"):format(type(k), tostring(k))
      ns[k] = true
   end
   tsort(key)
   return tconcat(key), ns
end

function methods:memoize(s)
   local k, ns = key_for_set(s)
   local r = self._[k] or ns
   self._[k] = r
   return r
end

methods.memoise = methods.memoize

local metatable = {
   __index = methods,
   __call = methods.memoize,
}

function new()
   return setmetatable({_={}}, metatable)
end
