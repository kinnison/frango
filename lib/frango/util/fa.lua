-- lib/frango/util/fa.lua
--
-- Finite (Both deterministic and non-) Automata
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

module(..., package.seeall)

EPSILON = "<EPSILON>"

local MIDSTATE = "mid"
local STARTSTATE = "start"
local ACCEPTINGSTATE = "accepting"

local methods = {}

local function _nil_or_copy(t)
   if t == nil then return end
   local r = {}
   for k, v in pairs(t) do
      r[k] = v
   end
   return r
end

function methods:newstate()
   local ns = self.statecounter
   self.statecounter = ns + 1
   ns = ("s%d"):format(ns)
   self.states[ns] = { stname = ns, stype = MIDSTATE, txout = {}, txin = {} }
   return ns
end

function methods:delstate(_st)
   local st = assert(self.states[_st], tostring(_st) .. " is not a state in " .. tostring(sel))
   assert(next(st.txout) == nil, "Cannot delete state " .. tostring(_st) .. " as it has arcs leading out of it")
   assert(next(st.txin) == nil, "Cannot delete state " .. tostring(_st) .. " as it has arcs leading into it")
   self.states[_st] = nil
end

function methods:statetype(st)
   local t = assert(self.states[st], tostring(st) .. " is not a state in " .. tostring(self))
   return t.stype, _nil_or_copy(t.accepts)
end

function methods:allstates()
   local ret = {}
   for k in pairs(self.states) do
      ret[k] = true
   end
   return ret
end

function methods:markstart(st)
   local t = assert(self.states[st], tostring(st) .. " is not a state in " .. tostring(self))
   assert(t.stype == MIDSTATE, tostring(st) .. " is not a mid-state")
   t.stype = STARTSTATE
end

function methods:unmarkstart(st)
   local t = assert(self.states[st], tostring(st) .. " is not a state in " .. tostring(self))
   assert(t.stype == STARTSTATE, tostring(st) .. " is not a start-state")
   t.stype = MIDSTATE
end

function methods:startstates()
   local ret = {}
   for k, t in pairs(self.states) do
      if t.stype == STARTSTATE then
	 ret[k] = true
      end
   end
   return ret
end

function methods:midstates()
   local ret = {}
   for k, t in pairs(self.states) do
      if t.stype == MIDSTATE then
	 ret[k] = true
      end
   end
   return ret
end

function methods:markaccepting(st, tag)
   local t = assert(self.states[st], tostring(st) .. " is not a state in " .. tostring(self))
   assert((t.stype == MIDSTATE) or (t.stype == ACCEPTINGSTATE), tostring(st) .. " is not a mid-state or accepting-state")
   t.stype = ACCEPTINGSTATE
   t.accepts = t.accepts or {}
   if tag then
      t.accepts[tag] = true
   end
end

function methods:unmarkaccepting(st, tag)
   local t = assert(self.states[st], tostring(st) .. " is not a state in " .. tostring(self))
   assert(t.stype == ACCEPTINGSTATE, tostring(st) .. " is not a mid-state")
   if tag then
      assert(t.accepts[tag], tostring(tag) .. " is not an accepting tag on " .. tostring(st))
      t.accepts[tag] = nil
      if next(t.accepts) == nil then
	 t.stype = MIDSTATE
	 t.accepts = nil
      end
   elseif next(t.accepts) == nil then
      t.stype = MIDSTATE
      t.accepts = nil
   else
      assert(false, "Unable to unmark tagged accepting state without the tag")
   end
end

function methods:acceptingstates()
   local ret = {}
   for k, t in pairs(self.states) do
      if t.stype == ACCEPTINGSTATE then
	 ret[k] = true
      end
   end
   return ret
end

function methods:newarc(_st1, token, _st2)
   local st1 = assert(self.states[_st1], tostring(_st1) .. " is not a state in " .. tostring(self))
   local st2 = assert(self.states[_st2], tostring(_st2) .. " is not a state in " .. tostring(self))
   local arcpresent = true
   local txst1 = st1.txout[token] or {}
   if not txst1[st2] then
      txst1[st2] = true
      st1.txout[token] = txst1
      arcpresent = false
   end
   local txst2 = st2.txin[token] or {}
   if not txst2[st1] then
      txst2[st1] = true
      st2.txin[token] = txst2
      arcpresent = false
   end
   assert(not arcpresent, "Arc already exists from " .. tostring(_st1) .. " on ".. tostring(token) .. " to " .. tostring(_st2))
end

function methods:delarc(_st1, token, _st2)
   local st1 = assert(self.states[_st1], tostring(_st1) .. " is not a state in " .. tostring(self))
   local st2 = assert(self.states[_st2], tostring(_st2) .. " is not a state in " .. tostring(self))
   local arcabsent = true
   local txst1 = st1.txout[token] or {}
   if txst1[st2] then
      txst1[st2] = nil
      st1.txout[token] = next(txst1) and txst1 or nil
      arcabsent = false
   end
   local txst2 = st2.txin[token] or {}
   if txst2[st1] then
      txst2[st1] = nil
      st2.txin[token] = next(txst2) and txst2 or nil
      arcabsent = falsex
   end
   assert(not arcabsent, "Arc did not exist from " .. tostring(_st1) .. " on ".. tostring(token) .. " to " .. tostring(_st2))
end

function methods:allarcs()
   local ret = {}
   for state, stab in pairs(self.states) do
      for token, goals in pairs(stab.txout) do
	 for goal in pairs(goals) do
	    ret[#ret+1] = {state, token, goal.stname}
	 end
      end
   end
   return ret
end

function methods:arcsinto(_st)
   local st = assert(self.states[_st], tostring(_st) .. " is not a state in " .. tostring(self))
   local ret = {}
   for token, sources in pairs(st.txin) do
      for source in pairs(sources) do
	 ret[#ret+1] = { source.stname, token, _st }
      end
   end
   return ret
end

function methods:arcsoutof(_st)
   local st = assert(self.states[_st], tostring(_st) .. " is not a state in " .. tostring(self))
   local ret = {}
   for token, goals in pairs(st.txout) do
      for goal in pairs(goals) do
	 ret[#ret+1] = { _st, token, goal.stname }
      end
   end
   return ret
end

-- Construction

local metatable = {
   __index = methods,
}


function new()
   local baseline = {
      states = {},
      statecounter = 0,
   }
   return setmetatable(baseline, metatable)
end
