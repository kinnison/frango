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

local memosetmod = require "frango.util.memoset"

local methods, _new = {}

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

function methods:newarc(_st1, token, _st2, existsok)
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
   assert((not arcpresent) or existsok, "Arc already exists from " .. tostring(_st1) .. " on ".. tostring(token) .. " to " .. tostring(_st2))
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

-- Convenient helper methods

function methods:__copyinto(new_fa)
   local statemap = {}
   for stname, stab in pairs(self.states) do
      statemap[stname] = new_fa:newstate()
      if (stab.stype == STARTSTATE) then
	 new_fa:markstart(statemap[stname])
      elseif (stab.stype == ACCEPTINGSTATE) then
	 if next(stab.accepts) then
	    for k in pairs(stab.accepts) do
	       new_fa:markaccepting(statemap[stname], k)
	    end
	 else
	    new_fa:markaccepting(statemap[stname])
	 end
      end
   end
   for _, arc in ipairs(self:allarcs()) do
      new_fa:newarc(statemap[arc[1]], arc[2], statemap[arc[3]])
   end
   return statemap
end

function methods:append(fa)
   local accepts = self:acceptingstates()
   local starts = fa:startstates()
   local statemap = fa:__copyinto(self)
   -- unmark "old" accepting states
   for state in pairs(accepts) do
      local _, acc = self:statetype(state)
      if next(acc) == nil then
	 self:unmarkaccepting(state)
      else
	 for tok in pairs(acc) do
	    self:unmarkaccepting(state, tok)
	 end
      end
   end
   -- unmark "new" start states
   for state in pairs(starts) do
      self:unmarkstart(statemap[state])
   end
   -- Apply epsilons
   for source in pairs(accepts) do
      for goal in pairs(starts) do
	 self:newarc(source, EPSILON, statemap[goal])
      end
   end
end

function methods:kleenestar()
   -- Convert the current FA to a kleene-closure star operation
   local starts = self:startstates()
   local accepts = self:acceptingstates()
   local accepttokens = {}
   -- Add a new EPSILON from every old END to every old START
   for s in pairs(starts) do
      for e in pairs(accepts) do
	 self:newarc(e, EPSILON, s)
	 local _, toks = self:statetype(e)
	 for t in pairs(toks) do
	    accepttokens[t] = true
	    self:unmarkaccepting(e, t)
	 end
      end
      self:unmarkstart(s)
   end
   -- Clear any remaining old accepts
   for e in pairs(self:acceptingstates()) do
      self:unmarkaccepting(e)
   end
   local newstart = self:newstate()
   local newacc = self:newstate()
   -- Mark the new start and accept tokens
   self:markstart(newstart)
   if next(accepttokens) then
      for t in pairs(accepttokens) do
	 self:markaccepting(newacc, t)
      end
   else
      self:markaccepting(newacc)
   end
   -- Add epsilon from the new start to every old start
   for s in pairs(starts) do
      self:newarc(newstart, EPSILON, s)
   end
   -- And from every old end to the new end
   for e in pairs(accepts) do
      self:newarc(e, EPSILON, newacc)
   end
   -- And finally the bypass epsilon from the new start to the new acc
   self:newarc(newstart, EPSILON, newacc)
end

function methods:bifurcate(fa)
   local statemap = fa:__copyinto(self)

   local oldstarts = self:startstates()
   -- Alternation is the creation of a new start state
   -- which is epsilon linked to the old start states of the two FAs
   local newstart = self:newstate()
   self:markstart(newstart)
   for s in pairs(oldstarts) do
      self:unmarkstart(s)
      self:newarc(newstart, EPSILON, s)
   end
end

function methods:alternate(fa)
   -- To alternate, first some bifurcation
   self:bifurcate(fa)
   -- Then the creation of a new accepting state.  All tokens are thusly
   -- transferred and EPSILON links from the old accepters to teh new one
   local tottoks = {}
   local newacc = self:newstate()
   local oldaccs = self:acceptingstates()
   for a in pairs(oldaccs) do
      local _, toks = self:statetype(a)
      if next(toks) then
	 for t in pairs(toks) do
	    self:unmarkaccepting(a, t)
	    tottoks[t] = true
	 end
      else
	 self:unmarkaccepting(a)
      end
      self:newarc(a, EPSILON, newacc)
   end
   if next(tottoks) then
      for t in pairs(tottoks) do
	 self:markaccepting(newacc, t)
      end
   else
      self:markaccepting(newacc)
   end
end

function methods:plus()
   -- Plus is {self}{self}*
   local starred = self:clone()
   starred:kleenestar()
   self:append(starred)
end

function methods:question()
   -- Simples, add epsilon from every start to every accepting state
   for s in pairs(self:startstates()) do
      for e in pairs(self:acceptingstates()) do
	 self:newarc(s, EPSILON, e)
      end
   end
end

-- Convenience routines for NFA->DFA conversion

function methods:epsilonclosure(stateset)
   local reachedset = {}
   local testset = {}
   for s in pairs(stateset) do
      testset[s] = true
   end
   while next(testset) do
      local state = next(testset)
      if not reachedset[state] then
	 reachedset[state] = true
	 for _, arc in ipairs(self:arcsoutof(state)) do
	    if arc[2] == EPSILON then
	       if not (reachedset[arc[3]] or testset[arc[3]]) then
		  testset[arc[3]] = true
	       end
	    end
	 end
      end
      testset[state] = nil
   end
   return reachedset
end

function methods:delta(stateset, token)
   local reachedset = {}
   for s in pairs(stateset) do
      for _, arc in ipairs(self:arcsoutof(s)) do
	 if arc[2] == token then
	    reachedset[arc[3]] = true
	 end
      end
   end
   return reachedset
end

-- Conversion from NFA -> DFA

function methods:makedfa()
   local ms = memosetmod.new()
   local statemap = {}
   local ret = _new()
   local none = ms{}

   local alphabet = {}

   for _, arc in pairs(self:allarcs()) do
      alphabet[arc[2]] = true
   end
   alphabet[EPSILON] = nil

   local acc = self:acceptingstates()
   local q0 = ms(self:epsilonclosure(self:startstates()))

   statemap[q0] = ret:newstate()
   ret:markstart(statemap[q0])

   local worklist = { [q0] = true }

   local function _printstate(n, _s)
	 io.stderr:write(("%s = {"):format(n))
	 local first = ""
	 local s = {}
	 for ss in pairs(_s) do
	    s[#s+1] = ss
	 end
	 table.sort(s)
	 for _, ss in ipairs(s) do
	    io.stderr:write(("%s %s"):format(first, ss))
	    first = ","
	 end
	 io.stderr:write(" }\n")
	 io.stderr:flush()
      end

   _printstate("acc", acc)

   _printstate("q0", q0)
      

   while next(worklist) do
      local q = next(worklist)
      worklist[q] = nil
      _printstate("q", q)
      for tok in pairs(alphabet) do
	 local t = ms(self:epsilonclosure(self:delta(q, tok)))
	 _printstate(("t[%s]"):format(tok), t)
	 if t ~= none then
	    if not statemap[t] then
	       statemap[t] = ret:newstate()
	       local marked = false
	       for st in pairs(t) do
		  if acc[st] then
		     local _, toks = self:statetype(st)
		     for newt in pairs(toks) do
			ret:markaccepting(statemap[t], newt)
		     end
		     if not marked then
			ret:markaccepting(statemap[t])
		     end
		  end
	       end
	       worklist[t] = true
	    end
	    ret:newarc(statemap[q], tok, statemap[t], true)
	 end
      end
   end
   return ret
end

-- Output mode

function methods:writedot(fh)
   fh:write("digraph FA {\n")
   for s in pairs(self:allstates()) do
      local st, toks = self:statetype(s)
      if st == MIDSTATE then
	 fh:write(("   %s [label=\"%s\"]\n"):format(s,s))
      elseif st == STARTSTATE then
	 fh:write(("   %s [label=\"%s\", color=red, sides=3, shape=polygon]\n"):format(s,s))
      else
	 if next(toks) == nil then
	    fh:write(("   %s [label=\"%s\", color=blue]\n"):format(s,s))
	 else
	    local toka = {}
	    for t in pairs(toks) do
	       toka[#toka+1] = t
	    end
	    fh:write(("   %s [label=\"%s [%s]\", color=blue]\n"):format(s, s, table.concat(toka, ",")))
	 end
      end
   end
   fh:write("\n")
   for _, arc in ipairs(self:allarcs()) do
      local s1, tok, s2 = unpack(arc)
      if tok == EPSILON then
	 fh:write(("   %s -> %s [weight=0, style=dashed]\n"):format(s1, s2))
      else
	 fh:write(("   %s -> %s [label=%q]\n"):format(s1, s2, tok))
      end
   end

   fh:write("}\n")
end

-- Construction

function methods:clone()
   local new_fa = new()
   self:__copyinto(new_fa)
   return new_fa
end

local metatable = {
   __index = methods,
}


function _new()
   local baseline = {
      states = {},
      statecounter = 0,
   }
   return setmetatable(baseline, metatable)
end

new = _new
