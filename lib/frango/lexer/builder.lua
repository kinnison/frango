-- lib/frango/lexer/builder.lua
--
-- Lexer builder
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

module(..., package.seeall)

local INCLUSIVE = "inclusive"
local EXCLUSIVE = "exclusive"

local memosetmod = require "frango.util.memoset"
local famod = require "frango.util.fa"
local remod = require "frango.util.re"
local lexermod = require "frango.lexer"

local methods = {}

function methods:newstate(statename, isexclusive)
   self.states[statename] = isexclusive and EXCLUSIVE or INCLUSIVE
end

function methods:startState(statename)
   self.startstate = statename
end

function methods:addRE(restr, actiontag, states)
   actiontag = actiontag or lexermod.MORETOKEN
   if actiontag == lexermod.MORETOKEN then
      actiontag = ("%s %d"):format(actiontag, self.morecounter)
      self.morecounter = self.morecounter + 1
   end
   local re = (type(restr) == "string") and remod.parse(restr, actiontag) or restr
   if not states then 
      states = {["*"] = true} 
   end
   local mstates = self.ms(states)
   self.exprs[re] = { states, actiontag }
   if actiontag then
      self.prio[#self.prio + 1] = actiontag
      self.prio[actiontag] = #self.prio
   end
end

function methods:build()
   -- The lexer has a number of states, each state needs a DFA building for it
   -- and then we work from there.
   local dfas = {}
   local _D = function(...) io.stderr:write(string.format(...)) end
   for sname, stype in pairs(self.states) do
      _D("Building state %s\n", sname)
      local fa
      for re, info in pairs(self.exprs) do
	 for qstate in pairs(info[1]) do
	    if (qstate == sname) or
	       ((qstate == "*" and stype == INCLUSIVE)) then
	       _D("Considering RE for %q because of qstate %q\n",
		  info[2] or "<NIL>", qstate)
	       if fa then
		  fa:bifurcate(re)
	       else
		  fa = re:clone()
	       end
	    end
	 end
      end
      _D("Running hopcroft\n")
      fa = fa:hopcroft()
      _D("Simplifying accepting states\n")
      for astate in pairs(fa:acceptingstates()) do
	 local _, toks = fa:statetype(astate)
	 local besttok = next(toks)
	 if besttok and next(toks, besttok) then
	    for tok in pairs(toks) do
	       _D("Comparing %s to %s\n", tostring(tok), tostring(besttok))
	       if self.prio[tok] < self.prio[besttok] then
		  besttok = tok
	       end
	    end
	    for tok in pairs(toks) do
	       if tok ~= besttok then
		  _D("Removing token %s as it is less good than %s\n",
		     tok, besttok)
		  fa:unmarkaccepting(astate, tok)
	       end
	    end
	 end
      end
      dfas[sname] = fa
   end
   _D("State RE DFAs built, preparing lexer...\n")
   local ret = lexermod.new()
   if self.trackws then
      ret:trackWhiteSpace()
   end
   for sname in pairs(self.states) do
      ret:addState(sname, dfas[sname])
   end
   ret:setState(self.startstate)
   return ret
end

local metatable = {
   __index = methods
}

function new(trackws)
   local state = {
      ms = memosetmod.new(),
      trackws = trackws, 
      states = {START = INCLUSIVE},
      exprs = {},
      startstate = "START",
      prio = {},
      morecounter = 0
   }
   return setmetatable(state, metatable)
end
