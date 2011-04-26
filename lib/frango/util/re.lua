-- lib/frango/util/re.lua
--
-- Regular expressions (as DFAs)
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

module(..., package.seeall)

local fa = require "frango.util.fa"

local EOS = "<EOS>"

local parseRE -- Forward declaration for bracketed expressions

-- This might need to be expanded later, but for now, cover ASCII usefully
local dot_min, dot_max = 1, 126

local function DEBUG(...)
   io.stderr:write("RE: ")
   io.stderr:write(string.format(...))
   io.stderr:write("\n")
   io.stderr:flush()
end

local function AtomicFA(c)
   DEBUG("New atomic FA for %q", c)
   local re_fa = fa.new()
   local st, ac = re_fa:newstate(), re_fa:newstate()
   re_fa:markstart(st)
   re_fa:markaccepting(ac)
   re_fa:newarc(st, c, ac)
   return re_fa
end

local function DotFA()
   DEBUG("New DotFA")
   local re_fa = fa.new()
   local st, ac = re_fa:newstate(), re_fa:newstate()
   re_fa:markstart(st)
   re_fa:markaccepting(ac)
   
   for i = dot_min, dot_max do
      re_fa:newarc(st, string.char(i), ac)
   end

   return re_fa
end

local function SetFA(s)
   DEBUG("New SetFA")
   local re_fa = fa.new()
   local st, ac = re_fa:newstate(), re_fa:newstate()
   re_fa:markstart(st)
   re_fa:markaccepting(ac)
   for c in pairs(s) do
      re_fa:newarc(st, c, ac)
   end
   return re_fa
end

local function parseSet(state)
   local set = {}
   local invert = false
   local lastadd, inrange = nil, false
   
   state:reject("]")
   state:reject(EOS)

   if state:peek() == "^" then
      DEBUG("Inverting Set")
      invert = true
      state:next()
   end

   while true do
      state:reject(EOS)
      local c = state:peek()
      DEBUG("Set, considering %q", c)
      if c == "-" and lastadd then
	 inrange = true
	 c = nil
	 state:next()
      elseif c == "\\" then
	 state:next()
	 state:reject(EOS)
	 c = state:peek()
      elseif c == "]" then
	 if inrange then
	    set["-"] = true
	 end
	 break
      end
      if c then
	 if inrange then
	    local oldn, newn = string.byte(lastadd), string.byte(c)
	    if oldn < newn then
	       for i = oldn + 1, newn do
		  set[string.char(i)] = true
	       end
	    else
	       set[c] = true
	       set["-"] = true
	    end
	    lastadd = nil
	    inrange = false
	 else
	    set[c] = true
	    lastadd = c
	 end
	 state:next()
      end
   end
   state:expect("]")
   if invert then
      local newset = {}
      for i = dot_min, dot_max do
	 local c = string.char(i)
	 if not set[c] then
	    newset[c] = true
	 end
      end
      set = newset
   end

   return SetFA(set)
end

local function parseAtom(state)
   local re_fa

   state:reject(EOS)
   state:reject(")")

   DEBUG("Atomic ponder of %q", state:peek())

   if state:peek() == "(" then
      state:next()
      re_fa = parseRE(state)
      state:expect(")")
      state:next()
   elseif state:peek() == "[" then
      state:next()
      re_fa = parseSet(state)
      state:expect("]")
      state:next()
   elseif state:peek() == "\\" then
      state:next()
      state:reject(EOS)
      re_fa = AtomicFA(state:peek())
      state:next()
   elseif state:peek() == "." then
      re_fa = DotFA()
      state:next()
   else
      re_fa = AtomicFA(state:peek())
      state:next()
   end
   return re_fa
end

local function parseModdedAtom(state)
   local re_fa = parseAtom(state)
   DEBUG("Considering mod of %q", state:peek())
   if state:peek() == "*" then
      DEBUG("Kleene Star")
      re_fa:kleenestar()
      state:next()
   elseif state:peek() == "+" then
      DEBUG("Plus")
      re_fa:plus()
      state:next()
   elseif state:peek() == "?" then
      DEBUG("Question")
      re_fa:question()
      state:next()
   end
   return re_fa
end

local alternateSM = {
   [EOS] = true,
   ["|"] = true,
   [")"] = true,
}
local function parseAlternate(state)
   local re_fa = parseModdedAtom(state)
   DEBUG("Alternation pondering %q", state:peek())
   while not alternateSM[state:peek()] do
      local re_fa2 = parseModdedAtom(state)
      re_fa:append(re_fa2)
      DEBUG("Alternation pondering %q", state:peek())
   end
   return re_fa
end

function parseRE(state)
   local re_fa = parseAlternate(state)

   while state:peek() == "|" do
      state:next()
      local re_fa2 = parseAlternate(state)
      re_fa:alternate(re_fa2)
   end

   return re_fa
end

function parse(restr)
   local state = {
      str = restr,
      pos = 1,
      peek = function(self)
		if self.pos > #self.str then
		   return EOS
		else
		   return string.sub(self.str, self.pos, self.pos)
		end
	     end,
      next = function(self)
		self.pos = self.pos + 1
	     end,
      expect = function(self, t)
		  if self:peek() ~= t then
		     error("Error at position " .. tostring(self.pos) .. " in " .. self.str .. " -- Expected " .. t .. " but got " .. self:peek())
		  end
	       end,
      reject = function(self, t)
		  if self:peek() == t then
		     error("Error at position " .. tostring(self.pos) .. " in " .. self.str .. " -- Expected anything but " .. t)
		  end
	       end,
   }

   DEBUG("Prepared state for %q", restr)

   local re_fa = parseRE(state)

   state:expect(EOS)

   -- Finally, convert re_fa into a DFA, with a single accepting state
   -- whose accept token is the regular expression we were given.
   local acc_fa = fa.new()
   local acc_start, acc_acc = acc_fa:newstate(), acc_fa:newstate()
   acc_fa:markstart(acc_start)
   acc_fa:markaccepting(acc_acc, restr)
   acc_fa:newarc(acc_start, fa.EPSILON, acc_acc)
   re_fa:append(acc_fa)
   return re_fa:makedfa(), re_fa
end