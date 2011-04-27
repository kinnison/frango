-- lib/frango/lexer.lua
--
-- Primary Lexer Driver
--
-- This file is part of the Frango suite of lexer/parser tools for Lua
--
-- Copyright 2011 Daniel Silverstone <dsilvers@digital-scurf.org>
--
-- Please see the COPYING file for licence details.
--

module(..., package.seeall)

MORETOKEN = "<MORE>"
ERRORTOKEN = "<ERROR>"
EOFTOKEN = "<EOF>"

local remod = require "frango.util.re"

local methods = {}

function methods:trackWhiteSpace()
   -- Set ourselves into whitespace tracking mode.
   assert(not self._.started, "Already started lexing, cannot track now")
   self._.trackws = true
   self.position.line = 1
   self.position.char = 1
   self._.lasttoktc = 0
   self._.lasttoknl = 0
end

function methods:addState(statename, dfa)
   assert(not self._.started, "Already started lexing, cannot add states now")
   self._.states[statename] = dfa
end

function methods:setState(sname)
   assert(self._.states[sname], "Unknown state name " .. tostring(sname))
   self._.statestack = { sname }
end

function methods:pushState(sname)
   assert(self._.states[sname], "Unknown state name " .. tostring(sname))   
   self._.statestack[#self._.statestack + 1] = sname
end

function methods:peekState()
   return self._.statestack[#self._.statestack]
end

function methods:popState()
   assert(#self._.statestack > 1, "Cannot pop last state on the stack, sorry")
   self._.statestack[#self._.statestack] = nil
end

local function _D(...) io.stderr:write(string.format(...)) end
_D=function(...)end

function methods:feed(str)
   if str == nil then
      _D("No more!\n")
      self._.nomore = true
   else
      if self._.bufpos > #self._.buffer then
	 _D("Truncating buffer\n")
	 self._.buffer = ""
	 self._.bufpos = 1
      else
	 _D("Trimming buffer by %d chars\n", self._.bufpos)
	 self._.buffer = string.sub(self._.buffer, self._.bufpos, -1)
	 _D("Buffer now starts with %s\n", string.sub(self._.buffer, 1, 1))
	 self._.bufpos = 1
      end
      self._.buffer = self._.buffer .. str
   end
end

function methods:__lex()
   -- Single attempt at lexing a token
   local cdfa = self._.states[self._.statestack[#self._.statestack]]
   _D("Starting match at %d which is a %s\n", self._.bufpos, string.sub(self._.buffer, self._.bufpos, self._.bufpos))
   local ok, len, toks = remod.anchoredmatch(cdfa, self._.buffer, self._.bufpos)
   if ok then
      local ss = string.sub(self._.buffer, self._.bufpos, self._.bufpos + len - 1)
      self._.bufpos = self._.bufpos + len
      return true, next(toks or {}), ss
   end
   -- Failed to match anything, why?
   self._.failpos = len
   if self._.failpos > #self._.buffer then
      -- We failed by passing beyond the end of the buffer
      -- So ask for more
      return false, MORETOKEN
   end
   -- We failed mid-stream, so report an error
   return false, ERRORTOKEN, len
end

function methods:lex()
   -- Returns true, TOKEN, CONTENT
   -- Returns false, message
   self.position.chars = self.position.chars + self._.lasttoklen
   if self._.trackws then
      self.position.char = self.position.char + self._.lasttoktc
      self.position.line = self.position.line + self._.lasttoknl
      self._.lasttoktc = 0
      self._.lasttoknl = 0
   end
   self._.lasttoklen = 0

   local ok, token, content = self:__lex()
   _D("OK=%s TOKEN=%s CONTENT=%q\n", tostring(ok), tostring(token), tostring(content))
   if not ok then
      if token == MORETOKEN then
	 if self._.nomore then
	    token = EOFTOKEN
	 end
      end
      return ok, token
   end

   self._.lasttoklen = #content

   if self._.trackws then
      -- Count newlines
      local nl, tc = 0, 0
      for c in content:gmatch("(.)") do
	 if c == "\n" then
	    nl = nl + 1
	    tc = 0
	 else
	    tc = tc + 1
	 end
      end
      self._.lasttoknl = nl
      self._.lasttoktc = tc
   end

   if token and string.sub(token, 1, #MORETOKEN) ~= MORETOKEN then
      return ok, token, content
   end

   -- No useful token, continue scanning...
   return methods.lex(self)
end

local mtab = {
   __index = methods,
}

function new()
   local state = {
      _ = {
	 buffer = "",
	 bufpos = 1,
	 nomore = false,
	 trackws = false,
	 started = false,
	 states = {},
	 statestack = {},
	 lasttoklen = 0,
      },
      position = {
	 chars = 0,
      }
   }
   return setmetatable(state, mtab)
end
