--[[
    Catify - Commercial Lua Obfuscator
    src/parser.lua - Lua 5.3 bytecode parser

    Reads the binary output of string.dump() and returns a structured Proto table.
    Format reference: Lua 5.3 source – lcode.c, ldump.c, lopcodes.h
]]

local Parser = {}

-- ─── Lua 5.3 opcode names (index 0..46) ──────────────────────────────────────
Parser.OPNAMES = {
    [0]  = "MOVE",    [1]  = "LOADK",    [2]  = "LOADKX",  [3]  = "LOADBOOL",
    [4]  = "LOADNIL", [5]  = "GETUPVAL", [6]  = "GETTABUP",[7]  = "GETTABLE",
    [8]  = "SETTABUP",[9]  = "SETUPVAL", [10] = "SETTABLE", [11] = "NEWTABLE",
    [12] = "SELF",    [13] = "ADD",       [14] = "SUB",      [15] = "MUL",
    [16] = "MOD",     [17] = "POW",       [18] = "DIV",      [19] = "IDIV",
    [20] = "BAND",    [21] = "BOR",       [22] = "BXOR",     [23] = "SHL",
    [24] = "SHR",     [25] = "UNM",       [26] = "BNOT",     [27] = "NOT",
    [28] = "LEN",     [29] = "CONCAT",    [30] = "JMP",      [31] = "EQ",
    [32] = "LT",      [33] = "LE",        [34] = "TEST",     [35] = "TESTSET",
    [36] = "CALL",    [37] = "TAILCALL",  [38] = "RETURN",   [39] = "FORLOOP",
    [40] = "FORPREP", [41] = "TFORCALL",  [42] = "TFORLOOP", [43] = "SETLIST",
    [44] = "CLOSURE", [45] = "VARARG",    [46] = "EXTRAARG",
}
Parser.NUM_OPCODES = 47

-- ─── Binary reader ────────────────────────────────────────────────────────────

local Reader = {}
Reader.__index = Reader

function Reader.new(data)
    return setmetatable({ data = data, pos = 1, size_t = 8 }, Reader)
end

function Reader:read_byte()
    local b = self.data:byte(self.pos)
    self.pos = self.pos + 1
    return b
end

function Reader:read_int()
    local v, p = string.unpack("<i4", self.data, self.pos)
    self.pos = p
    return v
end

function Reader:read_uint32()
    local v, p = string.unpack("<I4", self.data, self.pos)
    self.pos = p
    return v
end

-- Powers-of-two constants used by the 32-bit integer fallback
local _TWO32 = 4294967296.0      -- 2^32
local _TWO31 = 2147483648        -- 2^31  (high-bit threshold for sign detection)
local _TWO64 = 18446744073709551616.0  -- 2^64

function Reader:read_int64()
    -- Try signed 64-bit first (works on 64-bit Lua 5.3+)
    local ok, v, p = pcall(string.unpack, "<i8", self.data, self.pos)
    if ok then self.pos = p; return v end
    -- Fallback for 32-bit Lua: read as two unsigned 32-bit halves and combine.
    -- Integers beyond ±2^53 cannot be represented exactly as doubles, but valid
    -- Lua integer constants in practice are well within that range.
    local lo, p2 = string.unpack("<I4", self.data, self.pos)
    local hi, p3 = string.unpack("<I4", self.data, p2)
    self.pos = p3
    local val = lo + hi * _TWO32
    if hi >= _TWO31 then val = val - _TWO64 end
    return val
end

function Reader:read_double()
    local v, p = string.unpack("<d", self.data, self.pos)
    self.pos = p
    return v
end

--- Read a string in the Lua 5.3 bytecode format:
---   0x00                         → nil
---   byte (len+1) where len < 255 → short string (len bytes follow, no NUL)
---   0xFF, size_t (len+1)         → long string
function Reader:read_string()
    local b = self:read_byte()
    if b == 0 then return nil end
    local len
    if b == 0xFF then
        -- long string: read size_t (8 bytes on 64-bit Lua)
        local v, p = string.unpack("<I8", self.data, self.pos)
        self.pos = p
        len = v - 1
    else
        len = b - 1
    end
    if len == 0 then return "" end
    local s = self.data:sub(self.pos, self.pos + len - 1)
    self.pos = self.pos + len
    return s
end

-- ─── Proto parser ─────────────────────────────────────────────────────────────

local function parse_proto(r)
    local proto = {}

    -- Source / position info
    proto.source         = r:read_string()
    proto.linedefined    = r:read_int()
    proto.lastlinedefined= r:read_int()
    proto.numparams      = r:read_byte()
    proto.is_vararg      = r:read_byte()
    proto.maxstacksize   = r:read_byte()

    -- Instructions (0-indexed array of uint32)
    local sizecode = r:read_int()
    local code = {}
    for i = 0, sizecode - 1 do
        code[i] = r:read_uint32()
    end
    proto.code     = code
    proto.sizecode = sizecode

    -- Constants (0-indexed)
    local sizek = r:read_int()
    local k = {}
    for i = 0, sizek - 1 do
        local t = r:read_byte()
        if t == 0 then          -- LUA_TNIL
            k[i] = nil
        elseif t == 1 then      -- LUA_TBOOLEAN
            k[i] = (r:read_byte() ~= 0)
        elseif t == 3 then      -- LUA_TNUMFLT (float)
            k[i] = r:read_double()
        elseif t == 0x13 then   -- LUA_TNUMINT (integer)
            k[i] = r:read_int64()
        elseif t == 4 or t == 0x14 then  -- short/long string
            k[i] = r:read_string()
        else
            error(string.format("Unknown constant type 0x%02X at index %d", t, i))
        end
    end
    proto.k     = k
    proto.sizek = sizek

    -- Upvalue descriptors (0-indexed)
    local sizeupvalues = r:read_int()
    local upvals = {}
    for i = 0, sizeupvalues - 1 do
        upvals[i] = {
            instack = r:read_byte(),
            idx     = r:read_byte(),
        }
    end
    proto.upvals      = upvals
    proto.sizeupvalues= sizeupvalues

    -- Nested prototypes (0-indexed)
    local sizep = r:read_int()
    local p = {}
    for i = 0, sizep - 1 do
        p[i] = parse_proto(r)
    end
    proto.p     = p
    proto.sizep = sizep

    -- Debug info: line info
    local sizelineinfo = r:read_int()
    local lineinfo = {}
    for i = 0, sizelineinfo - 1 do
        lineinfo[i] = r:read_int()
    end
    proto.lineinfo     = lineinfo
    proto.sizelineinfo = sizelineinfo

    -- Debug info: local variables
    local sizelocvars = r:read_int()
    local locvars = {}
    for i = 0, sizelocvars - 1 do
        locvars[i] = {
            varname = r:read_string(),
            startpc = r:read_int(),
            endpc   = r:read_int(),
        }
    end
    proto.locvars     = locvars
    proto.sizelocvars = sizelocvars

    -- Debug info: upvalue names
    local sizeuvnames = r:read_int()
    local uvnames = {}
    for i = 0, sizeuvnames - 1 do
        uvnames[i] = r:read_string()
    end
    proto.uvnames     = uvnames
    proto.sizeuvnames = sizeuvnames

    return proto
end

-- ─── Public API ───────────────────────────────────────────────────────────────

--- Parse the output of string.dump() and return the top-level Proto table.
--- Raises an error if the bytecode header is invalid.
---@param bytecode string
---@return table proto
function Parser.parse(bytecode)
    local r = Reader.new(bytecode)

    -- Validate header
    local sig = bytecode:sub(1, 4)
    assert(sig == "\27Lua", "Invalid Lua signature")
    local ver = bytecode:byte(5)
    assert(
        ver == 0x53,
        string.format(
            "Unsupported Lua bytecode version 0x%02X (need 0x53 / Lua 5.3). Run Catify with lua5.3.",
            ver
        )
    )
    r.pos = 7   -- skip: sig(4) + version(1) + format(1)

    -- LUAC_DATA (6 bytes): "\x19\x93\r\n\x1a\n"
    r.pos = r.pos + 6
    -- sizeof fields: int, size_t, instruction, integer, number (5 bytes)
    local sz_int  = r:read_byte()
    local sz_st   = r:read_byte()
    local sz_ins  = r:read_byte()
    local sz_int2 = r:read_byte()
    local sz_num  = r:read_byte()
    assert(sz_int == 4,   "Expected sizeof(int)=4")
    assert(sz_ins == 4,   "Expected sizeof(Instruction)=4")
    -- LUAC_INT (integer) and LUAC_NUM (double)  – skip them
    r.pos = r.pos + sz_int2 + sz_num   -- 8 + 8 = 16 bytes

    -- One byte: number of upvalues for the main chunk
    local main_nupvals = r:read_byte()

    -- Parse the main function prototype
    local proto = parse_proto(r)
    proto.main_nupvals = main_nupvals
    return proto
end

return Parser
