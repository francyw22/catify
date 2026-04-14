--[[
    Catify - Commercial Lua Obfuscator
    src/utils.lua - Utility helpers: random identifiers, encryption, serialization
]]

local Utils = {}

-- ─── Random identifiers ──────────────────────────────────────────────────────

local ALPHA = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
local ALNUM = ALPHA .. "0123456789_"

--- Generate a single random valid Lua identifier
---@param min_len integer
---@param max_len integer
function Utils.rand_name(min_len, max_len)
    min_len = min_len or 6
    max_len = max_len or 14
    local len = math.random(min_len, max_len)
    local buf = {}
    local p0 = math.random(1, #ALPHA)
    buf[1] = ALPHA:sub(p0, p0)
    for i = 2, len do
        local p = math.random(1, #ALNUM)
        buf[i] = ALNUM:sub(p, p)
    end
    return table.concat(buf)
end

--- Generate `count` unique random identifiers (no collisions)
---@param count integer
function Utils.rand_names(count)
    local seen = {}
    local out  = {}
    while #out < count do
        local name = Utils.rand_name()
        if not seen[name] then
            seen[name] = true
            out[#out + 1] = name
        end
    end
    return out
end

-- ─── XOR cipher (pure Lua, Lua 5.1+) ─────────────────────────────────────────

--- XOR-cipher data with a repeating key
---@param data string
---@param key  string
---@return string
function Utils.xor(data, key)
    local klen = #key
    local out  = {}
    for i = 1, #data do
        out[i] = string.char(data:byte(i) ~ key:byte(((i - 1) % klen) + 1))
    end
    return table.concat(out)
end

--- Generate a random key of `len` bytes
---@param len integer
---@return string
function Utils.rand_key(len)
    len = len or 32
    local buf = {}
    for i = 1, len do
        buf[i] = string.char(math.random(1, 255))
    end
    return table.concat(buf)
end

-- ─── RC4 (PRGA-only, keyed with the supplied key) ────────────────────────────

--- RC4 cipher (symmetric – same function encrypts & decrypts)
---@param data string
---@param key  string
---@return string
function Utils.rc4(data, key)
    -- Key-scheduling (KSA)
    local S = {}
    for i = 0, 255 do S[i] = i end
    local j = 0
    local klen = #key
    for i = 0, 255 do
        j = (j + S[i] + key:byte((i % klen) + 1)) % 256
        S[i], S[j] = S[j], S[i]
    end
    -- Pseudo-random generation (PRGA)
    local out = {}
    local si = 0
    j = 0
    for n = 1, #data do
        si = (si + 1) % 256
        j  = (j + S[si]) % 256
        S[si], S[j] = S[j], S[si]
        out[n] = string.char(data:byte(n) ~ S[(S[si] + S[j]) % 256])
    end
    return table.concat(out)
end

-- ─── Table shuffle (Fisher–Yates) ────────────────────────────────────────────

--- Shuffle a 0-indexed table in-place
---@param t    table
---@param size integer  number of elements (indices 0 .. size-1)
function Utils.shuffle0(t, size)
    for i = size - 1, 1, -1 do
        local j = math.random(0, i)
        t[i], t[j] = t[j], t[i]
    end
end

--- Generate a random bijective opcode mapping:
---   opmap[orig_op] = shuffled_op   (what to write into bytecode)
---   revmap[shuffled_op] = orig_op  (what the VM decodes back)
---@param n integer number of opcodes
---@return table opmap, table revmap
function Utils.gen_opcode_map(n)
    -- Start with identity
    local opmap  = {}
    local revmap = {}
    for i = 0, n - 1 do opmap[i] = i end
    Utils.shuffle0(opmap, n)
    for orig = 0, n - 1 do
        revmap[opmap[orig]] = orig
    end
    return opmap, revmap
end

-- ─── Byte-string serialization helpers ───────────────────────────────────────

--- Encode a byte string as a Lua \NNN escape string (no quotes)
---@param data string
---@return string
function Utils.to_escape(data)
    local out = {}
    for i = 1, #data do
        out[i] = string.format("\\%d", data:byte(i))
    end
    return table.concat(out)
end

--- Encode a byte string as a hex-escaped Lua string literal (with quotes)
---@param data string
---@return string
function Utils.quoted_bytes(data)
    return '"' .. Utils.to_escape(data) .. '"'
end

-- ─── Little-endian binary writers (for custom bytecode format) ───────────────

local function pack_u8(v)
    return string.char(v & 0xFF)
end

local function pack_i32(v)
    v = v & 0xFFFFFFFF
    return string.char(v & 0xFF, (v >> 8) & 0xFF, (v >> 16) & 0xFF, (v >> 24) & 0xFF)
end

local function pack_u32(v)
    return pack_i32(v)
end

local function pack_f64(v)
    return string.pack("<d", v)
end

local function pack_i64(v)
    return string.pack("<i8", v)
end

local function pack_str(s)
    if s == nil then
        return pack_i32(0)
    end
    return pack_i32(#s) .. s
end

Utils.pack_u8  = pack_u8
Utils.pack_i32 = pack_i32
Utils.pack_u32 = pack_u32
Utils.pack_f64 = pack_f64
Utils.pack_i64 = pack_i64
Utils.pack_str = pack_str

-- ─── Number obfuscation ───────────────────────────────────────────────────────

--- Return a Lua expression that evaluates to the integer n,
--- assembled from random arithmetic on random parts.
---@param n integer
---@return string
function Utils.obfuscate_int(n)
    local a = math.random(1, 0x7FFF)
    local b = n - a
    -- e.g.  ( a + b )  or  ( a - (-b) )
    if math.random(1, 2) == 1 then
        return string.format("(%d+%d)", a, b)
    else
        return string.format("(%d-(%d))", a, -b)
    end
end

--- Return a complex multi-layer Lua expression that evaluates to integer n.
--- Uses XOR-split encoding (a ~ (a ~ n) == n) with additive noise so the
--- value is not trivially visible to a static decompiler.
---@param n integer  (any Lua integer, including large unsigned 32-bit values)
---@return string    Lua expression string
function Utils.obfuscate_int_deep(n)
    -- XOR split: let a = random, b = a XOR n → a XOR b == n
    local a = math.random(0, 0x3FFFFFFF)
    local b = a ~ n
    -- Additive noise: p + q − q cancels, but written as separate literals so
    -- a decompiler cannot trivially constant-fold the full expression.
    local p = math.random(1, 0xFFFF)
    local q = math.random(1, 0xFFFF)
    -- Final: (a ~ b) + (p + q) - p - q  ==  n
    return string.format("((%d~%d)+%d+%d-%d-%d)", a, b, p, q, p, q)
end

--- Return a triple-layer XOR+add expression that evaluates to integer n.
--- Harder to constant-fold than obfuscate_int_deep because of the extra layer.
---@param n integer
---@return string  Lua expression string
function Utils.obfuscate_int_triple(n)
    local a = math.random(0, 0x1FFFFFFF)
    local b = a ~ n
    local c = math.random(0, 0x1FFFFFFF)
    local d = c ~ b
    local p = math.random(1, 0x7FFF)
    local q = math.random(1, 0x7FFF)
    -- (a ~ (c ~ d)) ~ b  ==  a ~ b  ==  n, wrapped in +p-p noise
    return string.format("((%d~(%d~%d))~%d+%d-%d)", a, c, d, b, p, p)
end



local _CRC32_TABLE = (function()
    local t = {}
    for i = 0, 255 do
        local c = i
        for _ = 1, 8 do
            if c & 1 ~= 0 then c = 0xEDB88320 ~ (c >> 1)
            else                c = c >> 1
            end
        end
        t[i] = c
    end
    return t
end)()

--- Compute CRC32 (ISO 3309 / IEEE 802.3) of a byte string.
---@param data string
---@return integer  unsigned 32-bit CRC
function Utils.crc32(data)
    local crc = 0xFFFFFFFF
    for i = 1, #data do
        crc = _CRC32_TABLE[(crc ~ data:byte(i)) & 0xFF] ~ (crc >> 8)
    end
    return crc ~ 0xFFFFFFFF
end

-- ─── Base64 (for readable output variant) ────────────────────────────────────

local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

function Utils.base64_enc(data)
    local out = {}
    local pad = (3 - #data % 3) % 3
    for i = 1, #data, 3 do
        local b1 = data:byte(i)     or 0
        local b2 = data:byte(i + 1) or 0
        local b3 = data:byte(i + 2) or 0
        local n = (b1 << 16) | (b2 << 8) | b3
        out[#out + 1] = B64:sub((n >> 18) + 1, (n >> 18) + 1)
        out[#out + 1] = B64:sub(((n >> 12) & 63) + 1, ((n >> 12) & 63) + 1)
        out[#out + 1] = B64:sub(((n >>  6) & 63) + 1, ((n >>  6) & 63) + 1)
        out[#out + 1] = B64:sub((n & 63) + 1, (n & 63) + 1)
    end
    local result = table.concat(out)
    if pad > 0 then
        result = result:sub(1, -(pad + 1)) .. ("="):rep(pad)
    end
    return result
end

local B64_INV = {}
for i = 1, #B64 do B64_INV[B64:sub(i, i)] = i - 1 end

function Utils.base64_dec(data)
    data = data:gsub("=", "")
    local out = {}
    for i = 1, #data, 4 do
        local n = ((B64_INV[data:sub(i,   i)]   or 0) << 18)
                | ((B64_INV[data:sub(i+1, i+1)] or 0) << 12)
                | ((B64_INV[data:sub(i+2, i+2)] or 0) <<  6)
                |  (B64_INV[data:sub(i+3, i+3)] or 0)
        out[#out + 1] = string.char((n >> 16) & 0xFF)
        out[#out + 1] = string.char((n >>  8) & 0xFF)
        out[#out + 1] = string.char( n        & 0xFF)
    end
    return table.concat(out):sub(1, #data * 3 // 4)
end

return Utils
