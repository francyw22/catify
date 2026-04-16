--[[
    Catify - Commercial Lua Obfuscator
    src/utils.lua - Utility helpers: random identifiers, encryption, serialization
]]

local Utils = {}

-- ─── Random identifiers ──────────────────────────────────────────────────────

local LUA_KEYWORDS = {
    ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true, ["elseif"] = true,
    ["end"] = true, ["false"] = true, ["for"] = true, ["function"] = true, ["goto"] = true,
    ["if"] = true, ["in"] = true, ["local"] = true, ["nil"] = true, ["not"] = true,
    ["or"] = true, ["repeat"] = true, ["return"] = true, ["then"] = true, ["true"] = true,
    ["until"] = true, ["while"] = true,
}
local MAX_IDENTIFIER_GENERATION_ATTEMPTS = 1000

--- Generate a random valid Lua identifier using short alphanumeric names.
--- Example output: "aX", "bY3", "zKm"
---@param min_len integer?  minimum identifier length
---@param max_len integer?  maximum identifier length
function Utils.rand_name(min_len, max_len)
    min_len = min_len or 2
    max_len = max_len or 4
    if min_len < 1 then min_len = 1 end
    if max_len < min_len then max_len = min_len end

    local alpha = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    local alnum = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    for _ = 1, MAX_IDENTIFIER_GENERATION_ATTEMPTS do
        local len = math.random(min_len, max_len)
        -- First character must be a letter (valid Lua identifier start)
        local first_idx = math.random(1, #alpha)
        local buf = { alpha:sub(first_idx, first_idx) }
        for i = 2, len do
            local idx = math.random(1, #alnum)
            buf[#buf + 1] = alnum:sub(idx, idx)
        end
        local name = table.concat(buf)
        if not LUA_KEYWORDS[name] then
            return name
        end
    end
    error("Failed to generate a non-keyword Lua identifier")
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
--- Uses XOR-split encoding (a XOR b == n) with optional additive noise.
--- When xorname is provided the XOR is expressed as a function call (compatible
--- with all Lua versions including Luau/Lua 5.1).  When omitted the XOR is
--- pre-computed at generator time and only arithmetic noise is added.
---@param n       integer  (any Lua integer, including large unsigned 32-bit values)
---@param xorname string?  name of the runtime XOR function to call (e.g. the bXor variable)
---@return string          Lua expression string
function Utils.obfuscate_int_deep(n, xorname)
    -- XOR split: let a = random, b = a XOR n → a XOR b == n
    local a = math.random(0, 0x3FFFFFFF)
    local b = a ~ n   -- computed at generator time (generator runs Lua 5.3)
    local form = math.random(1, 7)
    if xorname then
        -- Emit function-call syntax so the output is valid in all Lua versions
        if form == 1 then
            -- No noise: bare XOR pair
            return string.format("(%s(%d,%d))", xorname, a, b)
        elseif form == 2 then
            -- Noise inside second operand: xor(a, b+p-p)
            local p = math.random(1, 0x7FFF)
            return string.format("(%s(%d,(%d+%d-%d)))", xorname, a, b, p, p)
        elseif form == 3 then
            -- Noise around result: xor(a,b)+p-p
            local p = math.random(1, 0x7FFF)
            return string.format("((%s(%d,%d))+%d-%d)", xorname, a, b, p, p)
        elseif form == 4 then
            -- Double-cancel noise: xor(a,b)+p+q-p-q
            local p = math.random(1, 0x7FFF)
            local q = math.random(1, 0x7FFF)
            return string.format("((%s(%d,%d))+%d+%d-%d-%d)", xorname, a, b, p, q, p, q)
        elseif form == 5 then
            -- Cancelled XOR shell around the split.
            local p = math.random(0, 0x3FFFFFFF)
            return string.format("(%s(%s(%d,%d),%s(%d,%d)))", xorname, xorname, a, b, xorname, p, p)
        elseif form == 6 then
            -- Independent split + combine with explicit cancelled sub-tree.
            local c = math.random(0, 0x3FFFFFFF)
            local d = math.random(0, 0x3FFFFFFF)
            return string.format("(%s(%s(%d,%d),%s(%s(%d,%d),%s(%d,%d))))", xorname, xorname, a, b, xorname, xorname, c, d, xorname, c, d)
        elseif form == 7 then
            -- Extra arithmetic shell with nested no-op XOR.
            local p = math.random(1, 0x3FFF)
            local q = math.random(0, 0x3FFFFFFF)
            return string.format("((%s(%d,%d))+(%s(%d,%d))+%d-%d)", xorname, a, b, xorname, q, q, p, p)
        end
    else
        -- No xorname: pre-compute XOR and use arithmetic-only noise
        local result = n  -- a ~ b == n
        if form == 1 then
            return tostring(result)
        elseif form == 2 then
            local p = math.random(1, 0x7FFF)
            return string.format("(%d+%d-%d)", result, p, p)
        elseif form == 3 then
            local p = math.random(1, 0x7FFF)
            return string.format("(%d-%d+%d)", result, p, p)
        elseif form == 4 then
            local p = math.random(1, 0x7FFF)
            local q = math.random(1, 0x7FFF)
            return string.format("(%d+%d+%d-%d-%d)", result, p, q, p, q)
        elseif form == 5 then
            local p = math.random(1, 0x3FFF)
            local q = math.random(1, 0x3FFF)
            return string.format("((%d+%d+%d)-(%d+%d))", result, p, q, p, q)
        elseif form == 6 then
            local p = math.random(1, 0x1FFF)
            return string.format("((%d+%d)-%d)", result, p, p)
        elseif form == 7 then
            local p = math.random(1, 0x3FFF)
            local q = math.random(1, 0x3FFF)
            return string.format("((%d-%d)+(%d+%d-%d))", result, p, p, q, q)
        end
    end
end

--- Return a triple-layer XOR expression (with optional additive noise) that evaluates to integer n.
--- Noise form is randomised so the pattern differs from obfuscate_int_deep.
---@param n       integer
---@param xorname string?  name of the runtime XOR function to call
---@return string  Lua expression string
function Utils.obfuscate_int_triple(n, xorname)
    local a = math.random(0, 0x1FFFFFFF)
    local b = a ~ n
    local c = math.random(0, 0x1FFFFFFF)
    local d = c ~ b
    -- xorname(a, xorname(c, d)) == a XOR (c XOR b) == a XOR b == n
    -- (c XOR d = c XOR (c XOR b) = b, so the inner xorname yields b, outer yields a XOR b = n)
    local form = math.random(1, 3)
    if xorname then
        -- Emit function-call syntax compatible with all Lua versions
        if form == 1 then
            return string.format("(%s(%d,%s(%d,%d)))", xorname, a, xorname, c, d)
        elseif form == 2 then
            local p = math.random(1, 0x7FFF)
            return string.format("((%s(%d,%s(%d,%d)))+%d-%d)", xorname, a, xorname, c, d, p, p)
        else
            local p = math.random(1, 0x3FFF)
            return string.format("(%s(%d,%s(%d,(%d+%d-%d))))", xorname, a, xorname, c, d, p, p)
        end
    else
        -- No xorname: pre-compute XOR and use arithmetic-only noise
        local result = n  -- (a XOR (c XOR d)) XOR b == n
        if form == 1 then
            return tostring(result)
        elseif form == 2 then
            local p = math.random(1, 0x7FFF)
            return string.format("(%d+%d-%d)", result, p, p)
        else
            local p = math.random(1, 0x3FFF)
            local q = math.random(1, 0x3FFF)
            return string.format("(%d+%d+%d-%d-%d)", result, p, q, p, q)
        end
    end
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

-- ─── AES-256-CTR cipher ───────────────────────────────────────────────────────

local AES_SBOX = {
    [0]=0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
}

local AES_RCON = {[1]=0x01000000,[2]=0x02000000,[3]=0x04000000,[4]=0x08000000,
                  [5]=0x10000000,[6]=0x20000000,[7]=0x40000000}

local function _xtime(a)
    return ((a << 1) ~ (a >= 0x80 and 0x1b or 0)) & 0xFF
end

local function _aes_subword(w)
    return (AES_SBOX[(w>>24)&0xFF] << 24) | (AES_SBOX[(w>>16)&0xFF] << 16) |
           (AES_SBOX[(w>>8)&0xFF]  << 8)  |  AES_SBOX[w&0xFF]
end

local function _aes256_key_expand(key)
    local w = {}
    for i = 0, 7 do
        w[i] = (key:byte(i*4+1) << 24) | (key:byte(i*4+2) << 16) |
               (key:byte(i*4+3) << 8)  |  key:byte(i*4+4)
    end
    for i = 8, 59 do
        local temp = w[i-1]
        if i % 8 == 0 then
            temp = ((temp << 8) | (temp >> 24)) & 0xFFFFFFFF
            temp = _aes_subword(temp)
            temp = (temp ~ AES_RCON[i // 8]) & 0xFFFFFFFF
        elseif i % 8 == 4 then
            temp = _aes_subword(temp)
        end
        w[i] = (w[i-8] ~ temp) & 0xFFFFFFFF
    end
    return w
end

local function _aes256_encrypt_block(blk, rk)
    local s = {}
    for i = 0, 15 do s[i] = blk:byte(i+1) end
    for c = 0, 3 do
        local w = rk[c]
        s[c*4]   = s[c*4]   ~ ((w>>24)&0xFF)
        s[c*4+1] = s[c*4+1] ~ ((w>>16)&0xFF)
        s[c*4+2] = s[c*4+2] ~ ((w>>8) &0xFF)
        s[c*4+3] = s[c*4+3] ~  (w     &0xFF)
    end
    for r = 1, 13 do
        for i = 0, 15 do s[i] = AES_SBOX[s[i]] end
        local t
        t=s[1]; s[1]=s[5]; s[5]=s[9]; s[9]=s[13]; s[13]=t
        t=s[2]; local t2=s[6]; s[2]=s[10]; s[6]=s[14]; s[10]=t; s[14]=t2
        t=s[3]; s[3]=s[15]; s[15]=s[11]; s[11]=s[7]; s[7]=t
        for c = 0, 3 do
            local a0,a1,a2,a3 = s[c*4],s[c*4+1],s[c*4+2],s[c*4+3]
            s[c*4]   = _xtime(a0)~_xtime(a1)~a1~a2~a3
            s[c*4+1] = a0~_xtime(a1)~_xtime(a2)~a2~a3
            s[c*4+2] = a0~a1~_xtime(a2)~_xtime(a3)~a3
            s[c*4+3] = _xtime(a0)~a0~a1~a2~_xtime(a3)
        end
        for c = 0, 3 do
            local w = rk[r*4+c]
            s[c*4]   = s[c*4]   ~ ((w>>24)&0xFF)
            s[c*4+1] = s[c*4+1] ~ ((w>>16)&0xFF)
            s[c*4+2] = s[c*4+2] ~ ((w>>8) &0xFF)
            s[c*4+3] = s[c*4+3] ~  (w     &0xFF)
        end
    end
    for i = 0, 15 do s[i] = AES_SBOX[s[i]] end
    local t
    t=s[1]; s[1]=s[5]; s[5]=s[9]; s[9]=s[13]; s[13]=t
    t=s[2]; local t2=s[6]; s[2]=s[10]; s[6]=s[14]; s[10]=t; s[14]=t2
    t=s[3]; s[3]=s[15]; s[15]=s[11]; s[11]=s[7]; s[7]=t
    for c = 0, 3 do
        local w = rk[56+c]
        s[c*4]   = s[c*4]   ~ ((w>>24)&0xFF)
        s[c*4+1] = s[c*4+1] ~ ((w>>16)&0xFF)
        s[c*4+2] = s[c*4+2] ~ ((w>>8) &0xFF)
        s[c*4+3] = s[c*4+3] ~  (w     &0xFF)
    end
    local out = {}
    for i = 0, 15 do out[i+1] = string.char(s[i]) end
    return table.concat(out)
end

--- AES-256-CTR cipher (symmetric - same function encrypts and decrypts)
--- key must be exactly 32 bytes, nonce exactly 8 bytes
---@param data  string
---@param key   string  32 bytes
---@param nonce string  8 bytes
---@return string
function Utils.aes256_ctr(data, key, nonce)
    assert(#key == 32, "AES-256 key must be 32 bytes")
    assert(#nonce == 8, "AES-256 nonce must be 8 bytes")
    local rk  = _aes256_key_expand(key)
    local out = {}
    local ctr = 0
    local pos = 1
    local dlen = #data
    while pos <= dlen do
        local ctr_block = nonce .. string.pack("<I4", ctr) .. string.pack("<I4", 0)
        local ks = _aes256_encrypt_block(ctr_block, rk)
        local blen = math.min(16, dlen - pos + 1)
        for i = 1, blen do
            out[#out+1] = string.char(data:byte(pos+i-1) ~ ks:byte(i))
        end
        pos = pos + 16
        ctr = ctr + 1
    end
    return table.concat(out)
end

--- Generate a random 8-byte nonce
---@return string
function Utils.rand_nonce()
    local buf = {}
    for i = 1, 8 do buf[i] = string.char(math.random(0, 255)) end
    return table.concat(buf)
end

-- ─── SHA-256 ──────────────────────────────────────────────────────────────────

local SHA256_K = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,
    0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,
    0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,
    0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,
    0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,
    0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,
    0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,
    0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,
    0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,
}

local function _ror32(x, n) return ((x >> n) | (x << (32-n))) & 0xFFFFFFFF end

--- Compute SHA-256 of data, returns 32-byte binary string
---@param data string
---@return string
function Utils.sha256(data)
    local h = {
        0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
        0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19,
    }
    local len    = #data
    local bitlen = len * 8
    local padded = data .. "\x80"
    while #padded % 64 ~= 56 do padded = padded .. "\x00" end
    local hi = (bitlen >> 32) & 0xFFFFFFFF
    local lo =  bitlen        & 0xFFFFFFFF
    padded = padded .. string.pack(">I4", hi) .. string.pack(">I4", lo)
    local w = {}
    for blk = 1, #padded, 64 do
        for i = 1, 16 do
            local v = string.unpack(">I4", padded, blk + (i-1)*4)
            w[i] = v & 0xFFFFFFFF
        end
        for i = 17, 64 do
            local s0 = _ror32(w[i-15],7)~_ror32(w[i-15],18)~(w[i-15]>>3)
            local s1 = _ror32(w[i-2],17)~_ror32(w[i-2],19)~(w[i-2]>>10)
            w[i] = (w[i-16]+s0+w[i-7]+s1) & 0xFFFFFFFF
        end
        local a,b,c,d,e,f,g,hv = h[1],h[2],h[3],h[4],h[5],h[6],h[7],h[8]
        for i = 1, 64 do
            local S1  = _ror32(e,6)~_ror32(e,11)~_ror32(e,25)
            local ch  = (e&f)~((~e)&g)
            local t1  = (hv+S1+ch+SHA256_K[i]+w[i]) & 0xFFFFFFFF
            local S0  = _ror32(a,2)~_ror32(a,13)~_ror32(a,22)
            local maj = (a&b)~(a&c)~(b&c)
            local t2  = (S0+maj) & 0xFFFFFFFF
            hv=g; g=f; f=e
            e=(d+t1) & 0xFFFFFFFF
            d=c; c=b; b=a
            a=(t1+t2) & 0xFFFFFFFF
        end
        h[1]=(h[1]+a) &0xFFFFFFFF; h[2]=(h[2]+b) &0xFFFFFFFF
        h[3]=(h[3]+c) &0xFFFFFFFF; h[4]=(h[4]+d) &0xFFFFFFFF
        h[5]=(h[5]+e) &0xFFFFFFFF; h[6]=(h[6]+f) &0xFFFFFFFF
        h[7]=(h[7]+g) &0xFFFFFFFF; h[8]=(h[8]+hv)&0xFFFFFFFF
    end
    local out = {}
    for i = 1, 8 do out[i] = string.pack(">I4", h[i]) end
    return table.concat(out)
end

-- ─── Base91 ──────────────────────────────────────────────────────────────────
local BASE91_ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~\""

--- Base91 encoder
---@param data string
---@return string
function Utils.base91_enc(data)
    local alpha = BASE91_ALPHA
    local b, n = 0, 0
    local out = {}
    for i = 1, #data do
        b = b | (data:byte(i) << n)
        n = n + 8
        if n > 13 then
            local t = b & 8191
            if t > 88 then
                b = b >> 13; n = n - 13
            else
                t = b & 16383; b = b >> 14; n = n - 14
            end
            out[#out+1] = alpha:sub((t % 91)+1, (t % 91)+1)
            out[#out+1] = alpha:sub((t // 91)+1, (t // 91)+1)
        end
    end
    if n > 0 then
        out[#out+1] = alpha:sub((b % 91)+1, (b % 91)+1)
        if n > 7 or b >= 91 then
            out[#out+1] = alpha:sub((b // 91)+1, (b // 91)+1)
        end
    end
    return table.concat(out)
end

--- Base91 decoder
---@param data string
---@return string
function Utils.base91_dec(data)
    local alpha = BASE91_ALPHA
    local decode = {}
    for i = 1, #alpha do decode[alpha:byte(i)] = i - 1 end
    local v, b, n = -1, 0, 0
    local out = {}
    for i = 1, #data do
        local p = decode[data:byte(i)]
        if p ~= nil then
            if v < 0 then
                v = p
            else
                v = v + p * 91
                b = b | (v << n)
                if (v & 8191) > 88 then n = n + 13 else n = n + 14 end
                repeat
                    out[#out+1] = string.char(b & 255)
                    b = b >> 8
                    n = n - 8
                until n <= 7
                v = -1
            end
        end
    end
    if v > -1 then
        out[#out+1] = string.char((b | (v << n)) & 255)
    end
    return table.concat(out)
end

return Utils
