--[[
    Catify Runtime VM

    Static, parameterized Lua 5.3 / Roblox Luau VM interpreter.
    Load via HTTP and call the returned function:

        local rt = loadstring(game:HttpGet("https://raw.githubusercontent.com/francyw22/catify/main/runtime/vm.lua"))
        rt()(_cfg, _payload)

    Parameters:
        cfg     table    {key, nonce, sxor, sha, revmap}
            key    : string   32-byte AES-256-CTR key
            nonce  : string   8-byte CTR nonce
            sxor   : integer  string-constant XOR key (0-255)
            sha    : table    {[0..7]} expected SHA-256 uint32 words
            revmap : table    {[shuffled_op]=real_op} (0-indexed, 0..46)
        payload  string   Encrypted bytecode blob
]]
return function(cfg, payload)

-- ── 1. Bitwise compatibility (Lua 5.3 native ops or Roblox Luau bit32) ─────────
local _bxor, _bnot, _band, _bor, _bshl, _bshr
if type(bit32) == 'table' and type(bit32.bxor) == 'function' then
    _bxor = bit32.bxor
    _bnot = bit32.bnot
    _band = bit32.band
    _bor  = bit32.bor
    _bshl = bit32.lshift or function(a,b)
        if b >= 32 then return 0 end
        return bit32.band(a * (2^b), 0xFFFFFFFF)
    end
    _bshr = bit32.rshift or function(a,b)
        if b >= 32 then return 0 end
        return math.floor(bit32.band(a, 0xFFFFFFFF) / (2^b))
    end
else
    local _L = (type(load)=='function' and load) or (type(loadstring)=='function' and loadstring)
    if not _L then error('Catify: missing bitwise support', 0) end
    _bxor = _L('return function(a,b) return a~b end')()
    _bnot = _L('return function(a)   return ~a  end')()
    _band = _L('return function(a,b) return a&b end')()
    _bor  = _L('return function(a,b) return a|b end')()
    _bshl = _L('return function(a,b) return a<<b end')()
    _bshr = _L('return function(a,b) return a>>b end')()
end

-- ── 2. Binary read/write helpers ──────────────────────────────────────────────
local function rdU4le(s, p)
    local b1,b2,b3,b4 = s:byte(p, p+3)
    return b1 + b2*256 + b3*65536 + b4*16777216, p+4
end
local function rdI4le(s, p)
    local v, np = rdU4le(s, p)
    if v >= 2147483648 then v = v - 4294967296 end
    return v, np
end
local function rdF64le(s, p)
    if type(string.unpack) == 'function' then return string.unpack('<d', s, p) end
    local b1,b2,b3,b4,b5,b6,b7,b8 = s:byte(p, p+7)
    local sgn  = (b8 >= 128) and -1 or 1
    local exp  = (b8 % 128)*16 + math.floor(b7/16)
    local mant = (b7%16)*281474976710656 + b6*1099511627776 + b5*4294967296
                 + b4*16777216 + b3*65536 + b2*256 + b1
    if exp == 0 then
        if mant == 0 then return sgn*0, p+8 end
        return sgn*(2^(1-1023))*(mant/4503599627370496), p+8
    end
    if exp == 2047 then
        if mant == 0 then return sgn*(1/0), p+8 end
        return 0/0, p+8
    end
    return sgn*(2^(exp-1023))*(1 + mant/4503599627370496), p+8
end
local function wrU4be(v)
    return string.char(_band(_bshr(v,24),255), _band(_bshr(v,16),255),
                       _band(_bshr(v,8),255),  _band(v,255))
end

-- ── 3. AES-256-CTR decrypt ────────────────────────────────────────────────────
local _sbox = {[0]=
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
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
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16}

local function _xtime(a)
    return _band(_bxor(_bshl(a, 1), (a >= 0x80 and 0x1b or 0)), 0xFF)
end

local function _expand_key(k)
    local w = {}
    for i = 0, 7 do
        w[i] = _bor(_bor(_bor(_bshl(k:byte(i*4+1), 24),
                              _bshl(k:byte(i*4+2), 16)),
                         _bshl(k:byte(i*4+3), 8)),
                    k:byte(i*4+4))
    end
    local rcon = {0x01000000,0x02000000,0x04000000,0x08000000,
                  0x10000000,0x20000000,0x40000000}
    for i = 8, 59 do
        local t = w[i-1]
        if i % 8 == 0 then
            -- RotWord
            t = _band(_bor(_bshl(t, 8), _bshr(t, 24)), 0xFFFFFFFF)
            -- SubWord
            t = _bor(_bor(_bor(
                _bshl(_sbox[_band(_bshr(t,24),0xFF)], 24),
                _bshl(_sbox[_band(_bshr(t,16),0xFF)], 16)),
                _bshl(_sbox[_band(_bshr(t, 8),0xFF)],  8)),
                _sbox[_band(t, 0xFF)])
            -- Rcon
            t = _band(_bxor(t, rcon[i//8]), 0xFFFFFFFF)
        elseif i % 8 == 4 then
            t = _bor(_bor(_bor(
                _bshl(_sbox[_band(_bshr(t,24),0xFF)], 24),
                _bshl(_sbox[_band(_bshr(t,16),0xFF)], 16)),
                _bshl(_sbox[_band(_bshr(t, 8),0xFF)],  8)),
                _sbox[_band(t, 0xFF)])
        end
        w[i] = _band(_bxor(w[i-8], t), 0xFFFFFFFF)
    end
    return w
end

local function _aes_block(blk, rk)
    local s = {}
    for i = 0, 15 do s[i] = blk:byte(i+1) end
    -- Initial AddRoundKey
    for c = 0, 3 do
        local ww = rk[c]
        s[c*4]   = _bxor(s[c*4],   _band(_bshr(ww,24), 0xFF))
        s[c*4+1] = _bxor(s[c*4+1], _band(_bshr(ww,16), 0xFF))
        s[c*4+2] = _bxor(s[c*4+2], _band(_bshr(ww, 8), 0xFF))
        s[c*4+3] = _bxor(s[c*4+3], _band(ww, 0xFF))
    end
    -- Rounds 1-13
    for r = 1, 13 do
        -- SubBytes
        for i = 0, 15 do s[i] = _sbox[s[i]] end
        -- ShiftRows
        local t
        t=s[1];  s[1]=s[5];  s[5]=s[9];  s[9]=s[13]; s[13]=t
        t=s[2]; local t2=s[6]; s[2]=s[10]; s[6]=s[14]; s[10]=t; s[14]=t2
        t=s[3];  s[3]=s[15]; s[15]=s[11]; s[11]=s[7];  s[7]=t
        -- MixColumns
        for c = 0, 3 do
            local a0,a1,a2,a3 = s[c*4],s[c*4+1],s[c*4+2],s[c*4+3]
            s[c*4]   = _bxor(_bxor(_bxor(_bxor(_xtime(a0),_xtime(a1)),a1),a2),a3)
            s[c*4+1] = _bxor(_bxor(_bxor(_bxor(a0,_xtime(a1)),_xtime(a2)),a2),a3)
            s[c*4+2] = _bxor(_bxor(_bxor(_bxor(a0,a1),_xtime(a2)),_xtime(a3)),a3)
            s[c*4+3] = _bxor(_bxor(_bxor(_bxor(_xtime(a0),a0),a1),a2),_xtime(a3))
        end
        -- AddRoundKey
        for c = 0, 3 do
            local ww = rk[r*4+c]
            s[c*4]   = _bxor(s[c*4],   _band(_bshr(ww,24), 0xFF))
            s[c*4+1] = _bxor(s[c*4+1], _band(_bshr(ww,16), 0xFF))
            s[c*4+2] = _bxor(s[c*4+2], _band(_bshr(ww, 8), 0xFF))
            s[c*4+3] = _bxor(s[c*4+3], _band(ww, 0xFF))
        end
    end
    -- Final round (no MixColumns)
    for i = 0, 15 do s[i] = _sbox[s[i]] end
    local t
    t=s[1];  s[1]=s[5];  s[5]=s[9];  s[9]=s[13]; s[13]=t
    t=s[2]; local t2=s[6]; s[2]=s[10]; s[6]=s[14]; s[10]=t; s[14]=t2
    t=s[3];  s[3]=s[15]; s[15]=s[11]; s[11]=s[7];  s[7]=t
    for c = 0, 3 do
        local ww = rk[56+c]
        s[c*4]   = _bxor(s[c*4],   _band(_bshr(ww,24), 0xFF))
        s[c*4+1] = _bxor(s[c*4+1], _band(_bshr(ww,16), 0xFF))
        s[c*4+2] = _bxor(s[c*4+2], _band(_bshr(ww, 8), 0xFF))
        s[c*4+3] = _bxor(s[c*4+3], _band(ww, 0xFF))
    end
    local o = {}
    for i = 0, 15 do o[i+1] = string.char(s[i]) end
    return table.concat(o)
end

local function aes256_ctr(d, k, nn)
    local rk = _expand_key(k)
    local out = {}
    local ctr, pos, dl = 0, 1, #d
    while pos <= dl do
        local cb = nn .. string.char(
            ctr%256, (ctr//256)%256, (ctr//65536)%256, (ctr//16777216)%256
        ) .. "\0\0\0\0"
        local ks = _aes_block(cb, rk)
        local bl = math.min(16, dl - pos + 1)
        for i = 1, bl do
            out[#out+1] = string.char(_bxor(d:byte(pos+i-1), ks:byte(i)))
        end
        pos = pos + 16
        ctr = ctr + 1
    end
    return table.concat(out)
end

-- ── 4. SHA-256 ────────────────────────────────────────────────────────────────
local _sha_k = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2}

local function sha256(s)
    local function rr(x,n)
        return _band(_bor(_bshr(x,n), _bshl(x,32-n)), 0xFFFFFFFF)
    end
    local h = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
               0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}
    local bl = #s * 8
    local pd = s .. '\x80'
    while #pd % 64 ~= 56 do pd = pd .. '\x00' end
    pd = pd .. wrU4be(_band(_bshr(bl, 32), 0xFFFFFFFF)) .. wrU4be(_band(bl, 0xFFFFFFFF))
    local w = {}
    for blk = 1, #pd, 64 do
        for i = 1, 16 do
            local o = blk + (i-1)*4
            local b1,b2,b3,b4 = pd:byte(o, o+3)
            w[i] = _band(b1*16777216 + b2*65536 + b3*256 + b4, 0xFFFFFFFF)
        end
        for i = 17, 64 do
            local s0 = _bxor(_bxor(rr(w[i-15],7), rr(w[i-15],18)), _bshr(w[i-15],3))
            local s1 = _bxor(_bxor(rr(w[i-2],17), rr(w[i-2],19)), _bshr(w[i-2],10))
            w[i] = _band(w[i-16] + s0 + w[i-7] + s1, 0xFFFFFFFF)
        end
        local a,b,c,d,e,f,g,hv = h[1],h[2],h[3],h[4],h[5],h[6],h[7],h[8]
        for i = 1, 64 do
            local S1  = _bxor(_bxor(rr(e,6), rr(e,11)), rr(e,25))
            local ch  = _bxor(_band(e,f), _band(_bnot(e),g))
            local t1  = _band(hv + S1 + ch + _sha_k[i] + w[i], 0xFFFFFFFF)
            local S0  = _bxor(_bxor(rr(a,2), rr(a,13)), rr(a,22))
            local maj = _bxor(_bxor(_band(a,b), _band(a,c)), _band(b,c))
            local t2  = _band(S0 + maj, 0xFFFFFFFF)
            hv=g; g=f; f=e; e=_band(d+t1,0xFFFFFFFF)
            d=c; c=b; b=a; a=_band(t1+t2,0xFFFFFFFF)
        end
        h[1]=_band(h[1]+a,0xFFFFFFFF); h[2]=_band(h[2]+b,0xFFFFFFFF)
        h[3]=_band(h[3]+c,0xFFFFFFFF); h[4]=_band(h[4]+d,0xFFFFFFFF)
        h[5]=_band(h[5]+e,0xFFFFFFFF); h[6]=_band(h[6]+f,0xFFFFFFFF)
        h[7]=_band(h[7]+g,0xFFFFFFFF); h[8]=_band(h[8]+hv,0xFFFFFFFF)
    end
    local out = {}
    for i = 1, 8 do
        local wv = h[i]
        out[i] = string.char(wv//16777216, (wv//65536)%256, (wv//256)%256, wv%256)
    end
    return table.concat(out)
end

-- ── 5. Integrity check ────────────────────────────────────────────────────────
do
    local hash = sha256(payload)
    local sha_cfg = cfg.sha
    for i = 0, 7 do
        local off = i*4 + 1
        local cw = hash:byte(off)*16777216 + hash:byte(off+1)*65536
                 + hash:byte(off+2)*256    + hash:byte(off+3)
        if cw ~= sha_cfg[i] then
            error('Catify: integrity check failed', 0)
        end
    end
end

-- ── 6. Decrypt payload ────────────────────────────────────────────────────────
local raw = aes256_ctr(payload, cfg.key, cfg.nonce)
payload = nil  -- wipe ciphertext

-- ── 7. Deserialize proto ──────────────────────────────────────────────────────
local _dpos  = 1
local _ddata = raw

local function _rb()
    local v = _ddata:byte(_dpos)
    _dpos = _dpos + 1
    return v
end
local function _ri32()
    local v, p = rdI4le(_ddata, _dpos)
    _dpos = p; return v
end
local function _ri64()
    local lo, p1 = rdU4le(_ddata, _dpos); _dpos = p1
    local hi, p2 = rdU4le(_ddata, _dpos); _dpos = p2
    if hi == 0 then return lo end
    local v = lo + hi*(2^32)
    if hi >= (2^31) then v = v - (2^64) end
    return v
end
local function _rf64()
    local v, p = rdF64le(_ddata, _dpos)
    _dpos = p; return v
end
local function _rstr()
    local n, p = rdI4le(_ddata, _dpos); _dpos = p
    local s = _ddata:sub(_dpos, _dpos + n - 1)
    _dpos = _dpos + n
    return s
end

local sxor   = cfg.sxor
local revmap = cfg.revmap

local _load_proto
_load_proto = function()
    local p = {}
    p.numparams   = _rb()
    p.is_vararg   = _rb()
    p.maxstacksize= _rb()

    local sc = _ri32(); p.sizecode = sc
    local code = {}; p.code = code
    for i = 0, sc-1 do
        local v, np = rdU4le(_ddata, _dpos)
        code[i] = v; _dpos = np
    end

    local sk = _ri32(); p.sizek = sk
    local k = {}; p.k = k
    for i = 0, sk-1 do
        local t = _rb()
        if     t == 0 then k[i] = nil
        elseif t == 1 then k[i] = false
        elseif t == 2 then k[i] = true
        elseif t == 3 then k[i] = _ri64()
        elseif t == 4 then k[i] = _rf64()
        elseif t == 5 then
            local sx  = _rstr()
            local key = _bxor(sxor, _band(i, 255))
            local sd  = {}
            for si = 1, #sx do
                sd[si] = string.char(_bxor(sx:byte(si), key))
            end
            k[i] = table.concat(sd)
        end
    end

    local su = _ri32(); p.sizeupvalues = su
    local uvs = {}; p.upvals = uvs
    for i = 0, su-1 do
        uvs[i] = { instack = _rb(), idx = _rb() }
    end

    local sp = _ri32(); p.sizep = sp
    local pp = {}; p.p = pp
    for i = 0, sp-1 do pp[i] = _load_proto() end

    return p
end

local proto = _load_proto()
raw = nil; _ddata = nil  -- wipe

-- ── 8. Build dispatch fwdmap ──────────────────────────────────────────────────
-- revmap[shuffled] = real → fwdmap[real] = shuffled (for dispatch table indexing)
local fwdmap = {}
for shuffled = 0, 46 do
    local real = revmap[shuffled]
    if real ~= nil then fwdmap[real] = shuffled end
end

-- ── 9. table.pack / table.unpack compatibility ────────────────────────────────
local _pack   = (table and table.pack) or function(...) return {n=select('#',...),...} end
local _unpack = (table and table.unpack) or unpack
if type(_unpack) ~= 'function' then
    local function _up(t,i,j) i=i or 1; j=j or #t
        if i > j then return end
        return t[i], _up(t,i+1,j)
    end
    _unpack = _up
end

-- ── 10. VM executor ───────────────────────────────────────────────────────────
local function execute(eProto, eUpvals, ...)
    local eArgs  = _pack(...)
    local eRegs  = setmetatable({}, {__index=function(t,k) local b={};t[k]=b;return b end})
    for i = 0, eProto.maxstacksize + 63 do eRegs[i] = {} end
    for i = 0, eProto.numparams - 1 do eRegs[i].v = eArgs[i+1] end
    local eVararg = {}
    if eProto.is_vararg ~= 0 then
        for i = eProto.numparams+1, eArgs.n do eVararg[#eVararg+1] = eArgs[i] end
    end

    local ePc     = 0
    local eTop    = -1
    local eCode   = eProto.code
    local eKst    = eProto.k
    local eProtos = eProto.p
    local eDone   = false
    local eRetVals= {}
    local eRetN   = 0

    local function eRk(x)
        if x >= 256 then return eKst[x-256] else return eRegs[x].v end
    end

    -- Build dispatch closures indexed by REAL opcode, then remap via fwdmap.
    local rd = {}  -- rd[real_op] = handler

    -- [0] MOVE
    rd[0] = function(A,B) eRegs[A].v = eRegs[B].v end
    -- [1] LOADK
    rd[1] = function(A,B,C,Bx) eRegs[A].v = eKst[Bx] end
    -- [2] LOADKX  (next inst is EXTRAARG carrying the constant index in Ax=bits[6..])
    rd[2] = function(A)
        local ni = eCode[ePc]; ePc = ePc+1
        eRegs[A].v = eKst[_bshr(ni, 6)]
    end
    -- [3] LOADBOOL
    rd[3] = function(A,B,C)
        eRegs[A].v = (B ~= 0)
        if C ~= 0 then ePc = ePc+1 end
    end
    -- [4] LOADNIL
    rd[4] = function(A,B)
        for i = A, A+B do eRegs[i].v = nil end
    end
    -- [5] GETUPVAL
    rd[5] = function(A,B)
        local u = eUpvals[B]; eRegs[A].v = u and u.v or nil
    end
    -- [6] GETTABUP
    rd[6] = function(A,B,C)
        local u = eUpvals[B]; eRegs[A].v = u and u.v[eRk(C)]
    end
    -- [7] GETTABLE
    rd[7] = function(A,B,C) eRegs[A].v = eRegs[B].v[eRk(C)] end
    -- [8] SETTABUP
    rd[8] = function(A,B,C)
        local u = eUpvals[A]; if u then u.v[eRk(B)] = eRk(C) end
    end
    -- [9] SETUPVAL
    rd[9] = function(A,B) eUpvals[B].v = eRegs[A].v end
    -- [10] SETTABLE
    rd[10] = function(A,B,C) eRegs[A].v[eRk(B)] = eRk(C) end
    -- [11] NEWTABLE
    rd[11] = function(A) eRegs[A].v = {} end
    -- [12] SELF
    rd[12] = function(A,B,C)
        eRegs[A+1].v = eRegs[B].v
        eRegs[A].v   = eRegs[B].v[eRk(C)]
    end
    -- [13] ADD
    rd[13] = function(A,B,C) eRegs[A].v = eRk(B) + eRk(C) end
    -- [14] SUB
    rd[14] = function(A,B,C) eRegs[A].v = eRk(B) - eRk(C) end
    -- [15] MUL
    rd[15] = function(A,B,C) eRegs[A].v = eRk(B) * eRk(C) end
    -- [16] MOD
    rd[16] = function(A,B,C) eRegs[A].v = eRk(B) % eRk(C) end
    -- [17] POW
    rd[17] = function(A,B,C) eRegs[A].v = eRk(B) ^ eRk(C) end
    -- [18] DIV
    rd[18] = function(A,B,C) eRegs[A].v = eRk(B) / eRk(C) end
    -- [19] IDIV
    rd[19] = function(A,B,C) eRegs[A].v = eRk(B) // eRk(C) end
    -- [20] BAND
    rd[20] = function(A,B,C) eRegs[A].v = _band(eRk(B), eRk(C)) end
    -- [21] BOR
    rd[21] = function(A,B,C) eRegs[A].v = _bor(eRk(B), eRk(C)) end
    -- [22] BXOR
    rd[22] = function(A,B,C) eRegs[A].v = _bxor(eRk(B), eRk(C)) end
    -- [23] SHL
    rd[23] = function(A,B,C) eRegs[A].v = _bshl(eRk(B), eRk(C)) end
    -- [24] SHR
    rd[24] = function(A,B,C) eRegs[A].v = _bshr(eRk(B), eRk(C)) end
    -- [25] UNM
    rd[25] = function(A,B) eRegs[A].v = -eRegs[B].v end
    -- [26] BNOT
    rd[26] = function(A,B) eRegs[A].v = _bnot(eRegs[B].v) end
    -- [27] NOT
    rd[27] = function(A,B) eRegs[A].v = not eRegs[B].v end
    -- [28] LEN
    rd[28] = function(A,B) eRegs[A].v = #eRegs[B].v end
    -- [29] CONCAT
    rd[29] = function(A,B,C)
        local t = {}
        for i = B, C do t[#t+1] = tostring(eRegs[i].v) end
        eRegs[A].v = table.concat(t)
    end
    -- [30] JMP
    rd[30] = function(A,B,C,Bx,sBx) ePc = ePc + sBx end
    -- [31] EQ
    rd[31] = function(A,B,C)
        if (eRk(B) == eRk(C)) ~= (A ~= 0) then ePc = ePc+1 end
    end
    -- [32] LT
    rd[32] = function(A,B,C)
        if (eRk(B) < eRk(C)) ~= (A ~= 0) then ePc = ePc+1 end
    end
    -- [33] LE
    rd[33] = function(A,B,C)
        if (eRk(B) <= eRk(C)) ~= (A ~= 0) then ePc = ePc+1 end
    end
    -- [34] TEST
    rd[34] = function(A,B,C)
        if (not not eRegs[A].v) ~= (C ~= 0) then ePc = ePc+1 end
    end
    -- [35] TESTSET
    rd[35] = function(A,B,C)
        if (not not eRegs[B].v) == (C ~= 0) then
            eRegs[A].v = eRegs[B].v
        else
            ePc = ePc+1
        end
    end
    -- [36] CALL
    rd[36] = function(A,B,C)
        local fn    = eRegs[A].v
        local cargs = {}
        local nargs = B == 0 and eTop-A or B-1
        for i = 1, nargs do cargs[i] = eRegs[A+i].v end
        local results = _pack(fn(_unpack(cargs, 1, nargs)))
        if C == 0 then
            for i = 0, results.n-1 do
                if not eRegs[A+i] then eRegs[A+i] = {} end
                eRegs[A+i].v = results[i+1]
            end
            eTop = A + results.n - 1
        else
            for i = 0, C-2 do
                if not eRegs[A+i] then eRegs[A+i] = {} end
                eRegs[A+i].v = results[i+1]
            end
        end
    end
    -- [37] TAILCALL
    rd[37] = function(A,B)
        local fn    = eRegs[A].v
        local cargs = {}
        local nargs = B == 0 and eTop-A or B-1
        for i = 1, nargs do cargs[i] = eRegs[A+i].v end
        local results = _pack(fn(_unpack(cargs, 1, nargs)))
        eDone = true; eRetN = results.n
        for i = 1, eRetN do eRetVals[i] = results[i] end
    end
    -- [38] RETURN
    rd[38] = function(A,B)
        eDone = true
        if B == 1 then eRetN = 0; return end
        local nelem = B == 0 and eTop or A+B-2
        eRetN = 0
        for i = A, nelem do eRetN = eRetN+1; eRetVals[eRetN] = eRegs[i].v end
    end
    -- [39] FORLOOP
    rd[39] = function(A,B,C,Bx,sBx)
        eRegs[A].v = eRegs[A].v + eRegs[A+2].v
        local idx  = eRegs[A].v
        local lim  = eRegs[A+1].v
        local step = eRegs[A+2].v
        if (step > 0 and idx <= lim) or (step < 0 and idx >= lim) then
            ePc = ePc + sBx; eRegs[A+3].v = idx
        end
    end
    -- [40] FORPREP
    rd[40] = function(A,B,C,Bx,sBx)
        eRegs[A].v = eRegs[A].v - eRegs[A+2].v
        ePc = ePc + sBx
    end
    -- [41] TFORCALL
    rd[41] = function(A,B,C)
        local results = _pack(eRegs[A].v(eRegs[A+1].v, eRegs[A+2].v))
        for i = 1, C do
            if not eRegs[A+2+i] then eRegs[A+2+i] = {} end
            eRegs[A+2+i].v = results[i]
        end
    end
    -- [42] TFORLOOP
    rd[42] = function(A,B,C,Bx,sBx)
        if eRegs[A+1].v ~= nil then
            eRegs[A].v = eRegs[A+1].v; ePc = ePc + sBx
        end
    end
    -- [43] SETLIST
    local BATCH = 50
    rd[43] = function(A,B,C)
        local off
        if C == 0 then
            local ni = eCode[ePc]; ePc = ePc+1
            off = (_bshr(ni, 6) - 1) * BATCH
        else
            off = (C-1) * BATCH
        end
        local nelem = B == 0 and eTop-A or B
        for i = 1, nelem do eRegs[A].v[off+i] = eRegs[A+i].v end
    end
    -- [44] CLOSURE
    rd[44] = function(A,B,C,Bx)
        local sub  = eProtos[Bx]
        local suvs = {}
        for i = 0, sub.sizeupvalues-1 do
            local uv = sub.upvals[i]
            if uv.instack == 1 then
                suvs[i] = eRegs[uv.idx]
            else
                local u = eUpvals[uv.idx]; suvs[i] = u or {}
            end
        end
        local _csuvs, _cbx = suvs, Bx
        eRegs[A].v = function(...) return execute(eProtos[_cbx], _csuvs, ...) end
    end
    -- [45] VARARG
    rd[45] = function(A,B)
        if B == 0 then
            for i = 0, #eVararg-1 do
                if not eRegs[A+i] then eRegs[A+i] = {} end
                eRegs[A+i].v = eVararg[i+1]
            end
            eTop = A + #eVararg - 1
        else
            for i = 0, B-2 do
                if not eRegs[A+i] then eRegs[A+i] = {} end
                eRegs[A+i].v = eVararg[i+1]
            end
        end
    end
    -- [46] EXTRAARG (no-op when reached standalone)
    rd[46] = function() end

    -- Remap real-opcode handlers → shuffled-opcode dispatch table
    local dispatch = {}
    for real = 0, 46 do
        local shuffled = fwdmap[real]
        if shuffled ~= nil then dispatch[shuffled] = rd[real] end
    end
    -- No-ops for virtual opcodes (junk instructions use opcodes 47-63)
    local _nop = function() end
    for vop = 47, 63 do dispatch[vop] = _nop end

    -- Decode masks (standard Lua 5.3 instruction layout)
    local M63  = 0x3F;  local M255 = 0xFF
    local M511 = 0x1FF; local M18  = 0x3FFFF
    local BIAS = 131071
    local SH6  = 6; local SH14 = 14; local SH23 = 23

    while not eDone do
        local inst = eCode[ePc]; ePc = ePc+1
        local op   = _band(inst, M63)
        local A    = _band(_bshr(inst, SH6),  M255)
        local B    = _band(_bshr(inst, SH23), M511)
        local C    = _band(_bshr(inst, SH14), M511)
        local Bx   = _band(_bshr(inst, SH14), M18)
        local sBx  = Bx - BIAS
        local h    = dispatch[op]
        if h then h(A, B, C, Bx, sBx)
        else error('Catify: unknown opcode ' .. tostring(op), 0) end
    end
    return _unpack(eRetVals, 1, eRetN)
end

-- ── 11. Bootstrap: resolve environment and run ────────────────────────────────
local env_box
do
    local e = (type(_ENV)=='table' and _ENV)
           or (type(getfenv)=='function' and getfenv(0))
           or (type(_G)=='table' and _G)
           or {}
    env_box = { v = (type(e)=='table' and e) or {} }
end

execute(proto, setmetatable({[0]=env_box}, {
    __index = function(t,k) local b={}; t[k]=b; return b end
}))

end  -- return function(cfg, payload)
