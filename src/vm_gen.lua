--[[
    Catify - Commercial Lua Obfuscator
    src/vm_gen.lua  - VM code generator

    Responsibilities:
      1. Re-serialize the (already opcode-shuffled) Proto tree into a compact
         custom binary format.
      2. Encrypt that blob with RC4 (key supplied by the caller).
      3. Emit a self-contained Lua 5.3 source file that:
           • Decrypts and deserializes the blob at runtime.
           • Runs a complete Lua 5.3 virtual machine implementing all 47 opcodes.
           • Uses shuffled opcode numbers, random local-variable names, and a
             state-machine dispatch loop for control-flow obfuscation.
]]

local VmGen = {}

-- ─── Custom bytecode serializer ───────────────────────────────────────────────
-- Format (all integers little-endian):
--   byte  numparams
--   byte  is_vararg
--   byte  maxstacksize
--   i32   sizecode
--   i32[sizecode] code
--   i32   sizek
--   constants (byte type, then value)
--     type 0 → nil
--     type 1 → false
--     type 2 → true
--     type 3 → int  (i64, 8 bytes)
--     type 4 → flt  (f64, 8 bytes)
--     type 5 → str  (i32 len, then bytes)
--   i32   sizeupvals
--   [sizeupvals] × { byte instack, byte idx }
--   i32   sizep
--   [sizep] × proto   (recursive)

local function ser_u8(v)   return string.char(v & 0xFF) end
local function ser_i32(v)
    v = v & 0xFFFFFFFF
    return string.char(v & 0xFF, (v>>8) & 0xFF, (v>>16) & 0xFF, (v>>24) & 0xFF)
end
local function ser_f64(v)  return string.pack("<d", v)  end
local function ser_i64(v)  return string.pack("<i8", v) end
local function ser_str(s)  return ser_i32(#s) .. s      end

local function serialize_proto(proto)
    local buf = {}
    local function w(s) buf[#buf+1] = s end

    w(ser_u8(proto.numparams))
    w(ser_u8(proto.is_vararg))
    w(ser_u8(proto.maxstacksize))

    -- Instructions (already shuffled by passes.lua)
    w(ser_i32(proto.sizecode))
    for i = 0, proto.sizecode - 1 do
        w(ser_i32(proto.code[i]))
    end

    -- Constants
    w(ser_i32(proto.sizek))
    for i = 0, proto.sizek - 1 do
        local c = proto.k[i]
        local ct = type(c)
        if c == nil then
            w(ser_u8(0))
        elseif ct == "boolean" then
            w(ser_u8(c and 2 or 1))
        elseif ct == "number" then
            if math.type(c) == "integer" then
                w(ser_u8(3))
                w(ser_i64(c))
            else
                w(ser_u8(4))
                w(ser_f64(c))
            end
        elseif ct == "string" then
            w(ser_u8(5))
            w(ser_str(c))
        else
            error("Unknown constant type: " .. ct)
        end
    end

    -- Upvalue descriptors
    w(ser_i32(proto.sizeupvalues))
    for i = 0, proto.sizeupvalues - 1 do
        w(ser_u8(proto.upvals[i].instack))
        w(ser_u8(proto.upvals[i].idx))
    end

    -- Nested prototypes (recursive)
    w(ser_i32(proto.sizep))
    for i = 0, proto.sizep - 1 do
        w(serialize_proto(proto.p[i]))
    end

    return table.concat(buf)
end

-- ─── Lua source code builder ───────────────────────────────────────────────────

-- Emit a byte-array as a Lua string literal using \NNN escapes (no quotes).
local function bytes_esc(data)
    local t = {}
    for i = 1, #data do t[i] = string.format("\\%d", data:byte(i)) end
    return table.concat(t)
end

-- Emit the encrypted blob as a chunked table matching the superflow_bytecode
-- style from reference implementations.  Each entry is a \NNN-escaped string
-- of at most CHUNK_SIZE bytes so the output stays readable and mirrors the
-- reference obfuscator's layout.
local CHUNK_SIZE = 200
local function emit_payload_table(data, tbl_name)
    local parts = {}
    parts[#parts+1] = "local " .. tbl_name .. "={\n"
    local i = 1
    while i <= #data do
        local chunk = data:sub(i, i + CHUNK_SIZE - 1)
        parts[#parts+1] = '  "' .. bytes_esc(chunk) .. '",\n'
        i = i + CHUNK_SIZE
    end
    parts[#parts+1] = "}\n"
    return table.concat(parts)
end

-- Emit an integer as a Lua numeric literal (optionally obfuscated).
local function int_lit(n)
    return tostring(math.tointeger(n) or n)
end

-- ─── VM Lua template (generated with random names at call time) ────────────────

--- Generate the complete obfuscated Lua source for the given proto.
---@param proto   table   Top-level proto (opcodes already shuffled in .code arrays)
---@param revmap  table   revmap[shuffled_op] = real_op  (0-indexed)
---@param key     string  RC4 key used to encrypt the bytecode blob
---@param utils   table   The Utils module (for RC4 and rand_names)
---@return string  Lua source
function VmGen.generate(proto, revmap, key, utils)
    -- ── 1. Serialize + encrypt the custom bytecode ───────────────────────────
    local raw  = serialize_proto(proto)
    local blob = utils.rc4(raw, key)

    -- ── 2. Generate random identifiers for all locals ───────────────────────
    -- We need ~80 unique names for VM internals
    local N  = utils.rand_names(100)
    local ni = 0
    local function vn()   -- "variable name"
        ni = ni + 1
        return N[ni]
    end

    -- Core names
    local vExec     = vn()   -- main execute function
    local vDeser    = vn()   -- deserializer function
    local vDecrypt  = vn()   -- RC4 decrypt function
    local vRevmap   = vn()   -- revmap table
    local vKey      = vn()   -- RC4 key string
    local vBlob     = vn()   -- encrypted bytecode blob
    local vProto    = vn()   -- top-level proto after deserialization
    local vEnv      = vn()   -- _ENV box

    -- Deserializer internals
    local dPos      = vn()
    local dData     = vn()
    local dRb       = vn()   -- read byte
    local dRi32     = vn()   -- read i32
    local dRi64     = vn()   -- read i64
    local dRf64     = vn()   -- read f64
    local dRstr     = vn()   -- read string

    -- RC4 internals
    local rc4S      = vn()
    local rc4I      = vn()
    local rc4J      = vn()
    local rc4Out    = vn()
    local rc4N      = vn()
    local rc4Tmp    = vn()
    local rc4Klen   = vn()
    local rc4K      = vn()   -- key param
    local rc4D      = vn()   -- data param

    -- Execute function params/locals
    local eProto    = vn()
    local eUpvals   = vn()
    local eVararg   = vn()
    local eRegs     = vn()
    local eTop      = vn()
    local ePc       = vn()
    local eCode     = vn()
    local eKst      = vn()
    local eProtos   = vn()
    local eArgs     = vn()
    local eInst     = vn()
    local eOp       = vn()
    local eA        = vn()
    local eB        = vn()
    local eC        = vn()
    local eBx       = vn()
    local eSBx      = vn()
    local eRk       = vn()
    local eRet      = vn()
    local eCallArgs = vn()
    local eNargs    = vn()
    local eResults  = vn()
    local eFn       = vn()
    local eOffset   = vn()
    local eNelem    = vn()
    local eSuvs     = vn()
    local eUv       = vn()
    local eSub      = vn()
    local eState    = vn()   -- dispatch state for CF obfuscation
    local eIdx      = vn()
    local eLim      = vn()
    local eStep     = vn()
    local eI        = vn()
    local eT        = vn()
    -- spare names for junk code
    local jA        = vn()
    local jB        = vn()
    local jC        = vn()
    -- anti-tamper names
    local atPayload = vn()   -- catify_payload table name
    local atCrc     = vn()   -- expected CRC variable
    local atCalc    = vn()   -- computed CRC variable
    local atDbg     = vn()   -- debug reference

    -- ── 3. Compute CRC32 of the encrypted blob for anti-tamper ──────────────
    local blob_crc = utils.crc32(blob)

    -- ── 4. Build the revmap literal ─────────────────────────────────────────
    local revmap_parts = {}
    for shuffled = 0, 46 do
        revmap_parts[#revmap_parts+1] = string.format("[%d]=%d", shuffled, revmap[shuffled] or shuffled)
    end
    local revmap_lit = "{" .. table.concat(revmap_parts, ",") .. "}"

    -- ── 4. Junk-code snippets (dead branches, always-false conditions) ────────
    local junk_seed = math.random(10000, 99999)
    local function junk_stmt(indent)
        -- A bogus computation that is never reachable or has no side-effects
        local a = math.random(1, 100)
        local b = math.random(200, 300)
        return string.format(
            "%slocal %s=%d;if %s>%d then %s=%s*%d end\n",
            indent, jA, a, jA, b, jA, jA, math.random(2,9))
    end

    -- ── 5. Assemble source ────────────────────────────────────────────────────
    local src = {}
    local function L(s) src[#src+1] = s .. "\n" end
    local function LF(fmt, ...) L(string.format(fmt, ...)) end

    -- Header comment (obfuscated watermark)
    L("-- [Catify] Protected Script – do not edit")
    L("do")
    L("local _=tostring;local __=type;local ___=pcall;local ____=load")

    -- RC4 decrypt function
    LF("local function %s(%s,%s)", vDecrypt, rc4D, rc4K)
    LF("  local %s={}",          rc4S)
    LF("  for %s=0,255 do %s[%s]=%s end", rc4I, rc4S, rc4I, rc4I)
    LF("  local %s=0", rc4J)
    LF("  local %s=#%s", rc4Klen, rc4K)
    LF("  for %s=0,255 do", rc4I)
    LF("    %s=(%s+%s[%s]+%s:byte((%s%%%s)+1))%%256", rc4J, rc4J, rc4S, rc4I, rc4K, rc4I, rc4Klen)
    LF("    %s[%s],%s[%s]=%s[%s],%s[%s]", rc4S, rc4I, rc4S, rc4J, rc4S, rc4J, rc4S, rc4I)
    LF("  end")
    LF("  local %s={}", rc4Out)
    LF("  %s=0", rc4I)
    LF("  %s=0", rc4J)
    LF("  for %s=1,#%s do", rc4N, rc4D)
    LF("    %s=(%s+1)%%256", rc4I, rc4I)
    LF("    %s=(%s+%s[%s])%%256", rc4J, rc4J, rc4S, rc4I)
    LF("    %s[%s],%s[%s]=%s[%s],%s[%s]", rc4S, rc4I, rc4S, rc4J, rc4S, rc4J, rc4S, rc4I)
    LF("    %s[%s]=string.char(%s:byte(%s)~%s[(%s[%s]+%s[%s])%%256])",
       rc4Out, rc4N, rc4D, rc4N, rc4S, rc4S, rc4I, rc4S, rc4J)
    LF("  end")
    LF("  return table.concat(%s)", rc4Out)
    LF("end")

    -- Deserializer
    LF("local %s", dPos)
    LF("local %s", dData)
    LF("local function %s() local v=%s:byte(%s);%s=%s+1;return v end", dRb, dData, dPos, dPos, dPos)
    LF("local function %s() local v,p=string.unpack('<i4',%s,%s);%s=p;return v end", dRi32, dData, dPos, dPos)
    LF("local function %s() local v,p=string.unpack('<i8',%s,%s);%s=p;return v end", dRi64, dData, dPos, dPos)
    LF("local function %s() local v,p=string.unpack('<d',%s,%s);%s=p;return v end",  dRf64, dData, dPos, dPos)
    LF("local function %s() local n=%s();return %s:sub(%s,%s+n-1) end", dRstr, dRi32, dData, dPos, dPos)
    -- The actual string-read lambda must also advance pos
    -- Rewrite dRstr properly:
    -- The sub call above reads without advancing; fix:
    src[#src] = string.format(
        "local function %s() local n=%s();local s=%s:sub(%s,%s+n-1);%s=%s+n;return s end\n",
        dRstr, dRi32, dData, dPos, dPos, dPos, dPos)

    -- Recursive prototype loader (declared forward)
    local vLoadProto = vn()
    LF("local %s", vLoadProto)
    LF("%s=function()", vLoadProto)
    LF("  local p={}")
    LF("  p.numparams=%s()",   dRb)
    LF("  p.is_vararg=%s()",   dRb)
    LF("  p.maxstacksize=%s()", dRb)
    LF("  local sc=%s(); p.sizecode=sc", dRi32)
    LF("  local code={}; p.code=code")
    LF("  for i=0,sc-1 do code[i]=string.unpack('<I4',%s,%s); %s=%s+4 end",
       dData, dPos, dPos, dPos)
    -- Constants
    LF("  local sk=%s(); p.sizek=sk", dRi32)
    LF("  local k={}; p.k=k")
    LF("  for i=0,sk-1 do")
    LF("    local t=%s()", dRb)
    LF("    if t==0 then k[i]=nil")
    LF("    elseif t==1 then k[i]=false")
    LF("    elseif t==2 then k[i]=true")
    LF("    elseif t==3 then k[i]=%s()", dRi64)
    LF("    elseif t==4 then k[i]=%s()", dRf64)
    LF("    elseif t==5 then k[i]=%s()", dRstr)
    LF("    end")
    LF("  end")
    -- Upvalues
    LF("  local su=%s(); p.sizeupvalues=su", dRi32)
    LF("  local uvs={}; p.upvals=uvs")
    LF("  for i=0,su-1 do uvs[i]={instack=%s(),idx=%s()} end", dRb, dRb)
    -- Nested protos
    LF("  local sp=%s(); p.sizep=sp", dRi32)
    LF("  local pp={}; p.p=pp")
    LF("  for i=0,sp-1 do pp[i]=%s() end", vLoadProto)
    LF("  return p")
    LF("end")

    -- Revmap (shuffled→real opcode)
    LF("local %s=%s", vRevmap, revmap_lit)

    -- The execute function
    LF("local function %s(%s,%s,...)", vExec, eProto, eUpvals)
    LF("  local %s=table.pack(...)", eArgs)
    -- Allocate register boxes (auto-create missing boxes via metatable)
    LF("  local %s=setmetatable({},{__index=function(t,k) local b={};t[k]=b;return b end})", eRegs)
    -- Pre-fill params and low registers
    LF("  for %s=0,%s.maxstacksize+63 do %s[%s]={} end", eI, eProto, eRegs, eI)
    -- Fill params
    LF("  for %s=0,%s.numparams-1 do %s[%s].v=%s[%s+1] end", eI, eProto, eRegs, eI, eArgs, eI)
    -- Vararg
    LF("  local %s={}", eVararg)
    LF("  if %s.is_vararg~=0 then", eProto)
    LF("    for %s=%s.numparams+1,%s.n do %s[#%s+1]=%s[%s] end",
       eI, eProto, eArgs, eVararg, eVararg, eArgs, eI)
    LF("  end")
    -- Locals
    LF("  local %s=0", ePc)
    LF("  local %s=-1", eTop)
    LF("  local %s=%s.code",   eCode,   eProto)
    LF("  local %s=%s.k",      eKst,    eProto)
    LF("  local %s=%s.p",      eProtos, eProto)
    -- rk helper (inline-able)
    LF("  local function %s(x) if x>=256 then return %s[x-256] else return %s[x].v end end",
       eRk, eKst, eRegs)

    -- ── Main dispatch loop (state-machine style) ─────────────────────────────
    LF("  local %s=0", eState)
    LF("  while true do")
    -- Fetch + decode
    LF("    local %s=%s[%s]", eInst, eCode, ePc)
    LF("    %s=%s+1", ePc, ePc)
    LF("    local %s=%s[%s&0x3F]", eOp, vRevmap, eInst)
    LF("    local %s=(%s>>6)&0xFF",  eA, eInst)
    LF("    local %s=(%s>>23)&0x1FF",eB, eInst)
    LF("    local %s=(%s>>14)&0x1FF",eC, eInst)
    LF("    local %s=(%s>>14)&0x3FFFF",eBx, eInst)
    LF("    local %s=%s-131071",   eSBx, eBx)
    -- Junk check (dead code)
    LF("    %s=%s", eState, eOp)
    L (junk_stmt("    "))
    -- Dispatch: split into two blocks to avoid "too many elseifs" in some interpreters
    LF("    if %s<24 then", eState)
    LF("      if %s==0 then %s[%s].v=%s[%s].v",        eState, eRegs, eA, eRegs, eB)
    LF("      elseif %s==1 then %s[%s].v=%s[%s]",      eState, eRegs, eA, eKst,  eBx)
    -- LOADKX
    LF("      elseif %s==2 then",                       eState)
    LF("        local ni=%s[%s];%s=%s+1;%s[%s].v=%s[ni>>6]", eCode, ePc, ePc, ePc, eRegs, eA, eKst)
    -- LOADBOOL
    LF("      elseif %s==3 then %s[%s].v=(%s~=0);if %s~=0 then %s=%s+1 end",
       eState, eRegs, eA, eB, eC, ePc, ePc)
    -- LOADNIL
    LF("      elseif %s==4 then for %s=%s,%s+%s do %s[%s].v=nil end",
       eState, eI, eA, eA, eB, eRegs, eI)
    -- GETUPVAL: defensive access – if upvals[B] is nil return nil (don't error)
    LF("      elseif %s==5 then local _uv=%s[%s];%s[%s].v=_uv and _uv.v or nil",
       eState, eUpvals, eB, eRegs, eA)
    -- GETTABUP
    LF("      elseif %s==6 then %s[%s].v=%s[%s].v[%s(%s)]",
       eState, eRegs, eA, eUpvals, eB, eRk, eC)
    -- GETTABLE
    LF("      elseif %s==7 then %s[%s].v=%s[%s].v[%s(%s)]",
       eState, eRegs, eA, eRegs, eB, eRk, eC)
    -- SETTABUP
    LF("      elseif %s==8 then %s[%s].v[%s(%s)]=%s(%s)",
       eState, eUpvals, eA, eRk, eB, eRk, eC)
    -- SETUPVAL
    LF("      elseif %s==9 then %s[%s].v=%s[%s].v",    eState, eUpvals, eB, eRegs, eA)
    -- SETTABLE
    LF("      elseif %s==10 then %s[%s].v[%s(%s)]=%s(%s)",
       eState, eRegs, eA, eRk, eB, eRk, eC)
    -- NEWTABLE
    LF("      elseif %s==11 then %s[%s].v={}",          eState, eRegs, eA)
    -- SELF
    LF("      elseif %s==12 then %s[%s+1].v=%s[%s].v;%s[%s].v=%s[%s].v[%s(%s)]",
       eState, eRegs, eA, eRegs, eB, eRegs, eA, eRegs, eB, eRk, eC)
    -- ADD SUB MUL MOD POW DIV IDIV
    LF("      elseif %s==13 then %s[%s].v=%s(%s)+%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==14 then %s[%s].v=%s(%s)-%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==15 then %s[%s].v=%s(%s)*%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==16 then %s[%s].v=%s(%s)%%%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==17 then %s[%s].v=%s(%s)^%s(%s)",  eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==18 then %s[%s].v=%s(%s)/%s(%s)",  eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==19 then %s[%s].v=%s(%s)//%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    -- BAND BOR BXOR SHL SHR
    LF("      elseif %s==20 then %s[%s].v=%s(%s)&%s(%s)",  eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==21 then %s[%s].v=%s(%s)|%s(%s)",  eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==22 then %s[%s].v=%s(%s)~%s(%s)",  eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==23 then %s[%s].v=%s(%s)<<%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      end")
    LF("    elseif %s<47 then", eState)
    -- SHR UNM BNOT NOT LEN CONCAT
    LF("      if %s==24 then %s[%s].v=%s(%s)>>%s(%s)", eState, eRegs, eA, eRk, eB, eRk, eC)
    LF("      elseif %s==25 then %s[%s].v=-%s[%s].v",  eState, eRegs, eA, eRegs, eB)
    LF("      elseif %s==26 then %s[%s].v=~%s[%s].v",  eState, eRegs, eA, eRegs, eB)
    LF("      elseif %s==27 then %s[%s].v=not %s[%s].v",eState, eRegs, eA, eRegs, eB)
    LF("      elseif %s==28 then %s[%s].v=#%s[%s].v",  eState, eRegs, eA, eRegs, eB)
    -- CONCAT
    LF("      elseif %s==29 then", eState)
    LF("        local %s={}", eT)
    LF("        for %s=%s,%s do %s[#%s+1]=tostring(%s[%s].v) end", eI, eB, eC, eT, eT, eRegs, eI)
    LF("        %s[%s].v=table.concat(%s)", eRegs, eA, eT)
    -- JMP
    LF("      elseif %s==30 then %s=%s+%s", eState, ePc, ePc, eSBx)
    -- EQ LT LE TEST TESTSET
    LF("      elseif %s==31 then if(%s(%s)==%s(%s))~=(%s~=0) then %s=%s+1 end",
       eState, eRk, eB, eRk, eC, eA, ePc, ePc)
    LF("      elseif %s==32 then if(%s(%s)<%s(%s))~=(%s~=0) then %s=%s+1 end",
       eState, eRk, eB, eRk, eC, eA, ePc, ePc)
    LF("      elseif %s==33 then if(%s(%s)<=%s(%s))~=(%s~=0) then %s=%s+1 end",
       eState, eRk, eB, eRk, eC, eA, ePc, ePc)
    LF("      elseif %s==34 then if(not not %s[%s].v)~=(%s~=0) then %s=%s+1 end",
       eState, eRegs, eA, eC, ePc, ePc)
    LF("      elseif %s==35 then if(not not %s[%s].v)==(%s~=0) then %s[%s].v=%s[%s].v else %s=%s+1 end",
       eState, eRegs, eB, eC, eRegs, eA, eRegs, eB, ePc, ePc)
    -- CALL
    LF("      elseif %s==36 then", eState)
    LF("        local %s=%s[%s].v", eFn, eRegs, eA)
    LF("        local %s={}", eCallArgs)
    LF("        local %s=%s==0 and %s-%s or %s-1", eNargs, eB, eTop, eA, eB)
    LF("        for %s=1,%s do %s[%s]=%s[%s+%s].v end", eI, eNargs, eCallArgs, eI, eRegs, eA, eI)
    LF("        local %s=table.pack(%s(table.unpack(%s,1,%s)))", eResults, eFn, eCallArgs, eNargs)
    LF("        if %s==0 then", eC)
    LF("          for %s=0,%s.n-1 do if not %s[%s+%s] then %s[%s+%s]={} end;%s[%s+%s].v=%s[%s+1] end",
       eI, eResults, eRegs, eA, eI, eRegs, eA, eI, eRegs, eA, eI, eResults, eI)
    LF("          %s=%s+%s.n-1", eTop, eA, eResults)
    LF("        else")
    LF("          for %s=0,%s-2 do if not %s[%s+%s] then %s[%s+%s]={} end;%s[%s+%s].v=%s[%s+1] end",
       eI, eC, eRegs, eA, eI, eRegs, eA, eI, eRegs, eA, eI, eResults, eI)
    LF("        end")
    -- TAILCALL
    LF("      elseif %s==37 then", eState)
    LF("        local %s=%s[%s].v", eFn, eRegs, eA)
    LF("        local %s={}", eCallArgs)
    LF("        local %s=%s==0 and %s-%s or %s-1", eNargs, eB, eTop, eA, eB)
    LF("        for %s=1,%s do %s[%s]=%s[%s+%s].v end", eI, eNargs, eCallArgs, eI, eRegs, eA, eI)
    LF("        return %s(table.unpack(%s,1,%s))", eFn, eCallArgs, eNargs)
    -- RETURN
    LF("      elseif %s==38 then", eState)
    LF("        if %s==1 then return end", eB)
    LF("        local %s={}", eRet)
    LF("        local %s=%s==0 and %s or %s+%s-2", eNelem, eB, eTop, eA, eB)
    LF("        for %s=%s,%s do %s[#%s+1]=%s[%s].v end", eI, eA, eNelem, eRet, eRet, eRegs, eI)
    LF("        return table.unpack(%s)", eRet)
    -- FORLOOP
    LF("      elseif %s==39 then", eState)
    LF("        %s[%s].v=%s[%s].v+%s[%s+2].v", eRegs, eA, eRegs, eA, eRegs, eA)
    LF("        local %s=%s[%s].v", eIdx,  eRegs, eA)
    LF("        local %s=%s[%s+1].v", eLim, eRegs, eA)
    LF("        local %s=%s[%s+2].v", eStep,eRegs, eA)
    LF("        if(%s>0 and %s<=%s) or (%s<0 and %s>=%s) then", eStep, eIdx, eLim, eStep, eIdx, eLim)
    LF("          %s=%s+%s;%s[%s+3].v=%s", ePc, ePc, eSBx, eRegs, eA, eIdx)
    LF("        end")
    -- FORPREP
    LF("      elseif %s==40 then", eState)
    LF("        %s[%s].v=%s[%s].v-%s[%s+2].v;%s=%s+%s", eRegs, eA, eRegs, eA, eRegs, eA, ePc, ePc, eSBx)
    -- TFORCALL
    LF("      elseif %s==41 then", eState)
    LF("        local %s=table.pack(%s[%s].v(%s[%s+1].v,%s[%s+2].v))",
       eResults, eRegs, eA, eRegs, eA, eRegs, eA)
    LF("        for %s=1,%s do if not %s[%s+2+%s] then %s[%s+2+%s]={} end;%s[%s+2+%s].v=%s[%s] end",
       eI, eC, eRegs, eA, eI, eRegs, eA, eI, eRegs, eA, eI, eResults, eI)
    -- TFORLOOP
    LF("      elseif %s==42 then", eState)
    LF("        if %s[%s+1].v~=nil then %s[%s].v=%s[%s+1].v;%s=%s+%s end",
       eRegs, eA, eRegs, eA, eRegs, eA, ePc, ePc, eSBx)
    -- SETLIST
    LF("      elseif %s==43 then", eState)
    LF("        local %s", eOffset)
    LF("        if %s==0 then local ni=%s[%s];%s=%s+1;%s=(ni>>6)*50 else %s=(%s-1)*50 end",
       eC, eCode, ePc, ePc, ePc, eOffset, eOffset, eC)
    LF("        local %s=%s==0 and %s-%s or %s", eNelem, eB, eTop, eA, eB)
    LF("        for %s=1,%s do %s[%s].v[%s+%s]=%s[%s+%s].v end",
       eI, eNelem, eRegs, eA, eOffset, eI, eRegs, eA, eI)
    -- CLOSURE: build suvs defensively (nil upvals become empty boxes)
    LF("      elseif %s==44 then", eState)
    LF("        local %s=%s[%s]", eSub, eProtos, eBx)
    LF("        local %s={}", eSuvs)
    LF("        for %s=0,%s.sizeupvalues-1 do", eI, eSub)
    LF("          local %s=%s.upvals[%s]", eUv, eSub, eI)
    LF("          if %s.instack==1 then %s[%s]=%s[%s.idx]", eUv, eSuvs, eI, eRegs, eUv)
    LF("          else local _u=%s[%s.idx];%s[%s]=_u or {} end", eUpvals, eUv, eSuvs, eI)
    LF("        end")
    LF("        local cap_%s,%s_sv=%s,%s", eI, eI, eSuvs, eBx)
    LF("        %s[%s].v=function(...) return %s(%s[%s_sv],cap_%s,...) end",
       eRegs, eA, vExec, eProtos, eI, eI)
    -- VARARG
    LF("      elseif %s==45 then", eState)
    LF("        if %s==0 then", eB)
    LF("          for %s=0,#%s-1 do if not %s[%s+%s] then %s[%s+%s]={} end;%s[%s+%s].v=%s[%s+1] end",
       eI, eVararg, eRegs, eA, eI, eRegs, eA, eI, eRegs, eA, eI, eVararg, eI)
    LF("          %s=%s+#%s-1", eTop, eA, eVararg)
    LF("        else")
    LF("          for %s=0,%s-2 do if not %s[%s+%s] then %s[%s+%s]={} end;%s[%s+%s].v=%s[%s+1] end",
       eI, eB, eRegs, eA, eI, eRegs, eA, eI, eRegs, eA, eI, eVararg, eI)
    LF("        end")
    -- EXTRAARG – handled inline by LOADKX/SETLIST
    LF("      end")
    LF("    end")
    LF("  end")
    LF("end")  -- end execute function

    -- ── Main: emit payload, anti-tamper, decrypt, deserialize, run ──────────
    -- Chunked encrypted payload table (mirrors superflow_bytecode format)
    src[#src+1] = emit_payload_table(blob, atPayload)

    -- RC4 key
    LF("local %s=\"%s\"", vKey, bytes_esc(key))

    -- Anti-tamper 1: CRC32 integrity check of the encrypted blob
    -- Inline CRC32 (so we don't depend on external functions at runtime)
    LF("local function _crc32_(s)")
    LF("  local _t={}")
    LF("  for _i=0,255 do")
    LF("    local _c=_i")
    LF("    for _=1,8 do if _c&1~=0 then _c=0xEDB88320~(_c>>1) else _c=_c>>1 end end")
    LF("    _t[_i]=_c")
    LF("  end")
    LF("  local _r=0xFFFFFFFF")
    LF("  for _i=1,#s do _r=_t[(_r~s:byte(_i))&0xFF]~(_r>>8) end")
    LF("  return _r~0xFFFFFFFF")
    LF("end")
    -- Compute expected CRC and verify
    LF("local %s=%s", atCrc, tostring(blob_crc))
    LF("local %s=table.concat(%s)", vBlob, atPayload)
    LF("%s=nil", atPayload)   -- wipe payload table after concat
    LF("local %s=_crc32_(%s)", atCalc, vBlob)
    LF("if %s~=%s then error('Catify: integrity check failed',0) end", atCalc, atCrc)

    -- Anti-tamper 2: debug hook detection
    LF("local %s=rawget(_ENV,'debug')", atDbg)
    LF("if %s and type(%s.gethook)=='function' then", atDbg, atDbg)
    LF("  if %s.gethook()~=nil then error('Catify: debug hook detected',0) end", atDbg)
    LF("end")

    -- Anti-tamper 3: critical global integrity check
    LF("do")
    LF("  local _req={tostring=tostring,type=type,pcall=pcall,load=load,string=string,table=table}")
    LF("  for _k,_v in pairs(_req) do")
    LF("    if _v==nil then error('Catify: environment tampered ('.._k..')',0) end")
    LF("  end")
    LF("end")

    -- Decrypt and deserialize
    LF("%s=%s(%s,%s)", vBlob, vDecrypt, vBlob, vKey)
    LF("%s=nil;%s=nil", vKey, vDecrypt)   -- wipe key and decryptor
    LF("%s=1", dPos)
    LF("%s=%s", dData, vBlob)
    LF("local %s=%s()", vProto, vLoadProto)
    LF("%s=nil;%s=nil;%s=nil", vBlob, dData, vLoadProto)  -- wipe after load
    LF("local %s={v=_ENV}", vEnv)
    -- Initial upvals table uses a metatable so any upval[N] always returns a box
    LF("%s(%s,setmetatable({[0]=%s},{__index=function(t,k)local b={};t[k]=b;return b end}))",
       vExec, vProto, vEnv)
    L("end")

    return table.concat(src)
end

return VmGen
