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

-- sxor: optional byte (0-255) XOR-applied to every string constant before
-- the outer RC4 pass, providing a second independent encryption layer.
local function serialize_proto(proto, sxor)
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
            if sxor and sxor ~= 0 then
                -- XOR each byte with the per-session key before storing.
                local enc = {}
                for i = 1, #c do
                    enc[i] = string.char(c:byte(i) ~ sxor)
                end
                w(ser_str(table.concat(enc)))
            else
                w(ser_str(c))
            end
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
        w(serialize_proto(proto.p[i], sxor))
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
-- The table name is always the literal "superflow_bytecode" (global, no local)
-- so it matches the reference format exactly.
local CHUNK_SIZE = 200
local PAYLOAD_TABLE_NAME = "superflow_bytecode"
local function emit_payload_table(data)
    local parts = {}
    parts[#parts+1] = PAYLOAD_TABLE_NAME .. "={"
    local i = 1
    while i <= #data do
        local chunk = data:sub(i, i + CHUNK_SIZE - 1)
        if i > 1 then parts[#parts+1] = "," end
        parts[#parts+1] = '"' .. bytes_esc(chunk) .. '"'
        i = i + CHUNK_SIZE
    end
    parts[#parts+1] = "};"
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
    local sxor_byte = math.random(1, 255)     -- per-session string XOR key
    local raw  = serialize_proto(proto, sxor_byte)
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
    -- anti-tamper names (atPayload is now the fixed string "superflow_bytecode")
    local atCrc     = vn()   -- expected CRC variable
    local atCalc    = vn()   -- computed CRC variable
    local atDbg     = vn()   -- debug reference
    local vStrXor   = vn()   -- string-constant XOR key (second encryption layer)
    local atVer     = vn()   -- Lua version check scratch
    local atRaw     = vn()   -- raw* functions check scratch
    -- decoy function names
    local vDecoy    = vn()   -- decoy function (defined, never called)
    local dkA       = vn()
    local dkB       = vn()
    local dkC       = vn()
    local dkD       = vn()
    -- dispatch table VM state names
    local vDispatch = vn()   -- opcode dispatch table
    local eDone     = vn()   -- execution-done flag
    local eRetVals  = vn()   -- return-values accumulator
    local eRetN     = vn()   -- number of return values

    -- ── 3. Compute CRC32 of the encrypted blob for anti-tamper ──────────────
    local blob_crc = utils.crc32(blob)

    -- ── 4. Build the revmap literal ─────────────────────────────────────────
    local revmap_parts = {}
    for shuffled = 0, 46 do
        revmap_parts[#revmap_parts+1] = string.format("[%d]=%d", shuffled, revmap[shuffled] or shuffled)
    end
    local revmap_lit = "{" .. table.concat(revmap_parts, ",") .. "}"

    -- ── 4. Junk-code snippets (opaque predicates, dead branches) ─────────────
    local junk_seed = math.random(10000, 99999)
    -- Eight forms of always-dead opaque predicates / no-op computations:
    --  form 1: x XOR x == 0, never > 0
    --  form 2: n // n == 1, never < 1
    --  form 3: (a+b)*c - (a+b)*c == 0, never > 1
    --  form 4: #"literal" == known length, dead if branch
    --  form 5: table constructor immediately discarded, length always 0
    --  form 6: multi-step XOR chain that cancels to 0
    --  form 7: math.max(a, b) identity (a >= b, so result == a, dead sub-branch)
    --  form 8: string rep + len identity (len("#") * n == n)
    local junk_forms = {
        -- form 1: x XOR x == 0
        function(indent)
            local a = math.random(1, 0x7FFF)
            local b = math.random(1, 0xFF)
            return string.format(
                "%sdo local %s=%d*%d;local %s=%s~%s;if %s>0 then %s=%s+%d end end\n",
                indent, jA, a, b, jB, jA, jA, jB, jA, jA, math.random(1, 0xFF))
        end,
        -- form 2: integer division identity
        function(indent)
            local a = math.random(2, 0x3FFF)
            local c = math.random(1, 9)
            return string.format(
                "%sdo local %s=%d+%d;local %s=%s//%s;if %s<%d then %s=%s*%d end end\n",
                indent, jA, a, c, jB, jA, jA, jB, 1, jA, jA, math.random(2, 9))
        end,
        -- form 3: product minus itself
        function(indent)
            local a = math.random(1, 0x1FFF)
            local b = math.random(1, 0x1FFF)
            local c = math.random(1, 7)
            local prod = (a + b) * c
            return string.format(
                "%sdo local %s=(%d+%d)*%d;local %s=%s-%d;if %s>1 then %s=%s^2 end end\n",
                indent, jA, a, b, c, jB, jA, prod, jB, jA, jA)
        end,
        -- form 4: string length identity (dead branch on impossible length)
        function(indent)
            local words = {"catify","obfuscate","runtime","protect","bytecode","virtual"}
            local w = words[math.random(1, #words)]
            local wrong_len = #w + math.random(1, 5)
            return string.format(
                "%sdo local %s=#%q;if %s==%d then %s=%s*0 end end\n",
                indent, jA, w, jA, wrong_len, jA, jA)
        end,
        -- form 5: empty table, length check always 0
        function(indent)
            local n = math.random(1, 9)
            return string.format(
                "%sdo local %s={};for %s=1,%d do end;if #%s>0 then %s[1]=nil end end\n",
                indent, jA, jB, n, jA, jA)
        end,
        -- form 6: multi-step XOR chain cancelling to 0
        function(indent)
            local x = math.random(1, 0xFFFF)
            local y = math.random(1, 0xFFFF)
            local z = x ~ y
            return string.format(
                "%sdo local %s=%d;local %s=%d;local %s=%s~%s;if (%s~%s)>0 then %s=%s|1 end end\n",
                indent, jA, x, jB, y, jC, jA, jB, jC, jA, jB, jB)
        end,
        -- form 7: math.max identity (always picks first arg)
        function(indent)
            local big = math.random(0x1000, 0x7FFF)
            local small = math.random(1, big - 1)
            local wrong = small - math.random(1, small)
            return string.format(
                "%sdo local %s=math.max(%d,%d);if %s<%d then %s=%s+1 end end\n",
                indent, jA, big, small, jA, big, jA, jA)
        end,
        -- form 8: string.rep + #  identity
        function(indent)
            local ch = string.char(math.random(65, 90))   -- A-Z
            local n  = math.random(3, 8)
            return string.format(
                "%sdo local %s=string.rep(%q,%d);if #%s~=%d then %s=nil end end\n",
                indent, jA, ch, n, jA, n, jA)
        end,
    }
    local function junk_stmt(indent)
        return junk_forms[math.random(1, #junk_forms)](indent)
    end
    -- Emit `k` consecutive junk statements with the given indent.
    local function junk_block(indent, k)
        local out = {}
        for _ = 1, k do out[#out+1] = junk_stmt(indent) end
        return table.concat(out)
    end

    -- ── 5. Assemble source ────────────────────────────────────────────────────
    local src = {}
    local function L(s) src[#src+1] = s .. "\n" end
    local function LF(fmt, ...) L(string.format(fmt, ...)) end

    -- ── Header comment matching reference obfuscator style ───────────────────
    L("--[[\n\tCatify — Lua Script Protector\n\thttps://github.com/francyw22/catempire\n]]")

    -- ── Chunked payload table at the top (reference style: global assignment) ─
    -- This is emitted first so it matches the reference's `superflow_bytecode={...}`
    -- layout exactly: the table is defined before the VM runtime code.
    src[#src+1] = emit_payload_table(blob) .. "\n"

    -- Wrap all VM internals in a do...end block so locals don't pollute global scope
    L("do")
    L("local _=tostring;local __=type;local ___=pcall;local ____=load")
    -- Junk block at top of do-scope (dead computations, not reachable by any real code path)
    src[#src+1] = junk_block("", math.random(2, 4))
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
    -- Junk block between RC4 function and deserializer
    src[#src+1] = junk_block("", math.random(2, 3))
    -- Decoy function: looks like a secondary hash/encode but is never called.
    -- Its body is all dead computation (XOR mixing on random constants).
    do
        local da = math.random(1, 0x7FFF)
        local db = math.random(1, 0x7FFF)
        local dc = math.random(1, 0xFFFF)
        LF("local function %s(%s)", vDecoy, dkA)
        LF("  local %s=%d local %s=%d local %s=%s~%d", dkB, da, dkC, db, dkD, dkA, dc)
        LF("  for %s=1,#%s do %s=%s~string.byte(%s,%s) end", dkB, dkA, dkC, dkC, dkA, dkB)
        LF("  return %s~%s", dkC, dkD)
        LF("end")
    end

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

    -- Emit the string-constant XOR key as an obfuscated math expression so it
    -- is not visible as a plain integer literal in the output.
    do
        local sx_a = math.random(0, 255)
        local sx_b = sx_a ~ sxor_byte  -- XOR split: sx_a ~ sx_b == sxor_byte
        local sx_p = math.random(1, 0xFFFF)
        local sx_q = math.random(1, 0xFFFF)
        LF("local %s=((%d~%d)+%d+%d-%d-%d)", vStrXor, sx_a, sx_b, sx_p, sx_q, sx_p, sx_q)
    end

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
    LF("    elseif t==5 then local _sx=%s();local _sd={};for _si=1,#_sx do _sd[_si]=string.char(_sx:byte(_si)~%s)end;k[i]=table.concat(_sd)", dRstr, vStrXor)
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
    -- Junk block after revmap declaration
    src[#src+1] = junk_block("", math.random(1, 3))

    -- The execute function (dispatch-table based)
    LF("local function %s(%s,%s,...)", vExec, eProto, eUpvals)
    LF("  local %s=table.pack(...)", eArgs)
    -- Junk at function entry
    src[#src+1] = junk_block("  ", math.random(1, 2))
    -- Allocate register boxes (auto-create missing boxes via metatable)
    LF("  local %s=setmetatable({},{__index=function(t,k) local b={};t[k]=b;return b end})", eRegs)
    LF("  for %s=0,%s.maxstacksize+63 do %s[%s]={} end", eI, eProto, eRegs, eI)
    -- Fill params
    LF("  for %s=0,%s.numparams-1 do %s[%s].v=%s[%s+1] end", eI, eProto, eRegs, eI, eArgs, eI)
    -- Vararg
    LF("  local %s={}", eVararg)
    LF("  if %s.is_vararg~=0 then", eProto)
    LF("    for %s=%s.numparams+1,%s.n do %s[#%s+1]=%s[%s] end",
       eI, eProto, eArgs, eVararg, eVararg, eArgs, eI)
    LF("  end")
    -- VM state locals
    LF("  local %s=0", ePc)
    LF("  local %s=-1", eTop)
    LF("  local %s=%s.code",   eCode,   eProto)
    LF("  local %s=%s.k",      eKst,    eProto)
    LF("  local %s=%s.p",      eProtos, eProto)
    -- Execution-done flag and return-value storage
    LF("  local %s=false", eDone)
    LF("  local %s={}", eRetVals)
    LF("  local %s=0", eRetN)
    -- rk helper: read register or constant
    LF("  local function %s(x) if x>=256 then return %s[x-256] else return %s[x].v end end",
       eRk, eKst, eRegs)

    -- ── Opcode dispatch table: one closure per opcode, indexed by real opcode ──
    LF("  local %s={}", vDispatch)
    -- Junk between table creation and first handler
    src[#src+1] = junk_block("  ", math.random(1, 2))

    -- [0] MOVE
    LF("  %s[0]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA, eRegs,eB)
    -- [1] LOADK
    LF("  %s[1]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s] end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA, eKst,eBx)
    -- [2] LOADKX  (next instruction is EXTRAARG carrying the index)
    LF("  %s[2]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local _ni=%s[%s];%s=%s+1;%s[%s].v=%s[_ni>>6]", eCode,ePc,ePc,ePc, eRegs,eA,eKst)
    LF("  end")
    -- [3] LOADBOOL
    LF("  %s[3]=function(%s,%s,%s,%s,%s) %s[%s].v=(%s~=0);if %s~=0 then %s=%s+1 end end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA,eB, eC,ePc,ePc)
    -- [4] LOADNIL
    LF("  %s[4]=function(%s,%s,%s,%s,%s) for _i=%s,%s+%s do %s[_i].v=nil end end",
       vDispatch, eA,eB,eC,eBx,eSBx, eA,eA,eB, eRegs)
    src[#src+1] = junk_block("  ", 1)   -- junk between handler groups
    -- [5] GETUPVAL (defensive: nil upval box → nil)
    LF("  %s[5]=function(%s,%s,%s,%s,%s) local _u=%s[%s];%s[%s].v=_u and _u.v or nil end",
       vDispatch, eA,eB,eC,eBx,eSBx, eUpvals,eB, eRegs,eA)
    -- [6] GETTABUP
    LF("  %s[6]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v[%s(%s)] end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA, eUpvals,eB, eRk,eC)
    -- [7] GETTABLE
    LF("  %s[7]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v[%s(%s)] end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA, eRegs,eB, eRk,eC)
    -- [8] SETTABUP
    LF("  %s[8]=function(%s,%s,%s,%s,%s) %s[%s].v[%s(%s)]=%s(%s) end",
       vDispatch, eA,eB,eC,eBx,eSBx, eUpvals,eA, eRk,eB, eRk,eC)
    -- [9] SETUPVAL
    LF("  %s[9]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v end",
       vDispatch, eA,eB,eC,eBx,eSBx, eUpvals,eB, eRegs,eA)
    -- [10] SETTABLE
    LF("  %s[10]=function(%s,%s,%s,%s,%s) %s[%s].v[%s(%s)]=%s(%s) end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA, eRk,eB, eRk,eC)
    src[#src+1] = junk_block("  ", 1)
    -- [11] NEWTABLE
    LF("  %s[11]=function(%s,%s,%s,%s,%s) %s[%s].v={} end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA)
    -- [12] SELF
    LF("  %s[12]=function(%s,%s,%s,%s,%s) %s[%s+1].v=%s[%s].v;%s[%s].v=%s[%s].v[%s(%s)] end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA, eRegs,eB, eRegs,eA, eRegs,eB, eRk,eC)
    -- [13..19] Arithmetic: ADD SUB MUL MOD POW DIV IDIV
    LF("  %s[13]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)+%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[14]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)-%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[15]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)*%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[16]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)%%%s(%s) end",vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[17]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)^%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[18]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)/%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[19]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)//%s(%s) end",vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    src[#src+1] = junk_block("  ", 1)
    -- [20..24] Bitwise: BAND BOR BXOR SHL SHR
    LF("  %s[20]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)&%s(%s) end",  vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[21]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)|%s(%s) end",  vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[22]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)~%s(%s) end",  vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[23]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)<<%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[24]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)>>%s(%s) end", vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    -- [25..28] Unary: UNM BNOT NOT LEN
    LF("  %s[25]=function(%s,%s,%s,%s,%s) %s[%s].v=-%s[%s].v end",     vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    LF("  %s[26]=function(%s,%s,%s,%s,%s) %s[%s].v=~%s[%s].v end",     vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    LF("  %s[27]=function(%s,%s,%s,%s,%s) %s[%s].v=not %s[%s].v end",  vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    LF("  %s[28]=function(%s,%s,%s,%s,%s) %s[%s].v=#%s[%s].v end",     vDispatch,eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    src[#src+1] = junk_block("  ", 1)
    -- [29] CONCAT
    LF("  %s[29]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local _t={}")
    LF("    for _i=%s,%s do _t[#_t+1]=tostring(%s[_i].v) end", eB,eC,eRegs)
    LF("    %s[%s].v=table.concat(_t)", eRegs,eA)
    LF("  end")
    -- [30] JMP  (modifies pc via upvalue – Lua closure upvalue sharing)
    LF("  %s[30]=function(%s,%s,%s,%s,%s) %s=%s+%s end",
       vDispatch, eA,eB,eC,eBx,eSBx, ePc,ePc,eSBx)
    -- [31..33] Comparisons: EQ LT LE
    LF("  %s[31]=function(%s,%s,%s,%s,%s) if(%s(%s)==%s(%s))~=(%s~=0) then %s=%s+1 end end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRk,eB,eRk,eC,eA,ePc,ePc)
    LF("  %s[32]=function(%s,%s,%s,%s,%s) if(%s(%s)<%s(%s))~=(%s~=0) then %s=%s+1 end end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRk,eB,eRk,eC,eA,ePc,ePc)
    LF("  %s[33]=function(%s,%s,%s,%s,%s) if(%s(%s)<=%s(%s))~=(%s~=0) then %s=%s+1 end end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRk,eB,eRk,eC,eA,ePc,ePc)
    -- [34] TEST
    LF("  %s[34]=function(%s,%s,%s,%s,%s) if(not not %s[%s].v)~=(%s~=0) then %s=%s+1 end end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA,eC,ePc,ePc)
    -- [35] TESTSET
    LF("  %s[35]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    if(not not %s[%s].v)==(%s~=0) then %s[%s].v=%s[%s].v else %s=%s+1 end",
       eRegs,eB,eC, eRegs,eA,eRegs,eB, ePc,ePc)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [36] CALL
    LF("  %s[36]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local %s=%s[%s].v", eFn,eRegs,eA)
    LF("    local %s={}", eCallArgs)
    LF("    local %s=%s==0 and %s-%s or %s-1", eNargs,eB,eTop,eA,eB)
    LF("    for _i=1,%s do %s[_i]=%s[%s+_i].v end", eNargs,eCallArgs,eRegs,eA)
    LF("    local %s=table.pack(%s(table.unpack(%s,1,%s)))", eResults,eFn,eCallArgs,eNargs)
    LF("    if %s==0 then", eC)
    LF("      for _i=0,%s.n-1 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       eResults,eRegs,eA,eRegs,eA,eRegs,eA,eResults)
    LF("      %s=%s+%s.n-1", eTop,eA,eResults)
    LF("    else")
    LF("      for _i=0,%s-2 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       eC,eRegs,eA,eRegs,eA,eRegs,eA,eResults)
    LF("    end")
    LF("  end")
    -- [37] TAILCALL (simulated as call + done; avoids TCO loss of semantics)
    LF("  %s[37]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local %s=%s[%s].v", eFn,eRegs,eA)
    LF("    local %s={}", eCallArgs)
    LF("    local %s=%s==0 and %s-%s or %s-1", eNargs,eB,eTop,eA,eB)
    LF("    for _i=1,%s do %s[_i]=%s[%s+_i].v end", eNargs,eCallArgs,eRegs,eA)
    LF("    local %s=table.pack(%s(table.unpack(%s,1,%s)))", eResults,eFn,eCallArgs,eNargs)
    LF("    %s=true;%s=%s.n", eDone,eRetN,eResults)
    LF("    for _i=1,%s do %s[_i]=%s[_i] end", eRetN,eRetVals,eResults)
    LF("  end")
    -- [38] RETURN
    LF("  %s[38]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    %s=true", eDone)
    LF("    if %s==1 then %s=0;return end", eB,eRetN)
    LF("    local %s=%s==0 and %s or %s+%s-2", eNelem,eB,eTop,eA,eB)
    LF("    %s=0", eRetN)
    LF("    for _i=%s,%s do %s=%s+1;%s[%s]=%s[_i].v end", eA,eNelem,eRetN,eRetN,eRetVals,eRetN,eRegs)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [39] FORLOOP
    LF("  %s[39]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    %s[%s].v=%s[%s].v+%s[%s+2].v", eRegs,eA,eRegs,eA,eRegs,eA)
    LF("    local %s=%s[%s].v;local %s=%s[%s+1].v;local %s=%s[%s+2].v",
       eIdx,eRegs,eA, eLim,eRegs,eA, eStep,eRegs,eA)
    LF("    if(%s>0 and %s<=%s)or(%s<0 and %s>=%s) then %s=%s+%s;%s[%s+3].v=%s end",
       eStep,eIdx,eLim,eStep,eIdx,eLim, ePc,ePc,eSBx, eRegs,eA,eIdx)
    LF("  end")
    -- [40] FORPREP
    LF("  %s[40]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v-%s[%s+2].v;%s=%s+%s end",
       vDispatch, eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eA,eRegs,eA, ePc,ePc,eSBx)
    -- [41] TFORCALL
    LF("  %s[41]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local %s=table.pack(%s[%s].v(%s[%s+1].v,%s[%s+2].v))",
       eResults,eRegs,eA,eRegs,eA,eRegs,eA)
    LF("    for _i=1,%s do if not %s[%s+2+_i] then %s[%s+2+_i]={} end;%s[%s+2+_i].v=%s[_i] end",
       eC,eRegs,eA,eRegs,eA,eRegs,eA,eResults)
    LF("  end")
    -- [42] TFORLOOP
    LF("  %s[42]=function(%s,%s,%s,%s,%s)",vDispatch,eA,eB,eC,eBx,eSBx)
    LF("    if %s[%s+1].v~=nil then %s[%s].v=%s[%s+1].v;%s=%s+%s end",
       eRegs,eA, eRegs,eA,eRegs,eA, ePc,ePc,eSBx)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [43] SETLIST
    LF("  %s[43]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local _off")
    LF("    if %s==0 then local _ni=%s[%s];%s=%s+1;_off=(_ni>>6)*50 else _off=(%s-1)*50 end",
       eC,eCode,ePc,ePc,ePc,eC)
    LF("    local %s=%s==0 and %s-%s or %s", eNelem,eB,eTop,eA,eB)
    LF("    for _i=1,%s do %s[%s].v[_off+_i]=%s[%s+_i].v end", eNelem,eRegs,eA,eRegs,eA)
    LF("  end")
    -- [44] CLOSURE: captures suvs+proto-index via local aliases (safe even
    --              when eI is reused as a loop counter elsewhere)
    LF("  %s[44]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    local %s=%s[%s]", eSub,eProtos,eBx)
    LF("    local %s={}", eSuvs)
    LF("    for _i=0,%s.sizeupvalues-1 do", eSub)
    LF("      local %s=%s.upvals[_i]", eUv,eSub)
    LF("      if %s.instack==1 then %s[_i]=%s[%s.idx]", eUv,eSuvs,eRegs,eUv)
    LF("      else local _u=%s[%s.idx];%s[_i]=_u or {} end", eUpvals,eUv,eSuvs)
    LF("    end")
    LF("    local _csuvs,_cbx=%s,%s", eSuvs,eBx)
    LF("    %s[%s].v=function(...) return %s(%s[_cbx],_csuvs,...) end", eRegs,eA,vExec,eProtos)
    LF("  end")
    -- [45] VARARG
    LF("  %s[45]=function(%s,%s,%s,%s,%s)", vDispatch, eA,eB,eC,eBx,eSBx)
    LF("    if %s==0 then", eB)
    LF("      for _i=0,#%s-1 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       eVararg,eRegs,eA,eRegs,eA,eRegs,eA,eVararg)
    LF("      %s=%s+#%s-1", eTop,eA,eVararg)
    LF("    else")
    LF("      for _i=0,%s-2 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       eB,eRegs,eA,eRegs,eA,eRegs,eA,eVararg)
    LF("    end")
    LF("  end")
    -- [46] EXTRAARG  (consumed by LOADKX/SETLIST; treated as no-op if reached alone)
    LF("  %s[46]=function(%s,%s,%s,%s,%s) end", vDispatch, eA,eB,eC,eBx,eSBx)

    src[#src+1] = junk_block("  ", math.random(1, 2))

    -- ── Main fetch-decode-dispatch loop ──────────────────────────────────────
    LF("  while not %s do", eDone)
    LF("    local %s=%s[%s]", eInst,eCode,ePc)
    LF("    %s=%s+1", ePc,ePc)
    LF("    local %s=%s[%s&0x3F]", eOp,vRevmap,eInst)
    LF("    local %s=(%s>>6)&0xFF",   eA,  eInst)
    LF("    local %s=(%s>>23)&0x1FF", eB,  eInst)
    LF("    local %s=(%s>>14)&0x1FF", eC,  eInst)
    LF("    local %s=(%s>>14)&0x3FFFF",eBx,eInst)
    LF("    local %s=%s-131071",       eSBx,eBx)
    LF("    %s[%s](%s,%s,%s,%s,%s)", vDispatch,eOp,eA,eB,eC,eBx,eSBx)
    LF("  end")
    LF("  return table.unpack(%s,1,%s)", eRetVals,eRetN)
    LF("end")  -- end execute function
    -- Junk block after execute function definition
    src[#src+1] = junk_block("", math.random(2, 4))

    -- ── Main: anti-tamper, decrypt, deserialize, run ──────────
    -- The payload table (superflow_bytecode) was already emitted at the top of the file.

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
    -- Emit expected CRC as an obfuscated XOR-split expression.
    local crc_a = math.random(0, 0x3FFFFFFF)
    local crc_b = crc_a ~ blob_crc
    local crc_p = math.random(1, 0xFFFF)
    local crc_q = math.random(1, 0xFFFF)
    LF("local %s=((%d~%d)+%d+%d-%d-%d)", atCrc, crc_a, crc_b, crc_p, crc_q, crc_p, crc_q)
    LF("local %s=table.concat(%s)", vBlob, PAYLOAD_TABLE_NAME)
    LF("%s=nil", PAYLOAD_TABLE_NAME)   -- wipe payload table after concat
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

    -- Anti-tamper 4: Lua version must be 5.3 or 5.4
    LF("do local %s=_VERSION;if not %s or (not %s:find('5%%.3') and not %s:find('5%%.4')) then error('Catify: unsupported Lua version',0) end end",
       atVer, atVer, atVer, atVer)

    -- Anti-tamper 5: core standard functions must be genuine callable values
    LF("do local %s={rawequal,rawget,rawset,rawlen,select,ipairs,pairs,next,unpack or table.unpack};for _,_f in ipairs(%s) do if type(_f)~='function' then error('Catify: environment tampered (core)',0) end end end",
       atRaw, atRaw)

    -- Anti-tamper 6: type() sanity (standard type names must not be overridden)
    LF("do if type(nil)~='nil' or type(0)~='number' or type('')~='string' or type({})~='table' or type(type)~='function' then error('Catify: environment tampered (type)',0) end end")

    -- Anti-tamper 7: string standard library sanity
    LF("do if string.byte('A')~=65 or string.char(65)~='A' or string.len('ab')~=2 then error('Catify: environment tampered (strlib)',0) end end")

    -- Anti-tamper 8: math library sanity
    LF("do if not math.maxinteger or math.maxinteger<=0 or math.mininteger>=0 then error('Catify: environment tampered (math)',0) end end")

    -- Anti-tamper 9: table library sanity (insert/remove must be callable)
    LF("do if type(table.insert)~='function' or type(table.remove)~='function' or type(table.concat)~='function' then error('Catify: environment tampered (tablelib)',0) end end")

    -- Anti-tamper 10: coroutine library basic check
    LF("do if type(coroutine)~='table' or type(coroutine.wrap)~='function' then error('Catify: environment tampered (coroutine)',0) end end")

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
