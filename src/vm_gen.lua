--[[
    Catify - Commercial Lua Obfuscator
    src/vm_gen.lua  - VM code generator

    Responsibilities:
      1. Re-serialize the (already opcode-shuffled) Proto tree into a compact
         custom binary format.
      2. Encrypt that blob with AES-256-CTR (32-byte key + 8-byte nonce supplied by the caller).
      3. Emit a self-contained Lua 5.3 source file that:
           • Decodes Base91 payload, checks SHA-256 integrity, decrypts with AES-256-CTR.
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
                local ok, packed = pcall(string.pack, "<i8", c)
                if ok then
                    w(ser_u8(3))
                    w(packed)
                else
                    -- Fallback: store as float.  Integers whose magnitude exceeds
                    -- 2^53 cannot be exactly represented as doubles; in practice
                    -- Lua integer constants in real scripts are well within that range.
                    w(ser_u8(4))
                    w(ser_f64(c * 1.0))
                end
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

-- The payload is Base91-encoded and emitted as a single quoted string literal.
-- Base91 uses only safe printable ASCII characters, making the output resilient
-- to any third-party tool that processes or re-encodes the generated Lua file.
local PAYLOAD_VAR_NAME = "superflow_bytecode"
local function emit_payload_b91(b91str)
    -- Declare as local inside the wrapper function so it doesn't pollute global scope.
    return "local " .. PAYLOAD_VAR_NAME .. "=" .. string.format("%q", b91str) .. ";"
end

-- Emit an integer as a Lua numeric literal (optionally obfuscated).
local function int_lit(n)
    return tostring(math.tointeger(n) or n)
end

-- ─── VM Lua template (generated with random names at call time) ────────────────

--- Generate the complete obfuscated Lua source for the given proto.
---@param proto   table   Top-level proto (opcodes already shuffled in .code arrays)
---@param revmap  table   revmap[shuffled_op] = real_op  (0-indexed)
---@param key     string  AES-256 key (32 bytes) used to encrypt the bytecode blob
---@param nonce   string  AES-256-CTR nonce (8 bytes)
---@param utils   table   The Utils module (for aes256_ctr, sha256, base91_enc, rand_names)
---@return string  Lua source
function VmGen.generate(proto, revmap, key, nonce, utils)
    -- ── 1. Serialize + encrypt the custom bytecode ───────────────────────────
    local sxor_byte = math.random(1, 255)     -- per-session string XOR key
    local raw  = serialize_proto(proto, sxor_byte)
    local blob = utils.aes256_ctr(raw, key, nonce)
    local b91_blob = utils.base91_enc(blob)   -- Base91-encode for safe single-string payload

    -- ── 2. Generate random identifiers for all locals ───────────────────────
    -- We need ~80 unique names for VM internals
    local N  = utils.rand_names(200)
    local ni = 0
    local function vn()   -- "variable name"
        ni = ni + 1
        return N[ni]
    end

    -- Core names
    local vExec     = vn()   -- main execute function
    local vDeser    = vn()   -- deserializer function
    local vDecrypt  = vn()   -- RC4 decrypt function
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

    -- AES-256-CTR inline variables
    local aesSbox   = vn()   -- S-box table name
    local aesXt     = vn()   -- xtime helper function name
    local aesKe     = vn()   -- key expand function name
    local aesEb     = vn()   -- block encrypt function name
    local vNonce    = vn()   -- nonce variable name
    -- SHA-256 inline variables
    local shaFn     = vn()   -- sha256 function name
    local shaK      = vn()   -- K constants table name (unused var, kept for naming pool)
    local shaH      = vn()   -- hash state name
    local shaW      = vn()   -- message schedule name
    -- Base91 inline decoder variables
    local b91Alpha  = vn()   -- alphabet string variable
    local b91Dec    = vn()   -- decoder function name
    local b91Tbl    = vn()   -- lookup table name
    local b91V      = vn()   -- v variable
    local b91B      = vn()   -- b variable
    local b91N_     = vn()   -- n variable (trailing _ to avoid clash with Lua keyword)
    local b91Out    = vn()   -- output table
    local b91P      = vn()   -- p (decoded value) variable
    local b91I      = vn()   -- input parameter name

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
    -- anti-tamper names (atPayload is now the fixed string "superflow_bytecode")
    local atCrc     = vn()   -- expected CRC variable
    local atCalc    = vn()   -- computed CRC variable
    local atDbg     = vn()   -- debug reference (kept for SHA block)
    local vStrXor   = vn()   -- string-constant XOR key (second encryption layer)
    local atVer     = vn()   -- Lua version check scratch
    local atRaw     = vn()   -- raw* functions check scratch
    -- Anti-keylogger variable names
    local atKl1     = vn()
    local atKl2     = vn()
    local atKl3     = vn()
    local atKl4     = vn()
    -- Anti-environmental logger variable names
    local atEnv1    = vn()
    local atEnv2    = vn()
    local atEnv3    = vn()
    -- Anti-tamper block executor (XOR decoder + load())
    local vAtExec   = vn()
    -- SHA-256 integrity check variable names
    local atSha     = vn()
    local atShaExp  = vn()
    -- Watermark variable name
    local vWm       = vn()
    -- Bootstrap helper aliases
    local bsToStr   = vn()
    local bsType    = vn()
    local bsPcall   = vn()
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
    -- Key/nonce split chunk names (multi-layer key protection)
    local vKp1 = vn()   -- key bytes 1-8,  pre-XOR'd with chunk mask 1
    local vKp2 = vn()   -- key bytes 9-16, pre-XOR'd with chunk mask 2
    local vKp3 = vn()   -- key bytes 17-24,pre-XOR'd with chunk mask 3
    local vKp4 = vn()   -- key bytes 25-32,pre-XOR'd with chunk mask 4
    local vNp1 = vn()   -- nonce bytes 1-4, pre-XOR'd with nonce mask 1
    local vNp2 = vn()   -- nonce bytes 5-8, pre-XOR'd with nonce mask 2
    local vDk1 = vn()   -- decoy key fragment 1 (never used for real decryption)
    local vDk2 = vn()   -- decoy key fragment 2 (never used for real decryption)
    -- Bitwise compat helpers: use bit32 (Roblox Luau) or native ops loaded via load()
    -- (native ops in load() strings bypass Luau's parser so older Luau versions work too)
    local bXor = vn()   -- bitwise XOR  (a ~ b)
    local bNot = vn()   -- bitwise NOT  (~a)
    local bAnd = vn()   -- bitwise AND  (a & b)
    local bOr  = vn()   -- bitwise OR   (a | b)
    local bShl = vn()   -- left shift   (a << b)
    local bShr = vn()   -- right shift  (a >> b)
    local b32Bx = vn()  -- obfuscated key: "bxor"
    local b32Bn = vn()  -- obfuscated key: "bnot"
    local b32Ba = vn()  -- obfuscated key: "band"
    local b32Bo = vn()  -- obfuscated key: "bor"
    local b32Ls = vn()  -- obfuscated key: "lshift"
    local b32Rs = vn()  -- obfuscated key: "rshift"
    local vLoadCompat = vn() -- load/loadstring runtime loader
    local vPack = vn()       -- table.pack compat
    local vUnpack = vn()     -- table.unpack compat
    -- Binary codec helpers for runtimes without string.pack/unpack (e.g. Luau)
    local rdU4le = vn()
    local rdI4le = vn()
    local rdF64le = vn()
    local wrU4be = vn()

    -- Helper: emit an obfuscated integer expression using the runtime bXor function
    -- so no ~ operator appears in the generated output (Luau/Lua 5.1 compatible).
    local function _obfInt(n)
        local mode = math.random(0, 5)
        if mode == 0 then
            return utils.obfuscate_int_deep(n, bXor)
        elseif mode == 1 then
            return utils.obfuscate_int_triple(n, bXor)
        elseif mode == 2 then
            return utils.obfuscate_int_deep(n)
        elseif mode == 3 then
            return utils.obfuscate_int_triple(n)
        elseif mode == 4 then
            return utils.obfuscate_int(n)
        elseif mode == 5 then
            return utils.obfuscate_int_deep(n, bXor)
        end
    end
    local function _obfByte(n)
        return string.format("%s(%s,255)", bAnd, _obfInt(n))
    end
    local function _obfLitStr(s)
        local parts = {}
        for i = 1, #s do parts[i] = _obfByte(s:byte(i)) end
        return string.format("string.char(%s)", table.concat(parts, ","))
    end
    -- Like _obfLitStr but emits only plain arithmetic (no bAnd/bXor references).
    -- Safe to use BEFORE the bitwise compat block has been emitted in the output.
    -- Each byte is split into high/low nibbles; the generated code reconstructs
    -- the byte as (h*16+l) — no library function needed.
    local function _earlyLitStr(s)
        local parts = {}
        for i = 1, #s do
            local b = s:byte(i)
            local h = math.floor(b / 16)   -- high nibble, portable across Lua versions
            local lo = b % 16               -- low  nibble
            parts[i] = string.format("(%d*16+%d)", h, lo)
        end
        return string.format("string.char(%s)", table.concat(parts, ","))
    end

    -- ── 3. Compute SHA-256 of the encrypted blob for anti-tamper ─────────────
    local blob_sha = utils.sha256(blob)

    -- ── 4. Build the fwdmap (real opcode → shuffled opcode) ─────────────────
    -- The dispatch table will be indexed by shuffled opcodes so that the
    -- real opcode numbers are not visible in the generated output.
    local fwdmap = {}
    for shuffled = 0, 46 do
        fwdmap[revmap[shuffled] or shuffled] = shuffled
    end

    -- ── 4. Junk-code snippets (opaque predicates, dead branches) ─────────────
    -- Each form picks its own fresh single-letter or short names so that
    -- consecutive junk blocks never share the same variable identifiers.
    -- Fifteen human-style single/two-letter names to draw from; forms pick
    -- 2-3 distinct ones so the pattern varies visually.
    local _JN = {"x","y","n","v","t","a","b","s","c","r","m","p","q","k","e"}
    local function jpick()
        return _JN[math.random(1, #_JN)]
    end
    local function jpick2()
        local i = math.random(1, #_JN)
        local j = math.random(1, #_JN - 1)
        if j >= i then j = j + 1 end
        return _JN[i], _JN[j]
    end
    local function jpick3()
        local i = math.random(1, #_JN)
        local j, k2
        repeat j = math.random(1, #_JN) until j ~= i
        repeat k2 = math.random(1, #_JN) until k2 ~= i and k2 ~= j
        return _JN[i], _JN[j], _JN[k2]
    end

    -- Ten forms of always-dead opaque predicates / no-op computations:
    --  form 1: x XOR x == 0, never > 0
    --  form 2: n // n == 1, never < 1
    --  form 3: (a+b)*c - (a+b)*c == 0, never > 1
    --  form 4: #"literal" == known length, dead if branch
    --  form 5: table constructor immediately discarded, length always 0
    --  form 6: multi-step XOR chain that cancels to 0
    --  form 7: math.max(a, b) identity (a >= b, so result == a, dead sub-branch)
    --  form 8: string.rep + #  identity
    --  form 9: fake config table with dead branch (looks like real init code)
    --  form 10: fake string sanitize (dead upper/lower branch)
    local junk_forms = {
        -- form 1: x XOR x == 0
        function(indent)
            local v1, v2 = jpick2()
            local a = math.random(1, 0x7FFF)
            local b = math.random(1, 0xFF)
            return string.format(
                "%sdo local %s=%d*%d;local %s=%s(%s,%s);if %s>0 then %s=%s+%d end end\n",
                indent, v1, a, b, v2, bXor, v1, v1, v2, v1, v1, math.random(1, 0xFF))
        end,
        -- form 2: integer division identity
        function(indent)
            local v1, v2 = jpick2()
            local a = math.random(2, 0x3FFF)
            local c = math.random(1, 9)
            return string.format(
                "%sdo local %s=%d+%d;local %s=%s//%s;if %s<%d then %s=%s*%d end end\n",
                indent, v1, a, c, v2, v1, v1, v2, 1, v1, v1, math.random(2, 9))
        end,
        -- form 3: product minus itself
        function(indent)
            local v1, v2 = jpick2()
            local a = math.random(1, 0x1FFF)
            local b = math.random(1, 0x1FFF)
            local c = math.random(1, 7)
            local prod = (a + b) * c
            return string.format(
                "%sdo local %s=(%d+%d)*%d;local %s=%s-%d;if %s>1 then %s=%s^2 end end\n",
                indent, v1, a, b, c, v2, v1, prod, v2, v1, v1)
        end,
        -- form 4: string length identity (dead branch on impossible length)
        function(indent)
            local v1 = jpick()
            local words = {"cache","token","handle","driver","plugin","loader"}
            local w = words[math.random(1, #words)]
            local wrong_len = #w + math.random(1, 5)
            return string.format(
                "%sdo local %s=#%q;if %s==%d then %s=%s*0 end end\n",
                indent, v1, w, v1, wrong_len, v1, v1)
        end,
        -- form 5: empty table, length check always 0
        function(indent)
            local v1, v2 = jpick2()
            local n = math.random(1, 9)
            return string.format(
                "%sdo local %s={};for %s=1,%d do end;if #%s>0 then %s[1]=nil end end\n",
                indent, v1, v2, n, v1, v1)
        end,
        -- form 6: multi-step XOR chain cancelling to 0
        function(indent)
            local v1, v2, v3 = jpick3()
            local x = math.random(1, 0xFFFF)
            local y = math.random(1, 0xFFFF)
            local z = x ~ y
            return string.format(
                "%sdo local %s=%d;local %s=%d;local %s=%s(%s,%s);if %s(%s,%s)>0 then %s=%s(%s,1) end end\n",
                indent, v1, x, v2, y, v3, bXor, v1, v2, bXor, v3, v1, v2, bOr, v2)
        end,
        -- form 7: math.max identity (always picks first arg)
        function(indent)
            local v1 = jpick()
            local big = math.random(0x1000, 0x7FFF)
            local small = math.random(1, big - 1)
            return string.format(
                "%sdo local %s=math.max(%d,%d);if %s<%d then %s=%s+1 end end\n",
                indent, v1, big, small, v1, big, v1, v1)
        end,
        -- form 8: string.rep + #  identity
        function(indent)
            local v1 = jpick()
            local ch = string.char(math.random(97, 122))   -- a-z
            local n  = math.random(3, 8)
            return string.format(
                "%sdo local %s=string.rep(%q,%d);if #%s~=%d then %s=nil end end\n",
                indent, v1, ch, n, v1, n, v1)
        end,
        -- form 9: fake config table with dead branch (looks like real init code)
        function(indent)
            local v1 = jpick()
            local cfg_keys = {"timeout","retries","verbose","mode","level","limit"}
            local k = cfg_keys[math.random(1, #cfg_keys)]
            local v = math.random(0, 1) == 1 and "true" or tostring(math.random(1,9))
            return string.format(
                "%sdo local %s={%s=%s};if %s.%s==nil then %s.%s=%s end end\n",
                indent, v1, k, v, v1, k, v1, k, v)
        end,
        -- form 10: fake string sanitize (dead upper/lower branch)
        function(indent)
            local v1, v2 = jpick2()
            local words = {"data","value","result","output","buffer","token"}
            local w = words[math.random(1, #words)]
            return string.format(
                "%sdo local %s=%q;local %s=string.upper(%s);if #%s<0 then %s=%s end end\n",
                indent, v1, w, v2, v1, v2, v1, v2)
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

    -- ── Header comment (minimal, for compact output) ─────────────────────────
    -- (intentionally omitted for compact output)

    -- ── Wrap all VM internals in a self-contained immediately-invoked function ──
    -- This keeps all locals scoped and propagates return values like AstrarServices style.
    L("return(function(...)")
    -- ── Base91-encoded payload declared as local inside the wrapper function ──────────
    src[#src+1] = emit_payload_b91(b91_blob) .. "\n"
    LF("local %s=tostring;local %s=type;local %s=pcall", bsToStr, bsType, bsPcall)
    LF("local %s=(type(load)=='function' and load) or (type(loadstring)=='function' and loadstring) or nil", vLoadCompat)
    LF("local %s=(table and table.pack) or function(...) return {n=select('#', ...),...} end", vPack)
    LF("local %s=(table and table.unpack) or unpack", vUnpack)
    LF("if type(%s)~='function' then local function _up(t,i,j) i=i or 1;j=j or #t;if i>j then return end;return t[i],_up(t,i+1,j) end;%s=_up end", vUnpack, vUnpack)
    -- Bitwise compat: use bit32 library if available (Roblox Luau), otherwise
    -- compile native Lua 5.3 operators via loader so the Luau parser never sees ~, &, |, <<, >>
    LF("local %s,%s,%s,%s,%s,%s", bXor,bNot,bAnd,bOr,bShl,bShr)
    LF("local %s,%s,%s,%s,%s,%s=%s,%s,%s,%s,%s,%s", b32Bx,b32Bn,b32Ba,b32Bo,b32Ls,b32Rs,
       _earlyLitStr("bxor"),_earlyLitStr("bnot"),_earlyLitStr("band"),_earlyLitStr("bor"),_earlyLitStr("lshift"),_earlyLitStr("rshift"))
    LF("local bit32Available=type(bit32)=='table' and type(bit32[%s])=='function' and type(bit32[%s])=='function' and type(bit32[%s])=='function' and type(bit32[%s])=='function'", b32Bx,b32Bn,b32Ba,b32Bo)
    LF("if bit32Available then")
    LF("  %s=bit32[%s];%s=bit32[%s];%s=bit32[%s];%s=bit32[%s]", bXor,b32Bx,bNot,b32Bn,bAnd,b32Ba,bOr,b32Bo)
    -- bit32.lshift and bit32.rshift may be absent in some Roblox Luau builds.
    -- Fall back to a math-based equivalent using bit32.band (always present).
    LF("  %s=bit32[%s] or function(a,b) if b>=32 then return 0 end;return bit32[%s](a*(2^b),0xFFFFFFFF) end", bShl,b32Ls,b32Ba)
    LF("  %s=bit32[%s] or function(a,b) if b>=32 then return 0 end;return math.floor(bit32[%s](a,0xFFFFFFFF)/(2^b)) end", bShr,b32Rs,b32Ba)
    LF("else")
    LF("  if type(%s)~='function' then error('Catify: missing bitwise support',0) end", vLoadCompat)
    LF("  local _f=%s('return function(a,b)return a~b end');if type(_f)~='function' then error('Catify: missing bitwise support',0) end;%s=_f()", vLoadCompat, bXor)
    LF("  _f=%s('return function(a)return ~a end');if type(_f)~='function' then error('Catify: missing bitwise support',0) end;%s=_f()", vLoadCompat, bNot)
    LF("  _f=%s('return function(a,b)return a&b end');if type(_f)~='function' then error('Catify: missing bitwise support',0) end;%s=_f()", vLoadCompat, bAnd)
    LF("  _f=%s('return function(a,b)return a|b end');if type(_f)~='function' then error('Catify: missing bitwise support',0) end;%s=_f()", vLoadCompat, bOr)
    LF("  _f=%s('return function(a,b)return a<<b end');if type(_f)~='function' then error('Catify: missing bitwise support',0) end;%s=_f()", vLoadCompat, bShl)
    LF("  _f=%s('return function(a,b)return a>>b end');if type(_f)~='function' then error('Catify: missing bitwise support',0) end;%s=_f()", vLoadCompat, bShr)
    LF("end")
    -- Binary helpers: avoid hard dependency on string.pack/unpack at runtime.
    LF("local function %s(_s,_p) local _b1,_b2,_b3,_b4=_s:byte(_p,_p+3);return _b1+_b2*256+_b3*65536+_b4*16777216,_p+4 end", rdU4le)
    LF("local function %s(_s,_p) local _v,_np=%s(_s,_p);if _v>=2147483648 then _v=_v-4294967296 end;return _v,_np end", rdI4le, rdU4le)
    LF("local function %s(_s,_p)", rdF64le)
    LF("  if type(string.unpack)=='function' then return string.unpack('<d',_s,_p) end")
    LF("  local _DBL_BIAS=1023")
    LF("  local _DBL_MANT=4503599627370496")
    LF("  local _DBL_EXP_MAX=2047")
    LF("  local _b1,_b2,_b3,_b4,_b5,_b6,_b7,_b8=_s:byte(_p,_p+7)")
    LF("  local _sgn=(_b8>=128) and -1 or 1")
    LF("  local _exp=((_b8%%128)*16)+math.floor(_b7/16)")
    LF("  local _mant=(_b7%%16)*281474976710656+_b6*1099511627776+_b5*4294967296+_b4*16777216+_b3*65536+_b2*256+_b1")
    LF("  if _exp==0 then if _mant==0 then return _sgn*0,_p+8 end;return _sgn*(2^(1-_DBL_BIAS))*(_mant/_DBL_MANT),_p+8 end")
    LF("  if _exp==_DBL_EXP_MAX then if _mant==0 then return _sgn*(1/0),_p+8 end;return 0/0,_p+8 end")
    LF("  return _sgn*(2^(_exp-_DBL_BIAS))*(1+_mant/_DBL_MANT),_p+8")
    LF("end")
    LF("local function %s(_v) return string.char(%s(%s(_v,24),255),%s(%s(_v,16),255),%s(%s(_v,8),255),%s(_v,255)) end", wrU4be, bAnd, bShr, bAnd, bShr, bAnd, bShr, bAnd)
    -- Junk block at top of do-scope (dead computations, not reachable by any real code path)
    src[#src+1] = junk_block("", math.random(2, 4))
    -- ── Emit payload concatenation helper (decoy wrapper using allocated names) ──
    -- ── Real inline Base91 decoder (decodes the payload back to the AES blob) ──
    LF("local %s=%s", b91Alpha, _obfLitStr("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_`{|}~\""))
    LF("local %s={}", b91Tbl)
    LF("for _i=1,#%s do %s[%s:byte(_i)]=_i-1 end", b91Alpha, b91Tbl, b91Alpha)
    LF("local function %s(%s)", b91Dec, b91I)
    LF("  local %s,%s,%s=-1,0,0 local %s={}", b91V, b91B, b91N_, b91Out)
    LF("  for _i=1,#%s do local %s=%s[%s:byte(_i)]", b91I, b91P, b91Tbl, b91I)
    LF("    if %s~=nil then if %s<0 then %s=%s", b91P, b91V, b91V, b91P)
    LF("    else %s=%s+%s*91 %s=%s(%s,%s(%s,%s))", b91V, b91V, b91P, b91B, bOr, b91B, bShl, b91V, b91N_)
    LF("      if %s(%s,8191)>88 then %s=%s+13 else %s=%s+14 end", bAnd, b91V, b91N_, b91N_, b91N_, b91N_)
    LF("      repeat %s[#%s+1]=string.char(%s(%s,255)) %s=%s(%s,8) %s=%s-8 until %s<=7", b91Out, b91Out, bAnd, b91B, b91B, bShr, b91B, b91N_, b91N_, b91N_)
    LF("      %s=-1 end end end", b91V)
    LF("  if %s>-1 then %s[#%s+1]=string.char(%s(%s(%s,%s(%s,%s)),255)) end", b91V, b91Out, b91Out, bAnd, bOr, b91B, bShl, b91V, b91N_)
    LF("  return table.concat(%s) end", b91Out)
    src[#src+1] = junk_block("", math.random(1, 2))
    -- ── Emit inline AES-256-CTR decrypt ─────────────────────────────────────
    -- S-box table literal
    local sbox_vals = {0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16}
    -- XOR all S-box entries with a random session mask so the table is not
    -- recognisable as the standard AES S-box.  An inline loop unmasks at runtime.
    local sbox_mask = math.random(1, 255)
    local sbox_strs = {}
    for i = 1, #sbox_vals do sbox_strs[i] = tostring(sbox_vals[i] ~ sbox_mask) end
    LF("local %s={[0]=%s}", aesSbox, table.concat(sbox_strs, ","))
    LF("do local _m=%s;for _i=0,255 do %s[_i]=%s(%s[_i],_m) end end",
       _obfInt(sbox_mask), aesSbox, bXor, aesSbox)
    LF("local function %s(_a) return %s(%s(%s(_a,1),(_a>=0x80 and 0x1b or 0)),0xFF) end", aesXt, bAnd, bXor, bShl)
    LF("local function %s(_k)", aesKe)
    LF("  local _w={}")
    LF("  for _i=0,7 do _w[_i]=%s(%s(%s(%s(_k:byte(_i*4+1),24),%s(_k:byte(_i*4+2),16)),%s(_k:byte(_i*4+3),8)),_k:byte(_i*4+4)) end", bOr,bOr,bOr,bShl,bShl,bShl)
    -- Mask AES round constants (Rcon) so they don't fingerprint AES key schedule.
    do
        local rc_raw  = {0x01000000,0x02000000,0x04000000,0x08000000,0x10000000,0x20000000,0x40000000}
        local rc_mask = math.random(1, 0x3FFFFFFF)
        local rc_strs = {}
        for i = 1, 7 do rc_strs[i] = string.format("[%d]=%d", i, (rc_raw[i] ~ rc_mask) & 0xFFFFFFFF) end
        LF("  local _rc={%s}", table.concat(rc_strs, ","))
        LF("  do local _rm=%s;for _i=1,7 do _rc[_i]=%s(%s(_rc[_i],_rm),0xFFFFFFFF) end end",
           _obfInt(rc_mask), bAnd, bXor)
    end
    LF("  for _i=8,59 do")
    LF("    local _t=_w[_i-1]")
    LF("    if _i%%8==0 then")
    LF("      _t=%s(%s(%s(_t,8),%s(_t,24)),0xFFFFFFFF)", bAnd,bOr,bShl,bShr)
    LF("      _t=%s(%s(%s(%s(%s[%s(%s(_t,24),0xFF)],24),%s(%s[%s(%s(_t,16),0xFF)],16)),%s(%s[%s(%s(_t,8),0xFF)],8)),%s[%s(_t,0xFF)])", bOr,bOr,bOr,bShl,aesSbox,bAnd,bShr,bShl,aesSbox,bAnd,bShr,bShl,aesSbox,bAnd,bShr,aesSbox,bAnd)
    LF("      _t=%s(%s(_t,_rc[_i//8]),0xFFFFFFFF)", bAnd,bXor)
    LF("    elseif _i%%8==4 then")
    LF("      _t=%s(%s(%s(%s(%s[%s(%s(_t,24),0xFF)],24),%s(%s[%s(%s(_t,16),0xFF)],16)),%s(%s[%s(%s(_t,8),0xFF)],8)),%s[%s(_t,0xFF)])", bOr,bOr,bOr,bShl,aesSbox,bAnd,bShr,bShl,aesSbox,bAnd,bShr,bShl,aesSbox,bAnd,bShr,aesSbox,bAnd)
    LF("    end")
    LF("    _w[_i]=%s(%s(_w[_i-8],_t),0xFFFFFFFF)", bAnd,bXor)
    LF("  end")
    LF("  return _w")
    LF("end")
    LF("local function %s(_blk,_rk)", aesEb)
    LF("  local _s={}")
    LF("  for _i=0,15 do _s[_i]=_blk:byte(_i+1) end")
    LF("  for _c=0,3 do local _w=_rk[_c];_s[_c*4]=%s(_s[_c*4],%s(%s(_w,24),0xFF));_s[_c*4+1]=%s(_s[_c*4+1],%s(%s(_w,16),0xFF));_s[_c*4+2]=%s(_s[_c*4+2],%s(%s(_w,8),0xFF));_s[_c*4+3]=%s(_s[_c*4+3],%s(_w,0xFF)) end", bXor,bAnd,bShr,bXor,bAnd,bShr,bXor,bAnd,bShr,bXor,bAnd)
    LF("  for _r=1,13 do")
    LF("    for _i=0,15 do _s[_i]=%s[_s[_i]] end", aesSbox)
    LF("    local _t;_t=_s[1];_s[1]=_s[5];_s[5]=_s[9];_s[9]=_s[13];_s[13]=_t")
    LF("    _t=_s[2];local _t2=_s[6];_s[2]=_s[10];_s[6]=_s[14];_s[10]=_t;_s[14]=_t2")
    LF("    _t=_s[3];_s[3]=_s[15];_s[15]=_s[11];_s[11]=_s[7];_s[7]=_t")
    LF("    for _c=0,3 do")
    LF("      local _a0,_a1,_a2,_a3=_s[_c*4],_s[_c*4+1],_s[_c*4+2],_s[_c*4+3]")
    LF("      _s[_c*4]=%s(%s(%s(%s(%s(_a0),%s(_a1)),_a1),_a2),_a3)", bXor,bXor,bXor,bXor,aesXt,aesXt)
    LF("      _s[_c*4+1]=%s(%s(%s(%s(_a0,%s(_a1)),%s(_a2)),_a2),_a3)", bXor,bXor,bXor,bXor,aesXt,aesXt)
    LF("      _s[_c*4+2]=%s(%s(%s(%s(_a0,_a1),%s(_a2)),%s(_a3)),_a3)", bXor,bXor,bXor,bXor,aesXt,aesXt)
    LF("      _s[_c*4+3]=%s(%s(%s(%s(%s(_a0),_a0),_a1),_a2),%s(_a3))", bXor,bXor,bXor,bXor,aesXt,aesXt)
    LF("    end")
    LF("    for _c=0,3 do local _w=_rk[_r*4+_c];_s[_c*4]=%s(_s[_c*4],%s(%s(_w,24),0xFF));_s[_c*4+1]=%s(_s[_c*4+1],%s(%s(_w,16),0xFF));_s[_c*4+2]=%s(_s[_c*4+2],%s(%s(_w,8),0xFF));_s[_c*4+3]=%s(_s[_c*4+3],%s(_w,0xFF)) end", bXor,bAnd,bShr,bXor,bAnd,bShr,bXor,bAnd,bShr,bXor,bAnd)
    LF("  end")
    LF("  for _i=0,15 do _s[_i]=%s[_s[_i]] end", aesSbox)
    LF("  local _t;_t=_s[1];_s[1]=_s[5];_s[5]=_s[9];_s[9]=_s[13];_s[13]=_t")
    LF("  _t=_s[2];local _t2=_s[6];_s[2]=_s[10];_s[6]=_s[14];_s[10]=_t;_s[14]=_t2")
    LF("  _t=_s[3];_s[3]=_s[15];_s[15]=_s[11];_s[11]=_s[7];_s[7]=_t")
    LF("  for _c=0,3 do local _w=_rk[56+_c];_s[_c*4]=%s(_s[_c*4],%s(%s(_w,24),0xFF));_s[_c*4+1]=%s(_s[_c*4+1],%s(%s(_w,16),0xFF));_s[_c*4+2]=%s(_s[_c*4+2],%s(%s(_w,8),0xFF));_s[_c*4+3]=%s(_s[_c*4+3],%s(_w,0xFF)) end", bXor,bAnd,bShr,bXor,bAnd,bShr,bXor,bAnd,bShr,bXor,bAnd)
    LF("  local _o={};for _i=0,15 do _o[_i+1]=string.char(_s[_i]) end;return table.concat(_o)")
    LF("end")
    LF("local function %s(_d,_k,_nn)", vDecrypt)
    LF("  local _rk=%s(_k)", aesKe)
    LF("  local _out={};local _ctr=0;local _pos=1;local _dl=#_d")
    LF("  while _pos<=_dl do")
    LF("    local _cb=_nn..string.char(_ctr%%256,(_ctr//256)%%256,(_ctr//65536)%%256,(_ctr//16777216)%%256)..\"\\0\\0\\0\\0\"")
    LF("    local _ks=%s(_cb,_rk)", aesEb)
    LF("    local _bl=math.min(16,_dl-_pos+1)")
    LF("    for _i=1,_bl do _out[#_out+1]=string.char(%s(_d:byte(_pos+_i-1),_ks:byte(_i))) end", bXor)
    LF("    _pos=_pos+16;_ctr=_ctr+1")
    LF("  end")
    LF("  return table.concat(_out)")
    LF("end")
    -- Junk block between AES function and deserializer
    src[#src+1] = junk_block("", math.random(2, 3))
    -- Decoy function: looks like a secondary hash/encode but is never called.
    -- Its body is all dead computation (XOR mixing on random constants).
    do
        local da = math.random(1, 0x7FFF)
        local db = math.random(1, 0x7FFF)
        local dc = math.random(1, 0xFFFF)
        LF("local function %s(%s)", vDecoy, dkA)
        LF("  local %s=%d local %s=%d local %s=%s(%s,%d)", dkB, da, dkC, db, dkD, bXor, dkA, dc)
        LF("  for %s=1,#%s do %s=%s(%s,string.byte(%s,%s)) end", dkB, dkA, dkC, bXor, dkC, dkA, dkB)
        LF("  return %s(%s,%s)", bXor, dkC, dkD)
        LF("end")
    end

    -- Deserializer
    LF("local %s", dPos)
    LF("local %s", dData)
    LF("local function %s() local v=%s:byte(%s);%s=%s+1;return v end", dRb, dData, dPos, dPos, dPos)
    LF("local function %s() local v,p=%s(%s,%s);%s=p;return v end", dRi32, rdI4le, dData, dPos, dPos)
    -- dRi64: decode via two LE u32 words (works on Lua/Luau without string.unpack).
    LF("local function %s()", dRi64)
    LF("  local _lo,_p1=%s(%s,%s);%s=_p1", rdU4le, dData, dPos, dPos)
    LF("  local _hi,_p2=%s(%s,%s);%s=_p2", rdU4le, dData, dPos, dPos)
    LF("  if _hi==0 then return _lo end")
    LF("  local _v=_lo+_hi*(2^32)")
    LF("  if _hi>=(2^31) then _v=_v-(2^64) end")
    LF("  return _v")
    LF("end")
    LF("local function %s() local v,p=%s(%s,%s);%s=p;return v end",  dRf64, rdF64le, dData, dPos, dPos)
    -- dRstr: emit once (correctly advancing pos)
    LF("local function %s() local _n,_p=%s(%s,%s);%s=_p;local _s=%s:sub(%s,%s+_n-1);%s=%s+_n;return _s end",
       dRstr, rdI4le, dData, dPos, dPos, dData, dPos, dPos, dPos, dPos)

    -- Emit the string-constant XOR key as an obfuscated math expression so it
    -- is not visible as a plain integer literal in the output.
    do
        local sx_a = math.random(0, 255)
        local sx_b = sx_a ~ sxor_byte  -- XOR split: sx_a ~ sx_b == sxor_byte
        local sx_p = math.random(1, 0xFFFF)
        local sx_q = math.random(1, 0xFFFF)
        LF("local %s=(%s(%d,%d)+%d+%d-%d-%d)", vStrXor, bXor, sx_a, sx_b, sx_p, sx_q, sx_p, sx_q)
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
    LF("  for i=0,sc-1 do local _v,_p=%s(%s,%s);code[i]=_v;%s=_p end",
       rdU4le, dData, dPos, dPos)
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
    LF("    elseif t==5 then local _sx=%s();local _sd={};for _si=1,#_sx do _sd[_si]=string.char(%s(_sx:byte(_si),%s))end;k[i]=table.concat(_sd)", dRstr, bXor, vStrXor)
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

    -- (dispatch table indexed by shuffled opcode – no separate revmap needed)
    -- Junk block after VM setup
    src[#src+1] = junk_block("", math.random(1, 3))

    -- The execute function (dispatch-table based)
    LF("local function %s(%s,%s,...)", vExec, eProto, eUpvals)
    LF("  local %s=%s(...)", eArgs, vPack)
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
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v end",
       vDispatch, fwdmap[0], eA,eB,eC,eBx,eSBx, eRegs,eA, eRegs,eB)
    -- [1] LOADK
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s] end",
       vDispatch, fwdmap[1], eA,eB,eC,eBx,eSBx, eRegs,eA, eKst,eBx)
    -- [2] LOADKX  (next instruction is EXTRAARG carrying the index)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[2], eA,eB,eC,eBx,eSBx)
    LF("    local _ni=%s[%s];%s=%s+1;%s[%s].v=%s[%s(_ni,6)]", eCode,ePc,ePc,ePc, eRegs,eA,eKst,bShr)
    LF("  end")
    -- [3] LOADBOOL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=(%s~=0);if %s~=0 then %s=%s+1 end end",
       vDispatch, fwdmap[3], eA,eB,eC,eBx,eSBx, eRegs,eA,eB, eC,ePc,ePc)
    -- [4] LOADNIL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) for _i=%s,%s+%s do %s[_i].v=nil end end",
       vDispatch, fwdmap[4], eA,eB,eC,eBx,eSBx, eA,eA,eB, eRegs)
    src[#src+1] = junk_block("  ", 1)   -- junk between handler groups
    -- [5] GETUPVAL (defensive: nil upval box → nil)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) local _u=%s[%s];%s[%s].v=_u and _u.v or nil end",
       vDispatch, fwdmap[5], eA,eB,eC,eBx,eSBx, eUpvals,eB, eRegs,eA)
    -- [6] GETTABUP (defensive: missing upval box → nil; present box → normal indexing)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) local _u=%s[%s];%s[%s].v=_u and _u.v[%s(%s)] end",
       vDispatch, fwdmap[6], eA,eB,eC,eBx,eSBx, eUpvals,eB, eRegs,eA, eRk,eC)
    -- [7] GETTABLE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v[%s(%s)] end",
       vDispatch, fwdmap[7], eA,eB,eC,eBx,eSBx, eRegs,eA, eRegs,eB, eRk,eC)
    -- [8] SETTABUP (defensive: missing upval box → no-op; present box → normal indexing)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) local _u=%s[%s];if _u then _u.v[%s(%s)]=%s(%s) end end",
       vDispatch, fwdmap[8], eA,eB,eC,eBx,eSBx, eUpvals,eA, eRk,eB, eRk,eC)
    -- [9] SETUPVAL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v end",
       vDispatch, fwdmap[9], eA,eB,eC,eBx,eSBx, eUpvals,eB, eRegs,eA)
    -- [10] SETTABLE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v[%s(%s)]=%s(%s) end",
       vDispatch, fwdmap[10], eA,eB,eC,eBx,eSBx, eRegs,eA, eRk,eB, eRk,eC)
    src[#src+1] = junk_block("  ", 1)
    -- [11] NEWTABLE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v={} end",
       vDispatch, fwdmap[11], eA,eB,eC,eBx,eSBx, eRegs,eA)
    -- [12] SELF
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s+1].v=%s[%s].v;%s[%s].v=%s[%s].v[%s(%s)] end",
       vDispatch, fwdmap[12], eA,eB,eC,eBx,eSBx, eRegs,eA, eRegs,eB, eRegs,eA, eRegs,eB, eRk,eC)
    -- [13..19] Arithmetic: ADD SUB MUL MOD POW DIV IDIV
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)+%s(%s) end", vDispatch,fwdmap[13],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)-%s(%s) end", vDispatch,fwdmap[14],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)*%s(%s) end", vDispatch,fwdmap[15],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)%%%s(%s) end",vDispatch,fwdmap[16],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)^%s(%s) end", vDispatch,fwdmap[17],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)/%s(%s) end", vDispatch,fwdmap[18],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)//%s(%s) end",vDispatch,fwdmap[19],eA,eB,eC,eBx,eSBx, eRegs,eA,eRk,eB,eRk,eC)
    src[#src+1] = junk_block("  ", 1)
    -- [20..24] Bitwise: BAND BOR BXOR SHL SHR
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  vDispatch,fwdmap[20],eA,eB,eC,eBx,eSBx, eRegs,eA,bAnd,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  vDispatch,fwdmap[21],eA,eB,eC,eBx,eSBx, eRegs,eA,bOr, eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  vDispatch,fwdmap[22],eA,eB,eC,eBx,eSBx, eRegs,eA,bXor,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  vDispatch,fwdmap[23],eA,eB,eC,eBx,eSBx, eRegs,eA,bShl,eRk,eB,eRk,eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  vDispatch,fwdmap[24],eA,eB,eC,eBx,eSBx, eRegs,eA,bShr,eRk,eB,eRk,eC)
    -- [25..28] Unary: UNM BNOT NOT LEN
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=-%s[%s].v end",          vDispatch,fwdmap[25],eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s[%s].v) end",       vDispatch,fwdmap[26],eA,eB,eC,eBx,eSBx, eRegs,eA,bNot,eRegs,eB)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=not %s[%s].v end",  vDispatch,fwdmap[27],eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=#%s[%s].v end",     vDispatch,fwdmap[28],eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eB)
    src[#src+1] = junk_block("  ", 1)
    -- [29] CONCAT
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[29], eA,eB,eC,eBx,eSBx)
    LF("    local _t={}")
    LF("    for _i=%s,%s do _t[#_t+1]=tostring(%s[_i].v) end", eB,eC,eRegs)
    LF("    %s[%s].v=table.concat(_t)", eRegs,eA)
    LF("  end")
    -- [30] JMP  (modifies pc via upvalue – Lua closure upvalue sharing)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s=%s+%s end",
       vDispatch, fwdmap[30], eA,eB,eC,eBx,eSBx, ePc,ePc,eSBx)
    -- [31..33] Comparisons: EQ LT LE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(%s(%s)==%s(%s))~=(%s~=0) then %s=%s+1 end end",
       vDispatch, fwdmap[31], eA,eB,eC,eBx,eSBx, eRk,eB,eRk,eC,eA,ePc,ePc)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(%s(%s)<%s(%s))~=(%s~=0) then %s=%s+1 end end",
       vDispatch, fwdmap[32], eA,eB,eC,eBx,eSBx, eRk,eB,eRk,eC,eA,ePc,ePc)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(%s(%s)<=%s(%s))~=(%s~=0) then %s=%s+1 end end",
       vDispatch, fwdmap[33], eA,eB,eC,eBx,eSBx, eRk,eB,eRk,eC,eA,ePc,ePc)
    -- [34] TEST
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(not not %s[%s].v)~=(%s~=0) then %s=%s+1 end end",
       vDispatch, fwdmap[34], eA,eB,eC,eBx,eSBx, eRegs,eA,eC,ePc,ePc)
    -- [35] TESTSET
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[35], eA,eB,eC,eBx,eSBx)
    LF("    if(not not %s[%s].v)==(%s~=0) then %s[%s].v=%s[%s].v else %s=%s+1 end",
       eRegs,eB,eC, eRegs,eA,eRegs,eB, ePc,ePc)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [36] CALL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[36], eA,eB,eC,eBx,eSBx)
    LF("    local %s=%s[%s].v", eFn,eRegs,eA)
    LF("    local %s={}", eCallArgs)
    LF("    local %s=%s==0 and %s-%s or %s-1", eNargs,eB,eTop,eA,eB)
    LF("    for _i=1,%s do %s[_i]=%s[%s+_i].v end", eNargs,eCallArgs,eRegs,eA)
    LF("    local %s=%s(%s(%s(%s,1,%s)))", eResults,vPack,eFn,vUnpack,eCallArgs,eNargs)
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
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[37], eA,eB,eC,eBx,eSBx)
    LF("    local %s=%s[%s].v", eFn,eRegs,eA)
    LF("    local %s={}", eCallArgs)
    LF("    local %s=%s==0 and %s-%s or %s-1", eNargs,eB,eTop,eA,eB)
    LF("    for _i=1,%s do %s[_i]=%s[%s+_i].v end", eNargs,eCallArgs,eRegs,eA)
    LF("    local %s=%s(%s(%s(%s,1,%s)))", eResults,vPack,eFn,vUnpack,eCallArgs,eNargs)
    LF("    %s=true;%s=%s.n", eDone,eRetN,eResults)
    LF("    for _i=1,%s do %s[_i]=%s[_i] end", eRetN,eRetVals,eResults)
    LF("  end")
    -- [38] RETURN
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[38], eA,eB,eC,eBx,eSBx)
    LF("    %s=true", eDone)
    LF("    if %s==1 then %s=0;return end", eB,eRetN)
    LF("    local %s=%s==0 and %s or %s+%s-2", eNelem,eB,eTop,eA,eB)
    LF("    %s=0", eRetN)
    LF("    for _i=%s,%s do %s=%s+1;%s[%s]=%s[_i].v end", eA,eNelem,eRetN,eRetN,eRetVals,eRetN,eRegs)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [39] FORLOOP
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[39], eA,eB,eC,eBx,eSBx)
    LF("    %s[%s].v=%s[%s].v+%s[%s+2].v", eRegs,eA,eRegs,eA,eRegs,eA)
    LF("    local %s=%s[%s].v;local %s=%s[%s+1].v;local %s=%s[%s+2].v",
       eIdx,eRegs,eA, eLim,eRegs,eA, eStep,eRegs,eA)
    LF("    if(%s>0 and %s<=%s)or(%s<0 and %s>=%s) then %s=%s+%s;%s[%s+3].v=%s end",
       eStep,eIdx,eLim,eStep,eIdx,eLim, ePc,ePc,eSBx, eRegs,eA,eIdx)
    LF("  end")
    -- [40] FORPREP
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v-%s[%s+2].v;%s=%s+%s end",
       vDispatch, fwdmap[40], eA,eB,eC,eBx,eSBx, eRegs,eA,eRegs,eA,eRegs,eA, ePc,ePc,eSBx)
    -- [41] TFORCALL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[41], eA,eB,eC,eBx,eSBx)
    LF("    local %s=%s(%s[%s].v(%s[%s+1].v,%s[%s+2].v))",
       eResults,vPack,eRegs,eA,eRegs,eA,eRegs,eA)
    LF("    for _i=1,%s do if not %s[%s+2+_i] then %s[%s+2+_i]={} end;%s[%s+2+_i].v=%s[_i] end",
       eC,eRegs,eA,eRegs,eA,eRegs,eA,eResults)
    LF("  end")
    -- [42] TFORLOOP
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)",vDispatch,fwdmap[42],eA,eB,eC,eBx,eSBx)
    LF("    if %s[%s+1].v~=nil then %s[%s].v=%s[%s+1].v;%s=%s+%s end",
       eRegs,eA, eRegs,eA,eRegs,eA, ePc,ePc,eSBx)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [43] SETLIST
    -- LFIELDS_PER_FLUSH = 50 (matches Lua 5.3 lvm.c constant).
    -- When C==0 the block number is in the next EXTRAARG instruction's Ax field.
    -- Offset is (block_number - 1) * SETLIST_BATCH, consistent with the C!=0
    -- path: (C-1)*SETLIST_BATCH.
    local SETLIST_BATCH = 50
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[43], eA,eB,eC,eBx,eSBx)
    LF("    local _off")
    LF("    if %s==0 then local _ni=%s[%s];%s=%s+1;_off=(%s(_ni,6)-1)*%d else _off=(%s-1)*%d end",
       eC,eCode,ePc,ePc,ePc,bShr,SETLIST_BATCH,eC,SETLIST_BATCH)
    LF("    local %s=%s==0 and %s-%s or %s", eNelem,eB,eTop,eA,eB)
    LF("    for _i=1,%s do %s[%s].v[_off+_i]=%s[%s+_i].v end", eNelem,eRegs,eA,eRegs,eA)
    LF("  end")
    -- [44] CLOSURE: captures suvs+proto-index via local aliases (safe even
    --              when eI is reused as a loop counter elsewhere)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[44], eA,eB,eC,eBx,eSBx)
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
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", vDispatch, fwdmap[45], eA,eB,eC,eBx,eSBx)
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
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) end", vDispatch, fwdmap[46], eA,eB,eC,eBx,eSBx)

    src[#src+1] = junk_block("  ", math.random(1, 2))

    -- ── Pre-compute obfuscated mask/shift constants (evaluated once) ──────────
    local _m63   = _obfInt(0x3F)
    local _m255  = _obfInt(0xFF)
    local _m511  = _obfInt(0x1FF)
    local _m18   = _obfInt(0x3FFFF)
    local _bias  = _obfInt(131071)
    local _sh6   = _obfInt(6)
    local _sh14  = _obfInt(14)
    local _sh23  = _obfInt(23)
    -- Emit as locals inside execute (pre-computed, not re-evaluated per instruction)
    local eMask63  = vn(); local eMask255 = vn(); local eMask511 = vn()
    local eMask18  = vn(); local eBias    = vn()
    local eSh6     = vn(); local eSh14   = vn(); local eSh23 = vn()
    LF("  local %s=%s local %s=%s local %s=%s", eMask63,_m63, eMask255,_m255, eMask511,_m511)
    LF("  local %s=%s local %s=%s", eMask18,_m18, eBias,_bias)
    LF("  local %s=%s local %s=%s local %s=%s", eSh6,_sh6, eSh14,_sh14, eSh23,_sh23)

    -- ── Main fetch-decode-dispatch loop ──────────────────────────────────────
    LF("  while not %s do", eDone)
    LF("    local %s=%s[%s]", eInst,eCode,ePc)
    LF("    %s=%s+1", ePc,ePc)
    LF("    local %s=%s(%s,%s)", eOp,bAnd,eInst,eMask63)
    LF("    local %s=%s(%s(%s,%s),%s)",   eA,  bAnd,bShr,eInst,eSh6, eMask255)
    LF("    local %s=%s(%s(%s,%s),%s)",   eB,  bAnd,bShr,eInst,eSh23,eMask511)
    LF("    local %s=%s(%s(%s,%s),%s)",   eC,  bAnd,bShr,eInst,eSh14,eMask511)
    LF("    local %s=%s(%s(%s,%s),%s)",   eBx, bAnd,bShr,eInst,eSh14,eMask18)
    LF("    local %s=%s-%s",         eSBx,eBx,eBias)
    LF("    local %s=%s[%s]", "_dh_", vDispatch,eOp)
    LF("    if %s then %s(%s,%s,%s,%s,%s) else error('Catify: unknown opcode '..tostring(%s),0) end", "_dh_","_dh_",eA,eB,eC,eBx,eSBx,eOp)
    LF("  end")
    LF("  return %s(%s,1,%s)", vUnpack,eRetVals,eRetN)
    LF("end")  -- end execute function
    -- Junk block after execute function definition
    src[#src+1] = junk_block("", math.random(2, 4))

    -- ── Main: anti-tamper, decrypt, deserialize, run ──────────
    -- The payload table (superflow_bytecode) was already emitted at the top of the file.

    -- AES key split into 4 × 8-byte chunks with per-chunk runtime XOR masks.
    -- Each chunk's bytes are pre-XOR'd with a session mask at codegen time so
    -- evaluating the string.char() expressions only yields the masked (wrong) bytes.
    -- An assembly block right before decryption unmasks + concatenates them.
    -- Per-chunk masks (codegen time, stored for use in the assembly block below):
    local km = {math.random(1,255), math.random(1,255), math.random(1,255), math.random(1,255)}
    local nm = {math.random(1,255), math.random(1,255)}
    -- Forward-declare vKey and vNonce; will be assigned just before decryption.
    LF("local %s", vKey)
    LF("local %s", vNonce)
    -- Key chunk 1 (bytes 1-8, each pre-XOR'd with km[1])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(bi) ~ km[1]) end
        LF("local %s=string.char(%s)", vKp1, table.concat(t, ","))
    end
    -- Key chunk 2 (bytes 9-16, each pre-XOR'd with km[2])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(8+bi) ~ km[2]) end
        LF("local %s=string.char(%s)", vKp2, table.concat(t, ","))
    end
    -- Key chunk 3 (bytes 17-24, each pre-XOR'd with km[3])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(16+bi) ~ km[3]) end
        LF("local %s=string.char(%s)", vKp3, table.concat(t, ","))
    end
    -- Key chunk 4 (bytes 25-32, each pre-XOR'd with km[4])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(24+bi) ~ km[4]) end
        LF("local %s=string.char(%s)", vKp4, table.concat(t, ","))
    end
    -- Nonce chunk 1 (bytes 1-4, each pre-XOR'd with nm[1])
    do
        local t = {}
        for bi = 1, 4 do t[bi] = _obfByte(nonce:byte(bi) ~ nm[1]) end
        LF("local %s=string.char(%s)", vNp1, table.concat(t, ","))
    end
    -- Nonce chunk 2 (bytes 5-8, each pre-XOR'd with nm[2])
    do
        local t = {}
        for bi = 1, 4 do t[bi] = _obfByte(nonce:byte(4+bi) ~ nm[2]) end
        LF("local %s=string.char(%s)", vNp2, table.concat(t, ","))
    end
    -- Decoy key fragments (random bytes, never used for actual decryption)
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(math.random(0, 255)) end
        LF("local %s=string.char(%s)", vDk1, table.concat(t, ","))
    end
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(math.random(0, 255)) end
        LF("local %s=string.char(%s)", vDk2, table.concat(t, ","))
    end

    -- Anti-tamper 1: SHA-256 integrity check of the encrypted blob
    -- Emit inline SHA-256 function
    local sha_k_vals = {0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2}
    -- XOR all 64 SHA-256 K constants with a random session mask so they are not
    -- recognisable as the standard SHA-256 round constants.
    local sha_k_mask = math.random(1, 0x3FFFFFFF)
    local sha_k_strs = {}
    for i = 1, 64 do sha_k_strs[i] = tostring((sha_k_vals[i] ~ sha_k_mask) & 0xFFFFFFFF) end
    LF("local function %s(_s)", shaFn)
    LF("  local function _rr(_x,_n) return %s(%s(%s(_x,_n),%s(_x,32-_n)),0xFFFFFFFF) end", bAnd,bOr,bShr,bShl)
    LF("  local _k={%s}", table.concat(sha_k_strs, ","))
    LF("  do local _m=%s;for _i=1,64 do _k[_i]=%s(%s(_k[_i],_m),0xFFFFFFFF) end end",
       _obfInt(sha_k_mask), bAnd, bXor)
    -- Mask SHA-256 initial hash values (IV) so they don't fingerprint SHA-256 init.
    do
        local sha_h_raw  = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}
        local sha_h_mask = math.random(1, 0x3FFFFFFF)
        local sha_h_strs = {}
        for i = 1, 8 do sha_h_strs[i] = tostring((sha_h_raw[i] ~ sha_h_mask) & 0xFFFFFFFF) end
        LF("  local %s={%s}", shaH, table.concat(sha_h_strs, ","))
        LF("  do local _hm=%s;for _i=1,8 do %s[_i]=%s(%s(%s[_i],_hm),0xFFFFFFFF) end end",
           _obfInt(sha_h_mask), shaH, bAnd, bXor, shaH)
    end
    LF("  local _len=#_s;local _bl=_len*8")
    LF("  local _pd=_s..'\\x80'")
    LF("  while #_pd%%64~=56 do _pd=_pd..'\\x00' end")
    LF("  _pd=_pd..%s(%s(%s(_bl,32),0xFFFFFFFF))..%s(%s(_bl,0xFFFFFFFF))", wrU4be,bAnd,bShr,wrU4be,bAnd)
    LF("  local %s={}", shaW)
    LF("  for _blk=1,#_pd,64 do")
    LF("    for _i=1,16 do local _o=_blk+(_i-1)*4;local _b1,_b2,_b3,_b4=_pd:byte(_o,_o+3);%s[_i]=%s(_b1*16777216+_b2*65536+_b3*256+_b4,0xFFFFFFFF) end", shaW, bAnd)
    LF("    for _i=17,64 do")
    LF("      local _s0=%s(%s(_rr(%s[_i-15],7),_rr(%s[_i-15],18)),%s(%s[_i-15],3))", bXor,bXor,shaW,shaW,bShr,shaW)
    LF("      local _s1=%s(%s(_rr(%s[_i-2],17),_rr(%s[_i-2],19)),%s(%s[_i-2],10))", bXor,bXor,shaW,shaW,bShr,shaW)
    LF("      %s[_i]=%s(%s[_i-16]+_s0+%s[_i-7]+_s1,0xFFFFFFFF)", shaW,bAnd,shaW,shaW)
    LF("    end")
    LF("    local _a,_b,_c,_d,_e,_f,_g,_hv=%s[1],%s[2],%s[3],%s[4],%s[5],%s[6],%s[7],%s[8]", shaH,shaH,shaH,shaH,shaH,shaH,shaH,shaH)
    LF("    for _i=1,64 do")
    LF("      local _S1=%s(%s(_rr(_e,6),_rr(_e,11)),_rr(_e,25))", bXor,bXor)
    LF("      local _ch=%s(%s(_e,_f),%s(%s(_e),_g))", bXor,bAnd,bAnd,bNot)
    LF("      local _t1=%s(_hv+_S1+_ch+_k[_i]+%s[_i],0xFFFFFFFF)", bAnd, shaW)
    LF("      local _S0=%s(%s(_rr(_a,2),_rr(_a,13)),_rr(_a,22))", bXor,bXor)
    LF("      local _maj=%s(%s(%s(_a,_b),%s(_a,_c)),%s(_b,_c))", bXor,bXor,bAnd,bAnd,bAnd)
    LF("      local _t2=%s(_S0+_maj,0xFFFFFFFF)", bAnd)
    LF("      _hv=_g;_g=_f;_f=_e;_e=%s(_d+_t1,0xFFFFFFFF);_d=_c;_c=_b;_b=_a;_a=%s(_t1+_t2,0xFFFFFFFF)", bAnd,bAnd)
    LF("    end")
    LF("    %s[1]=%s(%s[1]+_a,0xFFFFFFFF);%s[2]=%s(%s[2]+_b,0xFFFFFFFF)", shaH,bAnd,shaH,shaH,bAnd,shaH)
    LF("    %s[3]=%s(%s[3]+_c,0xFFFFFFFF);%s[4]=%s(%s[4]+_d,0xFFFFFFFF)", shaH,bAnd,shaH,shaH,bAnd,shaH)
    LF("    %s[5]=%s(%s[5]+_e,0xFFFFFFFF);%s[6]=%s(%s[6]+_f,0xFFFFFFFF)", shaH,bAnd,shaH,shaH,bAnd,shaH)
    LF("    %s[7]=%s(%s[7]+_g,0xFFFFFFFF);%s[8]=%s(%s[8]+_hv,0xFFFFFFFF)", shaH,bAnd,shaH,shaH,bAnd,shaH)
    LF("  end")
    LF("  local _out={};for _i=1,8 do local _w=%s[_i];_out[_i]=%s(_w) end;return table.concat(_out)", shaH, wrU4be)
    LF("end")
    -- Decode Base91 payload into vBlob (binary AES-encrypted blob)
    LF("local %s=%s(%s)", vBlob, b91Dec, PAYLOAD_VAR_NAME)
    LF("%s=nil", PAYLOAD_VAR_NAME)   -- wipe payload after decoding
    -- SHA-256 integrity check: compute hash and compare exact bytes
    LF("local %s=%s(%s)", atSha, shaFn, vBlob)
    do
        local hmask = math.random(1, 255)
        local hparts = {}
        for i = 1, #blob_sha do hparts[i] = _obfByte(blob_sha:byte(i) ~ hmask) end
        local hchunks = {}
        for i = 1, #hparts, 60 do
            local ch = {}
            for j = i, math.min(i + 59, #hparts) do ch[#ch+1] = hparts[j] end
            hchunks[#hchunks+1] = string.format("string.char(%s)", table.concat(ch, ","))
        end
        local hmask_expr = _obfInt(hmask)
        local hraw = table.concat(hchunks, "..")
        LF("do local _eh=%s local _hd={} for _i=1,#_eh do _hd[_i]=string.char(%s(_eh:byte(_i),%s)) end %s=table.concat(_hd) end",
           hraw, bXor, hmask_expr, atShaExp)
    end
    -- Obfuscate the integrity-check error message so it doesn't appear as plaintext.
    do
        local emsg = "[RUNTIME_ERROR] Catify: intg?ity ch4k failed"
        local emask = math.random(1, 255)
        local eparts = {}
        for i = 1, #emsg do eparts[i] = _obfByte(emsg:byte(i) ~ emask) end
        -- Split into chunks of 60 to stay within Lua's register limit.
        local echunks = {}
        for i = 1, #eparts, 60 do
            local ch = {}
            for j = i, math.min(i + 59, #eparts) do ch[#ch+1] = eparts[j] end
            echunks[#echunks+1] = string.format("string.char(%s)", table.concat(ch, ","))
        end
        -- The XOR decode is inlined as a function expression; emask is obfuscated.
        local emask_expr = _obfInt(emask)
        local eraw = table.concat(echunks, "..")
        LF("if %s~=%s then local _em=%s local _ed={} for _i=1,#_em do _ed[_i]=string.char(%s(_em:byte(_i),%s)) end error(table.concat(_ed),0) end",
           atSha, atShaExp, eraw, bXor, emask_expr)
    end

    local env_expr = "((function() local _e=((type(_ENV)=='table' and _ENV) or (type(getfenv)=='function' and getfenv(0)) or (type(_G)=='table' and _G) or {}); return (type(_e)=='table' and _e) or {} end)())"

    -- ProjectDiamond anti-tamper
    LF("local ProjectDiamond_triggered = false")
    LF("local ProjectDiamond_ok, ProjectDiamond_err = pcall(function()")
    LF("    local ProjectDiamond_c1 = game.ClassName == 'DataModel'")
    LF("    local ProjectDiamond_c2 = workspace.ClassName == 'Workspace'")
    LF("    local ProjectDiamond_c3 = typeof(Enum.Material.Plastic) == 'EnumItem'")
    LF("    local ProjectDiamond_c4 = Enum.Material.Plastic.Value == 256")
    LF("    local ProjectDiamond_c5 = typeof(game.Changed) == 'RBXScriptSignal'")
    LF("    local ProjectDiamond_c6 = typeof(workspace.Changed) == 'RBXScriptSignal'")
    LF("    local ProjectDiamond_rs = game:GetService('RunService')")
    LF("    local ProjectDiamond_c7 = ProjectDiamond_rs.ClassName == 'RunService'")
    LF("    local ProjectDiamond_c8 = typeof(ProjectDiamond_rs.Heartbeat) == 'RBXScriptSignal'")
    LF("    local ProjectDiamond_c9 = ProjectDiamond_rs:IsClient() ~= ProjectDiamond_rs:IsServer()")
    LF("    local ProjectDiamond_part = Instance.new('Part')")
    LF("    local ProjectDiamond_c10 = typeof(ProjectDiamond_part) == 'Instance' and ProjectDiamond_part.ClassName == 'Part'")
    LF("    ProjectDiamond_part:Destroy()")
    LF("    local ProjectDiamond_c11 = workspace:GetFullName() == 'Workspace'")
    LF("    local ProjectDiamond_cf = CFrame.new(1, 2, 3)")
    LF("    local ProjectDiamond_c12 = ProjectDiamond_cf.X == 1 and ProjectDiamond_cf.Y == 2 and ProjectDiamond_cf.Z == 3")
    LF("    local ProjectDiamond_t1 = workspace.DistributedGameTime")
    LF("    task.wait(0.1)")
    LF("    local ProjectDiamond_t2 = workspace.DistributedGameTime")
    LF("    local ProjectDiamond_c13 = (ProjectDiamond_t2 - ProjectDiamond_t1) > 0")
    LF("    local ProjectDiamond_guid_ok, ProjectDiamond_guid = pcall(function()")
    LF("        return game:GetService('HttpService'):GenerateGUID(false)")
    LF("    end)")
    LF("    local ProjectDiamond_c14 = ProjectDiamond_guid_ok and #ProjectDiamond_guid == 36 and ProjectDiamond_guid:sub(9,9) == '-'")
    LF("    local ProjectDiamond_checks = {")
    LF("        ProjectDiamond_c1, ProjectDiamond_c2, ProjectDiamond_c3, ProjectDiamond_c4,")
    LF("        ProjectDiamond_c5, ProjectDiamond_c6, ProjectDiamond_c7, ProjectDiamond_c8,")
    LF("        ProjectDiamond_c9, ProjectDiamond_c10, ProjectDiamond_c11, ProjectDiamond_c12,")
    LF("        ProjectDiamond_c13, ProjectDiamond_c14")
    LF("    }")
    LF("    local ProjectDiamond_passed = 0")
    LF("    for _, ProjectDiamond_v in ipairs(ProjectDiamond_checks) do")
    LF("        if ProjectDiamond_v then ProjectDiamond_passed = ProjectDiamond_passed + 1 end")
    LF("    end")
    LF("    if ProjectDiamond_passed < #ProjectDiamond_checks then")
    LF("        ProjectDiamond_triggered = true")
    LF("    end")
    LF("end)")
    LF("if not ProjectDiamond_ok then")
    LF("    ProjectDiamond_triggered = true")
    LF("end")
    LF("if ProjectDiamond_triggered then")
    LF("    task.delay(math.random(6, 7), function()")
    LF("        print('Detected by catify :3')")
    LF("    end)")
    LF("    return")
    LF("end")

    -- Watermark: obfuscated ASCII cat watermark (sits in memory, never printed)
    local wm_bytes = {32,32,47,92,95,47,92,32,32,10,32,40,111,46,111,32,41,10,32,32,62,32,94,32,60,10,32,67,97,116,105,102,121,32,118,50,46,48}
    local wm_parts = {}
    for i = 1, #wm_bytes do wm_parts[i] = tostring(wm_bytes[i]) end
    LF("local %s=table.concat((function()local _t={};for _i,_v in ipairs({%s})do _t[_i]=string.char(_v)end;return _t end)())",
       vWm, table.concat(wm_parts, ","))

    -- Decrypt and deserialize
    -- Assemble the real key from 4 pre-masked chunks (runtime unmask).
    -- Assemble the real nonce from 2 pre-masked chunks.
    -- Both forward-declared earlier; wiped immediately after use.
    LF("do")
    LF("  local _kt={}")
    LF("  local _km1=%s;for _j=1,8 do _kt[_j]=string.char(%s(%s:byte(_j),_km1))end",
       _obfInt(km[1]), bXor, vKp1)
    LF("  local _km2=%s;for _j=1,8 do _kt[8+_j]=string.char(%s(%s:byte(_j),_km2))end",
       _obfInt(km[2]), bXor, vKp2)
    LF("  local _km3=%s;for _j=1,8 do _kt[16+_j]=string.char(%s(%s:byte(_j),_km3))end",
       _obfInt(km[3]), bXor, vKp3)
    LF("  local _km4=%s;for _j=1,8 do _kt[24+_j]=string.char(%s(%s:byte(_j),_km4))end",
       _obfInt(km[4]), bXor, vKp4)
    LF("  %s=table.concat(_kt)", vKey)
    LF("  %s=nil;%s=nil;%s=nil;%s=nil;_kt=nil", vKp1, vKp2, vKp3, vKp4)
    LF("  local _nt={}")
    LF("  local _nm1=%s;for _j=1,4 do _nt[_j]=string.char(%s(%s:byte(_j),_nm1))end",
       _obfInt(nm[1]), bXor, vNp1)
    LF("  local _nm2=%s;for _j=1,4 do _nt[4+_j]=string.char(%s(%s:byte(_j),_nm2))end",
       _obfInt(nm[2]), bXor, vNp2)
    LF("  %s=table.concat(_nt)", vNonce)
    LF("  %s=nil;%s=nil;_nt=nil", vNp1, vNp2)
    LF("end")
    LF("%s=%s(%s,%s,%s)", vBlob, vDecrypt, vBlob, vKey, vNonce)
    LF("%s=nil;%s=nil;%s=nil;%s=nil;%s=nil", vKey, vNonce, vDecrypt, vDk1, vDk2)   -- wipe key, nonce, decryptor, decoys
    LF("%s=1", dPos)
    LF("%s=%s", dData, vBlob)
    LF("local %s=%s()", vProto, vLoadProto)
    LF("%s=nil;%s=nil;%s=nil", vBlob, dData, vLoadProto)  -- wipe after load
    LF("local %s={v=%s}", vEnv, env_expr)
    -- Initial upvals table uses a metatable so any upval[N] always returns a box
    LF("return %s(%s,setmetatable({[0]=%s},{__index=function(t,k)local b={};t[k]=b;return b end}))",
       vExec, vProto, vEnv)
    L("end)(...)")

    -- ── Compact post-processing: strip indentation and join lines ────────────
    local full = table.concat(src)
    local compact_lines = {}
    for line in full:gmatch("[^\n]+") do
        -- Strip leading whitespace, then strip trailing whitespace separately
        local trimmed = line:match("^%s*(.+)$")
        if trimmed then
            trimmed = trimmed:match("^(.-)%s*$")
        end
        if trimmed and trimmed ~= "" then
            compact_lines[#compact_lines + 1] = trimmed
        end
    end
    -- Single-line header comment (matches the compact AstrarServices output style)
    local header = "-- This file was protected by Catify v2.0.0\n"
    return header .. table.concat(compact_lines, " ")
end

return VmGen
