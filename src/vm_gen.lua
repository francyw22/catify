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

-- The payload is Base85-encoded and emitted as a long-bracket string literal [=[...]=].
-- Base85 uses printable ASCII and avoids ']' and '%', making it safe in long brackets.
local PAYLOAD_VAR_NAME = "superflow_bytecode"
local ANTI_TAMPER_CHECK_COUNT = 32
local function emit_payload_b85(b85str)
    -- Use long-bracket literal so the string needs no escaping.
    return "local " .. PAYLOAD_VAR_NAME .. "=[=[" .. b85str .. "]=];"
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
    -- ChaCha20 replaces AES-256-CTR; nonce is still 8 bytes (compatible with rand_nonce)
    local blob = utils.chacha20(raw, key, nonce)
    local b85_blob = utils.base85_enc(blob)   -- Base85-encode for safe long-bracket payload

    -- ── 2. Generate random identifiers for all locals ───────────────────────
    -- We need ~80 unique names for VM internals
    local N  = utils.rand_names(240)
    local ni = 0
    local function vn()   -- "variable name"
        ni = ni + 1
        return N[ni]
    end

    -- Core names
    local vExec     = vn()   -- main execute function
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
    local eCallArgs = vn()
    local eNargs    = vn()
    local eResults  = vn()
    local eFn       = vn()
    local eNelem    = vn()
    local eSuvs     = vn()
    local eUv       = vn()
    local eSub      = vn()
    local eIdx      = vn()
    local eLim      = vn()
    local eStep     = vn()
    local eI        = vn()
    -- anti-tamper names (atPayload is now the fixed string "superflow_bytecode")
    local vStrXor   = vn()   -- string-constant XOR key (second encryption layer)
    -- SHA-256 integrity check variable names
    local atSha     = vn()
    local atShaExp  = vn()
    -- Runtime anti-tamper variable names (avoid static signatures in output)
    local atTrig    = vn()
    local atOk      = vn()
    local atRs      = vn()
    local atPart    = vn()
    local atFolder  = vn()
    local atPlayers = vn()
    local atHttp    = vn()
    local atCf      = vn()
    local atT1      = vn()
    local atT2      = vn()
    local atGuidOk  = vn()
    local atGuid    = vn()
    local atChecks  = vn()
    local atPassed  = vn()
    local atChkVal  = vn()
    local atMaterialEnums = vn()
    local atLighting = vn()
    local atCheckVars = {}
    for i = 1, ANTI_TAMPER_CHECK_COUNT do
        atCheckVars[i] = vn()
    end
    -- Watermark variable name
    local vWm       = vn()
    -- Extra randomized temp names for emitted anti-tamper/decode/watermark/key assembly code
    local atHashEnc = vn()
    local atHashDec = vn()
    local atHashI = vn()
    local atErrEnc = vn()
    local atErrDec = vn()
    local atErrI = vn()
    local atEnvTbl = vn()
    local wmTbl = vn()
    local wmI = vn()
    local wmV = vn()
    local keyTbl = vn()
    local nonceTbl = vn()
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
    -- Bitwise compat helpers: use randomized helper identifiers so fixed
    -- helper signatures don't appear in output.
    -- Native ops in load() strings bypass Luau's parser so older Luau versions work too.
    local bXor, bNot, bAnd, bOr, bShl, bShr =
        "__" .. vn() .. "_catify", "__" .. vn() .. "_catify", "__" .. vn() .. "_catify",
        "__" .. vn() .. "_catify", "__" .. vn() .. "_catify", "__" .. vn() .. "_catify"
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
            -- Pure arithmetic triple-sum: n = a + b + (n-a-b), no XOR
            local a = math.random(1, 0x3FFF)
            local b = math.random(1, 0x3FFF)
            return string.format("(%d+%d+%d)", a, b, n - a - b)
        end
    end
    local function _obfByte(n)
        -- Alternate between bitwise-AND mask and arithmetic modulo to vary patterns.
        if math.random(0, 1) == 0 then
            return string.format("%s(%s,255)", bAnd, _obfInt(n))
        else
            return string.format("(%s%%256)", _obfInt(n))
        end
    end
    -- _obfLitStr: emit a self-contained IIFE that recovers the original string at runtime.
    -- Two encoding strategies are chosen at random per call to break repetitive patterns:
    --   Strategy 0 (rolling XOR): cipher[i] = plain[i] XOR key[(i-1)%klen+1]
    --     decode: bXor(d[i], k[(i-1)%#k+1])
    --   Strategy 1 (rolling add-sub): cipher[i] = (plain[i] + key[(i-1)%klen+1]) % 256
    --     decode: (d[i] - k[(i-1)%#k+1]) % 256  (pure arithmetic, no bXor)
    -- Both strategies use _obfByte for per-byte obfuscation (arithmetic noise + mask).
    -- Each call produces a unique key, so identical strings differ across protected files.
    local function _obfLitStr(s)
        if #s == 0 then return '""' end
        -- Fresh random key and strategy for this string.
        local klen = math.random(3, 8)
        local key = {}
        for i = 1, klen do key[i] = math.random(0, 255) end
        local strategy = math.random(0, 1)
        local cipher = {}
        if strategy == 0 then
            -- Rolling XOR encryption
            for i = 1, #s do
                cipher[i] = s:byte(i) ~ key[((i - 1) % klen) + 1]
            end
        else
            -- Rolling add-mod-256 encryption
            for i = 1, #s do
                cipher[i] = (s:byte(i) + key[((i - 1) % klen) + 1]) % 256
            end
        end
        -- Obfuscate each key byte and cipher byte through _obfByte.
        local kparts, dparts = {}, {}
        for i = 1, klen    do kparts[i] = _obfByte(key[i])    end
        for i = 1, #cipher do dparts[i] = _obfByte(cipher[i]) end
        -- Build the IIFE without string.format to avoid escaping the literal '%' operator.
        local kArr = table.concat(kparts, ",")
        local dArr = table.concat(dparts, ",")
        if strategy == 0 then
            -- Decode: bXor(d[i], k[(i-1)%#k+1])
            local decLoop = "};local _o={};for _i=1,#_d do _o[_i]=string.char("
                         .. bXor .. "(_d[_i],_k[(_i-1)%#_k+1]))end;return table.concat(_o)end)()"
            return "(function()local _k={" .. kArr .. "};local _d={" .. dArr .. decLoop
        else
            -- Decode: (d[i] - k[(i-1)%#k+1]) % 256 — pure arithmetic, no bXor call
            local decLoop = "};local _o={};for _i=1,#_d do _o[_i]=string.char((_d[_i]-_k[(_i-1)%#_k+1])%256)end;return table.concat(_o)end)()"
            return "(function()local _k={" .. kArr .. "};local _d={" .. dArr .. decLoop
        end
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
    -- Shared pool for forms 15-18: all printable ASCII valid in Luau long strings,
    -- excluding ']' (would close [=[...]=]) and '%' (would corrupt string.format calls
    -- in the generator). Only Luau/Roblox-safe ASCII characters are included.
    local _JUNK_POOL = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789" ..
                       "!\"#$&'()*+,-./:;<=>?@[\\^_`{|}~"
    local function _junk_quote(s)
        return string.format("%q", s)
    end
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
        -- form 11: integer division identity (no bXor) – b * (a // b) == a when divisible
        function(indent)
            local v1, v2 = jpick2()
            local b = math.random(2, 9)
            local q = math.random(1, 100)
            local a = q * b  -- a is always divisible by b, so a // b == q
            return string.format(
                "%sdo local %s=%d;local %s=%s//%d;if %s~=%d then %s=%s*0 end end\n",
                indent, v1, a, v2, v1, b, v2, q, v1, v1)
        end,
        -- form 12: string.byte + string.char round-trip identity (no bXor)
        function(indent)
            local v1, v2 = jpick2()
            local bval = math.random(65, 90)  -- ASCII A-Z
            return string.format(
                "%sdo local %s=string.char(%d);local %s=string.byte(%s);if %s~=%d then %s=nil end end\n",
                indent, v1, bval, v2, v1, v2, bval, v1)
        end,
        -- form 13: math.floor identity – floor of an integer is itself (no bXor)
        function(indent)
            local v1 = jpick()
            local n = math.random(5, 9999)
            return string.format(
                "%sdo local %s=%d;if math.floor(%s)~=%s then %s=%s+1 end end\n",
                indent, v1, n, v1, v1, v1, v1)
        end,
        -- form 14: tostring + # length identity (no bXor)
        function(indent)
            local v1, v2 = jpick2()
            local n = math.random(10, 9999)
            local slen = #tostring(n)
            return string.format(
                "%sdo local %s=%d;local %s=#tostring(%s);if %s~=%d then %s=%s*0 end end\n",
                indent, v1, n, v2, v1, v2, slen, v1, v1)
        end,
        -- form 15: random garbage-string dead-code assignment (looks like obfuscated data/token)
        -- Generates a fresh random string of 300-1500 printable ASCII chars (mix of alphanumeric
        -- and Luau-valid symbols) each time; dead branch guarantees it never executes.
        -- Uses _JUNK_POOL (no ']' or '%'); string concatenation avoids format-string injection.
        function(indent)
            local len = math.random(300, 1500)
            local chars = {}
            for i = 1, len do
                local pos = math.random(1, #_JUNK_POOL)
                chars[i] = _JUNK_POOL:sub(pos, pos)
            end
            local garbage = table.concat(chars)
            local v1 = jpick()
            return indent.."do local "..v1.."=".._junk_quote(garbage)..";if #"..v1.."<0 then "..v1.."=nil end end\n"
        end,
        -- form 16: very large symbol-heavy garbage string (8000-20000 chars).
        -- Uses _JUNK_POOL (Luau-valid ASCII only); concatenation return avoids format-string injection.
        function(indent)
            local len = math.random(8000, 20000)
            local chars = {}
            for i = 1, len do
                local pos = math.random(1, #_JUNK_POOL)
                chars[i] = _JUNK_POOL:sub(pos, pos)
            end
            local garbage = table.concat(chars)
            local v1 = jpick()
            return indent.."do local "..v1.."=".._junk_quote(garbage)..";if #"..v1.."<0 then "..v1.."=nil end end\n"
        end,
        -- form 17: dead multi-string array — builds 50-150 symbol-heavy strings into a
        -- table array and concatenates them; dead branch discards the result.
        -- Each entry is 30-150 Luau-valid ASCII chars; total output 1500-22500 chars.
        function(indent)
            local count = math.random(50, 150)
            local entries = {}
            for i = 1, count do
                local slen = math.random(30, 150)
                local chars = {}
                for j = 1, slen do
                    local pos = math.random(1, #_JUNK_POOL)
                    chars[j] = _JUNK_POOL:sub(pos, pos)
                end
                entries[i] = _junk_quote(table.concat(chars))
            end
            local v1, v2 = jpick2()
            local tbl = table.concat(entries, ",")
            return indent.."do local "..v1.."={"..tbl.."};local "..v2.."=table.concat("..v1..");if #"..v2.."<0 then "..v2.."=nil end end\n"
        end,
        -- form 18: dead symbol-string array — 20-60 Luau-valid ASCII symbol strings stored
        -- in a table, length-checked, then discarded via always-false branch. Each string
        -- 20-80 chars. Concatenation-built return; no string.format injection risk.
        function(indent)
            local count = math.random(20, 60)
            local entries = {}
            for i = 1, count do
                local vlen = math.random(20, 80)
                local vchars = {}
                for j = 1, vlen do
                    local pos = math.random(1, #_JUNK_POOL)
                    vchars[j] = _JUNK_POOL:sub(pos, pos)
                end
                entries[i] = _junk_quote(table.concat(vchars))
            end
            local v1, v2 = jpick2()
            local tbl = table.concat(entries, ",")
            return indent.."do local "..v1.."={"..tbl.."};local "..v2.."=#"..v1..";if "..v2.."<0 then "..v1.."=nil end end\n"
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
    -- Quick sanity guard (matches the decoded VM style)
    L("if not ((type('') == 'string')) then return end")
    -- ── Base85-encoded payload declared as local inside the wrapper function ──────────
    src[#src+1] = emit_payload_b85(b85_blob) .. "\n"
    -- ── bit32 polyfill (from decoded VM) ───────────────────────────────────────
    -- Provides bit32.bxor/band/bor/bnot/lshift/rshift in all Lua/Luau environments.
    L("local bit32=(function()")
    L("  local b={}")
    L("  local _orig=bit32")
    L("  if _orig then for k,v in pairs(_orig) do b[k]=v end")
    L("  else")
    L("    b.bxor=function(a,b_) local p,r=1,0 for i=1,32 do if a%2~=b_%2 then r=r+p end a=math.floor(a/2) b_=math.floor(b_/2) p=p*2 end return r end")
    L("    b.band=function(a,b_) local p,r=1,0 for i=1,32 do if a%2==1 and b_%2==1 then r=r+p end a=math.floor(a/2) b_=math.floor(b_/2) p=p*2 end return r end")
    L("    b.bor=function(a,b_) local p,r=1,0 for i=1,32 do if a%2==1 or b_%2==1 then r=r+p end a=math.floor(a/2) b_=math.floor(b_/2) p=p*2 end return r end")
    L("    b.bnot=function(a) return b.bxor(a,4294967295) end")
    L("    b.lshift=function(a,n) return math.floor(a*(2^n))%4294967296 end")
    L("    b.rshift=function(a,n) return math.floor(a/(2^n)) end")
    L("  end")
    L("  return b")
    L("end)()")
    -- ── Standard library early-bind (anti-hook) ──────────────────────────────
    -- Capture stdlib references before any hook can replace them (matches decoded VM style).
    -- Only pre-allocate names used in multiple places; emit single-use ones inline.
    local _pcallBind = vn(); local _tostrBind = vn()
    local _atGuard = vn()
    do
        local _tb = vn(); local _mb1 = vn(); local _mb2 = vn()
        local _sb1 = vn(); local _sb2 = vn(); local _sb3 = vn()
        local _tb1 = vn(); local _tb2 = vn()
        LF("local %s=pcall;local %s=type;local %s=tostring", _pcallBind, _tb, _tostrBind)
        LF("local %s=math and math.floor;local %s=math and math.random", _mb1, _mb2)
        LF("local %s=string and string.char;local %s=string and string.byte;local %s=string and string.sub", _sb1, _sb2, _sb3)
        LF("local %s=table and table.concat;local %s=table and table.insert", _tb1, _tb2)
    end
    -- ── Anti-tamper init-bind check (hookfunction / getgenv / debug.info) ────
    -- Matches the decoded VM's _iKqRYpwQ / debug.info pattern.
    LF("local %s=0", _atGuard)
    L("do")
    L("  local _di=debug and debug.info or nil")
    L("  if _di then")
    L("    if pcall then local _s=_di(pcall,'s');if _s~='[C]' then "..string.format("%s=%s+200", _atGuard, _atGuard).." end end")
    L("    if tostring then local _s=_di(tostring,'s');if _s~='[C]' then "..string.format("%s=%s+200", _atGuard, _atGuard).." end end")
    L("    if pairs then local _s=_di(pairs,'s');if _s~='[C]' then "..string.format("%s=%s+200", _atGuard, _atGuard).." end end")
    L("    if setmetatable then local _s=_di(setmetatable,'s');if _s~='[C]' then "..string.format("%s=%s+200", _atGuard, _atGuard).." end end")
    L("  end")
    L("end")
    LF("%s(function()", _pcallBind)
    LF("  if getgenv then local _g=getgenv();if _g.pcall~=%s then %s=%s+150 end;if _g.tostring~=%s then %s=%s+100 end end", _pcallBind, _atGuard, _atGuard, _tostrBind, _atGuard, _atGuard)
    L("end)")
    LF("%s(function()", _pcallBind)
    LF("  if _ENV and (_ENV.hookfunction or _ENV.hookmetamethod or _ENV.replaceclosure) then %s=%s+200 end", _atGuard, _atGuard)
    L("end)")
    LF("if %s>500 then return end", _atGuard)
    LF("local %s=tostring;local %s=type;local %s=pcall", bsToStr, bsType, bsPcall)
    LF("local %s=(type(load)=='function' and load) or (type(loadstring)=='function' and loadstring) or nil", vLoadCompat)
    LF("local %s=(table and table.pack) or function(...) return {n=select('#', ...),...} end", vPack)
    LF("local %s=(table and table.unpack) or unpack", vUnpack)
    LF("if type(%s)~='function' then local function _up(t,i,j) i=i or 1;j=j or #t;if i>j then return end;return t[i],_up(t,i+1,j) end;%s=_up end", vUnpack, vUnpack)
    -- Bitwise compat: use bit32 library if available (Roblox Luau), otherwise
    -- compile native Lua 5.3 operators via loader so the Luau parser never sees ~, &, |, <<, >>
    LF("local %s,%s,%s,%s,%s,%s", bXor,bNot,bAnd,bOr,bShl,bShr)
    LF("local b,c,d,e,f,g=%s,%s,%s,%s,%s,%s",
       _earlyLitStr("bxor"),_earlyLitStr("bnot"),_earlyLitStr("band"),_earlyLitStr("bor"),_earlyLitStr("lshift"),_earlyLitStr("rshift"))
    LF("local bit32Available=type(bit32)=='table' and type(bit32[b])=='function' and type(bit32[c])=='function' and type(bit32[d])=='function' and type(bit32[e])=='function'")
    LF("if bit32Available then")
    LF("  %s=bit32[b];%s=bit32[c];%s=bit32[d];%s=bit32[e]", bXor,bNot,bAnd,bOr)
    -- bit32.lshift and bit32.rshift may be absent in some Roblox Luau builds.
    -- Fall back to a math-based equivalent using bit32.band (always present).
    LF("  %s=bit32[f] or function(a,b) if b>=32 then return 0 end;return bit32[d](a*(2^b),0xFFFFFFFF) end", bShl)
    LF("  %s=bit32[g] or function(a,b) if b>=32 then return 0 end;return math.floor(bit32[d](a,0xFFFFFFFF)/(2^b)) end", bShr)
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
    src[#src+1] = junk_block("", math.random(4, 8))
    -- ── Real inline Base85 decoder (decodes the payload back to the ChaCha20 blob) ──
    -- Matches the decoder from the decoded VM: LE word order, 'z' shorthand for zeros.
    -- decode 5-char group to 4 LE bytes helper
    LF("local function %s(_h)", b91Alpha)
    LF("  local _a,_b,_c,_d,_e=string.byte(_h,1,5)")
    LF("  local _v=(_a-33)*52200625+(_b-33)*614125+(_c-33)*7225+(_d-33)*85+(_e-33)")
    LF("  _v=_v%%4294967296")
    LF("  return string.char(_v%%256,math.floor(_v/256)%%256,math.floor(_v/65536)%%256,math.floor(_v/16777216)%%256)")
    LF("end")
    LF("local function %s(%s)", b91Dec, b91I)
    LF("  local _t=%s:gsub('z','!!!!!')", b91I)
    LF("  return (_t:gsub('.....',%s))", b91Alpha)
    LF("end")
    src[#src+1] = junk_block("", math.random(3, 6))
    -- ── Emit inline ChaCha20 decrypt (replaces AES-256-CTR) ─────────────────
    -- quarter-round helper (inner function), state variable names use b91Tbl etc.
    LF("local function %s(_k,_nn,_d)", vDecrypt)
    LF("  local _bx=bit32.bxor;local _ba=bit32.band;local _bo=bit32.bor")
    LF("  local _ls=bit32.lshift;local _rs=bit32.rshift")
    LF("  local _rl=function(_x,_n) return _bo(_ls(_ba(_x,_rs(0xFFFFFFFF,_n)),_n),_rs(_x,32-_n)) end")
    LF("  local _m32=function(_x) return _ba(_x,0xFFFFFFFF) end")
    LF("  local _add=function(_a,_b) return _m32(_a+_b) end")
    LF("  local _dl=#_d;local _out={};local _pos=0;local _ctr=0")
    -- key words
    LF("  local _kw={};for _i=0,7 do _kw[_i+1]=_m32(string.byte(_k,_i*4+1)+string.byte(_k,_i*4+2)*256+string.byte(_k,_i*4+3)*65536+string.byte(_k,_i*4+4)*16777216) end")
    -- nonce words (counter=_ctr as word 1, 8-byte nonce as words 2-3)
    LF("  local _nn1=_m32(string.byte(_nn,1)+string.byte(_nn,2)*256+string.byte(_nn,3)*65536+string.byte(_nn,4)*16777216)")
    LF("  local _nn2=_m32(string.byte(_nn,5)+string.byte(_nn,6)*256+string.byte(_nn,7)*65536+string.byte(_nn,8)*16777216)")
    LF("  local _C0,_C1,_C2,_C3=0x61707865,0x3320646e,0x79622d32,0x6b206574")
    LF("  while _pos<_dl do")
    LF("    local _st={_C0,_C1,_C2,_C3,_kw[1],_kw[2],_kw[3],_kw[4],_kw[5],_kw[6],_kw[7],_kw[8],_ctr,_nn1,_nn2,0}")
    LF("    local _ws={};for _i=1,16 do _ws[_i]=_st[_i] end")
    LF("    local function _qr(_a,_b,_c,_d_)")
    LF("      _ws[_a]=_add(_ws[_a],_ws[_b]);_ws[_d_]=_rl(_bx(_ws[_d_],_ws[_a]),16)")
    LF("      _ws[_c]=_add(_ws[_c],_ws[_d_]);_ws[_b]=_rl(_bx(_ws[_b],_ws[_c]),12)")
    LF("      _ws[_a]=_add(_ws[_a],_ws[_b]);_ws[_d_]=_rl(_bx(_ws[_d_],_ws[_a]),8)")
    LF("      _ws[_c]=_add(_ws[_c],_ws[_d_]);_ws[_b]=_rl(_bx(_ws[_b],_ws[_c]),7)")
    LF("    end")
    LF("    for _r=1,10 do")
    LF("      _qr(1,5,9,13);_qr(2,6,10,14);_qr(3,7,11,15);_qr(4,8,12,16)")
    LF("      _qr(1,6,11,16);_qr(2,7,12,13);_qr(3,8,9,14);_qr(4,5,10,15)")
    LF("    end")
    LF("    local _ks={};for _i=1,16 do _ks[_i]=_add(_ws[_i],_st[_i]) end")
    LF("    local _bl=math.min(64,_dl-_pos)")
    LF("    for _j=0,_bl-1 do")
    LF("      local _wi=math.floor(_j/4)+1;local _sh=(_j%%4)*8")
    LF("      local _kb=_ba(_rs(_ks[_wi],_sh),0xFF)")
    LF("      _out[#_out+1]=string.char(_bx(string.byte(_d,_pos+_j+1),_kb))")
    LF("    end")
    LF("    _pos=_pos+64;_ctr=_ctr+1")
    LF("  end")
    LF("  return table.concat(_out)")
    LF("end")
    -- Junk block between ChaCha20 function and deserializer
    src[#src+1] = junk_block("", math.random(4, 8))
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
    -- Extra junk between decoy and deserializer
    src[#src+1] = junk_block("", math.random(3, 6))

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
    -- Extra junk after deserializer/proto-loader
    src[#src+1] = junk_block("", math.random(3, 6))

    -- (dispatch table indexed by shuffled opcode – no separate revmap needed)
    -- Junk block after VM setup
    src[#src+1] = junk_block("", math.random(3, 6))

    -- The execute function (dispatch-table based)
    LF("local function %s(%s,%s,...)", vExec, eProto, eUpvals)
    LF("  local %s=%s(...)", eArgs, vPack)
    -- Junk at function entry
    src[#src+1] = junk_block("  ", math.random(2, 4))
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
    src[#src+1] = junk_block("", math.random(5, 10))

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
    -- Decode Base85 payload into vBlob (binary ChaCha20-encrypted blob)
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
        LF("do local %s=%s local %s={} for %s=1,#%s do %s[%s]=string.char(%s(%s:byte(%s),%s)) end %s=table.concat(%s) end",
           atHashEnc, hraw, atHashDec, atHashI, atHashEnc, atHashDec, atHashI, bXor, atHashEnc, atHashI, hmask_expr, atShaExp, atHashDec)
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
        LF("if %s~=%s then local %s=%s local %s={} for %s=1,#%s do %s[%s]=string.char(%s(%s:byte(%s),%s)) end error(table.concat(%s),0) end",
           atSha, atShaExp, atErrEnc, eraw, atErrDec, atErrI, atErrEnc, atErrDec, atErrI, bXor, atErrEnc, atErrI, emask_expr, atErrDec)
    end

    local env_expr = string.format("((function() local %s=((type(_ENV)=='table' and _ENV) or (type(getfenv)=='function' and getfenv(0)) or (type(_G)=='table' and _G) or {}); return (type(%s)=='table' and %s) or {} end)())", atEnvTbl, atEnvTbl, atEnvTbl)

    -- Anti-tamper: task.delay availability + hookfunction detection.
    -- Matches the decoded VM's sophisticated check style.
    LF("local %s, %s = pcall(function()", atOk, atChkVal)
    LF("    return typeof(task) == %s and typeof(task.delay) == %s", _obfLitStr("table"), _obfLitStr("function"))
    LF("end)")
    LF("local %s = not (%s and %s)", atTrig, atOk, atChkVal)
    LF("if %s then", atTrig)
    LF("    print('Detected by catify :3')")
    LF("    return")
    LF("end")
    -- Additional runtime guard: recheck accumulated tamper score from the top-level
    -- anti-hook init-bind block emitted at function entry.
    LF("if %s > 500 then return end", _atGuard)

    -- Watermark: obfuscated ASCII cat watermark (sits in memory, never printed)
    local wm_bytes = {32,32,47,92,95,47,92,32,32,10,32,40,111,46,111,32,41,10,32,32,62,32,94,32,60,10,32,67,97,116,105,102,121,32,118,50,46,48}
    local wm_parts = {}
    for i = 1, #wm_bytes do wm_parts[i] = tostring(wm_bytes[i]) end
    LF("local %s=table.concat((function()local %s={};for %s,%s in ipairs({%s})do %s[%s]=string.char(%s)end;return %s end)())",
       vWm, wmTbl, wmI, wmV, table.concat(wm_parts, ","), wmTbl, wmI, wmV, wmTbl)

    -- Decrypt and deserialize
    -- Assemble the real key from 4 pre-masked chunks (runtime unmask).
    -- Assemble the real nonce from 2 pre-masked chunks.
    -- Both forward-declared earlier; wiped immediately after use.
    LF("do")
    LF("  local %s={}", keyTbl)
    LF("  local mask1=%s;for i=1,8 do %s[i]=string.char(%s(%s:byte(i),mask1))end",
       _obfInt(km[1]), keyTbl, bXor, vKp1)
    LF("  local mask2=%s;for i=1,8 do %s[8+i]=string.char(%s(%s:byte(i),mask2))end",
       _obfInt(km[2]), keyTbl, bXor, vKp2)
    LF("  local mask3=%s;for i=1,8 do %s[16+i]=string.char(%s(%s:byte(i),mask3))end",
       _obfInt(km[3]), keyTbl, bXor, vKp3)
    LF("  local mask4=%s;for i=1,8 do %s[24+i]=string.char(%s(%s:byte(i),mask4))end",
       _obfInt(km[4]), keyTbl, bXor, vKp4)
    LF("  %s=table.concat(%s)", vKey, keyTbl)
    LF("  %s=nil;%s=nil;%s=nil;%s=nil;%s=nil", vKp1, vKp2, vKp3, vKp4, keyTbl)
    LF("  local %s={}", nonceTbl)
    LF("  local nmask1=%s;for j=1,4 do %s[j]=string.char(%s(%s:byte(j),nmask1))end",
       _obfInt(nm[1]), nonceTbl, bXor, vNp1)
    LF("  local nmask2=%s;for j=1,4 do %s[4+j]=string.char(%s(%s:byte(j),nmask2))end",
       _obfInt(nm[2]), nonceTbl, bXor, vNp2)
    LF("  %s=table.concat(%s)", vNonce, nonceTbl)
    LF("  %s=nil;%s=nil;%s=nil", vNp1, vNp2, nonceTbl)
    LF("end")
    LF("%s=%s(%s,%s,%s)", vBlob, vDecrypt, vKey, vNonce, vBlob)
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
