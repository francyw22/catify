--[[
    Catify - Commercial Lua Obfuscator
    src/vm_gen.lua  - VM code generator

    Responsibilities:
      1. Re-serialize the (already opcode-shuffled) Proto tree into a compact
         custom binary format.
      2. Encrypt that blob with AES-256-CTR (32-byte key + 8-byte nonce supplied by the caller).
      3. Emit a self-contained Lua 5.3 source file that:
           • Decodes custom Base85 payload, checks SHA-256 integrity, decrypts with AES-256-CTR.
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

-- The payload is custom-Base85 encoded and emitted as a single quoted string literal.
-- The alphabet uses only safe printable ASCII characters, making the output resilient
-- to any third-party tool that processes or re-encodes the generated Lua file.
local PAYLOAD_VAR_NAME = "superflow_bytecode"
local ANTI_TAMPER_CHECK_COUNT = 32
local function emit_payload_b85(b85str)
    -- Declare as local inside the wrapper function so it doesn't pollute global scope.
    return "local " .. PAYLOAD_VAR_NAME .. "=" .. string.format("%q", b85str) .. ";"
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
---@param utils   table   The Utils module (for aes256_ctr, sha256, base85_pack, rand_names)
---@return string  Lua source
function VmGen.generate(proto, revmap, key, nonce, utils)
    -- ── 1. Serialize + encrypt the custom bytecode ───────────────────────────
    local sxor_byte = math.random(1, 255)     -- per-session string XOR key
    local raw  = serialize_proto(proto, sxor_byte)
    local blob = utils.aes256_ctr(raw, key, nonce)
    local b85_blob = utils.base85_pack(blob)   -- RLE + Base85 custom packing

    -- ── 2. Generate random identifiers for all locals ───────────────────────
    -- We need ~80 unique names for VM internals
    local N  = utils.rand_names(200)
    local ni = 0
    local function vn()   -- "variable name"
        ni = ni + 1
        return N[ni]
    end
    local v = {}  -- names table: all vn()-allocated identifiers

    -- Core names
    v.vExec = vn()   -- main execute function
    v.vDecrypt = vn()   -- RC4 decrypt function
    v.vKey = vn()   -- RC4 key string
    v.vBlob = vn()   -- encrypted bytecode blob
    v.vProto = vn()   -- top-level proto after deserialization
    v.vEnv = vn()   -- _ENV box

    -- Deserializer internals
    v.dPos = vn()
    v.dData = vn()
    v.dRb = vn()   -- read byte
    v.dRi32 = vn()   -- read i32
    v.dRi64 = vn()   -- read i64
    v.dRf64 = vn()   -- read f64
    v.dRstr = vn()   -- read string

    -- AES-256-CTR inline variables
    v.aesSbox = vn()   -- S-box table name
    v.aesXt = vn()   -- xtime helper function name
    v.aesKe = vn()   -- key expand function name
    v.aesEb = vn()   -- block encrypt function name
    v.vNonce = vn()   -- nonce variable name
    -- SHA-256 inline variables
    v.shaFn = vn()   -- sha256 function name
    v.shaH = vn()   -- hash state name
    v.shaW = vn()   -- message schedule name
    -- Base85 inline decoder variables
    v.b91Alpha = vn()   -- alphabet string variable
    v.b91Dec = vn()   -- decoder function name
    v.b91Tbl = vn()   -- lookup table name
    v.b91V = vn()   -- v variable
    v.b91B = vn()   -- b variable
    v.b91N_ = vn()   -- n variable (trailing _ to avoid clash with Lua keyword)
    v.b91Out = vn()   -- output table
    v.b91P = vn()   -- p (decoded value) variable
    v.b91I = vn()   -- input parameter name
    -- (b85RleDec is now merged into b91Dec – no separate name needed)

    -- Execute function params/locals
    v.eProto = vn()
    v.eUpvals = vn()
    v.eVararg = vn()
    v.eRegs = vn()
    v.eTop = vn()
    v.ePc = vn()
    v.eCode = vn()
    v.eKst = vn()
    v.eProtos = vn()
    v.eArgs = vn()
    v.eInst = vn()
    v.eOp = vn()
    v.eA = vn()
    v.eB = vn()
    v.eC = vn()
    v.eBx = vn()
    v.eSBx = vn()
    v.eRk = vn()
    v.eCallArgs = vn()
    v.eNargs = vn()
    v.eResults = vn()
    v.eFn = vn()
    v.eNelem = vn()
    v.eSuvs = vn()
    v.eUv = vn()
    v.eSub = vn()
    v.eIdx = vn()
    v.eLim = vn()
    v.eStep = vn()
    v.eI = vn()
    -- anti-tamper names (atPayload is now the fixed string "superflow_bytecode")
    v.vStrXor = vn()   -- string-constant XOR key (second encryption layer)
    -- SHA-256 integrity check variable names
    v.atSha = vn()
    v.atShaExp = vn()
    -- Runtime anti-tamper variable names (avoid static signatures in output)
    v.atTrig = vn()
    v.atOk = vn()
    v.atRs = vn()
    v.atPart = vn()
    v.atFolder = vn()
    v.atPlayers = vn()
    v.atHttp = vn()
    v.atCf = vn()
    v.atT1 = vn()
    v.atT2 = vn()
    v.atGuidOk = vn()
    v.atGuid = vn()
    v.atChecks = vn()
    v.atPassed = vn()
    v.atChkVal = vn()
    v.atMaterialEnums = vn()
    v.atLighting = vn()
    v.atCheckVars = {}
    for i = 1, ANTI_TAMPER_CHECK_COUNT do
        v.atCheckVars[i] = vn()
    end
    -- Watermark variable name
    v.vWm = vn()
    -- Extra randomized temp names for emitted anti-tamper/decode/watermark/key assembly code
    v.atHashEnc = vn()
    v.atHashDec = vn()
    v.atHashI = vn()
    v.atErrEnc = vn()
    v.atErrDec = vn()
    v.atErrI = vn()
    v.atEnvTbl = vn()
    v.wmTbl = vn()
    v.wmI = vn()
    v.wmV = vn()
    v.keyTbl = vn()
    v.nonceTbl = vn()
    -- Bootstrap helper aliases
    v.bsToStr = vn()
    v.bsType = vn()
    v.bsPcall = vn()
    -- decoy function names
    v.vDecoy = vn()   -- decoy function (defined, never called)
    v.dkA = vn()
    v.dkB = vn()
    v.dkC = vn()
    v.dkD = vn()
    -- dispatch table VM state names
    v.vDispatch = vn()   -- opcode dispatch table
    v.eDone = vn()   -- execution-done flag
    v.eRetVals = vn()   -- return-values accumulator
    v.eRetN = vn()   -- number of return values
    -- Key/nonce split chunk names (multi-layer key protection)
    v.vKp1 = vn()   -- key bytes 1-8,  pre-XOR'd with chunk mask 1
    v.vKp2 = vn()   -- key bytes 9-16, pre-XOR'd with chunk mask 2
    v.vKp3 = vn()   -- key bytes 17-24,pre-XOR'd with chunk mask 3
    v.vKp4 = vn()   -- key bytes 25-32,pre-XOR'd with chunk mask 4
    v.vNp1 = vn()   -- nonce bytes 1-4, pre-XOR'd with nonce mask 1
    v.vNp2 = vn()   -- nonce bytes 5-8, pre-XOR'd with nonce mask 2
    v.vDk1 = vn()   -- decoy key fragment 1 (never used for real decryption)
    v.vDk2 = vn()   -- decoy key fragment 2 (never used for real decryption)
    -- Bitwise compat helpers: use randomized helper identifiers so fixed
    -- helper signatures don't appear in output.
    -- Helper names are randomized to reduce stable signatures in generated output.
    v.bXor, v.bNot, v.bAnd, v.bOr, v.bShl, v.bShr =
        vn(), vn(), vn(), vn(), vn(), vn()
    v.vPack = vn()       -- table.pack compat
    v.vUnpack = vn()     -- table.unpack compat
    -- Binary codec helpers for runtimes without string.pack/unpack (e.g. Luau)
    v.rdU4le = vn()
    v.rdI4le = vn()
    v.rdF64le = vn()
    v.wrU4be = vn()

    -- Helper: emit an obfuscated integer expression using the runtime v.bXor function
    -- so no ~ operator appears in the generated output (Luau/Lua 5.1 compatible).
    local function _obfInt(n)
        local mode = math.random(0, 5)
        if mode == 0 then
            return utils.obfuscate_int_deep(n, v.bXor)
        elseif mode == 1 then
            return utils.obfuscate_int_triple(n, v.bXor)
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
            return string.format("%s(%s,255)", v.bAnd, _obfInt(n))
        else
            return string.format("(%s%%256)", _obfInt(n))
        end
    end
    -- _obfLitStr: emit a self-contained IIFE that recovers the original string at runtime.
    -- Two encoding strategies are chosen at random per call to break repetitive patterns:
    --   Strategy 0 (rolling XOR): cipher[i] = plain[i] XOR key[(i-1)%klen+1]
    --     decode: v.bXor(d[i], k[(i-1)%#k+1])
    --   Strategy 1 (rolling add-sub): cipher[i] = (plain[i] + key[(i-1)%klen+1]) % 256
    --     decode: (d[i] - k[(i-1)%#k+1]) % 256  (pure arithmetic, no v.bXor)
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
            -- Decode: v.bXor(d[i], k[(i-1)%#k+1])
            local decLoop = "};local _o={};for _i=1,#_d do _o[_i]=string.char("
                         .. v.bXor .. "(_d[_i],_k[(_i-1)%#_k+1]))end;return table.concat(_o)end)()"
            return "(function()local _k={" .. kArr .. "};local _d={" .. dArr .. decLoop
        else
            -- Decode: (d[i] - k[(i-1)%#k+1]) % 256 — pure arithmetic, no v.bXor call
            local decLoop = "};local _o={};for _i=1,#_d do _o[_i]=string.char((_d[_i]-_k[(_i-1)%#_k+1])%256)end;return table.concat(_o)end)()"
            return "(function()local _k={" .. kArr .. "};local _d={" .. dArr .. decLoop
        end
    end
    -- Like _obfLitStr but emits only plain arithmetic (no v.bAnd/v.bXor references).
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
                indent, v1, a, b, v2, v.bXor, v1, v1, v2, v1, v1, math.random(1, 0xFF))
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
                indent, v1, x, v2, y, v3, v.bXor, v1, v2, v.bXor, v3, v1, v2, v.bOr, v2)
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
        -- form 11: integer division identity (no v.bXor) – b * (a // b) == a when divisible
        function(indent)
            local v1, v2 = jpick2()
            local b = math.random(2, 9)
            local q = math.random(1, 100)
            local a = q * b  -- a is always divisible by b, so a // b == q
            return string.format(
                "%sdo local %s=%d;local %s=%s//%d;if %s~=%d then %s=%s*0 end end\n",
                indent, v1, a, v2, v1, b, v2, q, v1, v1)
        end,
        -- form 12: string.byte + string.char round-trip identity (no v.bXor)
        function(indent)
            local v1, v2 = jpick2()
            local bval = math.random(65, 90)  -- ASCII A-Z
            return string.format(
                "%sdo local %s=string.char(%d);local %s=string.byte(%s);if %s~=%d then %s=nil end end\n",
                indent, v1, bval, v2, v1, v2, bval, v1)
        end,
        -- form 13: math.floor identity – floor of an integer is itself (no v.bXor)
        function(indent)
            local v1 = jpick()
            local n = math.random(5, 9999)
            return string.format(
                "%sdo local %s=%d;if math.floor(%s)~=%s then %s=%s+1 end end\n",
                indent, v1, n, v1, v1, v1, v1)
        end,
        -- form 14: tostring + # length identity (no v.bXor)
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
    -- ── Base85-encoded payload declared as local inside the wrapper function ──────────
    src[#src+1] = emit_payload_b85(b85_blob) .. "\n"
    LF("local %s=tostring;local %s=type;local %s=pcall", v.bsToStr, v.bsType, v.bsPcall)
    LF("local %s=(table and table.pack) or function(...) return {n=select('#', ...),...} end", v.vPack)
    LF("local %s=(table and table.unpack) or unpack", v.vUnpack)
    LF("if type(%s)~='function' then local function _up(t,i,j) i=i or 1;j=j or #t;if i>j then return end;return t[i],_up(t,i+1,j) end;%s=_up end", v.vUnpack, v.vUnpack)
    -- Bitwise compat: use bit32 library if available (Roblox Luau), otherwise
    -- fallback to portable arithmetic helpers (no dynamic load/loadstring).
    LF("local %s,%s,%s,%s,%s,%s", v.bXor,v.bNot,v.bAnd,v.bOr,v.bShl,v.bShr)
    LF("local b,c,d,e,f,g=%s,%s,%s,%s,%s,%s",
       _earlyLitStr("bxor"),_earlyLitStr("bnot"),_earlyLitStr("band"),_earlyLitStr("bor"),_earlyLitStr("lshift"),_earlyLitStr("rshift"))
    LF("local bit32Available=type(bit32)=='table' and type(bit32[b])=='function' and type(bit32[c])=='function' and type(bit32[d])=='function' and type(bit32[e])=='function'")
    LF("if bit32Available then")
    LF("  %s=bit32[b];%s=bit32[c];%s=bit32[d];%s=bit32[e]", v.bXor,v.bNot,v.bAnd,v.bOr)
    -- bit32.lshift and bit32.rshift may be absent in some Roblox Luau builds.
    -- Fall back to a math-based equivalent using bit32.band (always present).
    LF("  %s=bit32[f] or function(a,b) if b>=32 then return 0 end;a=bit32[d](a,0xFFFFFFFF);for _j=1,b do a=bit32[d](a+a,0xFFFFFFFF) end;return a end", v.bShl)
    LF("  %s=bit32[g] or function(a,b) if b>=32 then return 0 end;a=bit32[d](a,0xFFFFFFFF);for _j=1,b do a=math.floor(a/2) end;return a end", v.bShr)
    LF("else")
    LF("  local _MOD=4294967296")
    LF("  local function _u32(x) x=x%%_MOD if x<0 then x=x+_MOD end return x end")
    LF("  local function _band(a,b) a=_u32(a);b=_u32(b);local r=0;local m=1;for _i=1,32 do local aa=a%%2;local bb=b%%2;if aa==1 and bb==1 then r=r+m end;a=(a-aa)/2;b=(b-bb)/2;m=m*2 end;return _u32(r) end")
    LF("  local function _bor(a,b) a=_u32(a);b=_u32(b);local r=0;local m=1;for _i=1,32 do local aa=a%%2;local bb=b%%2;if aa==1 or bb==1 then r=r+m end;a=(a-aa)/2;b=(b-bb)/2;m=m*2 end;return _u32(r) end")
    LF("  local function _bxor(a,b) a=_u32(a);b=_u32(b);local r=0;local m=1;for _i=1,32 do local aa=a%%2;local bb=b%%2;if aa~=bb then r=r+m end;a=(a-aa)/2;b=(b-bb)/2;m=m*2 end;return _u32(r) end")
    LF("  local function _bnot(a) return _u32(4294967295-_u32(a)) end")
    LF("  local function _bshl(a,b) a=_u32(a);if b<=0 then return a end;if b>=32 then return 0 end;return _u32(a*(2^b)) end")
    LF("  local function _bshr(a,b) a=_u32(a);if b<=0 then return a end;if b>=32 then return 0 end;return math.floor(a/(2^b)) end")
    LF("  %s=_bxor;%s=_bnot;%s=_band;%s=_bor;%s=_bshl;%s=_bshr", v.bXor, v.bNot, v.bAnd, v.bOr, v.bShl, v.bShr)
    LF("end")
    -- Binary helpers: avoid hard dependency on string.pack/unpack at runtime.
    LF("local function %s(_s,_p) local _b1,_b2,_b3,_b4=_s:byte(_p,_p+3);return _b1+_b2*256+_b3*65536+_b4*16777216,_p+4 end", v.rdU4le)
    LF("local function %s(_s,_p) local _v,_np=%s(_s,_p);if _v>=2147483648 then _v=_v-4294967296 end;return _v,_np end", v.rdI4le, v.rdU4le)
    LF("local function %s(_s,_p)", v.rdF64le)
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
    LF("local function %s(_v) return string.char(%s(%s(_v,24),255),%s(%s(_v,16),255),%s(%s(_v,8),255),%s(_v,255)) end", v.wrU4be, v.bAnd, v.bShr, v.bAnd, v.bShr, v.bAnd, v.bShr, v.bAnd)
    -- Junk block at top of do-scope (dead computations, not reachable by any real code path)
    src[#src+1] = junk_block("", math.random(4, 8))
    -- ── Combined Luraph-style B85+RLE chain decoder ─────────────────────────────
    -- 8 distinct random state constants (per-build, hex/decimal mixed at emit time).
    do
        local _cUsed = {}
        local function _cSt()
            local sv
            repeat sv = math.random(0x10, 0xFF) until not _cUsed[sv]
            _cUsed[sv] = true
            return sv
        end
        -- State semantics (values random per-build):
        local CST_B85_CHK  = _cSt()   -- check if more B85 input
        local CST_B85_FILL = _cSt()   -- fill one char into group
        local CST_B85_EMIT = _cSt()   -- decode 5-char group to bytes
        local CST_B85_DONE = _cSt()   -- B85 finished → begin RLE
        local CST_RLE_CTRL = _cSt()   -- read RLE control byte
        local CST_RLE_LIT  = _cSt()   -- literal-copy segment
        local CST_RLE_RUN  = _cSt()   -- run-expand segment
        local CST_CHAIN_END= _cSt()   -- done (break)

        -- Format a state constant with visual variety (mix hex / decimal representations).
        local function stL(sv)
            local r = math.random(1, 5)
            if     r == 1 then return string.format("0x%02X", sv)
            elseif r == 2 then return string.format("0x%02x", sv)
            elseif r == 3 then return tostring(sv)
            elseif r == 4 then return string.format("(0x%X+0)", sv)
            else                return string.format("0X%02X", sv)
            end
        end

        LF("local %s=%s", v.b91Alpha, _obfLitStr("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_`{|}~"))
        LF("local %s={}", v.b91Tbl)
        LF("for _i=1,#%s do %s[%s:byte(_i)]=_i-1 end", v.b91Alpha, v.b91Tbl, v.b91Alpha)
        -- The chain function: one repeat…until false loop drives B85-decode then RLE-unpack.
        -- State variable: %s (random name).  All internal temps use short _-prefixed names
        -- to match the Luraph interpreter aesthetic (H/j/O/Q pattern).
        LF("local function %s(%s)", v.b91Dec, v.b91I)
        LF("  local %s=%s", v.b91V, stL(CST_B85_CHK))
        LF("  local _j")                           -- general-purpose temp (visual noise)
        LF("  local %s=1", v.b91B)                 -- B85 read cursor in payload
        LF("  local %s={84,84,84,84,84}", v.b91Out) -- reuse b91Out as the B85 group buffer
        LF("  local %s=0", v.b91N_)    -- B85 group size (0-5)
        LF("  local %s=1", v.b91P)    -- B85 fill index
        LF("  local _acc=0")          -- B85 group accumulator
        LF("  local _rr={}")          -- B85 decoded bytes accumulator (table until B85_DONE, then string)
        LF("  local _ri,_rc")         -- RLE: current position, current run/lit count
        LF("  local _ro={}")          -- RLE output table
        LF("  repeat")
        -- STATE: B85_CHK — check if payload has more chars
        LF("    if %s==%s then", v.b91V, stL(CST_B85_CHK))
        LF("      if %s>#%s then %s=%s", v.b91B, v.b91I, v.b91V, stL(CST_B85_DONE))
        LF("      else %s[1],%s[2],%s[3],%s[4],%s[5]=84,84,84,84,84", v.b91Out,v.b91Out,v.b91Out,v.b91Out,v.b91Out)
        LF("        %s=math.min(5,#%s-%s+1);%s=1;%s=%s", v.b91N_, v.b91I, v.b91B, v.b91P, v.b91V, stL(CST_B85_FILL))
        LF("      end")
        -- STATE: B85_FILL — fill one char per iteration into the group buffer
        LF("    elseif %s==%s then", v.b91V, stL(CST_B85_FILL))
        LF("      if %s<=%s then", v.b91P, v.b91N_)
        LF("        local _ch=%s[%s:byte(%s+%s-1)]", v.b91Tbl, v.b91I, v.b91B, v.b91P)
        LF("        if _ch==nil then break end")
        LF("        %s[%s]=_ch;%s=%s+1", v.b91Out, v.b91P, v.b91P, v.b91P)
        LF("      else %s=%s+%s;%s=%s end", v.b91B, v.b91B, v.b91N_, v.b91V, stL(CST_B85_EMIT))
        -- STATE: B85_EMIT — decode the filled 5-char group into raw bytes
        LF("    elseif %s==%s then", v.b91V, stL(CST_B85_EMIT))
        LF("      _acc=%s[1];for _k=2,5 do _acc=_acc*85+%s[_k] end", v.b91Out, v.b91Out)
        LF("      local _v1=%s(%s(_acc,%s),255)", v.bAnd, v.bShr, _obfInt(24))
        LF("      local _v2=%s(%s(_acc,%s),255)", v.bAnd, v.bShr, _obfInt(16))
        LF("      local _v3=%s(%s(_acc,%s),255)", v.bAnd, v.bShr, _obfInt(8))
        LF("      local _v4=%s(_acc,255)", v.bAnd)
        LF("      if %s>4 then _rr[#_rr+1]=string.char(_v1,_v2,_v3,_v4)", v.b91N_)
        LF("      elseif %s>3 then _rr[#_rr+1]=string.char(_v1,_v2,_v3)", v.b91N_)
        LF("      elseif %s>2 then _rr[#_rr+1]=string.char(_v1,_v2)", v.b91N_)
        LF("      elseif %s>1 then _rr[#_rr+1]=string.char(_v1) end", v.b91N_)
        LF("      %s=%s", v.b91V, stL(CST_B85_CHK))
        -- STATE: B85_DONE — B85 phase finished; initialise RLE phase
        LF("    elseif %s==%s then", v.b91V, stL(CST_B85_DONE))
        LF("      _j=table.concat(_rr);_rr=_j;_j=nil;_ri=1;_ro={};%s=%s", v.b91V, stL(CST_RLE_CTRL))
        -- STATE: RLE_CTRL — read one RLE control byte; branch to lit or run
        LF("    elseif %s==%s then", v.b91V, stL(CST_RLE_CTRL))
        LF("      if _ri>#_rr then %s=%s", v.b91V, stL(CST_CHAIN_END))
        LF("      else local _t=_rr:byte(_ri);_ri=_ri+1")
        LF("        if _t<128 then _rc=_t+1;%s=%s else _rc=_t-127;%s=%s end", v.b91V, stL(CST_RLE_LIT), v.b91V, stL(CST_RLE_RUN))
        LF("      end")
        -- STATE: RLE_LIT — copy a literal segment verbatim
        LF("    elseif %s==%s then", v.b91V, stL(CST_RLE_LIT))
        LF("      _ro[#_ro+1]=_rr:sub(_ri,_ri+_rc-1);_ri=_ri+_rc;%s=%s", v.b91V, stL(CST_RLE_CTRL))
        -- STATE: RLE_RUN — expand a run-length segment
        LF("    elseif %s==%s then", v.b91V, stL(CST_RLE_RUN))
        LF("      _ro[#_ro+1]=string.rep(_rr:sub(_ri,_ri),_rc);_ri=_ri+1;%s=%s", v.b91V, stL(CST_RLE_CTRL))
        -- STATE: CHAIN_END — all phases done; exit loop
        LF("    elseif %s==%s then break end", v.b91V, stL(CST_CHAIN_END))
        LF("  until false")
        LF("  return table.concat(_ro)")
        LF("end")
    end
    src[#src+1] = junk_block("", math.random(3, 6))
    -- ── Emit inline AES-256-CTR decrypt ─────────────────────────────────────
    -- S-box table literal
    local sbox_vals = {0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16}
    -- XOR all S-box entries with a random session mask so the table is not
    -- recognisable as the standard AES S-box.  An inline loop unmasks at runtime.
    local sbox_mask = math.random(1, 255)
    local sbox_strs = {}
    for i = 1, #sbox_vals do sbox_strs[i] = tostring(sbox_vals[i] ~ sbox_mask) end
    LF("local %s={[0]=%s}", v.aesSbox, table.concat(sbox_strs, ","))
    LF("do local _m=%s;for _i=0,255 do %s[_i]=%s(%s[_i],_m) end end",
       _obfInt(sbox_mask), v.aesSbox, v.bXor, v.aesSbox)
    LF("local function %s(_a) return %s(%s(%s(_a,1),(_a>=0x80 and 0x1b or 0)),0xFF) end", v.aesXt, v.bAnd, v.bXor, v.bShl)
    LF("local function %s(_k)", v.aesKe)
    LF("  local _w={}")
    LF("  for _i=0,7 do _w[_i]=%s(%s(%s(%s(_k:byte(_i*4+1),24),%s(_k:byte(_i*4+2),16)),%s(_k:byte(_i*4+3),8)),_k:byte(_i*4+4)) end", v.bOr,v.bOr,v.bOr,v.bShl,v.bShl,v.bShl)
    -- Mask AES round constants (Rcon) so they don't fingerprint AES key schedule.
    do
        local rc_raw  = {0x01000000,0x02000000,0x04000000,0x08000000,0x10000000,0x20000000,0x40000000}
        local rc_mask = math.random(1, 0x3FFFFFFF)
        local rc_strs = {}
        for i = 1, 7 do rc_strs[i] = string.format("[%d]=%d", i, (rc_raw[i] ~ rc_mask) & 0xFFFFFFFF) end
        LF("  local _rc={%s}", table.concat(rc_strs, ","))
        LF("  do local _rm=%s;for _i=1,7 do _rc[_i]=%s(%s(_rc[_i],_rm),0xFFFFFFFF) end end",
           _obfInt(rc_mask), v.bAnd, v.bXor)
    end
    LF("  for _i=8,59 do")
    LF("    local _t=_w[_i-1]")
    LF("    if _i%%8==0 then")
    LF("      _t=%s(%s(%s(_t,8),%s(_t,24)),0xFFFFFFFF)", v.bAnd,v.bOr,v.bShl,v.bShr)
    LF("      _t=%s(%s(%s(%s(%s[%s(%s(_t,24),0xFF)],24),%s(%s[%s(%s(_t,16),0xFF)],16)),%s(%s[%s(%s(_t,8),0xFF)],8)),%s[%s(_t,0xFF)])", v.bOr,v.bOr,v.bOr,v.bShl,v.aesSbox,v.bAnd,v.bShr,v.bShl,v.aesSbox,v.bAnd,v.bShr,v.bShl,v.aesSbox,v.bAnd,v.bShr,v.aesSbox,v.bAnd)
    LF("      _t=%s(%s(_t,_rc[_i//8]),0xFFFFFFFF)", v.bAnd,v.bXor)
    LF("    elseif _i%%8==4 then")
    LF("      _t=%s(%s(%s(%s(%s[%s(%s(_t,24),0xFF)],24),%s(%s[%s(%s(_t,16),0xFF)],16)),%s(%s[%s(%s(_t,8),0xFF)],8)),%s[%s(_t,0xFF)])", v.bOr,v.bOr,v.bOr,v.bShl,v.aesSbox,v.bAnd,v.bShr,v.bShl,v.aesSbox,v.bAnd,v.bShr,v.bShl,v.aesSbox,v.bAnd,v.bShr,v.aesSbox,v.bAnd)
    LF("    end")
    LF("    _w[_i]=%s(%s(_w[_i-8],_t),0xFFFFFFFF)", v.bAnd,v.bXor)
    LF("  end")
    LF("  return _w")
    LF("end")
    LF("local function %s(_blk,_rk)", v.aesEb)
    LF("  local _s={}")
    LF("  for _i=0,15 do _s[_i]=_blk:byte(_i+1) end")
    LF("  for _c=0,3 do local _w=_rk[_c];_s[_c*4]=%s(_s[_c*4],%s(%s(_w,24),0xFF));_s[_c*4+1]=%s(_s[_c*4+1],%s(%s(_w,16),0xFF));_s[_c*4+2]=%s(_s[_c*4+2],%s(%s(_w,8),0xFF));_s[_c*4+3]=%s(_s[_c*4+3],%s(_w,0xFF)) end", v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd)
    LF("  for _r=1,13 do")
    LF("    for _i=0,15 do _s[_i]=%s[_s[_i]] end", v.aesSbox)
    LF("    local _t;_t=_s[1];_s[1]=_s[5];_s[5]=_s[9];_s[9]=_s[13];_s[13]=_t")
    LF("    _t=_s[2];local _t2=_s[6];_s[2]=_s[10];_s[6]=_s[14];_s[10]=_t;_s[14]=_t2")
    LF("    _t=_s[3];_s[3]=_s[15];_s[15]=_s[11];_s[11]=_s[7];_s[7]=_t")
    LF("    for _c=0,3 do")
    LF("      local _a0,_a1,_a2,_a3=_s[_c*4],_s[_c*4+1],_s[_c*4+2],_s[_c*4+3]")
    LF("      _s[_c*4]=%s(%s(%s(%s(%s(_a0),%s(_a1)),_a1),_a2),_a3)", v.bXor,v.bXor,v.bXor,v.bXor,v.aesXt,v.aesXt)
    LF("      _s[_c*4+1]=%s(%s(%s(%s(_a0,%s(_a1)),%s(_a2)),_a2),_a3)", v.bXor,v.bXor,v.bXor,v.bXor,v.aesXt,v.aesXt)
    LF("      _s[_c*4+2]=%s(%s(%s(%s(_a0,_a1),%s(_a2)),%s(_a3)),_a3)", v.bXor,v.bXor,v.bXor,v.bXor,v.aesXt,v.aesXt)
    LF("      _s[_c*4+3]=%s(%s(%s(%s(%s(_a0),_a0),_a1),_a2),%s(_a3))", v.bXor,v.bXor,v.bXor,v.bXor,v.aesXt,v.aesXt)
    LF("    end")
    LF("    for _c=0,3 do local _w=_rk[_r*4+_c];_s[_c*4]=%s(_s[_c*4],%s(%s(_w,24),0xFF));_s[_c*4+1]=%s(_s[_c*4+1],%s(%s(_w,16),0xFF));_s[_c*4+2]=%s(_s[_c*4+2],%s(%s(_w,8),0xFF));_s[_c*4+3]=%s(_s[_c*4+3],%s(_w,0xFF)) end", v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd)
    LF("  end")
    LF("  for _i=0,15 do _s[_i]=%s[_s[_i]] end", v.aesSbox)
    LF("  local _t;_t=_s[1];_s[1]=_s[5];_s[5]=_s[9];_s[9]=_s[13];_s[13]=_t")
    LF("  _t=_s[2];local _t2=_s[6];_s[2]=_s[10];_s[6]=_s[14];_s[10]=_t;_s[14]=_t2")
    LF("  _t=_s[3];_s[3]=_s[15];_s[15]=_s[11];_s[11]=_s[7];_s[7]=_t")
    LF("  for _c=0,3 do local _w=_rk[56+_c];_s[_c*4]=%s(_s[_c*4],%s(%s(_w,24),0xFF));_s[_c*4+1]=%s(_s[_c*4+1],%s(%s(_w,16),0xFF));_s[_c*4+2]=%s(_s[_c*4+2],%s(%s(_w,8),0xFF));_s[_c*4+3]=%s(_s[_c*4+3],%s(_w,0xFF)) end", v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd,v.bShr,v.bXor,v.bAnd)
    LF("  local _o={};for _i=0,15 do _o[_i+1]=string.char(_s[_i]) end;return table.concat(_o)")
    LF("end")
    LF("local function %s(_d,_k,_nn)", v.vDecrypt)
    LF("  local _rk=%s(_k)", v.aesKe)
    LF("  local _out={};local _ctr=0;local _pos=1;local _dl=#_d")
    LF("  while _pos<=_dl do")
    LF("    local _cb=_nn..string.char(_ctr%%256,(_ctr//256)%%256,(_ctr//65536)%%256,(_ctr//16777216)%%256)..\"\\0\\0\\0\\0\"")
    LF("    local _ks=%s(_cb,_rk)", v.aesEb)
    LF("    local _bl=math.min(16,_dl-_pos+1)")
    LF("    for _i=1,_bl do _out[#_out+1]=string.char(%s(_d:byte(_pos+_i-1),_ks:byte(_i))) end", v.bXor)
    LF("    _pos=_pos+16;_ctr=_ctr+1")
    LF("  end")
    LF("  return table.concat(_out)")
    LF("end")
    -- Junk block between AES function and deserializer
    src[#src+1] = junk_block("", math.random(4, 8))
    -- Decoy function: looks like a secondary hash/encode but is never called.
    -- Its body is all dead computation (XOR mixing on random constants).
    do
        local da = math.random(1, 0x7FFF)
        local db = math.random(1, 0x7FFF)
        local dc = math.random(1, 0xFFFF)
        LF("local function %s(%s)", v.vDecoy, v.dkA)
        LF("  local %s=%d local %s=%d local %s=%s(%s,%d)", v.dkB, da, v.dkC, db, v.dkD, v.bXor, v.dkA, dc)
        LF("  for %s=1,#%s do %s=%s(%s,string.byte(%s,%s)) end", v.dkB, v.dkA, v.dkC, v.bXor, v.dkC, v.dkA, v.dkB)
        LF("  return %s(%s,%s)", v.bXor, v.dkC, v.dkD)
        LF("end")
    end
    -- Extra junk between decoy and deserializer
    src[#src+1] = junk_block("", math.random(3, 6))

    -- Deserializer
    LF("local %s", v.dPos)
    LF("local %s", v.dData)
    LF("local function %s() local v=%s:byte(%s);%s=%s+1;return v end", v.dRb, v.dData, v.dPos, v.dPos, v.dPos)
    LF("local function %s() local v,p=%s(%s,%s);%s=p;return v end", v.dRi32, v.rdI4le, v.dData, v.dPos, v.dPos)
    -- v.dRi64: decode via two LE u32 words (works on Lua/Luau without string.unpack).
    LF("local function %s()", v.dRi64)
    LF("  local _lo,_p1=%s(%s,%s);%s=_p1", v.rdU4le, v.dData, v.dPos, v.dPos)
    LF("  local _hi,_p2=%s(%s,%s);%s=_p2", v.rdU4le, v.dData, v.dPos, v.dPos)
    LF("  if _hi==0 then return _lo end")
    LF("  local _v=_lo+_hi*(2^32)")
    LF("  if _hi>=(2^31) then _v=_v-(2^64) end")
    LF("  return _v")
    LF("end")
    LF("local function %s() local v,p=%s(%s,%s);%s=p;return v end",  v.dRf64, v.rdF64le, v.dData, v.dPos, v.dPos)
    -- v.dRstr: emit once (correctly advancing pos)
    LF("local function %s() local _n,_p=%s(%s,%s);%s=_p;local _s=%s:sub(%s,%s+_n-1);%s=%s+_n;return _s end",
       v.dRstr, v.rdI4le, v.dData, v.dPos, v.dPos, v.dData, v.dPos, v.dPos, v.dPos, v.dPos)

    -- Emit the string-constant XOR key as an obfuscated math expression so it
    -- is not visible as a plain integer literal in the output.
    do
        local sx_a = math.random(0, 255)
        local sx_b = sx_a ~ sxor_byte  -- XOR split: sx_a ~ sx_b == sxor_byte
        local sx_p = math.random(1, 0xFFFF)
        local sx_q = math.random(1, 0xFFFF)
        LF("local %s=(%s(%d,%d)+%d+%d-%d-%d)", v.vStrXor, v.bXor, sx_a, sx_b, sx_p, sx_q, sx_p, sx_q)
    end

    -- Recursive prototype loader (declared forward)
    v.vLoadProto = vn()
    LF("local %s", v.vLoadProto)
    LF("%s=function()", v.vLoadProto)
    LF("  local p={}")
    LF("  p.numparams=%s()",   v.dRb)
    LF("  p.is_vararg=%s()",   v.dRb)
    LF("  p.maxstacksize=%s()", v.dRb)
    LF("  local sc=%s(); p.sizecode=sc", v.dRi32)
    LF("  local code={}; p.code=code")
    LF("  for i=0,sc-1 do local _v,_p=%s(%s,%s);code[i]=_v;%s=_p end",
       v.rdU4le, v.dData, v.dPos, v.dPos)
    -- Constants
    LF("  local sk=%s(); p.sizek=sk", v.dRi32)
    LF("  local k={}; p.k=k")
    LF("  for i=0,sk-1 do")
    LF("    local t=%s()", v.dRb)
    LF("    if t==0 then k[i]=nil")
    LF("    elseif t==1 then k[i]=false")
    LF("    elseif t==2 then k[i]=true")
    LF("    elseif t==3 then k[i]=%s()", v.dRi64)
    LF("    elseif t==4 then k[i]=%s()", v.dRf64)
    LF("    elseif t==5 then local _sx=%s();local _sd={};for _si=1,#_sx do _sd[_si]=string.char(%s(_sx:byte(_si),%s))end;k[i]=table.concat(_sd)", v.dRstr, v.bXor, v.vStrXor)
    LF("    end")
    LF("  end")
    -- Upvalues
    LF("  local su=%s(); p.sizeupvalues=su", v.dRi32)
    LF("  local uvs={}; p.upvals=uvs")
    LF("  for i=0,su-1 do uvs[i]={instack=%s(),idx=%s()} end", v.dRb, v.dRb)
    -- Nested protos
    LF("  local sp=%s(); p.sizep=sp", v.dRi32)
    LF("  local pp={}; p.p=pp")
    LF("  for i=0,sp-1 do pp[i]=%s() end", v.vLoadProto)
    LF("  return p")
    LF("end")
    -- Extra junk after deserializer/proto-loader
    src[#src+1] = junk_block("", math.random(3, 6))

    -- (dispatch table indexed by shuffled opcode – no separate revmap needed)
    -- Junk block after VM setup
    src[#src+1] = junk_block("", math.random(3, 6))

    -- The execute function (dispatch-table based)
    LF("local function %s(%s,%s,...)", v.vExec, v.eProto, v.eUpvals)
    LF("  local %s=%s(...)", v.eArgs, v.vPack)
    -- Junk at function entry
    src[#src+1] = junk_block("  ", math.random(2, 4))
    -- Allocate register boxes (auto-create missing boxes via metatable)
    LF("  local %s=setmetatable({},{__index=function(t,k) local b={};t[k]=b;return b end})", v.eRegs)
    LF("  for %s=0,%s.maxstacksize+63 do %s[%s]={} end", v.eI, v.eProto, v.eRegs, v.eI)
    -- Fill params
    LF("  for %s=0,%s.numparams-1 do %s[%s].v=%s[%s+1] end", v.eI, v.eProto, v.eRegs, v.eI, v.eArgs, v.eI)
    -- Vararg
    LF("  local %s={}", v.eVararg)
    LF("  if %s.is_vararg~=0 then", v.eProto)
    LF("    for %s=%s.numparams+1,%s.n do %s[#%s+1]=%s[%s] end",
       v.eI, v.eProto, v.eArgs, v.eVararg, v.eVararg, v.eArgs, v.eI)
    LF("  end")
    -- VM state locals
    LF("  local %s=0", v.ePc)
    LF("  local %s=-1", v.eTop)
    LF("  local %s=%s.code",   v.eCode,   v.eProto)
    LF("  local %s=%s.k",      v.eKst,    v.eProto)
    LF("  local %s=%s.p",      v.eProtos, v.eProto)
    -- Execution-done flag and return-value storage
    LF("  local %s=false", v.eDone)
    LF("  local %s={}", v.eRetVals)
    LF("  local %s=0", v.eRetN)
    -- rk helper: read register or constant
    LF("  local function %s(x) if x>=256 then return %s[x-256] else return %s[x].v end end",
       v.eRk, v.eKst, v.eRegs)

    -- ── Opcode dispatch table: one closure per opcode, indexed by real opcode ──
    LF("  local %s={}", v.vDispatch)
    -- Junk between table creation and first handler
    src[#src+1] = junk_block("  ", math.random(1, 2))

    -- [0] MOVE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v end",
       v.vDispatch, fwdmap[0], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA, v.eRegs,v.eB)
    -- [1] LOADK
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s] end",
       v.vDispatch, fwdmap[1], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA, v.eKst,v.eBx)
    -- [2] LOADKX  (next instruction is EXTRAARG carrying the index)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[2], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local _ni=%s[%s];%s=%s+1;%s[%s].v=%s[%s(_ni,6)]", v.eCode,v.ePc,v.ePc,v.ePc, v.eRegs,v.eA,v.eKst,v.bShr)
    LF("  end")
    -- [3] LOADBOOL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=(%s~=0);if %s~=0 then %s=%s+1 end end",
       v.vDispatch, fwdmap[3], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eB, v.eC,v.ePc,v.ePc)
    -- [4] LOADNIL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) for _i=%s,%s+%s do %s[_i].v=nil end end",
       v.vDispatch, fwdmap[4], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eA,v.eA,v.eB, v.eRegs)
    src[#src+1] = junk_block("  ", 1)   -- junk between handler groups
    -- [5] GETUPVAL (defensive: nil upval box → nil)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) local _u=%s[%s];%s[%s].v=_u and _u.v or nil end",
       v.vDispatch, fwdmap[5], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eUpvals,v.eB, v.eRegs,v.eA)
    -- [6] GETTABUP (defensive: missing upval box → nil; present box → normal indexing)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) local _u=%s[%s];%s[%s].v=_u and _u.v[%s(%s)] end",
       v.vDispatch, fwdmap[6], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eUpvals,v.eB, v.eRegs,v.eA, v.eRk,v.eC)
    -- [7] GETTABLE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v[%s(%s)] end",
       v.vDispatch, fwdmap[7], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA, v.eRegs,v.eB, v.eRk,v.eC)
    -- [8] SETTABUP (defensive: missing upval box → no-op; present box → normal indexing)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) local _u=%s[%s];if _u then _u.v[%s(%s)]=%s(%s) end end",
       v.vDispatch, fwdmap[8], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eUpvals,v.eA, v.eRk,v.eB, v.eRk,v.eC)
    -- [9] SETUPVAL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v end",
       v.vDispatch, fwdmap[9], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eUpvals,v.eB, v.eRegs,v.eA)
    -- [10] SETTABLE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v[%s(%s)]=%s(%s) end",
       v.vDispatch, fwdmap[10], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA, v.eRk,v.eB, v.eRk,v.eC)
    src[#src+1] = junk_block("  ", 1)
    -- [11] NEWTABLE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v={} end",
       v.vDispatch, fwdmap[11], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA)
    -- [12] SELF
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s+1].v=%s[%s].v;%s[%s].v=%s[%s].v[%s(%s)] end",
       v.vDispatch, fwdmap[12], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA, v.eRegs,v.eB, v.eRegs,v.eA, v.eRegs,v.eB, v.eRk,v.eC)
    -- [13..19] Arithmetic: ADD SUB MUL MOD POW DIV IDIV
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)+%s(%s) end", v.vDispatch,fwdmap[13],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)-%s(%s) end", v.vDispatch,fwdmap[14],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)*%s(%s) end", v.vDispatch,fwdmap[15],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)%%%s(%s) end",v.vDispatch,fwdmap[16],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)^%s(%s) end", v.vDispatch,fwdmap[17],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)/%s(%s) end", v.vDispatch,fwdmap[18],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s)//%s(%s) end",v.vDispatch,fwdmap[19],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRk,v.eB,v.eRk,v.eC)
    src[#src+1] = junk_block("  ", 1)
    -- [20..24] Bitwise: BAND BOR BXOR SHL SHR
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  v.vDispatch,fwdmap[20],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.bAnd,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  v.vDispatch,fwdmap[21],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.bOr, v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  v.vDispatch,fwdmap[22],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.bXor,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  v.vDispatch,fwdmap[23],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.bShl,v.eRk,v.eB,v.eRk,v.eC)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s(%s),%s(%s)) end",  v.vDispatch,fwdmap[24],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.bShr,v.eRk,v.eB,v.eRk,v.eC)
    -- [25..28] Unary: UNM BNOT NOT LEN
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=-%s[%s].v end",          v.vDispatch,fwdmap[25],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRegs,v.eB)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s(%s[%s].v) end",       v.vDispatch,fwdmap[26],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.bNot,v.eRegs,v.eB)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=not %s[%s].v end",  v.vDispatch,fwdmap[27],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRegs,v.eB)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=#%s[%s].v end",     v.vDispatch,fwdmap[28],v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRegs,v.eB)
    src[#src+1] = junk_block("  ", 1)
    -- [29] CONCAT
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[29], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local _t={}")
    LF("    for _i=%s,%s do _t[#_t+1]=tostring(%s[_i].v) end", v.eB,v.eC,v.eRegs)
    LF("    %s[%s].v=table.concat(_t)", v.eRegs,v.eA)
    LF("  end")
    -- [30] JMP  (modifies pc via upvalue – Lua closure upvalue sharing)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s=%s+%s end",
       v.vDispatch, fwdmap[30], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.ePc,v.ePc,v.eSBx)
    -- [31..33] Comparisons: EQ LT LE
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(%s(%s)==%s(%s))~=(%s~=0) then %s=%s+1 end end",
       v.vDispatch, fwdmap[31], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRk,v.eB,v.eRk,v.eC,v.eA,v.ePc,v.ePc)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(%s(%s)<%s(%s))~=(%s~=0) then %s=%s+1 end end",
       v.vDispatch, fwdmap[32], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRk,v.eB,v.eRk,v.eC,v.eA,v.ePc,v.ePc)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(%s(%s)<=%s(%s))~=(%s~=0) then %s=%s+1 end end",
       v.vDispatch, fwdmap[33], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRk,v.eB,v.eRk,v.eC,v.eA,v.ePc,v.ePc)
    -- [34] TEST
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) if(not not %s[%s].v)~=(%s~=0) then %s=%s+1 end end",
       v.vDispatch, fwdmap[34], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eC,v.ePc,v.ePc)
    -- [35] TESTSET
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[35], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    if(not not %s[%s].v)==(%s~=0) then %s[%s].v=%s[%s].v else %s=%s+1 end",
       v.eRegs,v.eB,v.eC, v.eRegs,v.eA,v.eRegs,v.eB, v.ePc,v.ePc)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [36] CALL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[36], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local %s=%s[%s].v", v.eFn,v.eRegs,v.eA)
    LF("    local %s={}", v.eCallArgs)
    LF("    local %s=%s==0 and %s-%s or %s-1", v.eNargs,v.eB,v.eTop,v.eA,v.eB)
    LF("    for _i=1,%s do %s[_i]=%s[%s+_i].v end", v.eNargs,v.eCallArgs,v.eRegs,v.eA)
    LF("    local %s=%s(%s(%s(%s,1,%s)))", v.eResults,v.vPack,v.eFn,v.vUnpack,v.eCallArgs,v.eNargs)
    LF("    if %s==0 then", v.eC)
    LF("      for _i=0,%s.n-1 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       v.eResults,v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA,v.eResults)
    LF("      %s=%s+%s.n-1", v.eTop,v.eA,v.eResults)
    LF("    else")
    LF("      for _i=0,%s-2 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       v.eC,v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA,v.eResults)
    LF("    end")
    LF("  end")
    -- [37] TAILCALL (simulated as call + done; avoids TCO loss of semantics)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[37], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local %s=%s[%s].v", v.eFn,v.eRegs,v.eA)
    LF("    local %s={}", v.eCallArgs)
    LF("    local %s=%s==0 and %s-%s or %s-1", v.eNargs,v.eB,v.eTop,v.eA,v.eB)
    LF("    for _i=1,%s do %s[_i]=%s[%s+_i].v end", v.eNargs,v.eCallArgs,v.eRegs,v.eA)
    LF("    local %s=%s(%s(%s(%s,1,%s)))", v.eResults,v.vPack,v.eFn,v.vUnpack,v.eCallArgs,v.eNargs)
    LF("    %s=true;%s=%s.n", v.eDone,v.eRetN,v.eResults)
    LF("    for _i=1,%s do %s[_i]=%s[_i] end", v.eRetN,v.eRetVals,v.eResults)
    LF("  end")
    -- [38] RETURN
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[38], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    %s=true", v.eDone)
    LF("    if %s==1 then %s=0;return end", v.eB,v.eRetN)
    LF("    local %s=%s==0 and %s or %s+%s-2", v.eNelem,v.eB,v.eTop,v.eA,v.eB)
    LF("    %s=0", v.eRetN)
    LF("    for _i=%s,%s do %s=%s+1;%s[%s]=%s[_i].v end", v.eA,v.eNelem,v.eRetN,v.eRetN,v.eRetVals,v.eRetN,v.eRegs)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [39] FORLOOP
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[39], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    %s[%s].v=%s[%s].v+%s[%s+2].v", v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA)
    LF("    local %s=%s[%s].v;local %s=%s[%s+1].v;local %s=%s[%s+2].v",
       v.eIdx,v.eRegs,v.eA, v.eLim,v.eRegs,v.eA, v.eStep,v.eRegs,v.eA)
    LF("    if(%s>0 and %s<=%s)or(%s<0 and %s>=%s) then %s=%s+%s;%s[%s+3].v=%s end",
       v.eStep,v.eIdx,v.eLim,v.eStep,v.eIdx,v.eLim, v.ePc,v.ePc,v.eSBx, v.eRegs,v.eA,v.eIdx)
    LF("  end")
    -- [40] FORPREP
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) %s[%s].v=%s[%s].v-%s[%s+2].v;%s=%s+%s end",
       v.vDispatch, fwdmap[40], v.eA,v.eB,v.eC,v.eBx,v.eSBx, v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA, v.ePc,v.ePc,v.eSBx)
    -- [41] TFORCALL
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[41], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local %s=%s(%s[%s].v(%s[%s+1].v,%s[%s+2].v))",
       v.eResults,v.vPack,v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA)
    LF("    for _i=1,%s do if not %s[%s+2+_i] then %s[%s+2+_i]={} end;%s[%s+2+_i].v=%s[_i] end",
       v.eC,v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA,v.eResults)
    LF("  end")
    -- [42] TFORLOOP
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)",v.vDispatch,fwdmap[42],v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    if %s[%s+1].v~=nil then %s[%s].v=%s[%s+1].v;%s=%s+%s end",
       v.eRegs,v.eA, v.eRegs,v.eA,v.eRegs,v.eA, v.ePc,v.ePc,v.eSBx)
    LF("  end")
    src[#src+1] = junk_block("  ", 1)
    -- [43] SETLIST
    -- LFIELDS_PER_FLUSH = 50 (matches Lua 5.3 lvm.c constant).
    -- When C==0 the block number is in the next EXTRAARG instruction's Ax field.
    -- Offset is (block_number - 1) * SETLIST_BATCH, consistent with the C!=0
    -- path: (C-1)*SETLIST_BATCH.
    local SETLIST_BATCH = 50
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[43], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local _off")
    LF("    if %s==0 then local _ni=%s[%s];%s=%s+1;_off=(%s(_ni,6)-1)*%d else _off=(%s-1)*%d end",
       v.eC,v.eCode,v.ePc,v.ePc,v.ePc,v.bShr,SETLIST_BATCH,v.eC,SETLIST_BATCH)
    LF("    local %s=%s==0 and %s-%s or %s", v.eNelem,v.eB,v.eTop,v.eA,v.eB)
    LF("    for _i=1,%s do %s[%s].v[_off+_i]=%s[%s+_i].v end", v.eNelem,v.eRegs,v.eA,v.eRegs,v.eA)
    LF("  end")
    -- [44] CLOSURE: captures suvs+proto-index via local aliases (safe even
    --              when v.eI is reused as a loop counter elsewhere)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[44], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    local %s=%s[%s]", v.eSub,v.eProtos,v.eBx)
    LF("    local %s={}", v.eSuvs)
    LF("    for _i=0,%s.sizeupvalues-1 do", v.eSub)
    LF("      local %s=%s.upvals[_i]", v.eUv,v.eSub)
    LF("      if %s.instack==1 then %s[_i]=%s[%s.idx]", v.eUv,v.eSuvs,v.eRegs,v.eUv)
    LF("      else local _u=%s[%s.idx];%s[_i]=_u or {} end", v.eUpvals,v.eUv,v.eSuvs)
    LF("    end")
    LF("    local _csuvs,_cbx=%s,%s", v.eSuvs,v.eBx)
    LF("    %s[%s].v=function(...) return %s(%s[_cbx],_csuvs,...) end", v.eRegs,v.eA,v.vExec,v.eProtos)
    LF("  end")
    -- [45] VARARG
    LF("  %s[%d]=function(%s,%s,%s,%s,%s)", v.vDispatch, fwdmap[45], v.eA,v.eB,v.eC,v.eBx,v.eSBx)
    LF("    if %s==0 then", v.eB)
    LF("      for _i=0,#%s-1 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       v.eVararg,v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA,v.eVararg)
    LF("      %s=%s+#%s-1", v.eTop,v.eA,v.eVararg)
    LF("    else")
    LF("      for _i=0,%s-2 do if not %s[%s+_i] then %s[%s+_i]={} end;%s[%s+_i].v=%s[_i+1] end",
       v.eB,v.eRegs,v.eA,v.eRegs,v.eA,v.eRegs,v.eA,v.eVararg)
    LF("    end")
    LF("  end")
    -- [46] EXTRAARG  (consumed by LOADKX/SETLIST; treated as no-op if reached alone)
    LF("  %s[%d]=function(%s,%s,%s,%s,%s) end", v.vDispatch, fwdmap[46], v.eA,v.eB,v.eC,v.eBx,v.eSBx)

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
    v.eMask63 = vn(); v.eMask255 = vn(); v.eMask511 = vn()
    v.eMask18 = vn(); v.eBias    = vn()
    v.eSh6 = vn(); v.eSh14   = vn(); v.eSh23 = vn()
    LF("  local %s=%s local %s=%s local %s=%s", v.eMask63,_m63, v.eMask255,_m255, v.eMask511,_m511)
    LF("  local %s=%s local %s=%s", v.eMask18,_m18, v.eBias,_bias)
    LF("  local %s=%s local %s=%s local %s=%s", v.eSh6,_sh6, v.eSh14,_sh14, v.eSh23,_sh23)

    -- ── Main fetch-decode-dispatch loop ──────────────────────────────────────
    LF("  while not %s do", v.eDone)
    LF("    local %s=%s[%s]", v.eInst,v.eCode,v.ePc)
    LF("    %s=%s+1", v.ePc,v.ePc)
    LF("    local %s=%s(%s,%s)", v.eOp,v.bAnd,v.eInst,v.eMask63)
    LF("    local %s=%s(%s(%s,%s),%s)",   v.eA,  v.bAnd,v.bShr,v.eInst,v.eSh6, v.eMask255)
    LF("    local %s=%s(%s(%s,%s),%s)",   v.eB,  v.bAnd,v.bShr,v.eInst,v.eSh23,v.eMask511)
    LF("    local %s=%s(%s(%s,%s),%s)",   v.eC,  v.bAnd,v.bShr,v.eInst,v.eSh14,v.eMask511)
    LF("    local %s=%s(%s(%s,%s),%s)",   v.eBx, v.bAnd,v.bShr,v.eInst,v.eSh14,v.eMask18)
    LF("    local %s=%s-%s",         v.eSBx,v.eBx,v.eBias)
    LF("    local %s=%s[%s]", "_dh_", v.vDispatch,v.eOp)
    LF("    if %s then %s(%s,%s,%s,%s,%s) else error(%s..tostring(%s),0) end", "_dh_","_dh_",v.eA,v.eB,v.eC,v.eBx,v.eSBx,_obfLitStr("Catify: unknown opcode "),v.eOp)
    LF("  end")
    LF("  return %s(%s,1,%s)", v.vUnpack,v.eRetVals,v.eRetN)
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
    -- Forward-declare v.vKey and v.vNonce; will be assigned just before decryption.
    LF("local %s", v.vKey)
    LF("local %s", v.vNonce)
    -- Key chunk 1 (bytes 1-8, each pre-XOR'd with km[1])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(bi) ~ km[1]) end
        LF("local %s=string.char(%s)", v.vKp1, table.concat(t, ","))
    end
    -- Key chunk 2 (bytes 9-16, each pre-XOR'd with km[2])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(8+bi) ~ km[2]) end
        LF("local %s=string.char(%s)", v.vKp2, table.concat(t, ","))
    end
    -- Key chunk 3 (bytes 17-24, each pre-XOR'd with km[3])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(16+bi) ~ km[3]) end
        LF("local %s=string.char(%s)", v.vKp3, table.concat(t, ","))
    end
    -- Key chunk 4 (bytes 25-32, each pre-XOR'd with km[4])
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(key:byte(24+bi) ~ km[4]) end
        LF("local %s=string.char(%s)", v.vKp4, table.concat(t, ","))
    end
    -- Nonce chunk 1 (bytes 1-4, each pre-XOR'd with nm[1])
    do
        local t = {}
        for bi = 1, 4 do t[bi] = _obfByte(nonce:byte(bi) ~ nm[1]) end
        LF("local %s=string.char(%s)", v.vNp1, table.concat(t, ","))
    end
    -- Nonce chunk 2 (bytes 5-8, each pre-XOR'd with nm[2])
    do
        local t = {}
        for bi = 1, 4 do t[bi] = _obfByte(nonce:byte(4+bi) ~ nm[2]) end
        LF("local %s=string.char(%s)", v.vNp2, table.concat(t, ","))
    end
    -- Decoy key fragments (random bytes, never used for actual decryption)
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(math.random(0, 255)) end
        LF("local %s=string.char(%s)", v.vDk1, table.concat(t, ","))
    end
    do
        local t = {}
        for bi = 1, 8 do t[bi] = _obfByte(math.random(0, 255)) end
        LF("local %s=string.char(%s)", v.vDk2, table.concat(t, ","))
    end

    -- Anti-tamper 1: SHA-256 integrity check of the encrypted blob
    -- Emit inline SHA-256 function
    local sha_k_vals = {0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2}
    -- XOR all 64 SHA-256 K constants with a random session mask so they are not
    -- recognisable as the standard SHA-256 round constants.
    local sha_k_mask = math.random(1, 0x3FFFFFFF)
    local sha_k_strs = {}
    for i = 1, 64 do sha_k_strs[i] = tostring((sha_k_vals[i] ~ sha_k_mask) & 0xFFFFFFFF) end
    LF("local function %s(_s)", v.shaFn)
    LF("  local function _rr(_x,_n) return %s(%s(%s(_x,_n),%s(_x,32-_n)),0xFFFFFFFF) end", v.bAnd,v.bOr,v.bShr,v.bShl)
    LF("  local _k={%s}", table.concat(sha_k_strs, ","))
    LF("  do local _m=%s;for _i=1,64 do _k[_i]=%s(%s(_k[_i],_m),0xFFFFFFFF) end end",
       _obfInt(sha_k_mask), v.bAnd, v.bXor)
    -- Mask SHA-256 initial hash values (IV) so they don't fingerprint SHA-256 init.
    do
        local sha_h_raw  = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}
        local sha_h_mask = math.random(1, 0x3FFFFFFF)
        local sha_h_strs = {}
        for i = 1, 8 do sha_h_strs[i] = tostring((sha_h_raw[i] ~ sha_h_mask) & 0xFFFFFFFF) end
        LF("  local %s={%s}", v.shaH, table.concat(sha_h_strs, ","))
        LF("  do local _hm=%s;for _i=1,8 do %s[_i]=%s(%s(%s[_i],_hm),0xFFFFFFFF) end end",
           _obfInt(sha_h_mask), v.shaH, v.bAnd, v.bXor, v.shaH)
    end
    LF("  local _len=#_s;local _bl=_len*8")
    LF("  local _pd=_s..'\\x80'")
    LF("  while #_pd%%64~=56 do _pd=_pd..'\\x00' end")
    LF("  _pd=_pd..%s(%s(%s(_bl,32),0xFFFFFFFF))..%s(%s(_bl,0xFFFFFFFF))", v.wrU4be,v.bAnd,v.bShr,v.wrU4be,v.bAnd)
    LF("  local %s={}", v.shaW)
    LF("  for _blk=1,#_pd,64 do")
    LF("    for _i=1,16 do local _o=_blk+(_i-1)*4;local _b1,_b2,_b3,_b4=_pd:byte(_o,_o+3);%s[_i]=%s(_b1*16777216+_b2*65536+_b3*256+_b4,0xFFFFFFFF) end", v.shaW, v.bAnd)
    LF("    for _i=17,64 do")
    LF("      local _s0=%s(%s(_rr(%s[_i-15],7),_rr(%s[_i-15],18)),%s(%s[_i-15],3))", v.bXor,v.bXor,v.shaW,v.shaW,v.bShr,v.shaW)
    LF("      local _s1=%s(%s(_rr(%s[_i-2],17),_rr(%s[_i-2],19)),%s(%s[_i-2],10))", v.bXor,v.bXor,v.shaW,v.shaW,v.bShr,v.shaW)
    LF("      %s[_i]=%s(%s[_i-16]+_s0+%s[_i-7]+_s1,0xFFFFFFFF)", v.shaW,v.bAnd,v.shaW,v.shaW)
    LF("    end")
    LF("    local _a,_b,_c,_d,_e,_f,_g,_hv=%s[1],%s[2],%s[3],%s[4],%s[5],%s[6],%s[7],%s[8]", v.shaH,v.shaH,v.shaH,v.shaH,v.shaH,v.shaH,v.shaH,v.shaH)
    LF("    for _i=1,64 do")
    LF("      local _S1=%s(%s(_rr(_e,6),_rr(_e,11)),_rr(_e,25))", v.bXor,v.bXor)
    LF("      local _ch=%s(%s(_e,_f),%s(%s(_e),_g))", v.bXor,v.bAnd,v.bAnd,v.bNot)
    LF("      local _t1=%s(_hv+_S1+_ch+_k[_i]+%s[_i],0xFFFFFFFF)", v.bAnd, v.shaW)
    LF("      local _S0=%s(%s(_rr(_a,2),_rr(_a,13)),_rr(_a,22))", v.bXor,v.bXor)
    LF("      local _maj=%s(%s(%s(_a,_b),%s(_a,_c)),%s(_b,_c))", v.bXor,v.bXor,v.bAnd,v.bAnd,v.bAnd)
    LF("      local _t2=%s(_S0+_maj,0xFFFFFFFF)", v.bAnd)
    LF("      _hv=_g;_g=_f;_f=_e;_e=%s(_d+_t1,0xFFFFFFFF);_d=_c;_c=_b;_b=_a;_a=%s(_t1+_t2,0xFFFFFFFF)", v.bAnd,v.bAnd)
    LF("    end")
    LF("    %s[1]=%s(%s[1]+_a,0xFFFFFFFF);%s[2]=%s(%s[2]+_b,0xFFFFFFFF)", v.shaH,v.bAnd,v.shaH,v.shaH,v.bAnd,v.shaH)
    LF("    %s[3]=%s(%s[3]+_c,0xFFFFFFFF);%s[4]=%s(%s[4]+_d,0xFFFFFFFF)", v.shaH,v.bAnd,v.shaH,v.shaH,v.bAnd,v.shaH)
    LF("    %s[5]=%s(%s[5]+_e,0xFFFFFFFF);%s[6]=%s(%s[6]+_f,0xFFFFFFFF)", v.shaH,v.bAnd,v.shaH,v.shaH,v.bAnd,v.shaH)
    LF("    %s[7]=%s(%s[7]+_g,0xFFFFFFFF);%s[8]=%s(%s[8]+_hv,0xFFFFFFFF)", v.shaH,v.bAnd,v.shaH,v.shaH,v.bAnd,v.shaH)
    LF("  end")
    LF("  local _out={};for _i=1,8 do local _w=%s[_i];_out[_i]=%s(_w) end;return table.concat(_out)", v.shaH, v.wrU4be)
    LF("end")
    -- Decode custom Base85 payload + RLE expansion into v.vBlob (binary AES-encrypted blob)
    LF("local %s=%s(%s)", v.vBlob, v.b91Dec, PAYLOAD_VAR_NAME)
    LF("%s=nil", PAYLOAD_VAR_NAME)   -- wipe payload after decoding
    -- SHA-256 integrity check: compute hash and compare exact bytes
    LF("local %s=%s(%s)", v.atSha, v.shaFn, v.vBlob)
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
           v.atHashEnc, hraw, v.atHashDec, v.atHashI, v.atHashEnc, v.atHashDec, v.atHashI, v.bXor, v.atHashEnc, v.atHashI, hmask_expr, v.atShaExp, v.atHashDec)
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
        LF("local _atRobloxCheckOk,_atRobloxCheckResult=pcall(function() return type(typeof)=='function' and typeof(task)=='table' end)")
        LF("local _atIsRobloxRuntime=_atRobloxCheckOk and _atRobloxCheckResult")
        LF("if %s~=%s then", v.atSha, v.atShaExp)
        LF("  local %s=%s", v.atErrEnc, eraw)
        LF("  local %s={}", v.atErrDec)
        LF("  for %s=1,#%s do %s[%s]=string.char(%s(%s:byte(%s),%s)) end", v.atErrI, v.atErrEnc, v.atErrDec, v.atErrI, v.bXor, v.atErrEnc, v.atErrI, emask_expr)
        LF("  local _atErr=table.concat(%s)", v.atErrDec)
        LF("  if _atIsRobloxRuntime then warn(_atErr) else error(_atErr,0) end")
        LF("end")
    end

    local env_expr = string.format("((function() local %s=((type(_ENV)=='table' and _ENV) or (type(getfenv)=='function' and getfenv(0)) or (type(_G)=='table' and _G) or {}); return (type(%s)=='table' and %s) or {} end)())", v.atEnvTbl, v.atEnvTbl, v.atEnvTbl)

    -- Minimal anti-tamper surface: verify delayed callback availability + Lighting clock integrity.
    -- All property/method names, constructor refs, and enum paths are obfuscated via _obfLitStr()
    -- to prevent static analysis from fingerprinting what the checks inspect.
    LF("local %s, %s = pcall(function()", v.atOk, v.atChkVal)
    -- Resolve the global env once, then alias all global constructors/enums through it so
    -- no plain identifiers like Vector3, Instance, Enum, RaycastParams appear in output.
    LF("    local %s=(type(_ENV)=='table' and _ENV) or (type(getfenv)=='function' and getfenv(0)) or _G or {}", v.atCheckVars[23])
    LF("    local %s=%s[%s]", v.atCheckVars[24], v.atCheckVars[23], _obfLitStr("Instance"))
    LF("    local %s=%s[%s]", v.atCheckVars[25], v.atCheckVars[23], _obfLitStr("Vector3"))
    LF("    local %s=%s[%s]", v.atCheckVars[26], v.atCheckVars[23], _obfLitStr("Enum"))
    LF("    local %s=%s[%s]", v.atCheckVars[27], v.atCheckVars[23], _obfLitStr("RaycastParams"))
    -- task.delay type check: use bracket notation so "delay" doesn't appear plaintext.
    LF("    if not (typeof(task) == %s and typeof(task[%s]) == %s) then return false end", _obfLitStr("table"), _obfLitStr("delay"), _obfLitStr("function"))
    -- GetService calls: method name obfuscated via bracket notation.
    LF("    local %s, %s = pcall(function() return game[%s](game,%s) end)", v.atCheckVars[11], v.atLighting, _obfLitStr("GetService"), _obfLitStr("Lighting"))
    LF("    if not %s then return false end", v.atCheckVars[11])
    -- Read ClockTime via bracket notation so property name is hidden.
    LF("    local %s = %s[%s]", v.atCheckVars[1], v.atLighting, _obfLitStr("ClockTime"))
    LF("    if type(%s) ~= %s then return false end", v.atCheckVars[1], _obfLitStr("number"))
    -- probeClockTime=13.75h (13:45); expected minutes=825 (13*60+45); inclusive tolerances absorb floating conversion/runtime variance.
    local probeClockExpr = string.format("((%s)/100)", _obfInt(1375))
    local probeClockTolExpr = string.format("(1/(%s))", _obfInt(10000))
    local probeMinutesExpr = _obfInt(825)
    local probeMinutesTolExpr = string.format("(1/(%s))", _obfInt(10))
    LF("    local %s, %s, %s, %s = %s, %s, %s, %s", v.atCheckVars[6], v.atCheckVars[7], v.atCheckVars[8], v.atCheckVars[9], probeClockExpr, probeClockTolExpr, probeMinutesExpr, probeMinutesTolExpr)
    LF("    local %s, %s = pcall(function()", v.atCheckVars[2], v.atCheckVars[3])
    LF("        %s[%s] = %s", v.atLighting, _obfLitStr("ClockTime"), v.atCheckVars[6])
    LF("        %s = %s[%s]", v.atCheckVars[4], v.atLighting, _obfLitStr("ClockTime"))
    LF("        %s = %s[%s](%s)", v.atCheckVars[5], v.atLighting, _obfLitStr("GetMinutesAfterMidnight"), v.atLighting)
    LF("    end)")
    LF("    local %s = pcall(function() %s[%s] = %s end)", v.atCheckVars[10], v.atLighting, _obfLitStr("ClockTime"), v.atCheckVars[1])
    LF("    if not %s then return false end", v.atCheckVars[2])
    LF("    if not %s then return false end", v.atCheckVars[10])
    LF("    if type(%s) ~= %s or type(%s) ~= %s then return false end", v.atCheckVars[4], _obfLitStr("number"), v.atCheckVars[5], _obfLitStr("number"))
    -- Validate probe readback against expected ClockTime/minutes with inclusive thresholds.
    LF("    if not (math.abs(%s - %s) <= %s and math.abs(%s - %s) <= %s) then return false end", v.atCheckVars[4], v.atCheckVars[6], v.atCheckVars[7], v.atCheckVars[5], v.atCheckVars[8], v.atCheckVars[9])
    -- Workspace raycast integrity probe: ball top-surface hit must match expected Y position.
    LF("    local %s, %s = pcall(function() return game[%s](game,%s) end)", v.atCheckVars[12], v.atCheckVars[13], _obfLitStr("GetService"), _obfLitStr("Workspace"))
    LF("    if not %s then return false end", v.atCheckVars[12])
    -- Instance.new via aliased constructor so "Instance" and "new" don't appear plaintext.
    LF("    local %s = %s[%s](%s)", v.atCheckVars[14], v.atCheckVars[24], _obfLitStr("new"), _obfLitStr("Part"))
    LF("    local %s, %s = pcall(function()", v.atCheckVars[15], v.atCheckVars[16])
    local atPartSizeExpr = _obfInt(10)
    local atRayStartYExpr = _obfInt(10)
    local atRayDeltaYExpr = string.format("(-%s)", _obfInt(20))
    local atHalfExpr = string.format("(%s/(%s))", _obfInt(1), _obfInt(2))
    local atRayTolExpr = string.format("(1/(%s))", _obfInt(10))
    -- All property assignments use bracket notation; Vector3/Enum accessed via aliased vars.
    LF("        %s[%s] = %s[%s](%s, %s, %s)", v.atCheckVars[14], _obfLitStr("Size"), v.atCheckVars[25], _obfLitStr("new"), atPartSizeExpr, atPartSizeExpr, atPartSizeExpr)
    LF("        %s[%s] = %s[%s][%s]", v.atCheckVars[14], _obfLitStr("Shape"), v.atCheckVars[26], _obfLitStr("PartType"), _obfLitStr("Ball"))
    LF("        %s[%s] = true", v.atCheckVars[14], _obfLitStr("Anchored"))
    LF("        %s[%s] = %s", v.atCheckVars[14], _obfLitStr("Parent"), v.atCheckVars[13])
    LF("        local %s = %s[%s]()", v.atCheckVars[17], v.atCheckVars[27], _obfLitStr("new"))
    LF("        %s[%s] = {%s}", v.atCheckVars[17], _obfLitStr("FilterDescendantsInstances"), v.atCheckVars[14])
    LF("        %s[%s] = %s[%s][%s]", v.atCheckVars[17], _obfLitStr("FilterType"), v.atCheckVars[26], _obfLitStr("RaycastFilterType"), _obfLitStr("Include"))
    LF("        local %s = %s[%s](%s, %s[%s] + %s[%s](0, %s, 0), %s[%s](0, %s, 0), %s)",
       v.atCheckVars[18],
       v.atCheckVars[13], _obfLitStr("Raycast"),
       v.atCheckVars[13],
       v.atCheckVars[14], _obfLitStr("Position"),
       v.atCheckVars[25], _obfLitStr("new"), atRayStartYExpr,
       v.atCheckVars[25], _obfLitStr("new"), atRayDeltaYExpr,
       v.atCheckVars[17])
    LF("        local %s = %s[%s][%s] * %s", v.atCheckVars[22], v.atCheckVars[14], _obfLitStr("Size"), _obfLitStr("Y"), atHalfExpr)
    LF("        return %s and math.abs(%s[%s][%s] - (%s[%s][%s] + %s)) <= %s",
       v.atCheckVars[18],
       v.atCheckVars[18], _obfLitStr("Position"), _obfLitStr("Y"),
       v.atCheckVars[14], _obfLitStr("Position"), _obfLitStr("Y"),
       v.atCheckVars[22], atRayTolExpr)
    LF("    end)")
    LF("    pcall(function() %s[%s](%s) end)", v.atCheckVars[14], _obfLitStr("Destroy"), v.atCheckVars[14])
    LF("    if not %s or not %s then return false end", v.atCheckVars[15], v.atCheckVars[16])
    -- Invalid-member probe: Luau should report invalid member on NUL-prefixed property access.
    LF("    local %s = %s[%s](%s)", v.atCheckVars[19], v.atCheckVars[24], _obfLitStr("new"), _obfLitStr("Part"))
    LF("    local %s, %s = pcall(function() return %s[%s] end)", v.atCheckVars[20], v.atCheckVars[21], v.atCheckVars[19], _obfLitStr("\0Property"))
    LF("    pcall(function() %s[%s](%s) end)", v.atCheckVars[19], _obfLitStr("Destroy"), v.atCheckVars[19])
    LF("    if not ((not %s) and %s and tostring(%s):find(%s, 1, true)) then return false end", v.atCheckVars[20], v.atCheckVars[21], v.atCheckVars[21], _obfLitStr("valid member"))
    LF("    return true")
    LF("end)")
    LF("local %s = not (%s and %s)", v.atTrig, v.atOk, v.atChkVal)
    LF("if %s then", v.atTrig)
    LF("    print(%s)", _obfLitStr("Detected by catify :3"))
    LF("    return")
    LF("end")

    -- Watermark: obfuscated ASCII cat watermark (sits in memory, never printed)
    local wm_bytes = {32,32,47,92,95,47,92,32,32,10,32,40,111,46,111,32,41,10,32,32,62,32,94,32,60,10,32,67,97,116,105,102,121,32,118,50,46,48}
    local wm_parts = {}
    for i = 1, #wm_bytes do wm_parts[i] = tostring(wm_bytes[i]) end
    LF("local %s={}", v.wmTbl)
    LF("for %s,%s in ipairs({%s})do %s[%s]=string.char(%s)end",
       v.wmI, v.wmV, table.concat(wm_parts, ","), v.wmTbl, v.wmI, v.wmV)
    LF("local %s=table.concat(%s)", v.vWm, v.wmTbl)

    -- Decrypt and deserialize
    -- Assemble the real key from 4 pre-masked chunks (runtime unmask).
    -- Assemble the real nonce from 2 pre-masked chunks.
    -- Both forward-declared earlier; wiped immediately after use.
    LF("do")
    LF("  local %s={}", v.keyTbl)
    LF("  local mask1=%s;for i=1,8 do %s[i]=string.char(%s(%s:byte(i),mask1))end",
       _obfInt(km[1]), v.keyTbl, v.bXor, v.vKp1)
    LF("  local mask2=%s;for i=1,8 do %s[8+i]=string.char(%s(%s:byte(i),mask2))end",
       _obfInt(km[2]), v.keyTbl, v.bXor, v.vKp2)
    LF("  local mask3=%s;for i=1,8 do %s[16+i]=string.char(%s(%s:byte(i),mask3))end",
       _obfInt(km[3]), v.keyTbl, v.bXor, v.vKp3)
    LF("  local mask4=%s;for i=1,8 do %s[24+i]=string.char(%s(%s:byte(i),mask4))end",
       _obfInt(km[4]), v.keyTbl, v.bXor, v.vKp4)
    LF("  %s=table.concat(%s)", v.vKey, v.keyTbl)
    LF("  %s=nil;%s=nil;%s=nil;%s=nil;%s=nil", v.vKp1, v.vKp2, v.vKp3, v.vKp4, v.keyTbl)
    LF("  local %s={}", v.nonceTbl)
    LF("  local nmask1=%s;for j=1,4 do %s[j]=string.char(%s(%s:byte(j),nmask1))end",
       _obfInt(nm[1]), v.nonceTbl, v.bXor, v.vNp1)
    LF("  local nmask2=%s;for j=1,4 do %s[4+j]=string.char(%s(%s:byte(j),nmask2))end",
       _obfInt(nm[2]), v.nonceTbl, v.bXor, v.vNp2)
    LF("  %s=table.concat(%s)", v.vNonce, v.nonceTbl)
    LF("  %s=nil;%s=nil;%s=nil", v.vNp1, v.vNp2, v.nonceTbl)
    LF("end")
    LF("%s=%s(%s,%s,%s)", v.vBlob, v.vDecrypt, v.vBlob, v.vKey, v.vNonce)
    LF("%s=nil;%s=nil;%s=nil;%s=nil;%s=nil;%s=nil", v.vKey, v.vNonce, v.vDecrypt, v.vDk1, v.vDk2, v.b91Dec)   -- wipe key, nonce, decryptor, decoys, decoder
    LF("%s=1", v.dPos)
    LF("%s=%s", v.dData, v.vBlob)
    LF("local %s=%s()", v.vProto, v.vLoadProto)
    LF("%s=nil;%s=nil;%s=nil", v.vBlob, v.dData, v.vLoadProto)  -- wipe after load
    LF("local %s={v=%s}", v.vEnv, env_expr)
    -- Initial upvals table uses a metatable so any upval[N] always returns a box
    LF("return %s(%s,setmetatable({[0]=%s},{__index=function(t,k)local b={};t[k]=b;return b end}))",
       v.vExec, v.vProto, v.vEnv)
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
