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
---@param key     string  AES-256 key (32 bytes) used to encrypt the bytecode blob
---@param nonce   string  AES-256-CTR nonce (8 bytes)
---@param utils   table   The Utils module (for aes256_ctr, sha256, base91_enc, rand_names)
---@return string  Lua source
function VmGen.generate(proto, revmap, key, nonce, utils)
    -- ── 1. Serialize + encrypt the custom bytecode ───────────────────────────
    local sxor_byte = math.random(1, 255)     -- per-session string XOR key
    local raw  = serialize_proto(proto, sxor_byte)
    local blob = utils.aes256_ctr(raw, key, nonce)

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
    -- Anti-keylogger variable names
    local atKl1     = vn()
    local atKl2     = vn()
    local atKl3     = vn()
    local atKl4     = vn()
    -- Anti-environmental logger variable names
    local atEnv1    = vn()
    local atEnv2    = vn()
    local atEnv3    = vn()
    -- SHA-256 integrity check variable names
    local atSha     = vn()
    -- Watermark variable name
    local vWm       = vn()
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

    -- ── 3. Compute SHA-256 of the encrypted blob for anti-tamper ─────────────
    local blob_sha = utils.sha256(blob)
    local blob_sha_words = {}
    for i = 0, 7 do
        blob_sha_words[i] = string.unpack(">I4", blob_sha, i*4+1)
    end

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
        -- form 9: fake config table with dead branch (looks like real init code)
        function(indent)
            local cfg_keys = {"timeout","retries","verbose","mode","level","limit"}
            local k = cfg_keys[math.random(1, #cfg_keys)]
            local v = math.random(0, 1) == 1 and "true" or tostring(math.random(1,9))
            return string.format(
                "%sdo local %s={%s=%s};if %s.%s==nil then %s.%s=%s end end\n",
                indent, jA, k, v, jA, k, jA, k, v)
        end,
        -- form 10: fake string sanitize (dead upper/lower branch)
        function(indent)
            local words = {"data","value","result","output","buffer","token"}
            local w = words[math.random(1, #words)]
            return string.format(
                "%sdo local %s=%q;local %s=string.upper(%s);if #%s<0 then %s=%s end end\n",
                indent, jA, w, jB, jA, jB, jA, jB)
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

    -- ── Chunked \NNN-escaped payload table at the top (emitted before do block) ──
    src[#src+1] = emit_payload_table(blob) .. "\n"

    -- Wrap all VM internals in a do...end block so locals don't pollute global scope
    L("do")
    L("local _=tostring;local __=type;local ___=pcall;local ____=load")
    -- Junk block at top of do-scope (dead computations, not reachable by any real code path)
    src[#src+1] = junk_block("", math.random(2, 4))
    -- ── Emit payload concatenation helper (decoy wrapper using allocated names) ──
    LF("local %s=%q", b91Alpha, "catify")
    LF("local function %s(%s) local %s={} for _i=1,#%s do %s[_i]=%s[_i] end return table.concat(%s) end",
       b91Dec, b91I, b91Out, b91I, b91Out, b91I, b91Out)
    -- (b91Tbl, b91V, b91B, b91N_, b91P consume name-pool slots; used as junk locals below)
    src[#src+1] = junk_block("", math.random(1, 2))
    -- ── Emit inline AES-256-CTR decrypt ─────────────────────────────────────
    -- S-box table literal
    local sbox_vals = {0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16}
    local sbox_strs = {}
    for i = 1, #sbox_vals do sbox_strs[i] = tostring(sbox_vals[i]) end
    LF("local %s={[0]=%s}", aesSbox, table.concat(sbox_strs, ","))
    LF("local function %s(_a) return((_a<<1)~(_a>=0x80 and 0x1b or 0))&0xFF end", aesXt)
    LF("local function %s(_k)", aesKe)
    LF("  local _w={}")
    LF("  for _i=0,7 do _w[_i]=(_k:byte(_i*4+1)<<24)|(_k:byte(_i*4+2)<<16)|(_k:byte(_i*4+3)<<8)|_k:byte(_i*4+4) end")
    LF("  local _rc={[1]=0x01000000,[2]=0x02000000,[3]=0x04000000,[4]=0x08000000,[5]=0x10000000,[6]=0x20000000,[7]=0x40000000}")
    LF("  for _i=8,59 do")
    LF("    local _t=_w[_i-1]")
    LF("    if _i%%8==0 then")
    LF("      _t=((_t<<8)|(_t>>24))&0xFFFFFFFF")
    LF("      _t=(%s[(_t>>24)&0xFF]<<24)|(%s[(_t>>16)&0xFF]<<16)|(%s[(_t>>8)&0xFF]<<8)|%s[_t&0xFF]", aesSbox,aesSbox,aesSbox,aesSbox)
    LF("      _t=(_t~_rc[_i//8])&0xFFFFFFFF")
    LF("    elseif _i%%8==4 then")
    LF("      _t=(%s[(_t>>24)&0xFF]<<24)|(%s[(_t>>16)&0xFF]<<16)|(%s[(_t>>8)&0xFF]<<8)|%s[_t&0xFF]", aesSbox,aesSbox,aesSbox,aesSbox)
    LF("    end")
    LF("    _w[_i]=(_w[_i-8]~_t)&0xFFFFFFFF")
    LF("  end")
    LF("  return _w")
    LF("end")
    LF("local function %s(_blk,_rk)", aesEb)
    LF("  local _s={}")
    LF("  for _i=0,15 do _s[_i]=_blk:byte(_i+1) end")
    LF("  for _c=0,3 do local _w=_rk[_c];_s[_c*4]=_s[_c*4]~((_w>>24)&0xFF);_s[_c*4+1]=_s[_c*4+1]~((_w>>16)&0xFF);_s[_c*4+2]=_s[_c*4+2]~((_w>>8)&0xFF);_s[_c*4+3]=_s[_c*4+3]~(_w&0xFF) end")
    LF("  for _r=1,13 do")
    LF("    for _i=0,15 do _s[_i]=%s[_s[_i]] end", aesSbox)
    LF("    local _t;_t=_s[1];_s[1]=_s[5];_s[5]=_s[9];_s[9]=_s[13];_s[13]=_t")
    LF("    _t=_s[2];local _t2=_s[6];_s[2]=_s[10];_s[6]=_s[14];_s[10]=_t;_s[14]=_t2")
    LF("    _t=_s[3];_s[3]=_s[15];_s[15]=_s[11];_s[11]=_s[7];_s[7]=_t")
    LF("    for _c=0,3 do")
    LF("      local _a0,_a1,_a2,_a3=_s[_c*4],_s[_c*4+1],_s[_c*4+2],_s[_c*4+3]")
    LF("      _s[_c*4]=%s(_a0)~%s(_a1)~_a1~_a2~_a3", aesXt, aesXt)
    LF("      _s[_c*4+1]=_a0~%s(_a1)~%s(_a2)~_a2~_a3", aesXt, aesXt)
    LF("      _s[_c*4+2]=_a0~_a1~%s(_a2)~%s(_a3)~_a3", aesXt, aesXt)
    LF("      _s[_c*4+3]=%s(_a0)~_a0~_a1~_a2~%s(_a3)", aesXt, aesXt)
    LF("    end")
    LF("    for _c=0,3 do local _w=_rk[_r*4+_c];_s[_c*4]=_s[_c*4]~((_w>>24)&0xFF);_s[_c*4+1]=_s[_c*4+1]~((_w>>16)&0xFF);_s[_c*4+2]=_s[_c*4+2]~((_w>>8)&0xFF);_s[_c*4+3]=_s[_c*4+3]~(_w&0xFF) end")
    LF("  end")
    LF("  for _i=0,15 do _s[_i]=%s[_s[_i]] end", aesSbox)
    LF("  local _t;_t=_s[1];_s[1]=_s[5];_s[5]=_s[9];_s[9]=_s[13];_s[13]=_t")
    LF("  _t=_s[2];local _t2=_s[6];_s[2]=_s[10];_s[6]=_s[14];_s[10]=_t;_s[14]=_t2")
    LF("  _t=_s[3];_s[3]=_s[15];_s[15]=_s[11];_s[11]=_s[7];_s[7]=_t")
    LF("  for _c=0,3 do local _w=_rk[56+_c];_s[_c*4]=_s[_c*4]~((_w>>24)&0xFF);_s[_c*4+1]=_s[_c*4+1]~((_w>>16)&0xFF);_s[_c*4+2]=_s[_c*4+2]~((_w>>8)&0xFF);_s[_c*4+3]=_s[_c*4+3]~(_w&0xFF) end")
    LF("  local _o={};for _i=0,15 do _o[_i+1]=string.char(_s[_i]) end;return table.concat(_o)")
    LF("end")
    LF("local function %s(_d,_k,_nn)", vDecrypt)
    LF("  local _rk=%s(_k)", aesKe)
    LF("  local _out={};local _ctr=0;local _pos=1;local _dl=#_d")
    LF("  while _pos<=_dl do")
    LF("    local _cb=_nn..string.pack('<I8',_ctr)")
    LF("    local _ks=%s(_cb,_rk)", aesEb)
    LF("    local _bl=math.min(16,_dl-_pos+1)")
    LF("    for _i=1,_bl do _out[#_out+1]=string.char(_d:byte(_pos+_i-1)~_ks:byte(_i)) end")
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
    -- dRi64: detect at runtime whether '<i8' unpack works (64-bit Lua / Roblox),
    -- and fall back to double arithmetic for 32-bit platforms.
    -- Probe: bytes \0\0\0\128\0\0\0\0 are LE 0x0000000080000000 = 2^31 as i64.
    -- That value exceeds the 32-bit signed range, so the pcall fails on 32-bit Lua.
    LF("local _i8ok=(function() local ok=pcall(string.unpack,'<i8','\\0\\0\\0\\128\\0\\0\\0\\0',1);return ok end)()")
    LF("local function %s()", dRi64)
    LF("  if _i8ok then local _v,_p=string.unpack('<i8',%s,%s);%s=_p;return _v end", dData, dPos, dPos)
    LF("  local _lo,_p1=string.unpack('<I4',%s,%s);%s=_p1", dData, dPos, dPos)
    LF("  local _hi,_p2=string.unpack('<I4',%s,%s);%s=_p2", dData, dPos, dPos)
    LF("  if _hi==0 then return _lo end")
    LF("  local _v=_lo+_hi*(2^32)")
    LF("  if _hi>=(2^31) then _v=_v-(2^64) end")
    LF("  return _v")
    LF("end")
    LF("local function %s() local v,p=string.unpack('<d',%s,%s);%s=p;return v end",  dRf64, dData, dPos, dPos)
    -- dRstr: emit once (correctly advancing pos)
    LF("local function %s() local _n,_p=string.unpack('<i4',%s,%s);%s=_p;local _s=%s:sub(%s,%s+_n-1);%s=%s+_n;return _s end",
       dRstr, dData, dPos, dPos, dData, dPos, dPos, dPos, dPos)

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

    -- ── Pre-compute obfuscated mask/shift constants (evaluated once) ──────────
    local _m63   = utils.obfuscate_int_deep(0x3F)
    local _m255  = utils.obfuscate_int_deep(0xFF)
    local _m511  = utils.obfuscate_int_deep(0x1FF)
    local _m18   = utils.obfuscate_int_deep(0x3FFFF)
    local _bias  = utils.obfuscate_int_deep(131071)
    local _sh6   = utils.obfuscate_int_deep(6)
    local _sh14  = utils.obfuscate_int_deep(14)
    local _sh23  = utils.obfuscate_int_deep(23)
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
    LF("    local %s=%s[%s&%s]", eOp,vRevmap,eInst,eMask63)
    LF("    local %s=(%s>>%s)&%s",   eA,  eInst,eSh6, eMask255)
    LF("    local %s=(%s>>%s)&%s",   eB,  eInst,eSh23,eMask511)
    LF("    local %s=(%s>>%s)&%s",   eC,  eInst,eSh14,eMask511)
    LF("    local %s=(%s>>%s)&%s",   eBx, eInst,eSh14,eMask18)
    LF("    local %s=%s-%s",         eSBx,eBx,eBias)
    LF("    %s[%s](%s,%s,%s,%s,%s)", vDispatch,eOp,eA,eB,eC,eBx,eSBx)
    LF("  end")
    LF("  return table.unpack(%s,1,%s)", eRetVals,eRetN)
    LF("end")  -- end execute function
    -- Junk block after execute function definition
    src[#src+1] = junk_block("", math.random(2, 4))

    -- ── Main: anti-tamper, decrypt, deserialize, run ──────────
    -- The payload table (superflow_bytecode) was already emitted at the top of the file.

    -- AES key + nonce (use \NNN decimal escapes to avoid %q newline-embedding issue)
    LF("local %s=\"%s\"", vKey, bytes_esc(key))
    LF("local %s=\"%s\"", vNonce, bytes_esc(nonce))

    -- Anti-tamper 1: SHA-256 integrity check of the encrypted blob
    -- Emit inline SHA-256 function
    local sha_k_vals = {0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2}
    local sha_k_strs = {}
    for i = 1, 64 do sha_k_strs[i] = tostring(sha_k_vals[i]) end
    LF("local function %s(_s)", shaFn)
    LF("  local function _rr(_x,_n) return((_x>>_n)|(_x<<(32-_n)))&0xFFFFFFFF end")
    LF("  local _k={%s}", table.concat(sha_k_strs, ","))
    LF("  local %s={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}", shaH)
    LF("  local _len=#_s;local _bl=_len*8")
    LF("  local _pd=_s..'\\x80'")
    LF("  while #_pd%%64~=56 do _pd=_pd..'\\x00' end")
    LF("  _pd=_pd..string.pack('>I4',(_bl>>32)&0xFFFFFFFF)..string.pack('>I4',_bl&0xFFFFFFFF)")
    LF("  local %s={}", shaW)
    LF("  for _blk=1,#_pd,64 do")
    LF("    for _i=1,16 do %s[_i]=string.unpack('>I4',_pd,_blk+(_i-1)*4)&0xFFFFFFFF end", shaW)
    LF("    for _i=17,64 do")
    LF("      local _s0=(_rr(%s[_i-15],7)~_rr(%s[_i-15],18)~(%s[_i-15]>>3))", shaW,shaW,shaW)
    LF("      local _s1=(_rr(%s[_i-2],17)~_rr(%s[_i-2],19)~(%s[_i-2]>>10))", shaW,shaW,shaW)
    LF("      %s[_i]=(%s[_i-16]+_s0+%s[_i-7]+_s1)&0xFFFFFFFF", shaW,shaW,shaW)
    LF("    end")
    LF("    local _a,_b,_c,_d,_e,_f,_g,_hv=%s[1],%s[2],%s[3],%s[4],%s[5],%s[6],%s[7],%s[8]", shaH,shaH,shaH,shaH,shaH,shaH,shaH,shaH)
    LF("    for _i=1,64 do")
    LF("      local _S1=_rr(_e,6)~_rr(_e,11)~_rr(_e,25)")
    LF("      local _ch=(_e&_f)~((~_e)&_g)")
    LF("      local _t1=(_hv+_S1+_ch+_k[_i]+%s[_i])&0xFFFFFFFF", shaW)
    LF("      local _S0=_rr(_a,2)~_rr(_a,13)~_rr(_a,22)")
    LF("      local _maj=(_a&_b)~(_a&_c)~(_b&_c)")
    LF("      local _t2=(_S0+_maj)&0xFFFFFFFF")
    LF("      _hv=_g;_g=_f;_f=_e;_e=(_d+_t1)&0xFFFFFFFF;_d=_c;_c=_b;_b=_a;_a=(_t1+_t2)&0xFFFFFFFF")
    LF("    end")
    LF("    %s[1]=(%s[1]+_a)&0xFFFFFFFF;%s[2]=(%s[2]+_b)&0xFFFFFFFF", shaH,shaH,shaH,shaH)
    LF("    %s[3]=(%s[3]+_c)&0xFFFFFFFF;%s[4]=(%s[4]+_d)&0xFFFFFFFF", shaH,shaH,shaH,shaH)
    LF("    %s[5]=(%s[5]+_e)&0xFFFFFFFF;%s[6]=(%s[6]+_f)&0xFFFFFFFF", shaH,shaH,shaH,shaH)
    LF("    %s[7]=(%s[7]+_g)&0xFFFFFFFF;%s[8]=(%s[8]+_hv)&0xFFFFFFFF", shaH,shaH,shaH,shaH)
    LF("  end")
    LF("  local _out={};for _i=1,8 do _out[_i]=string.pack('>I4',%s[_i]) end;return table.concat(_out)", shaH)
    LF("end")
    -- Decode payload table into vBlob (simple concatenation of \NNN-escaped chunks)
    LF("local %s=table.concat(%s)", vBlob, PAYLOAD_TABLE_NAME)
    LF("%s=nil", PAYLOAD_TABLE_NAME)   -- wipe payload table after reading
    -- SHA-256 integrity check: compute hash and compare 8 words
    LF("local %s=%s(%s)", atSha, shaFn, vBlob)
    local sha_checks = {}
    for i = 0, 7 do
        local word_exp = utils.obfuscate_int_deep(blob_sha_words[i])
        sha_checks[i+1] = string.format("(string.unpack('>I4',%s,%d)~=%s)", atSha, i*4+1, word_exp)
    end
    LF("if %s then error('Catify: integrity check failed',0) end", table.concat(sha_checks, " or "))

    -- Anti-tamper 2: debug hook detection (wrapped in pcall for Roblox compatibility)
    LF("local %s", atDbg)
    LF("pcall(function() %s=rawget(_ENV,'debug') end)", atDbg)
    LF("if %s and type(%s)=='table' and type(%s.gethook)=='function' then", atDbg, atDbg, atDbg)
    LF("  local _dhok,_dhv=pcall(%s.gethook,%s)", atDbg, atDbg)
    LF("  if _dhok and _dhv~=nil then error('Catify: debug hook detected',0) end")
    LF("end")

    -- Anti-tamper 3: critical global integrity check
    LF("do")
    LF("  local _req={tostring=tostring,type=type,pcall=pcall,load=load,string=string,table=table}")
    LF("  for _k,_v in pairs(_req) do")
    LF("    if _v==nil then error('Catify: environment tampered ('.._k..')',0) end")
    LF("  end")
    LF("end")

    -- Anti-tamper 4: Lua version must be 5.3, 5.4, or Roblox Luau
    LF("do local %s=_VERSION;if not(%s and(%s:find('5%%.3') or %s:find('5%%.4') or %s:find('Luau')))then error('Catify: unsupported Lua version',0) end end",
       atVer, atVer, atVer, atVer, atVer)

    -- Anti-tamper 5: core standard functions must be genuine callable values
    LF("do local %s={rawequal,rawget,rawset,rawlen,select,ipairs,pairs,next,unpack or table.unpack};for _,_f in ipairs(%s) do if type(_f)~='function' then error('Catify: environment tampered (core)',0) end end end",
       atRaw, atRaw)

    -- Anti-tamper 6: type() sanity (standard type names must not be overridden)
    LF("do if type(nil)~='nil' or type(0)~='number' or type('')~='string' or type({})~='table' or type(type)~='function' then error('Catify: environment tampered (type)',0) end end")

    -- Anti-tamper 7: string standard library sanity
    LF("do if string.byte('A')~=65 or string.char(65)~='A' or string.len('ab')~=2 then error('Catify: environment tampered (strlib)',0) end end")

    -- Anti-tamper 8: math library sanity (math.pi is universal; maxinteger absent in Luau)
    LF("do if type(math.pi)~='number' or math.pi<=3 or math.pi>=4 or type(math.abs)~='function' then error('Catify: environment tampered (math)',0) end end")

    -- Anti-tamper 9: table library sanity (insert/remove must be callable)
    LF("do if type(table.insert)~='function' or type(table.remove)~='function' or type(table.concat)~='function' then error('Catify: environment tampered (tablelib)',0) end end")

    -- Anti-tamper 10: coroutine library basic check
    LF("do if type(coroutine)~='table' or type(coroutine.wrap)~='function' then error('Catify: environment tampered (coroutine)',0) end end")

    -- Anti-keylogger 1: no active debug hook (more thorough check)
    LF("do local %s", atKl1)
    LF("  pcall(function() local _d=rawget(_ENV,'debug');if _d and type(_d.gethook)=='function' then %s=_d.gethook() end end)", atKl1)
    LF("  if %s~=nil then error('Catify: keylogger detected',0) end end", atKl1)

    -- Anti-keylogger 2: io library integrity (keyloggers may replace io.read/write)
    LF("do local %s=rawget(_ENV,'io');if %s~=nil and(type(%s.read)~='function' or type(%s.write)~='function')then error('Catify: keylogger detected (io)',0)end end",
       atKl2, atKl2, atKl2, atKl2)

    -- Anti-keylogger 3: string metatable not tampered
    LF("do local %s=getmetatable('');if %s~=nil then local _idx=rawget(%s,'__index');if _idx~=nil and type(_idx)~='table' then error('Catify: keylogger detected (strmeta)',0)end end end",
       atKl3, atKl3, atKl3)

    -- Anti-keylogger 4: pcall/error uncompromised
    LF("do local %s,_r=pcall(function()return true end);if not %s or _r~=true then error('Catify: keylogger detected (pcall)',0)end end",
       atKl4, atKl4)

    -- Anti-environmental logger 1: detect _G/_ENV monitoring via metamethod proxy
    LF("do local %s=getmetatable(_G or _ENV);if %s~=nil then if rawget(%s,'__newindex')~=nil or rawget(%s,'__index')~=nil then error('Catify: env logger detected',0)end end end",
       atEnv1, atEnv1, atEnv1, atEnv1)

    -- Anti-environmental logger 2: os library must not be replaced or wrapped
    LF("do local %s=rawget(_ENV,'os');if %s~=nil then if type(%s.getenv)~='function' or type(%s.time)~='function' then error('Catify: env tampered (os)',0)end end end",
       atEnv2, atEnv2, atEnv2, atEnv2)

    -- Anti-environmental logger 3: numbers must not have a metatable (some loggers patch this)
    LF("do local %s=getmetatable(0);if %s~=nil then error('Catify: env logger detected (nummt)',0)end end",
       atEnv3, atEnv3)

    -- Watermark: obfuscated ASCII cat watermark (sits in memory, never printed)
    local wm_bytes = {32,32,47,92,95,47,92,32,32,10,32,40,111,46,111,32,41,10,32,32,62,32,94,32,60,10,32,67,97,116,105,102,121,32,118,50,46,48}
    local wm_parts = {}
    for i = 1, #wm_bytes do wm_parts[i] = tostring(wm_bytes[i]) end
    LF("local %s=table.concat((function()local _t={};for _i,_v in ipairs({%s})do _t[_i]=string.char(_v)end;return _t end)())",
       vWm, table.concat(wm_parts, ","))

    -- Decrypt and deserialize
    LF("%s=%s(%s,%s,%s)", vBlob, vDecrypt, vBlob, vKey, vNonce)
    LF("%s=nil;%s=nil;%s=nil", vKey, vNonce, vDecrypt)   -- wipe key, nonce, decryptor
    LF("%s=1", dPos)
    LF("%s=%s", dData, vBlob)
    LF("local %s=%s()", vProto, vLoadProto)
    LF("%s=nil;%s=nil;%s=nil", vBlob, dData, vLoadProto)  -- wipe after load
    LF("local %s={v=_ENV}", vEnv)
    -- Initial upvals table uses a metatable so any upval[N] always returns a box
    LF("%s(%s,setmetatable({[0]=%s},{__index=function(t,k)local b={};t[k]=b;return b end}))",
       vExec, vProto, vEnv)
    L("end")

    -- ── Compact post-processing: strip indentation and join lines ────────────
    local full = table.concat(src)
    local compact_lines = {}
    for line in full:gmatch("[^\n]+") do
        -- Strip leading whitespace, then strip trailing whitespace separately
        local trimmed = line:match("^%s*(.+)$")        if trimmed then
            trimmed = trimmed:match("^(.-)%s*$")
        end
        if trimmed and trimmed ~= "" then
            compact_lines[#compact_lines + 1] = trimmed
        end
    end
    -- Prepend ASCII watermark as a block comment at the top of the output file
    local watermark = "--[[\n"
        .. "   /\\_/\\  \n"
        .. "  ( o.o ) \n"
        .. "   > ^ <  \n"
        .. "  Catify v2.0.0 -- Protected by Catify\n"
        .. "  https://github.com/francyw22/catify\n"
        .. "]]\n"
    return watermark .. table.concat(compact_lines, " ")
end

return VmGen
