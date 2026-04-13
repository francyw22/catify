--[[
    Catify - Commercial Lua Obfuscator
    src/passes.lua  - Obfuscation passes applied to the parsed Proto tree

    Passes (run in order by the pipeline):
      1. opcode_shuffle  – remap every instruction's opcode field using a random
                           bijective mapping; returns (new_proto, revmap).
      2. strip_debug     – remove source-name, line info, local-var names, and
                           upvalue names from every proto (makes decompilation harder).
      3. encrypt_strings – XOR every string constant with a per-constant key
                           derived from the global RC4 key; the VM template already
                           handles decryption at runtime via the kst[] table, so we
                           DON'T do this here (strings must be readable by the VM).
                           Instead this pass is a no-op placeholder kept for the
                           pipeline API so callers can extend it.
    All passes are pure (return a new/modified proto, never mutate the original in
    a way that breaks subsequent passes).
]]

local Passes = {}

-- ─── Helpers ─────────────────────────────────────────────────────────────────

--- Deep-copy a proto tree so we never mutate the parser's output.
local function clone_proto(p)
    local np = {}
    -- Scalars
    for _, f in ipairs({
        "numparams","is_vararg","maxstacksize",
        "sizecode","sizek","sizeupvalues","sizep",
        "sizelineinfo","sizelocvars","sizeuvnames",
        "source","linedefined","lastlinedefined","main_nupvals",
    }) do
        np[f] = p[f]
    end
    -- code  (0-indexed)
    local code = {}
    for i = 0, (p.sizecode or 0) - 1 do code[i] = p.code[i] end
    np.code = code
    -- k  (0-indexed, shallow – constants are immutable)
    local k = {}
    for i = 0, (p.sizek or 0) - 1 do k[i] = p.k[i] end
    np.k = k
    -- upvals  (0-indexed, shallow copy of descriptor tables)
    local uvs = {}
    for i = 0, (p.sizeupvalues or 0) - 1 do
        uvs[i] = { instack = p.upvals[i].instack, idx = p.upvals[i].idx }
    end
    np.upvals = uvs
    -- nested protos (recursive)
    local pp = {}
    for i = 0, (p.sizep or 0) - 1 do
        pp[i] = clone_proto(p.p[i])
    end
    np.p = pp
    -- debug arrays (shallow)
    local li = {}
    for i = 0, (p.sizelineinfo or 0) - 1 do li[i] = p.lineinfo[i] end
    np.lineinfo = li
    local lv = {}
    for i = 0, (p.sizelocvars or 0) - 1 do
        lv[i] = { varname = p.locvars[i].varname,
                  startpc  = p.locvars[i].startpc,
                  endpc    = p.locvars[i].endpc }
    end
    np.locvars = lv
    local uvn = {}
    for i = 0, (p.sizeuvnames or 0) - 1 do uvn[i] = p.uvnames[i] end
    np.uvnames = uvn
    return np
end

-- ─── Pass 1: Opcode shuffle ───────────────────────────────────────────────────

--- Replace every instruction's opcode field with a shuffled value.
--- The mapping is:  new_raw_op = opmap[original_op]
--- The VM will reverse it at runtime using revmap.
---
---@param proto  table   Parsed proto tree (will be cloned internally)
---@param utils  table   Utils module (provides gen_opcode_map)
---@return table new_proto, table revmap
function Passes.opcode_shuffle(proto, utils)
    local np = clone_proto(proto)
    local opmap, revmap = utils.gen_opcode_map(47)   -- 47 Lua 5.3 opcodes

    local function remap_proto(p)
        -- Re-encode each instruction
        for i = 0, p.sizecode - 1 do
            local inst    = p.code[i]
            local orig_op = inst & 0x3F
            local rest    = inst & 0xFFFFFFC0   -- bits 6..31 (A, B, C, Bx)
            p.code[i]     = rest | opmap[orig_op]
        end
        -- Recurse into nested protos
        for i = 0, p.sizep - 1 do
            remap_proto(p.p[i])
        end
    end

    remap_proto(np)
    return np, revmap
end

-- ─── Pass 2: Strip debug info ─────────────────────────────────────────────────

--- Remove source name, line info, local-var names, and upvalue names.
--- This makes bytecode-level decompilation produce unreadable output.
---@param proto table
---@return table stripped_proto
function Passes.strip_debug(proto)
    local np = clone_proto(proto)

    local function strip(p)
        p.source       = "@Catify"
        p.linedefined  = 0
        p.lastlinedefined = 0
        -- Wipe line-info array
        for i = 0, p.sizelineinfo - 1 do p.lineinfo[i] = 0 end
        -- Wipe local-var names
        for i = 0, p.sizelocvars - 1 do p.locvars[i].varname = "v" end
        -- Wipe upvalue names
        for i = 0, p.sizeuvnames - 1 do p.uvnames[i] = "u" end
        -- Recurse
        for i = 0, p.sizep - 1 do strip(p.p[i]) end
    end

    strip(np)
    return np
end

-- ─── Pass 3: String constant obfuscation ─────────────────────────────────────
-- NOTE: String constants must remain readable by the generated VM's kst[]
-- table lookup (the VM does NOT decrypt individual constants).  To apply
-- deeper string encryption, extend the VM template in vm_gen.lua to include
-- a per-constant decryption step and encode the strings here.
-- For now this pass is intentionally a no-op so the pipeline stays extensible.

---@param proto table
---@return table proto (unchanged)
function Passes.encrypt_strings(proto)
    return proto   -- placeholder – see note above
end

-- ─── Pass 4: Inject junk instructions (opaque predicates) ────────────────────
-- Insert NOP-equivalent instruction sequences (LOADBOOL + JMP 0 patterns)
-- that are unreachable or provably harmless.  This inflates the instruction
-- stream and confuses static decompilers.

--- Return a 32-bit Lua 5.3 instruction word (A B C format).
local function make_inst(op, A, B, C)
    return (op & 0x3F) | ((A & 0xFF) << 6) | ((C & 0x1FF) << 14) | ((B & 0x1FF) << 23)
end

--- Extract sBx from an instruction (bits 14-31, bias 131071).
local function get_sbx(inst)
    return ((inst >> 14) & 0x3FFFF) - 131071
end

--- Rebuild an instruction preserving op and A, with a new sBx value.
local function set_sbx(inst, new_sbx)
    local op     = inst & 0x3F
    local A      = (inst >> 6) & 0xFF
    local new_bx = (new_sbx + 131071) & 0x3FFFF
    return op | (A << 6) | (new_bx << 14)
end

--- Insert `count` junk LOADBOOL R(200) 0 0 instructions into proto.code at
--- random positions that are safe with respect to control flow:
---   • never between a conditional (EQ/LT/LE/TEST/TESTSET) and the JMP it guards
---   • all sBx-based jump targets (JMP, FORLOOP, FORPREP, TFORLOOP) are corrected
---   to account for the new instruction positions.
---@param proto table   mutated in-place (call after opcode_shuffle)
---@param opmap table   opmap[orig_op]=shuffled_op (for junk instruction opcode)
---@param count integer
function Passes.inject_junk(proto, opmap, count)
    count = count or 3

    -- Build revmap (shuffled → real) from opmap (real → shuffled)
    local revmap = {}
    if opmap then
        for real = 0, 46 do
            if opmap[real] then revmap[opmap[real]] = real end
        end
    else
        for i = 0, 46 do revmap[i] = i end
    end

    local JUNK_OP  = opmap and (opmap[3] or 3) or 3   -- shuffled LOADBOOL

    -- Real opcodes that conditionally skip the next instruction (always a JMP)
    local COND_SKIP = { [31]=true, [32]=true, [33]=true, [34]=true, [35]=true }
    -- Real opcodes that carry a relative sBx jump offset
    local JUMP_OPS  = { [30]=true, [39]=true, [40]=true, [42]=true }

    local function inject(p)
        local n = p.sizecode
        if n < 2 then return end

        -- 1. Mark positions where junk must NOT be prepended
        --    (the instruction immediately after a COND_SKIP must not be displaced)
        local protected = {}
        for i = 0, n - 1 do
            local rop = revmap[p.code[i] & 0x3F] or (p.code[i] & 0x3F)
            if COND_SKIP[rop] then protected[i + 1] = true end
        end

        -- 2. Collect candidate positions and pick up to `count` unique safe ones
        local candidates = {}
        for i = 0, n - 1 do
            if not protected[i] then candidates[#candidates + 1] = i end
        end
        local npts = math.min(count, #candidates)
        if npts == 0 then return end

        -- Fisher-Yates partial shuffle to pick npts unique candidates
        for j = 1, npts do
            local k = math.random(j, #candidates)
            candidates[j], candidates[k] = candidates[k], candidates[j]
        end
        local pts = {}
        for j = 1, npts do pts[#pts + 1] = candidates[j] end
        table.sort(pts)

        -- 3. Build old_index → new_index mapping (one junk added before each pt)
        local old_to_new = {}
        local off = 0
        local pi  = 1
        for i = 0, n - 1 do
            if pi <= #pts and pts[pi] == i then
                off = off + 1
                pi  = pi  + 1
            end
            old_to_new[i] = i + off
        end
        old_to_new[n] = n + off   -- sentinel (one past end, for forward jumps)

        -- 4. Build new instruction array, fixing sBx in jump instructions
        local new_code = {}
        local ni = 0
        pi = 1
        for i = 0, n - 1 do
            -- Prepend junk if this position was chosen
            if pi <= #pts and pts[pi] == i then
                new_code[ni] = make_inst(JUNK_OP, 200, 0, 0)
                ni = ni + 1
                pi = pi + 1
            end
            local inst = p.code[i]
            local rop  = revmap[inst & 0x3F] or (inst & 0x3F)
            if JUMP_OPS[rop] then
                -- Correct the relative jump offset
                local old_sbx    = get_sbx(inst)
                local old_target = i + 1 + old_sbx          -- absolute old target
                local new_i      = old_to_new[i]
                local new_target = old_to_new[old_target]
                                   or (old_target + off)     -- fallback
                local new_sbx    = new_target - (new_i + 1)
                inst = set_sbx(inst, new_sbx)
            end
            new_code[ni] = inst
            ni = ni + 1
        end

        p.code     = new_code
        p.sizecode = ni

        -- Recurse into nested protos
        for j = 0, p.sizep - 1 do inject(p.p[j]) end
    end

    inject(proto)
end

-- ─── Pipeline ─────────────────────────────────────────────────────────────────

--- Run all passes and return the final proto + revmap ready for vm_gen.
---@param proto  table   Raw proto from Parser.parse()
---@param utils  table   Utils module
---@param opts   table   Optional: { junk_count=N }
---@return table final_proto, table revmap, table opmap
function Passes.run_all(proto, utils, opts)
    opts = opts or {}

    -- 1. Strip debug info
    proto = Passes.strip_debug(proto)

    -- 2. Shuffle opcodes
    local opmap, revmap
    proto, revmap = Passes.opcode_shuffle(proto, utils)
    -- Derive opmap (orig→shuffled) from revmap (shuffled→orig)
    opmap = {}
    for shuffled = 0, 46 do
        local orig = revmap[shuffled]
        if orig then opmap[orig] = shuffled end
    end

    -- 3. Inject junk (after shuffle so junk uses shuffled opcode numbers)
    local jcount = opts.junk_count or math.random(3, 8)
    Passes.inject_junk(proto, opmap, jcount)

    -- 4. String pass (currently no-op)
    proto = Passes.encrypt_strings(proto)

    return proto, revmap, opmap
end

return Passes
