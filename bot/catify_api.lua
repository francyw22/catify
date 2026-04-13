--[[
    Catify API — bot/catify_api.lua

    Provides a simple in-process API around the Catify pipeline so that the
    Discord bot (or any other caller) can obfuscate Lua source code without
    spawning a subprocess.

    Usage:
        local CatifyAPI = require("bot.catify_api")

        local ok, result = CatifyAPI.obfuscate(lua_source_string, options)
        if ok then
            -- result is the obfuscated Lua source string
            print(result)
        else
            -- result is an error message string
            print("Error:", result)
        end

    Options (all optional):
        passes  (number)  — number of VM-wrapping passes (default 1, max 2)
        seed    (number)  — RNG seed for reproducible output (default: random)
]]

-- Locate the catify root directory (two levels up from this file's location).
local script_dir = debug.getinfo(1, "S").source:match("@(.+[/\\])") or ""
local root = script_dir .. "../"

-- Load Catify pipeline modules
local Parser  = dofile(root .. "src/parser.lua")
local Passes  = dofile(root .. "src/passes.lua")
local VmGen   = dofile(root .. "src/vm_gen.lua")
local Utils   = dofile(root .. "src/utils.lua")

local MAX_PASSES = 2
local MAX_SOURCE_BYTES = 512 * 1024   -- 512 KB input guard

local CatifyAPI = {}

--- Obfuscate a Lua 5.3 source string.
---@param source  string   Raw Lua source code to protect.
---@param opts    table?   Optional settings: { passes=1, seed=nil }
---@return boolean, string  ok, result (obfuscated source or error message)
function CatifyAPI.obfuscate(source, opts)
    if type(source) ~= "string" then
        return false, "source must be a string"
    end
    if #source > MAX_SOURCE_BYTES then
        return false, string.format("source too large (%d bytes, max %d)", #source, MAX_SOURCE_BYTES)
    end

    opts = opts or {}
    local passes = math.max(1, math.min(MAX_PASSES, math.tointeger(opts.passes or 1) or 1))
    local seed   = opts.seed or math.random(0, 2^31 - 1)
    math.randomseed(seed)

    -- ── Step 1: Compile Lua source to bytecode ──────────────────────────────
    local chunk, compile_err = load(source, "=input", "t")
    if not chunk then
        return false, "Lua compile error: " .. tostring(compile_err)
    end
    local bytecode = string.dump(chunk, true)   -- strip debug info

    -- ── Step 2: Iterative obfuscation passes ────────────────────────────────
    local current_source = source
    for pass = 1, passes do
        local bc = pass == 1 and bytecode or string.dump(
            assert(load(current_source, "=pass" .. pass)), true)

        -- Parse bytecode into a proto tree
        local ok_p, proto = pcall(Parser.parse, bc)
        if not ok_p then
            return false, "bytecode parse error (pass " .. pass .. "): " .. tostring(proto)
        end

        -- Apply obfuscation passes (opcode shuffle, junk injection, etc.)
        local proto_out, revmap = Passes.run_all(proto, Utils)

        -- Generate a fresh random RC4 key
        local key = Utils.rand_key(math.random(24, 48))

        -- Generate VM source
        local ok_g, vm_src = pcall(VmGen.generate, proto_out, revmap, key, Utils)
        if not ok_g then
            return false, "VM generation error (pass " .. pass .. "): " .. tostring(vm_src)
        end

        current_source = vm_src
    end

    return true, current_source
end

--- Quick helper: obfuscate source and return the result or raise an error.
---@param source  string
---@param opts    table?
---@return string  obfuscated source
function CatifyAPI.obfuscate_or_error(source, opts)
    local ok, result = CatifyAPI.obfuscate(source, opts)
    if not ok then error(result, 2) end
    return result
end

return CatifyAPI
