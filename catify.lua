#!/usr/bin/env lua5.3
--[[
    Catify - Commercial Lua Obfuscator  v1.0.0
    catify.lua - CLI entry point

    Usage:
        lua catify.lua <input.lua> [output.lua] [options]

    Options:
        --seed N        Use fixed random seed N (for reproducible output)
        --junk N        Number of junk-instruction clusters to inject (default: random 3-8)
        --no-strip      Do not strip debug info from the bytecode
        --passes N      Number of full obfuscation passes (default: 1; max: 3)

    Example:
        lua catify.lua myscript.lua myscript_protected.lua --junk 5 --passes 2
]]

-- ─── Bootstrap: locate src/ relative to this script ─────────────────────────
local script_dir = (arg[0] or "catify.lua"):match("^(.*[/\\])") or "./"
package.path = script_dir .. "src/?.lua;" .. package.path

local Utils  = require("utils")
local Parser = require("parser")
local Passes = require("passes")
local VmGen  = require("vm_gen")

-- ─── Banner ───────────────────────────────────────────────────────────────────
local BANNER = [[
   ____      _   _  __
  / ___|__ _| |_(_)/ _|_   _
 | |   / _` | __| | |_| | | |
 | |__| (_| | |_| |  _| |_| |
  \____\__,_|\__|_|_|  \__, |
                        |___/   v1.0.0 — Commercial Lua Obfuscator

  Options:
    --seed N        Use fixed random seed N (for reproducible output)
    --junk N        Number of junk-cluster insertion points (overrides --intensity)
    --intensity N   Junk density: 0=minimal 1=normal 2=high 3=extreme (default: 1)
    --no-strip      Do not strip debug info from the bytecode
    --passes N      Number of full obfuscation passes (default: 1; max: 3)
]]

-- Intensity → junk cluster count ranges
local INTENSITY_RANGES = {
    [0] = { min=1,  max=4  },
    [1] = { min=5,  max=14 },
    [2] = { min=12, max=24 },
    [3] = { min=20, max=40 },
}

-- ─── Argument parsing ─────────────────────────────────────────────────────────
local function parse_args(argv)
    local opts = {
        input      = nil,
        output     = nil,
        seed       = nil,
        junk_count = nil,
        strip      = true,
        passes     = 1,
        intensity  = 1,    -- 0=minimal, 1=normal, 2=high, 3=extreme
    }
    local i = 1
    while i <= #argv do
        local a = argv[i]
        if a == "--seed" then
            i = i + 1
            opts.seed = tonumber(argv[i]) or error("--seed requires a number")
        elseif a == "--junk" then
            i = i + 1
            opts.junk_count = math.max(0, math.floor(tonumber(argv[i])
                              or error("--junk requires a number")))
        elseif a == "--no-strip" then
            opts.strip = false
        elseif a == "--passes" then
            i = i + 1
            opts.passes = math.max(1, math.min(3, math.floor(tonumber(argv[i])
                          or error("--passes requires a number"))))
        elseif a == "--intensity" then
            i = i + 1
            opts.intensity = math.max(0, math.min(3, math.floor(tonumber(argv[i])
                             or error("--intensity requires a number 0-3"))))
        elseif a:sub(1, 2) == "--" then
            error("Unknown option: " .. a)
        elseif not opts.input then
            opts.input = a
        elseif not opts.output then
            opts.output = a
        else
            error("Unexpected argument: " .. a)
        end
        i = i + 1
    end
    return opts
end

-- ─── Helpers ──────────────────────────────────────────────────────────────────
local function read_file(path)
    local f, err = io.open(path, "rb")
    if not f then error("Cannot open '" .. path .. "': " .. err) end
    local data = f:read("*a")
    f:close()
    return data
end

local function write_file(path, data)
    local f, err = io.open(path, "wb")
    if not f then error("Cannot write '" .. path .. "': " .. err) end
    f:write(data)
    f:close()
end

local function info(fmt, ...)
    io.stderr:write(string.format("[Catify] " .. fmt .. "\n", ...))
end

-- ─── Main ─────────────────────────────────────────────────────────────────────
local function main(argv)
    io.stderr:write(BANNER .. "\n")

    local ok, opts_or_err = pcall(parse_args, argv)
    if not ok then
        io.stderr:write("Error: " .. tostring(opts_or_err) .. "\n\n")
        io.stderr:write("Usage: lua catify.lua <input.lua> [output.lua] [--seed N] [--junk N] [--intensity N] [--passes N] [--no-strip]\n")
        os.exit(1)
    end
    local opts = opts_or_err

    if not opts.input then
        io.stderr:write("Usage: lua catify.lua <input.lua> [output.lua] [--seed N] [--junk N] [--intensity N] [--passes N] [--no-strip]\n")
        os.exit(1)
    end

    -- Default output path
    if not opts.output then
        opts.output = opts.input:gsub("%.lua$", "") .. "_catified.lua"
    end

    -- Seed RNG
    local seed = opts.seed or math.floor(os.time() * 1000 % 2^31)
    math.randomseed(seed)
    info("Seed: %d", seed)

    -- ── Stage 1: Read and compile source ────────────────────────────────────
    info("Reading '%s'...", opts.input)
    local source = read_file(opts.input)

    info("Compiling Lua source...")
    local chunk, err = load(source, "@" .. opts.input)
    if not chunk then
        io.stderr:write("[Catify] Syntax error: " .. tostring(err) .. "\n")
        os.exit(1)
    end

    local bytecode = string.dump(chunk)
    info("Bytecode size: %d bytes", #bytecode)

    -- ── Stage 2: Parse bytecode ──────────────────────────────────────────────
    info("Parsing Lua 5.3 bytecode...")
    local ok2, proto_or_err = pcall(Parser.parse, bytecode)
    if not ok2 then
        io.stderr:write("[Catify] Parser error: " .. tostring(proto_or_err) .. "\n")
        os.exit(1)
    end
    local proto = proto_or_err
    info("Parsed: %d instructions, %d constants, %d nested protos",
         proto.sizecode, proto.sizek, proto.sizep)

    -- ── Stage 3: Obfuscation passes ──────────────────────────────────────────
    local result_code = nil
    local irange = INTENSITY_RANGES[opts.intensity] or INTENSITY_RANGES[1]
    info("Intensity: %d  (junk clusters %d-%d per function)", opts.intensity, irange.min, irange.max)

    for pass = 1, opts.passes do
        info("Obfuscation pass %d/%d...", pass, opts.passes)

        -- Generate a fresh random RC4 key per pass
        local key    = Utils.rand_key(math.random(24, 48))
        local pass_opts = {
            junk_count = opts.junk_count,   -- nil → random within intensity range
            junk_min   = irange.min,
            junk_max   = irange.max,
            strip      = opts.strip,
        }

        -- Run all bytecode-level passes
        local final_proto, revmap
        final_proto, revmap = Passes.run_all(proto, Utils, pass_opts)

        -- Generate VM + encrypted output
        info("  Generating VM code...")
        local generated = VmGen.generate(final_proto, revmap, key, Utils)
        info("  Generated VM size: %d bytes", #generated)

        if pass < opts.passes then
            -- Wrap the generated code and re-compile it for the next pass
            info("  Re-compiling output for next pass...")
            local wrap_fn, werr = load(generated, "@catify_pass" .. pass)
            if not wrap_fn then
                io.stderr:write("[Catify] Re-compile error (pass " .. pass .. "): " .. tostring(werr) .. "\n")
                os.exit(1)
            end
            bytecode = string.dump(wrap_fn)
            local ok3, p2 = pcall(Parser.parse, bytecode)
            if not ok3 then
                io.stderr:write("[Catify] Re-parse error: " .. tostring(p2) .. "\n")
                os.exit(1)
            end
            proto = p2
        else
            result_code = generated
        end
    end

    -- ── Stage 4: Write output ────────────────────────────────────────────────
    info("Writing '%s'...", opts.output)
    write_file(opts.output, result_code)

    -- Summary
    local original_size = #source
    local output_size   = #result_code
    info("Done!  %d → %d bytes  (%.1fx)",
         original_size, output_size, output_size / math.max(1, original_size))
    info("Protected with: opcode shuffle, RC4 encryption, debug strip, junk injection (intensity %d), VM dispatch obfuscation, anti-tamper (10 checks)", opts.intensity)
end

main(arg)
