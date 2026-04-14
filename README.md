# Catify — Lua Script Protector

**Catify** is a commercial-grade Lua 5.3 obfuscator that transforms scripts into self-contained,
heavily protected VM bytecode — matching the `superflow_bytecode` format used by Luarmor V4.

---

## Features

| Protection layer | Details |
|---|---|
| **Custom VM** | Full Lua 5.3 VM in generated source; all 47 opcodes implemented |
| **Opcode shuffle** | Real opcode numbers replaced by random shuffled IDs per output |
| **RC4 encryption** | Bytecode payload encrypted; key embedded in obfuscated form |
| **`superflow_bytecode`** | Chunked payload table identical to the Luarmor V4 reference format |
| **CRC-32 integrity** | Runtime CRC-32 check on the encrypted blob — exits on tampering |
| **Debug-hook detection** | Detects `debug.sethook` / `debug.getinfo` usage at runtime |
| **Environment check** | Verifies critical globals (`tostring`, `type`, `string`, …) are intact |
| **Junk injection** | Dead-code statements sprinkled throughout the VM dispatch loop |

---

## Quick Start

```bash
# Single-pass obfuscation
lua catify.lua myscript.lua output.lua

# Two-pass (VM wrapped inside another VM — much harder to reverse)
lua catify.lua --passes 2 myscript.lua output.lua

# Run the obfuscated script
lua output.lua
```

---

## Discord Bot

The `bot/` directory contains a **Discordia** (Luvit) Discord bot that exposes Catify as a
slash command.

### Setup

1. Install **Luvit** from https://luvit.io/  
2. Install Discordia: `lit install SinisterRectus/discordia`  
3. Copy the example config and add your token:
   ```bash
   cp bot/config.example.lua bot/config.lua
   # Edit bot/config.lua and set `token = "YOUR_BOT_TOKEN"`
   ```
4. Start the bot:
   ```bash
   luvit bot/discord_bot.lua
   ```

### Commands

| Command | Description |
|---|---|
| `!catify help` | Show usage |
| `!catify print("hi")` | Obfuscate inline Lua code |
| `!catify` + `.lua` file | Upload a file; bot returns the protected version |

### Environment variables (alternative to config.lua)

| Variable | Default | Description |
|---|---|---|
| `CATIFY_TOKEN` | — | Discord bot token (required if no config.lua) |
| `CATIFY_PREFIX` | `!` | Command prefix |

---

## Output Format

The generated file looks like:

```lua
--[[
    Catify — Lua Script Protector
    https://github.com/francyw22/catempire
]]
superflow_bytecode={"\152\168\186...", "\33\31\156..."};
do
local function <RC4_decrypt>(...) ... end
-- deserializer, VM execute function, anti-tamper checks …
end
```

---

## Project Structure

```
catify.lua          – CLI entry point
src/
  parser.lua        – Lua 5.3 bytecode parser
  passes.lua        – Obfuscation passes (opcode shuffle, junk injection…)
  vm_gen.lua        – VM source code generator
  utils.lua         – RC4, CRC-32, random name generator
bot/
  discord_bot.lua   – Discordia/Luvit Discord bot
  catify_api.lua    – In-process API wrapper around the pipeline
  config.example.lua– Example configuration (copy to config.lua)
.gitignore          – Excludes bot/config.lua (secrets)
```
