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

The `bot/` directory contains a **discord.js** (Node.js) Discord bot that exposes Catify as a
chat command.

### Requirements

- Node.js ≥ 18
- `lua` 5.3+ in your `PATH`

### Setup

1. Install Node.js dependencies:
   ```bash
   cd bot
   npm install
   ```
2. Copy the example env file and add your token:
   ```bash
   cp bot/.env.example bot/.env
   # Edit bot/.env and set CATIFY_TOKEN=YOUR_BOT_TOKEN
   ```
3. Enable the **Message Content** privileged intent for your bot at
   https://discord.com/developers/applications
4. Start the bot:
   ```bash
   npm start
   ```

### Commands

| Command | Description |
|---|---|
| `!catify help` | Show usage |
| `!catify print("hi")` | Obfuscate inline Lua code |
| `!catify` + `.lua` file | Upload a file; bot returns the protected version |

### Environment variables

| Variable | Default | Description |
|---|---|---|
| `CATIFY_TOKEN` | — | Discord bot token (required) |
| `CATIFY_PREFIX` | `!` | Command prefix |
| `CATIFY_PASSES` | `1` | Obfuscation passes (1 or 2) |
| `CATIFY_MAX_INLINE` | `32768` | Max inline code size in bytes |
| `CATIFY_MAX_FILE` | `524288` | Max attachment size in bytes |

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
  discord_bot.js    – discord.js (Node.js) Discord bot
  package.json      – Node.js dependencies
  .env.example      – Example environment config (copy to .env)
.gitignore          – Excludes bot/.env (secrets)
```
