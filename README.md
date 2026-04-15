# Catify — Lua Script Protector

**Catify** is a commercial-grade Lua 5.3 obfuscator that transforms scripts into self-contained,
heavily protected VM bytecode — matching the `superflow_bytecode` format used by Luarmor V4.

---

## Features

| Protection layer | Details |
|---|---|
| **Custom VM** | Full Lua 5.3 VM in generated source; all 47 opcodes + virtual decoy opcodes |
| **Opcode shuffle** | Real opcode numbers replaced by random shuffled IDs per output |
| **AES-256-CTR encryption** | Bytecode payload encrypted with a fresh 32-byte key + 8-byte nonce per run |
| **`\NNN` payload escapes** | Encrypted blob emitted as a Lua `\NNN` escaped string (`superflow_bytecode`) |
| **SHA-256 integrity** | Runtime SHA-256 check on the encrypted blob (8 obfuscated word comparisons) |
| **Anti-keylogger checks** | Runtime checks for debug hook, io library, string metatable, pcall integrity |
| **Debug-hook detection** | Detects `debug.sethook` / `debug.getinfo` usage at runtime |
| **Environment check** | Verifies critical globals and detects common env/logger hook patterns |
| **Junk injection** | Dead-code statements sprinkled throughout the VM dispatch loop |
| **ASCII cat watermark** | Obfuscated watermark string embedded in generated output |

---

## Quick Start

```bash
# Single-pass obfuscation
lua catify.lua myscript.lua output.lua

# Two-pass (VM wrapped inside another VM — much harder to reverse)
lua catify.lua --passes 2 myscript.lua output.lua

# Tiny Roblox output (runtime loaded remotely via HttpGet)
lua catify.lua myscript.lua output.lua --roblox

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
| `CATIFY_ROBLOX` | `false` | Enable tiny Roblox HTTP-runtime output mode |
| `CATIFY_ROBLOX_RUNTIME_URL` | `""` | Optional custom runtime URL for Roblox mode (enables Roblox mode when set) |
| `CATIFY_MAX_INLINE` | `32768` | Max inline code size in bytes |
| `CATIFY_MAX_FILE` | `524288` | Max attachment size in bytes |

---

## Output Format

The generated file looks like:

```lua
superflow_bytecode="\123\034\255..." -- \NNN-escaped encrypted payload
do
local <aes_sbox>={[0]=99,124,...}       -- AES S-box
local function <aes_xtime>(...) ... end
local function <aes_key_expand>(...) ... end
local function <aes_enc_block>(...) ... end
local function <aes_ctr_decrypt>(...) ... end  -- AES-256-CTR
-- SHA-256 integrity check, anti-keylogger checks …
-- deserializer, VM execute function …
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
  utils.lua         – AES-256-CTR, SHA-256, byte escaping, CRC-32, random name generator
bot/
  discord_bot.js    – discord.js (Node.js) Discord bot
  package.json      – Node.js dependencies
  .env.example      – Example environment config (copy to .env)
.gitignore          – Excludes bot/.env (secrets)
```
