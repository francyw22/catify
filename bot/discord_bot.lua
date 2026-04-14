--[[
    Catify Discord Bot — bot/discord_bot.lua

    A Discord bot that obfuscates Lua 5.3 scripts on demand.

    Requires:
      • Luvit  (https://luvit.io/)  — async Lua runtime with libuv
      • discordia  (https://github.com/SinisterRectus/Discordia)
            Install:  lit install SinisterRectus/discordia

    Quick start:
      1.  Copy bot/config.example.lua → bot/config.lua and fill in your token.
      2.  Run:   luvit bot/discord_bot.lua

    Commands (prefix configurable in config.lua, default "!"):
      !catify  <code>          — Obfuscate inline Lua code (wrap in a code block
                                 or paste raw; the bot strips ```lua ... ``` fences).
      !catify  (attachment)    — Upload a .lua file; the bot obfuscates it and
                                 returns the protected file as an attachment.
      !catify  help            — Show usage information.

    Anti-tamper notes shown in responses:
      The generated output includes:
        • CRC-32 payload integrity check
        • Debug-hook detection
        • Critical-global environment verification
        • RC4-encrypted bytecode + custom opcode shuffle
]]

local discordia = require("discordia")
local http      = require("coro-http")
local timer     = require("timer")
local fs        = require("fs")
local path      = require("path")

-- ── Configuration ─────────────────────────────────────────────────────────────
local config_path = path.join(path.dirname(debug.getinfo(1,"S").source:sub(2)), "config.lua")
local config = {}
if fs.existsSync(config_path) then
    config = dofile(config_path)
else
    -- Fallback: read token from environment variable CATIFY_TOKEN
    config.token  = os.getenv("CATIFY_TOKEN") or error("No bot token found. Set CATIFY_TOKEN or create bot/config.lua")
    config.prefix = os.getenv("CATIFY_PREFIX") or "!"
end

local PREFIX      = config.prefix or "!"
local MAX_INLINE  = config.max_inline_bytes  or  32 * 1024   -- 32 KB inline code limit
local MAX_FILE    = config.max_file_bytes    or 512 * 1024   -- 512 KB attachment limit
local TIMEOUT_MS  = config.timeout_ms        or 30000        -- 30 s obfuscation timeout
local PASSES      = config.passes            or 1

-- ── Load Catify API ──────────────────────────────────────────────────────────
local CatifyAPI = require("catify_api")   -- resolved relative to bot/ via package.path

-- ── Helper utilities ─────────────────────────────────────────────────────────

--- Strip ```lua … ``` or ``` … ``` code-fence markdown from a Discord message.
local function strip_code_fence(text)
    -- Remove opening fence (```lua or ```)
    text = text:gsub("^%s*```[%a]*%s*", "")
    -- Remove closing fence
    text = text:gsub("%s*```%s*$", "")
    return text
end

--- Truncate a string for safe display inside a Discord message.
local function truncate(s, max)
    if #s <= max then return s end
    return s:sub(1, max - 3) .. "..."
end

--- Send a plain-text reply that auto-deletes after `delay` seconds (0 = no delete).
local function reply(message, text, delay)
    local msg = message:reply(text)
    if delay and delay > 0 and msg then
        timer.setTimeout(delay * 1000, function() pcall(function() msg:delete() end) end)
    end
end

--- Download the first .lua attachment from a message.
--- Returns (content_string, filename) or (nil, err_string).
local function download_attachment(message)
    local attachment = message.attachments and message.attachments:first()
    if not attachment then
        return nil, "No attachment found."
    end
    local filename = attachment.filename or "script.lua"
    if not filename:match("%.lua$") then
        return nil, "Attachment must be a `.lua` file."
    end
    local size = attachment.size or 0
    if size > MAX_FILE then
        return nil, string.format("Attachment too large (%d KB, max %d KB).", size // 1024, MAX_FILE // 1024)
    end

    local ok, res, body = pcall(http.request, "GET", attachment.url)
    if not ok or res.code ~= 200 then
        return nil, "Failed to download attachment."
    end
    return body, filename
end

--- Run CatifyAPI.obfuscate in a protected call and return results.
local function do_obfuscate(source, passes)
    return CatifyAPI.obfuscate(source, { passes = passes })
end

-- ── Bot setup ─────────────────────────────────────────────────────────────────
local client = discordia.Client()

local HELP_TEXT = string.format([[
**Catify — Lua Script Protector**
Prefix: `%s`

**Commands:**
`%scatify <code>`  — Obfuscate inline Lua code.
  • Wrap your code in a ` ```lua ` block for best formatting.
  • Example:  `%scatify print("hello")`

`%scatify` *(with .lua attachment)*  — Obfuscate an uploaded `.lua` file.
  The bot replies with the protected file as a download.

`%scatify help`  — Show this message.

**Protections applied:**
• Custom opcode shuffle (VM-based execution)
• RC4 encryption of bytecode payload (`superflow_bytecode` format)
• CRC-32 payload integrity check (anti-tamper)
• Debug-hook detection
• Critical-global environment verification
]], PREFIX, PREFIX, PREFIX, PREFIX, PREFIX)

-- ── Command handler ───────────────────────────────────────────────────────────
client:on("messageCreate", function(message)
    -- Ignore bots
    if message.author.bot then return end

    local content = message.content or ""

    -- Check prefix
    if not content:find("^" .. PREFIX:gsub("[%(%)%.%%%+%-%*%?%[%^%$]", "%%%1"), 1, false) then
        return
    end

    -- Parse command
    local cmd_prefix = PREFIX .. "catify"
    if not content:lower():find("^" .. cmd_prefix:lower(), 1, true) then
        return
    end

    -- Everything after "!catify"
    local arg = content:sub(#cmd_prefix + 1):match("^%s*(.*)")

    -- Help
    if arg == "" or arg:lower() == "help" then
        -- If there's an attachment, fall through to file handling
        if arg == "" and not (message.attachments and message.attachments:first()) then
            message:reply(HELP_TEXT)
            return
        end
    end

    -- File attachment mode
    if message.attachments and message.attachments:first() then
        message:reply("⏳ Obfuscating attachment… please wait.")
        local source, err = download_attachment(message)
        if not source then
            message:reply("❌ " .. err)
            return
        end

        local ok, result = do_obfuscate(source, PASSES)
        if not ok then
            message:reply("❌ Obfuscation failed:\n```\n" .. truncate(result, 1800) .. "\n```")
            return
        end

        -- Write to a temp file and send as attachment
        local tmp = os.tmpname() .. ".lua"
        local f = io.open(tmp, "w")
        if f then
            f:write(result)
            f:close()
            message:reply {
                content = string.format(
                    "✅ Script protected! (%d → %d bytes, %.1fx)\n" ..
                    "**Protections:** opcode shuffle · RC4 encryption · CRC-32 · debug-hook detection · env check",
                    #source, #result, #result / math.max(1, #source)),
                file = tmp,
            }
            os.remove(tmp)
        else
            -- Fallback: send as code block (may be truncated)
            message:reply(
                "✅ Done!\n```lua\n" .. truncate(result, 1900) .. "\n```\n*(truncated — file too large)*")
        end
        return
    end

    -- Inline code mode
    if arg == "" or arg:lower() == "help" then
        message:reply(HELP_TEXT)
        return
    end

    local source = strip_code_fence(arg)
    if #source > MAX_INLINE then
        message:reply(string.format(
            "❌ Code too large for inline obfuscation (%d bytes, max %d KB). Please upload a `.lua` file instead.",
            #source, MAX_INLINE // 1024))
        return
    end

    message:reply("⏳ Obfuscating…")
    local ok, result = do_obfuscate(source, PASSES)
    if not ok then
        message:reply("❌ Obfuscation failed:\n```\n" .. truncate(result, 1800) .. "\n```")
        return
    end

    -- Send result
    if #result <= 1900 then
        message:reply("✅ Protected!\n```lua\n" .. result .. "\n```")
    else
        -- Too long for a code block — send as a file
        local tmp = os.tmpname() .. ".lua"
        local f = io.open(tmp, "w")
        if f then
            f:write(result)
            f:close()
            message:reply {
                content = string.format(
                    "✅ Script protected! (%d → %d bytes, %.1fx)\n" ..
                    "**Protections:** opcode shuffle · RC4 · CRC-32 · anti-debug · env check",
                    #source, #result, #result / math.max(1, #source)),
                file = tmp,
            }
            os.remove(tmp)
        else
            message:reply("✅ Done!\n```lua\n" .. truncate(result, 1900) .. "\n```")
        end
    end
end)

-- ── Ready event ───────────────────────────────────────────────────────────────
client:on("ready", function()
    print(string.format("[Catify Bot] Logged in as %s#%s",
        client.user.username, client.user.discriminator))
    print("[Catify Bot] Prefix: " .. PREFIX)
    print("[Catify Bot] Ready!")
    client:setActivity("Catify | " .. PREFIX .. "catify help")
end)

-- ── Login ─────────────────────────────────────────────────────────────────────
client:run("Bot " .. config.token)
