--[[
    Catify Bot Configuration — bot/config.lua

    Copy this file to bot/config.lua and fill in your values.
    DO NOT commit the real config.lua to version control (it is in .gitignore).
]]

return {
    -- Required: Your Discord bot token from https://discord.com/developers/applications
    token = "YOUR_BOT_TOKEN_HERE",

    -- Command prefix (default "!")
    prefix = "!",

    -- Number of obfuscation passes (1 or 2).
    -- Pass 2 wraps the entire obfuscated VM inside a second VM layer.
    -- This makes the output ~10× larger but significantly harder to reverse.
    passes = 1,

    -- Maximum Lua source size for inline (in-message) obfuscation (bytes)
    max_inline_bytes = 32 * 1024,      -- 32 KB

    -- Maximum Lua source size for file-attachment obfuscation (bytes)
    max_file_bytes = 512 * 1024,       -- 512 KB

    -- Obfuscation timeout in milliseconds (unused currently, reserved)
    timeout_ms = 30000,
}
