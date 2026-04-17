/*
    Catify Discord Bot — bot/discord_bot.js

    A Discord bot that obfuscates Lua 5.3 scripts on demand.

    Requires:
      • Node.js >= 18
      • discord.js  (npm install)
      • dotenv      (npm install)
      • Lua 5.3 runtime in PATH (`lua5.3`, `lua53`, or configured via CATIFY_LUA_BIN)

    Quick start:
      1.  Copy bot/.env.example → bot/.env and fill in your token.
      2.  Run:  npm install && npm start

    Commands (prefix configurable via CATIFY_PREFIX, default "!"):
      !catify  <code>       — Obfuscate inline Lua code (wrap in a ```lua block
                              or paste raw; the bot strips code-fence markdown).
      !catify  (attachment) — Upload a .lua/.txt file; the bot obfuscates it and
                              returns the protected file as an attachment.
      !catify  help         — Show usage information.
*/

"use strict";

require("dotenv").config({ path: __dirname + "/.env" });

const {
    Client,
    GatewayIntentBits,
    AttachmentBuilder,
} = require("discord.js");

const { execFile } = require("child_process");
const { promisify } = require("util");
const execFileAsync = promisify(execFile);

const crypto = require("crypto");
const fs   = require("fs");
const os   = require("os");
const path = require("path");
const https = require("https");
const http  = require("http");

// ── Configuration ──────────────────────────────────────────────────────────────
const TOKEN        = process.env.CATIFY_TOKEN  || null;
const PREFIX       = process.env.CATIFY_PREFIX || "!";
const PASSES       = Math.max(1, Math.min(2, parseInt(process.env.CATIFY_PASSES  || "1", 10)));
const MAX_INLINE   = parseInt(process.env.CATIFY_MAX_INLINE || String(32  * 1024), 10);
const MAX_FILE     = parseInt(process.env.CATIFY_MAX_FILE   || String(512 * 1024), 10);
const LUA_BIN      = (process.env.CATIFY_LUA_BIN || "").trim();
const LUA_VERSION_CHECK_TIMEOUT_MS = 5000;
// Generated protected outputs are substantially larger than tiny/invalid fragments; this guards obvious bad outputs.
const MIN_PROTECTED_OUTPUT_LENGTH = 200;
const PROTECTED_HEADER_REGEX = /^-- This file was protected by Catify v\d+\.\d+\.\d+(?:[-+][A-Za-z0-9.-]+)?/;
const PROTECTED_OUTPUT_MARKERS = [
    /\bsuperflow_bytecode\s*=/,
    /\bsetmetatable\(\{\[0\]=/,
    /\blocal\s+function\s+\w+\(/,
];

if (!TOKEN) {
    console.error("Error: CATIFY_TOKEN is not set. Create bot/.env from .env.example.");
    process.exit(1);
}

// Resolve the catify CLI entry point (one directory up from bot/)
const CATIFY_CLI = path.resolve(__dirname, "..", "catify.lua");
const ALLOWED_ATTACHMENT_EXTENSIONS = new Set([".lua", ".txt"]);
const LUA_BIN_CANDIDATES = LUA_BIN ? [LUA_BIN] : ["lua5.3", "lua53", "lua"];
let lua53RuntimePromise = null;

// ── Helpers ────────────────────────────────────────────────────────────────────

/** Strip ```lua … ``` or ``` … ``` or `…` code-fence markdown from a Discord message. */
function stripCodeFence(text) {
    // Strip triple backtick code fences (e.g. ```lua\n...\n```)
    text = text
        .replace(/^```[a-zA-Z]*\s*/, "")
        .replace(/\s*```\s*$/, "")
        .trim();
    // Strip single backtick inline code (e.g. `print("hello")`)
    // Only strip when there is exactly one backtick on each side (not `` or ```)
    if (
        text.startsWith("`") && text.endsWith("`") && text.length >= 2 &&
        !text.startsWith("``") && !text.endsWith("``")
    ) {
        text = text.slice(1, -1);
    }
    return text;
}

/** Truncate a string for safe display inside a Discord message. */
function truncate(s, max) {
    if (s.length <= max) return s;
    return s.slice(0, max - 3) + "...";
}

/**
 * Produce a user-safe obfuscation error string with script-focused details only.
 * @param {unknown} err
 * @returns {string}
 */
function formatObfuscationError(err) {
    const raw = String((err && (err.stderr || err.message)) || "").replace(/\r/g, "");
    if (/\[Catify\]\s*Unsupported Lua runtime/i.test(raw)) {
        return "❌ Catify bot config error: Lua 5.3 is required on the bot host. " +
            "Install/use 'lua5.3' or set 'CATIFY_LUA_BIN' to a Lua 5.3 executable.";
    }
    if ((err && err.code) === "CATIFY_LUA53_NOT_FOUND") {
        return "❌ Catify bot config error: Lua 5.3 runtime was not found. " +
            "Install Lua 5.3 and/or set 'CATIFY_LUA_BIN' in bot/.env.";
    }
    if ((err && err.code) === "CATIFY_LUA_BIN_INVALID") {
        return "❌ Catify bot config error: CATIFY_LUA_BIN contains invalid characters. " +
            "Use only an executable name/path (no spaces or arguments).";
    }
    const lines = raw.split("\n").map((s) => s.trim()).filter(Boolean);
    const catifyLine = lines.find((line) =>
        /\[Catify\]\s*(Syntax error|Parser error|Re-compile error|Re-parse error)/i.test(line)
    );
    const detail = (catifyLine || lines[lines.length - 1] || "unknown error")
        .replace(/^\[Catify\]\s*/i, "");
    return "error while obfuscating. due to the error in your script:\n```\n" +
        truncate(detail, 1800) +
        "\n```";
}

/**
 * Resolve a Lua 5.3 executable from configured/default candidates.
 * @returns {Promise<string>}
 */
async function resolveLua53Runtime() {
    if (LUA_BIN && !isValidLuaBin(LUA_BIN)) {
        const err = new Error("Invalid CATIFY_LUA_BIN value");
        err.code = "CATIFY_LUA_BIN_INVALID";
        throw err;
    }
    for (const bin of LUA_BIN_CANDIDATES) {
        try {
            const { stdout } = await execFileAsync(bin, ["-e", "io.write(_VERSION or '')"], {
                timeout: LUA_VERSION_CHECK_TIMEOUT_MS,
            });
            const versionLine = String(stdout || "").trim();
            if (/^Lua\s+5\.3\b/i.test(versionLine)) {
                return bin;
            }
        } catch (_) {
            // Try next candidate.
        }
    }
    const err = new Error("Lua 5.3 runtime not found");
    err.code = "CATIFY_LUA53_NOT_FOUND";
    throw err;
}

function getLua53Runtime() {
    if (!lua53RuntimePromise) lua53RuntimePromise = resolveLua53Runtime();
    return lua53RuntimePromise;
}

function isValidLuaBin(value) {
    if (!value || /\s/.test(value) || value.startsWith("-")) return false;
    if (path.isAbsolute(value)) {
        const normalized = path.normalize(value);
        return !normalized.split(path.sep).includes("..");
    }
    return /^[A-Za-z0-9_.-]+$/.test(value);
}

/**
 * Validate minimal structural integrity of Catify output before replying to the user.
 * @param {string} content
 * @returns {boolean}
 */
function hasValidProtectedOutput(content) {
    if (typeof content !== "string" || content.length === 0) return false;
    if (content.length < MIN_PROTECTED_OUTPUT_LENGTH) return false;
    if (!PROTECTED_HEADER_REGEX.test(content)) return false;
    for (const marker of PROTECTED_OUTPUT_MARKERS) {
        if (!marker.test(content)) return false;
    }
    return true;
}

/**
 * Build output attachment name by appending `_catified` and preserving extension.
 * @param {string} inputName
 * @returns {string}
 */
function buildOutputAttachmentName(inputName) {
    const parsed = path.parse(inputName || "catified.lua");
    const ext = parsed.ext || ".lua";
    return `${parsed.name}_catified${ext}`;
}

/**
 * Download a URL and resolve with the buffer, or reject on error.
 * @param {string} url
 * @returns {Promise<Buffer>}
 */
function downloadUrl(url) {
    return new Promise((resolve, reject) => {
        const mod = url.startsWith("https") ? https : http;
        mod.get(url, (res) => {
            if (res.statusCode !== 200) {
                return reject(new Error(`HTTP ${res.statusCode}`));
            }
            const chunks = [];
            res.on("data", (chunk) => chunks.push(chunk));
            res.on("end",  () => resolve(Buffer.concat(chunks)));
            res.on("error", reject);
        }).on("error", reject);
    });
}

/**
 * Run the Catify CLI on the given source string.
 * Writes a temp input file, invokes `lua catify.lua`, reads the output.
 *
 * @param {string} source  Raw Lua source code.
 * @param {number} passes  Number of obfuscation passes.
 * @returns {Promise<string>}  Obfuscated Lua source.
 */
async function obfuscate(source, passes) {
    const tmpDir  = os.tmpdir();
    const id      = crypto.randomUUID();
    const inFile  = path.join(tmpDir, `catify_in_${id}.lua`);
    const outFile = path.join(tmpDir, `catify_out_${id}.lua`);

    try {
        fs.writeFileSync(inFile, source, "utf8");
        const luaRuntime = await getLua53Runtime();

        await execFileAsync(luaRuntime, [
            CATIFY_CLI,
            inFile,
            outFile,
            "--passes", String(passes),
        ], { timeout: 60000 });

        return fs.readFileSync(outFile, "utf8");
    } finally {
        try { fs.unlinkSync(inFile);  } catch (_) {}
        try { fs.unlinkSync(outFile); } catch (_) {}
    }
}

// ── Help text ─────────────────────────────────────────────────────────────────
const HELP_TEXT = `**Catify obfuscator**
Prefix: \`${PREFIX}\`

**Commands:**
\`${PREFIX}catify <code>\`  — Obfuscate inline Lua code.
  • Wrap your code in a \`\`\`lua\`\`\` block for best formatting.
  • Example:  \`${PREFIX}catify print("hello")\`

\`${PREFIX}catify\` *(with .lua/.txt attachment)*  — Obfuscate an uploaded \`.lua\` or \`.txt\` file.
  The bot replies with the protected file as a download.

\`${PREFIX}catify help\`  — Show this message.

**love applied:**
***too much***`;

// ── Discord client ─────────────────────────────────────────────────────────────
const client = new Client({
    intents: [
        GatewayIntentBits.Guilds,
        GatewayIntentBits.GuildMessages,
        GatewayIntentBits.MessageContent,
    ],
});

client.once("ready", () => {
    console.log(`[Catify Bot] Logged in as ${client.user.tag}`);
    console.log(`[Catify Bot] Prefix: ${PREFIX}`);
    console.log(`[Catify Bot] Ready!`);
    client.user.setActivity(`Catify | ${PREFIX}catify help`);
});

// ── Command handler ───────────────────────────────────────────────────────────
client.on("messageCreate", async (message) => {
    // Ignore bots
    if (message.author.bot) return;

    const content = message.content || "";
    const cmdFull = `${PREFIX}catify`;

    // Must start with the command prefix (case-insensitive)
    if (!content.toLowerCase().startsWith(cmdFull.toLowerCase())) return;

    // Everything after "!catify"
    const arg = content.slice(cmdFull.length).trim();

    // ── File attachment mode ─────────────────────────────────────────────────
    const attachment = message.attachments.first();
    if (attachment) {
        const attachmentExt = path.extname((attachment.name || "").toLowerCase());
        if (!ALLOWED_ATTACHMENT_EXTENSIONS.has(attachmentExt)) {
            await message.reply("❌ Attachment must be a `.lua` or `.txt` file.");
            return;
        }
        const size = attachment.size || 0;
        if (size > MAX_FILE) {
            await message.reply(
                `❌ Attachment too large (${Math.round(size / 1024)} KB, max ${MAX_FILE / 1024} KB).`
            );
            return;
        }

        await message.reply("⏳ Obfuscating attachment… please wait.");

        let source;
        try {
            const buf = await downloadUrl(attachment.url);
            source = buf.toString("utf8");
        } catch (err) {
            await message.reply("❌ Failed to download attachment.");
            return;
        }

        let result;
        try {
            result = await obfuscate(source, PASSES);
        } catch (err) {
            await message.reply(formatObfuscationError(err));
            return;
        }
        if (!hasValidProtectedOutput(result)) {
            await message.reply("❌ Integrity check failed for protected output. Try again.");
            return;
        }

        const ratio = (result.length / Math.max(1, source.length)).toFixed(1);
        await message.reply({
            content: "Obfuscated successfully",
            files: [new AttachmentBuilder(Buffer.from(result, "utf8"), { name: buildOutputAttachmentName(attachment.name) })],
        });
        return;
    }

    // ── Help ─────────────────────────────────────────────────────────────────
    if (arg === "" || arg.toLowerCase() === "help") {
        await message.reply(HELP_TEXT);
        return;
    }

    // ── Inline code mode ─────────────────────────────────────────────────────
    const source = stripCodeFence(arg);
    if (source.length > MAX_INLINE) {
        await message.reply(
            `❌ Code too large for inline obfuscation (${source.length} bytes, max ${MAX_INLINE / 1024} KB). ` +
            "Please upload a `.lua` or `.txt` file instead."
        );
        return;
    }

    await message.reply("⏳ Obfuscating…");

    let result;
    try {
        result = await obfuscate(source, PASSES);
    } catch (err) {
        await message.reply(formatObfuscationError(err));
        return;
    }
    if (!hasValidProtectedOutput(result)) {
        await message.reply("❌ Integrity check failed for protected output. Try again.");
        return;
    }

    const ratio = (result.length / Math.max(1, source.length)).toFixed(1);

    if (result.length <= 1900) {
        await message.reply("Obfuscated successfully\n```lua\n" + result + "\n```");
    } else {
        await message.reply({
            content: "Obfuscated successfully",
            files: [new AttachmentBuilder(Buffer.from(result, "utf8"), { name: "catified.lua" })],
        });
    }
});

// ── Login ─────────────────────────────────────────────────────────────────────
client.login(TOKEN);
