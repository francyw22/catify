/*
    Catify Discord Bot — bot/discord_bot.js

    A Discord bot that obfuscates Lua 5.3 scripts on demand.

    Requires:
      • Node.js >= 18
      • discord.js  (npm install)
      • dotenv      (npm install)
      • lua 5.3+ in PATH

    Quick start:
      1.  Copy bot/.env.example → bot/.env and fill in your token.
      2.  Run:  npm install && npm start

    Commands (prefix configurable via CATIFY_PREFIX, default "!"):
      !catify  <code>       — Obfuscate inline Lua code (wrap in a ```lua block
                              or paste raw; the bot strips code-fence markdown).
      !catify  (attachment) — Upload a .lua file; the bot obfuscates it and
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

if (!TOKEN) {
    console.error("Error: CATIFY_TOKEN is not set. Create bot/.env from .env.example.");
    process.exit(1);
}

// Resolve the catify CLI entry point (one directory up from bot/)
const CATIFY_CLI = path.resolve(__dirname, "..", "catify.lua");

// ── Helpers ────────────────────────────────────────────────────────────────────

/** Strip ```lua … ``` or ``` … ``` or `…` code-fence markdown from a Discord message. */
function stripCodeFence(text) {
    // Strip triple backtick code fences (e.g. ```lua\n...\n```)
    text = text
        .replace(/^```[a-zA-Z]*\s*/, "")
        .replace(/\s*```\s*$/, "")
        .trim();
    // Strip single backtick inline code (e.g. `print("hello")`)
    if (text.startsWith("`") && text.endsWith("`") && text.length >= 2) {
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

        await execFileAsync("lua", [
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
const HELP_TEXT = `**Catify — Lua Script Protector**
Prefix: \`${PREFIX}\`

**Commands:**
\`${PREFIX}catify <code>\`  — Obfuscate inline Lua code.
  • Wrap your code in a \`\`\`lua\`\`\` block for best formatting.
  • Example:  \`${PREFIX}catify print("hello")\`

\`${PREFIX}catify\` *(with .lua attachment)*  — Obfuscate an uploaded \`.lua\` file.
  The bot replies with the protected file as a download.

\`${PREFIX}catify help\`  — Show this message.

**Protections applied:**
• Custom opcode shuffle (VM-based execution)
• RC4 encryption of bytecode payload
• CRC-32 payload integrity check (anti-tamper)
• Debug-hook detection
• Critical-global environment verification`;

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
        if (!attachment.name.endsWith(".lua")) {
            await message.reply("❌ Attachment must be a `.lua` file.");
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
            await message.reply(
                "❌ Obfuscation failed:\n```\n" + truncate(String(err.stderr || err.message), 1800) + "\n```"
            );
            return;
        }

        const ratio = (result.length / Math.max(1, source.length)).toFixed(1);
        await message.reply({
            content:
                `✅ Script protected! (${source.length} → ${result.length} bytes, ${ratio}×)\n` +
                "**Protections:** opcode shuffle · RC4 encryption · CRC-32 · debug-hook detection · env check",
            files: [new AttachmentBuilder(Buffer.from(result, "utf8"), { name: attachment.name })],
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
            "Please upload a `.lua` file instead."
        );
        return;
    }

    await message.reply("⏳ Obfuscating…");

    let result;
    try {
        result = await obfuscate(source, PASSES);
    } catch (err) {
        await message.reply(
            "❌ Obfuscation failed:\n```\n" + truncate(String(err.stderr || err.message), 1800) + "\n```"
        );
        return;
    }

    const ratio = (result.length / Math.max(1, source.length)).toFixed(1);

    if (result.length <= 1900) {
        await message.reply("✅ Protected!\n```lua\n" + result + "\n```");
    } else {
        await message.reply({
            content:
                `✅ Script protected! (${source.length} → ${result.length} bytes, ${ratio}×)\n` +
                "**Protections:** opcode shuffle · RC4 · CRC-32 · anti-debug · env check",
            files: [new AttachmentBuilder(Buffer.from(result, "utf8"), { name: "catified.lua" })],
        });
    }
});

// ── Login ─────────────────────────────────────────────────────────────────────
client.login(TOKEN);
