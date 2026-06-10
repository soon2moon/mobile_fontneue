// Minimal puppeteer-core client for the smoke checks in this directory.
//
// Requirements:
//  1. The app dev server running (default http://localhost:5174/, override APP_URL).
//  2. A Chromium-based browser listening for CDP on port 9223 (override BROWSER_URL), e.g.:
//     chrome --headless=new --no-sandbox --remote-debugging-port=9223 \
//       --user-data-dir=/tmp/cft-profile --window-size=1440,900 about:blank
//  3. puppeteer-core resolvable: `npm i -D puppeteer-core` or set PPTR_MODULES to a
//     node_modules directory that contains it.
//
// Run a check with: node scripts/verify/<check>.mjs

import { mkdirSync } from 'node:fs';
mkdirSync('/tmp/shots', { recursive: true }); // checks save screenshots here

const PPTR_MODULES = process.env.PPTR_MODULES
  || '/home/ucan/.claude/plugins/cache/claude-plugins-official/chrome-devtools-mcp/1.2.0/node_modules';

let puppeteer;
try {
  ({ default: puppeteer } = await import('puppeteer-core'));
} catch {
  ({ default: puppeteer } = await import(`${PPTR_MODULES}/puppeteer-core/lib/puppeteer/puppeteer-core.js`));
}

const BROWSER_URL = process.env.BROWSER_URL || 'http://127.0.0.1:9223';
export const APP_URL = process.env.APP_URL || 'http://localhost:5174/';

export async function withPage(fn, { fresh = false } = {}) {
  const browser = await puppeteer.connect({ browserURL: BROWSER_URL, defaultViewport: null });
  const pages = await browser.pages();
  let page = pages.find(p => p.url().startsWith('http://localhost')) || pages[0];
  if (!page || fresh) page = await browser.newPage();
  const consoleMessages = [];
  page.on('console', m => {
    const type = m.type();
    if (type === 'error' || type === 'warn' || type === 'warning') {
      consoleMessages.push({ type, text: m.text() });
    }
  });
  page.on('pageerror', e => consoleMessages.push({ type: 'pageerror', text: String(e) }));
  try {
    const result = await fn(page);
    return { result, consoleMessages };
  } finally {
    await browser.disconnect();
  }
}

export async function run(fn, opts) {
  try {
    const { result, consoleMessages } = await withPage(fn, opts);
    console.log(JSON.stringify({ ok: true, result, consoleMessages }, null, 2));
  } catch (err) {
    console.log(JSON.stringify({ ok: false, error: String(err && err.stack || err) }));
    process.exitCode = 1;
  }
}
