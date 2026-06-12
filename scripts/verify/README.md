# Browser smoke checks

Scripted regression checks for the refactor (see `docs/SMOKE.md` for the manual checklist).
Each script drives the real app through CDP and prints a JSON report; `consoleMessages`
must stay empty.

## Setup

1. Start the dev server: `npm run dev` (default checked URL: `http://localhost:5174/`,
   override with `APP_URL`).
2. Start a CDP browser on port 9223 (override with `BROWSER_URL`):

   ```sh
   ~/.cache/chrome-for-testing/chrome/linux-149.0.7827.55/chrome-linux64/chrome \
     --headless=new --no-sandbox --remote-debugging-port=9223 \
     --user-data-dir=$HOME/.cache/chrome-for-testing/profile \
     --window-size=1440,900 about:blank
   ```

   (`--no-sandbox` is needed on Ubuntu 23.10+ where unprivileged user namespaces
   are restricted by AppArmor. Any Chromium with `--remote-debugging-port` works.)
3. `puppeteer-core` must be importable — either `npm i -D puppeteer-core` or set
   `PPTR_MODULES` to a node_modules dir containing it.

## Checks

| Script | Covers |
| --- | --- |
| `smoke-draw.mjs` | rect draw, undo/redo, session reload round-trip |
| `phase05.mjs` | legacy session-key migration, guides removal, B/G hotkeys |
| `phase15.mjs` | pasted images arrive at 100% opacity |
| `phase2.mjs` | layers + inspector panels render (extracted leaf components) |
| `phase3.mjs` | wheel zoom anchoring, async image placement, image undo/redo |
| `phase4.mjs` | layer hide/show/lock/delete + undo, layer session round-trip |
| `phase5-desktop.mjs` | pen (close + curve), pencil, shift-rect, marquee+drag, undo chain |
| `phase5-mobile.mjs` | touch draw, pinch zoom, two-finger pan, long-press menu (390px viewport) |
| `phase7a-text.mjs` | text tool: editor commit, session/undo/reload, dbl-click re-edit, drag/scale, export, empty-draft discard |
| `phase7a-mobile.mjs` | mobile text: drawer arm, tap-edit, backdrop commit, contextmenu actions, duplicate |
| `phase7b-inspector.mjs` | unified Inspector: live stroke fields, mixed placeholders, image/text sections, defaults, upload repoints |
| `phase7c-color.mjs` | fillColor: per-color composite groups, picker-drag undo granularity, export alignment, donut hole, legacy-session fallback |
| `phase7d-consistency.mjs` | portaled tooltips, shape-flyout Popover, Esc consumed by popovers, edge-safe mobile menu + compat-click survival, renamed export context |
| `phase8a-consistency.mjs` | inspector card fits + never focus-scrolls (desktop/mobile); shape/options/auto-correct/clear buttons use the shared Tooltip |
| `phase8b-hotkeys.mjs` | Figma hotkeys (H hand, ⇧P pencil, L line, Ctrl+letter ignored, B/G dead) + wording (Pen/Move/Hand/Design/Canvas Grid, stroke Weight/Position) |
| `phase8c1-tokens.mjs` | computed UI colors track the CSS-variable tokens; no hex utility classes remain; new shapes use the themed defaults |
| `phase8c2-dark.mjs` | dark palette (#1e1e1e/#2c2c2c/#0d99ff), white/light-gray new-content defaults, dark tooltips, legacy art pinned to #344054 |
| `export.mjs` | SVG export markup + PNG rasterization (download intercept) |

Run: `node scripts/verify/<script>.mjs`. Screenshots land in `/tmp/shots/`.

Warning: the scripts clear `localStorage` for the app origin while running.
