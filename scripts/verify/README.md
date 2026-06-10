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
| `phase2.mjs` | layers + stroke panels render (extracted leaf components) |
| `phase3.mjs` | wheel zoom anchoring, async image placement, image undo/redo |
| `phase4.mjs` | layer hide/show/lock/delete + undo, layer session round-trip |
| `phase5-desktop.mjs` | pen (close + curve), pencil, shift-rect, marquee+drag, undo chain |
| `export.mjs` | SVG export markup + PNG rasterization (download intercept) |

Run: `node scripts/verify/<script>.mjs`. Screenshots land in `/tmp/shots/`.

Warning: the scripts clear `localStorage` for the app origin while running.
