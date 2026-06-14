# PLAN.md

The project anchor: current milestone, status, roadmap, and pointers. Stable — it changes at phase
or decision boundaries, not every commit. The granular checklist lives in `TASKS.md`; decisions in
`docs/decisions/`.

## Active milestone

**M2 — UX refinement (Figma-aligned).** Bring the editor UI to industry standard: accent active /
selected states, a reworked 2-row stroke section, and a unified icon-nav panel stack — matching the
`references.local/` images. M1 (documentation foundation) is done.

## Current status / you are here

**M2 in progress.** Implemented and build-clean: the `accent` / `accent-soft` tokens + `.panel-scroll`
utility; active toolbar/shape-menu buttons → `bg-accent` and selected layer rows → `bg-accent-soft`;
the stroke section relaid out (color/hex/opacity over align/weight); and the unified panel stack
(icon-nav, hover-× remove, collapse, single-item pill, flattened layers) across desktop + mobile
(`PanelsContainer.jsx` + `useUIShell` `togglePanel`/`removePanel`). Remaining: verification (harness +
manual + visual vs references), especially mobile. Branch `update/ux-overhaul`. See `TASKS.md`.

## Roadmap (milestones)

- **M1 — Documentation foundation** ← active.
- **M2 — UX refinement (Figma-aligned).** Refine existing toolbar / inspector / panels; make
  active/selected states consistent (shared `accent-active` / `selected-row` utility); optional
  squircle chrome. *Refine, don't add tooling.*
- **M3 — UX-conventions alignment.** Close any naming/shortcut gaps vs Figma (already mostly aligned).
- **M4 — Tooling.** ESLint + Prettier (currently absent) for machine-enforced consistency.
- **M5 — Onboarding.** `CONTRIBUTING.md`, README polish, PR/issue templates; rename the legacy
  `mobile-font-editor` package / `mobile_fontneue` dir.
- **M6 — Reconcile** the `theme.js` ↔ `index.css` palette sync (a check, or a single source).
- **Frozen (not scheduled):** LLM/Claude integration — parked in `docs/frozen/llm-integration.md`.
  Do not load in normal sessions.

**M1 acceptance:** docs match code (spot-checked), `npm run build` clean, `CLAUDE.md` < 200 lines,
`ARCHITECTURE.md` / `DESIGN.md` skimmable in ~2 min, frozen file not linked from any auto-loaded doc.

## Decisions

See `docs/decisions/`: `0001` documentation framework; `0002` product direction (target user, Figma
anchor, refine-don't-accrete, non-goals, LLM frozen).

## Known issues / deferred

- **`docs/SMOKE.md`** had stale "dark theme / dark JPG bg" lines — corrected to the current light
  `#f5f5f5` canvas during M1.
- **Legacy names:** `package.json` `mobile-font-editor`, dir `mobile_fontneue`, `typolab-session-v1`
  migration key — rename deferred to M5.
- **Palette sync:** accent/canvas live in both `index.css` and `theme.js` by necessity (SVG can't
  read CSS vars); kept in sync manually — automate in M6.
- No ESLint/Prettier or unit tests yet (M4).

## History (archived — migrated from session memory)

Pivot of `mobile_fontneue` from a font tool to a general vector editor, on branch
`update/ux-overhaul`.

- **Phases 0–6 — refactor:** broke a monolith into hooks/components; document state into
  `useObjects` / `useSelection` / `useLayers` / `useHistory` / `useUIShell`, domain math into
  `src/lib/*`.
- **Phase 7 — UX overhaul** (thru `83e4f76`): live text objects, unified Inspector ("Design"),
  independent fill color + per-color composite fills, `Toggle` / `Tooltip` / `Popover` primitives,
  shared mobile context menu.
- **Phase 8 — Figma alignment** (`4859d78`→`b954759`): 8A inspector overflow fix + tooltips on all
  toolbar buttons; 8B Figma hotkeys (V/H/P/⇧P/R/O/L/T/U) + wording (Inspector→Design, Stroke
  Width→Weight, Align→Position); 8C tokenized ~277 color classes to CSS-var Tailwind tokens; 8D quiet
  UI (Ctrl+\); 8E shared canvas context menu; 8F frames (= artboards): model, tool (F),
  select/move/non-uniform resize, Design presets, frame-scoped export.
- **UX pass #2** (2026-06-13, committed thru `f66f83d`): theme flipped to **light** canvas
  (`--color-canvas #f5f5f5`, `--color-accent #007eea`); tight/solid selection box; frame rename via
  double-click label; **derived** (not stored) frame nesting (center-inside rule); frame export
  children-only + optional transparent background; per-path fill/stroke opacity; context-menu rewrite
  with an Arrange side-flyout. Verified by `scripts/verify/uxpass2.mjs` (+ updated suite); build clean.
