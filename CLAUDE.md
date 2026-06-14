# CLAUDE.md — vector editor

A lightweight, browser-based **vector editor** (React 19 + Vite 7 + Tailwind 3). Fast, simple,
inexpensive vector graphics (icons, logos, simple illustrations, web/social graphics) for
designers. UX modeled on **Figma**.

> Legacy names linger from an earlier font-tool idea — `package.json` name `mobile-font-editor`,
> the repo dir `mobile_fontneue`, the `typolab-session-v1` migration key. Ignore them; this is a
> general-purpose vector editor (current session key: `vector-editor-session-v1`).

## Session protocol (read first)

At the start of a session, read in order:

1. `ARCHITECTURE.md` — what exists & where (module map, state owners, reusable primitives).
2. `DESIGN.md` — design tokens, shared utilities, active/selected + panel rules.
3. `PLAN.md` — current milestone, status, what's next.

Also `docs/ux-conventions.md` (terminology + keyboard map). Treat these as the durable project
context; don't re-derive it from chat history.

- **Before creating anything** (component, hook, util, CSS class, token): check the
  `ARCHITECTURE.md` primitives index and `DESIGN.md` token/utility tables. Reuse or extend — don't
  fork or duplicate. If something similar exists, extend it.
- **On a doc-vs-code conflict:** stop. Decide whether the doc is stale or the code violates the
  intended rule, fix the correct source of truth, and note it in `PLAN.md`.
- **Tracking:** tick `TASKS.md` after each significant step; update `PLAN.md` / an ADR at phase or
  decision boundaries. Significant decisions → `docs/decisions/` (ADR-lite).

## Principles

- **Figma-aligned** — naming, keyboard shortcuts, and interactions match what Figma users expect
  (`docs/ux-conventions.md`).
- **Refine, don't accrete** — prefer simplifying / refactoring / removing over adding tools or
  panels. Complexity is a regression. Don't add a new tool/panel when refining an existing one
  achieves the goal.

## Commands

- `npm run dev` — Vite dev server (commonly `http://localhost:5173/` or `:5174/`).
- `npm run build` — production build · `npm run preview` — serve the build.
- Manual QA: `docs/SMOKE.md` (run after every change; desktop + ≤900px mobile).
- Scripted QA: `node scripts/verify/<script>.mjs` (CDP harness, Chrome-for-Testing on `:9223`;
  see `scripts/verify/README.md`). `consoleMessages` must stay empty.
- No ESLint/Prettier yet (tracked in `TASKS.md`) — match the surrounding code style.

## Architecture in one screen

- **Canvas** — `src/components/Canvas/Canvas.jsx` (SVG render) + `src/hooks/usePointerInteraction.js`
  (all pointer/draw/gesture logic; the large one).
- **Inspector** ("Design" panel) — `src/components/Inspector/*` + `useInspectorModel`.
- **Panels** — `src/components/Panels/PanelsContainer.jsx`; registry `src/config/panels.js`.
- **Toolbar** — `src/components/Toolbar/{DesktopToolbar,MobileControls}.jsx`.
- **Shared UI primitives** — `src/ui/*` (+ `src/ui/inputs/*`); see the index in `ARCHITECTURE.md`.
- **Domain logic** — `src/lib/*` (geometry, paths, shapes, hitTest, export, objectModel…).
- **State** — React Context in `src/state/EditorContext.jsx` + `useState` in `App.jsx` + hooks
  (NOT a store). Owners listed in `ARCHITECTURE.md`.
- **Document model** — the whole scene is **serializable JSON** persisted by
  `useSessionPersistence`; raw objects are validated through the factory/normalizer layer in
  `src/lib/objectModel.js`. **All producers (persistence, clipboard, future import) go through the
  normalizers — never a parallel object model.**
- **Tokens** — CSS vars in `src/index.css` (`:root`) → Tailwind in `tailwind.config.js`; canvas/SVG
  colors in `src/theme.js`, kept in sync (see `DESIGN.md`).

## Conventions

- Match local patterns. Keep `ARCHITECTURE.md` / `DESIGN.md` skimmable (~2 min) — detail lives in
  code.
- Commits: conventional style + `Co-Authored-By: Claude …`. Branch off `main`; active branch is
  `update/ux-overhaul`. Commit/push only when asked.

## Do not open

- `docs/frozen/` holds **parked** work (currently: LLM/Claude integration). It is frozen and out of
  scope — **do not read it in normal sessions** (it wastes tokens). Open it only if the user
  explicitly reactivates that work.
- `references.local/` (git-ignored) is the maintainer's visual-reference library — read a specific
  image only when a task needs it.
