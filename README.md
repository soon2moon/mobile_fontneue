# Vector Editor

A lightweight, browser-based vector editor (React + Vite + Tailwind) for quick, editable vector
graphics — icons, logos, simple illustrations, and web/social graphics — with a Figma-style UI.

> Some identifiers still carry the project's earlier font-tool name (`mobile-font-editor` in
> `package.json`, the `mobile_fontneue` directory). This is a general-purpose vector editor; a
> rename is tracked in `TASKS.md`.

## Run

```sh
npm install
npm run dev      # Vite dev server (http://localhost:5173 or :5174)
npm run build    # production build → dist/
npm run preview  # serve the build
```

Deployed to GitHub Pages on push to `main` (`.github/workflows/`).

## Testing / QA

- Manual smoke checklist: `docs/SMOKE.md` (desktop + ≤900px mobile).
- Scripted regression checks: `node scripts/verify/<script>.mjs` (see `scripts/verify/README.md`).
- No unit tests / linter yet (tracked in `TASKS.md`).

## Project docs

| Doc | What |
|---|---|
| `CLAUDE.md` | Entry point + working protocol (also auto-read by Claude Code each session) |
| `VISION.md` | What this is, who it's for, non-goals |
| `ARCHITECTURE.md` | Module map, state owners, reusable primitives |
| `DESIGN.md` | Design tokens, utilities, visual rules |
| `docs/ux-conventions.md` | Terminology + keyboard shortcuts (Figma-aligned) |
| `PLAN.md` / `TASKS.md` | Current milestone + roadmap |
| `docs/decisions/` | Architecture / product decision records (ADRs) |

## Stack

React 19 · Vite 7 · Tailwind 3 · lucide-react · @floating-ui/react · react-colorful. No TypeScript.
