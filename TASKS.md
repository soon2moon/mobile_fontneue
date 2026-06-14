# TASKS.md

Live checklist — tick items as they land. Status prose lives in `PLAN.md` (single source); this file
is just the boxes, grouped by milestone.

## M1 — Documentation foundation (active)

- [x] `CLAUDE.md` (entry + session protocol + frozen-dir rule)
- [x] `ARCHITECTURE.md` (module map, state SoT, document-model/normalizer contract, primitives index)
- [x] `DESIGN.md` (token tables, named utilities, active/selected + panel rules, palette-sync note)
- [x] `docs/ux-conventions.md` (Figma terminology + keyboard map)
- [x] `VISION.md`, `README.md`
- [x] `PLAN.md`, `TASKS.md`
- [ ] `docs/decisions/` (README + 0001 + 0002)
- [ ] `docs/frozen/llm-integration.md` (FROZEN banner; not linked from auto-loaded docs)
- [ ] `references.local/` scaffold + `.gitignore` entry (local, uncommitted)
- [ ] Fix stale `docs/SMOKE.md` theme lines (dark → light `#f5f5f5`)
- [ ] Trim the `ux-overhaul-refactor-status` memory note to a pointer; update `MEMORY.md`
- [ ] Verify: `npm run build` clean; freeze grep; references git-ignored; `CLAUDE.md` < 200 lines

## M2 — UX refinement (Figma-aligned) — *refine, don't add tooling*

- [x] Accent tokens: `accent` (solid) for active toolbar/menu, `accent-soft` (tint) for selected
      rows + active nav; `.panel-scroll` utility
- [x] Active toolbar / shape-menu buttons → `bg-accent`; selected layer rows → `bg-accent-soft`
- [x] Stroke section: 2-row layout (color/hex/opacity, then align/weight)
- [x] Panel stack overhaul (icon-nav, hover-× remove, collapse-to-icons, single-item pill,
      flattened layer rows, custom scrollbar) — desktop + mobile
- [ ] Verify (build + harness + manual + visual vs `references.local/`)
- [ ] (Deferred) true squircle chrome — currently Tailwind `rounded-*`

## M3 — UX-conventions alignment

- [ ] Audit naming + shortcuts vs `docs/ux-conventions.md`; close any gaps (mostly aligned already)

## M4 — Tooling

- [ ] ESLint (flat config) + Prettier; wire an npm script; first pass over `src/`

## M5 — Onboarding

- [ ] `CONTRIBUTING.md`; README polish; PR/issue templates
- [ ] Rename legacy `mobile-font-editor` package / `mobile_fontneue` dir

## M6 — Palette sync

- [ ] Single-source (or a check) for the `theme.js` ↔ `index.css` accent/canvas sync

## Frozen (not scheduled)

- LLM/Claude integration → `docs/frozen/llm-integration.md` (do not load in normal sessions).
