# VISION.md

## What it is

A **lightweight, browser-based vector editor** — fast, simple, and inexpensive — for making
*editable* vector graphics: icons, logos, simple illustrations, diagrams, and web/social graphics.
Modern, Figma-style UX.

## Who it's for

**Designers** (and design-adjacent makers) who want quick vector work without Illustrator's weight,
cost, or learning curve — in a UI they already understand (Figma conventions).

## The problem

Pro vector tools (Illustrator) are heavy, expensive, and slow to learn; many lightweight tools are
too limited or clunky. This targets the sweet spot: **small, learnable, fast** — good enough for the
common asset types above, pleasant to use, free to run in a browser.

## Principles

- **Figma-aligned** — naming, shortcuts, and interactions match what Figma users expect.
- **Refine, don't accrete** — simplicity, learnability, and speed are features. Prefer
  refining / removing over adding. Complexity is a regression.
- **Editable by construction** — output is real vector objects (a serializable JSON scene), not flat
  images.

## Non-goals (deliberately out of scope)

- Full Illustrator parity (mesh gradients, brushes, advanced typography, effects).
- Real-time multi-user collaboration.
- Print / prepress (CMYK, bleed).
- Raster / photo editing (images are placed, not pixel-edited).

These keep the tool lightweight on purpose. Revisit only with a strong reason — and record it as an
ADR (`docs/decisions/`).

## Status & direction

Current work and the milestone roadmap live in `PLAN.md` / `TASKS.md`. Architecture and design
contracts are in `ARCHITECTURE.md` / `DESIGN.md`. Parked / future directions (not active) live in
`docs/frozen/`.
