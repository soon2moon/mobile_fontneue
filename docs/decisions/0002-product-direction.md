# 0002. Product direction

- Status: Accepted
- Date: 2026-06-13

## Context

The project pivoted from a font tool to a general vector editor. It needed an explicit product north
star: who it's for, what it competes with, and what it deliberately won't do.

## Decision

- **P1 — Target user:** designers / design-adjacent makers who want lightweight, inexpensive vector
  creation (icons, logos, simple illustrations, web/social graphics).
- **P2 — UX anchor: Figma.** Naming, shortcuts, and interactions follow Figma (the audience already
  knows it; the code already uses Figma's "frame" vocabulary, so churn is low).
- **P3 — Refine, don't accrete.** Prefer simplifying / refactoring / removing over adding tooling.
  Complexity is a regression.
- **P4 — LLM/Claude integration is FROZEN.** A future pillar, parked in
  `docs/frozen/llm-integration.md`, excluded from the active docs and the session protocol. Revisit
  only after the foundation is concrete and the user reactivates it.
- **P5 — Non-goals:** full Illustrator parity, real-time collaboration, print/CMYK/prepress, raster
  editing. (See `VISION.md`.)

## Consequences

- Positioning matches the proven lightweight-web-vector niche (Vectr / Vectorpea / Boxy SVG) rather
  than Illustrator or Figma-style collaboration.
- M2/M3 (UX refinement + convention alignment) follow P2/P3. The frozen LLM work is captured but not
  scheduled.
