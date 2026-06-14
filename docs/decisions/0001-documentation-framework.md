# 0001. Documentation & process framework

- Status: Accepted
- Date: 2026-06-13

## Context

The project is maintained largely with Claude Code across many sessions and should be hand-off-ready
to a third person. There was no `CLAUDE.md`, `README`, or architecture/design/plan docs — only a
manual smoke checklist and the verify harness. Project state was tracked only in Claude's
machine-local memory, which a third person who clones the repo never sees.

## Decision

- `CLAUDE.md` (root, committed, < 200 lines) is the auto-loaded entry point and session protocol; it
  references the guardrail docs **by path** (not `@import`, which would load them into context every
  session).
- `ARCHITECTURE.md` and `DESIGN.md` are descriptive contracts of **what exists now** (skimmable in
  ~2 min, pointing at code). `docs/ux-conventions.md` holds terminology + the keyboard map.
- `PLAN.md` is a stable anchor (current milestone, status, roadmap); `TASKS.md` is the churny
  checklist. PLAN owns the single status line; TASKS owns the boxes.
- Significant decisions are recorded here in `docs/decisions/`.
- In-repo docs own project state. Claude's auto-memory is trimmed to user prefs + environment gotchas
  + a pointer to `PLAN.md` (the anti-pattern being tracking project status only in memory).
- Task tracking stays in-repo markdown (a solo project) rather than GitHub Issues.

## Consequences

- A fresh session / third person reads the repo, not chat history. Docs are part of the work: a phase
  isn't done until its doc impact is handled.
- If a doc and the code disagree, that's a bug to surface and fix (see `CLAUDE.md` protocol).
- Grounding: Claude Code memory docs (keep `CLAUDE.md` small; `@import` costs tokens); MADR for ADRs;
  in-repo markdown fits solo projects.
