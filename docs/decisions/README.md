# Architecture / product decision records (ADRs)

Significant, hard-to-reverse decisions live here as short markdown files, versioned with the code —
one decision per file, numbered `NNNN-short-title.md`.

Template (MADR-lite) — each ADR has:

- **Title:** `# NNNN. <title>`
- **Status:** Proposed | Accepted | Superseded by NNNN — plus a **Date** (YYYY-MM-DD)
- **Context** — the forces: what's true, the problem, the constraints
- **Decision** — what we chose
- **Consequences** — results, trade-offs, follow-ups

Add an ADR when a choice is architecturally or product-significant and a future maintainer would ask
"why is it this way?". Link related ADRs by number; don't rewrite history — supersede instead.
