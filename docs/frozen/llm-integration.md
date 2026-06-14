# FROZEN — LLM / Claude integration

> **STATUS: FROZEN.** Not part of active work. **Do not load this file in normal sessions** — it
> wastes tokens. Open it only if the user explicitly reactivates LLM/Claude integration. Nothing in
> the auto-loaded docs (`CLAUDE.md`, `ARCHITECTURE.md`, `DESIGN.md`, `VISION.md`) links here;
> `PLAN.md` carries only a one-line "Frozen" pointer.

Parked thinking, preserved so it isn't re-derived later. Frozen until the documentation/product
foundation is concrete (ADR 0002, P4).

## The idea

Let an LLM/agent — primarily the user's **Claude.ai subscription**, working from Claude web — produce
**native, editable** vector content in the app, not flat images.

## Why it's feasible here

The whole scene is already a serializable JSON document, and `src/lib/objectModel.js` validates raw
objects (factories + `normalize*`) for both persisted sessions and clipboard payloads. An agent is
just a third producer of the same raw objects → output lands as native, user-editable objects. (See
the document-model / normalizer contract in `ARCHITECTURE.md`.)

## Keystone: one scene-JSON schema

Define a single schema (the existing persistence payload shape, or a curated subset). It is the paste
format, the structured-output schema, and a connector tool's input at once; the existing normalizers
validate all three. Build it first.

## Paths (recommended order)

- **A — Copy/paste (or claude.ai *Project*) bridge. Start here.** Uses the **subscription** ($0),
  works on the hosted https site. Claude web emits scene-JSON; an "Import/Paste scene JSON" entry
  point validates via the normalizers and merges via the existing setters.
- **B — In-app "Generate" via the Anthropic API + structured outputs.** Cleanest UX, but **separate
  per-token billing (≠ the subscription)** and a static GitHub Pages site **can't hold an API key** →
  needs a serverless (or local) proxy. `output_config.format` (json_schema) guarantees valid output.
  Models: `claude-opus-4-8` default; `claude-haiku-4-5` / `claude-sonnet-4-6` for cheap generation.
- **C — Live push from Claude web via an MCP custom connector.** The literal "Claude web → site," but
  a static SPA needs a small bridge/backend to receive the push, and connector availability is
  plan-dependent. Later.
- Local LLM (Ollama / LM Studio) is a deprioritized alternative — browser mixed-content blocks the
  hosted https site, so it's usable only locally.

## Key facts (so they aren't re-researched)

- The **claude.ai subscription ≠ the Anthropic API**: the subscription can't be called
  programmatically / billed from the app. Subscription use = Path A; in-app calls = Path B (API).
- A static site cannot safely embed an API key → a proxy is required for Path B.
- Guardrail (already a general rule in `ARCHITECTURE.md`): any document-object producer validates
  through the existing normalizers — no parallel object model.

## Sources

- Claude subscription vs API, structured outputs, static-site key handling: Anthropic docs —
  https://platform.claude.com/docs/en/build-with-claude/structured-outputs.md
