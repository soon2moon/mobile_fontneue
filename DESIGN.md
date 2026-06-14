# DESIGN.md

The design-system contract: what to use, when, and what's forbidden. Use token **names**, never raw
values. Skim in ~2 min. Visual target: **Figma** — off-white `#f5f5f5` canvas, `#2c2c2c` chrome,
`#007eea` accent.

## Color tokens

Defined as CSS variables in `src/index.css` (`:root`, RGB triplets) and exposed as Tailwind classes
in `tailwind.config.js`. Use the Tailwind class; never the raw value.

| Token (`--var` / Tailwind) | Use for |
|---|---|
| `--color-canvas` / `bg-canvas` | Drawing surface (off-white) |
| `--color-raised` / `bg-raised` | Panels / floating chrome (`#2c2c2c`) |
| `--color-sunken` / `bg-sunken` | Inset wells, inputs |
| `--color-pressed` / `bg-pressed` | Hover/press fill on controls |
| `--color-edge`, `--color-edge-strong` / `border-edge*` | Hairline / stronger borders |
| `--color-ink` / `text-ink` | Primary text/foreground |
| `--color-secondary`, `--color-muted` / `text-*` | Secondary / muted text |
| `--color-accent` / `text-accent`, `bg-accent` | **Active** toolbar buttons + menu hover (`#007eea`) |
| `--color-accent-strong` | Brighter accent (`#339bff`) |
| `--color-accent-soft` / `bg-accent-soft` | **Selected** layer rows + active panel-nav tint |
| `--color-danger`, `--color-danger-bg` | Destructive states |
| `--color-chip` / `bg-chip` | Pills / badges |
| `--color-tooltip`, `-ink`, `-chip` | Tooltip surface / text / chip |
| `--color-scrim` / `bg-scrim` | Modal / overlay scrim |
| `--color-shadow` | Backing var for the shadow tokens below |

**Shadow tokens** (`tailwind.config.js` → `shadow-*`): `shadow-card`, `shadow-menu`,
`shadow-popover`, `shadow-sheet`, `shadow-float`. (No radius tokens — corners use Tailwind
`rounded-*`.)

### Canvas / SVG colors live in `src/theme.js`

SVG presentation attributes can't read CSS variables, so canvas-side colors (`main`, `nodeFill`,
`bg`, `gridline*`, `accent`, `accentStrong`, `marqueeFill`, …) are JS values in `src/theme.js`.

> **Sync requirement (not a bug):** the accent (`#007eea`) and canvas tone (`#f5f5f5`) intentionally
> live in **both** `index.css` and `theme.js`. When retuning the palette, change both. The split is
> by necessity — do **not** "dedupe" it into one place.

### New-content vs legacy defaults (`src/constants.js`)

- New content: `NEW_SHAPE_FILL_COLOR #d9d9d9`, `NEW_SHAPE_STROKE_COLOR #1e1e1e`,
  `NEW_TEXT_FILL_COLOR #1e1e1e` (dark ink on the light canvas).
- Legacy art is pinned to `#344054` (`DEFAULT_*_COLOR`) so pre-existing sessions render unchanged.

## Named utilities (what exists today, in `src/index.css`)

- Tool cursors: `.cursor-pen`, `.cursor-pencil`, `.cursor-rotate`, `.cursor-crosshair`,
  `.cursor-text`, `.cursor-nwse` / `nesw` / `move` / `grab` / `grabbing` / `default`.
- Mobile chrome animation: `.mobile-drawer*`, `.mobile-panels*`.
- `.panel-scroll` — thin custom scrollbar for long panel content (e.g. the layers list).
- Everything else is Tailwind token classes — no other custom `.ui-*` utilities exist yet.

## Active / selected state

The accent is the one active/selected color (matches the canvas selection chrome):
- **Active** toolbar buttons, shape-menu items, and context-menu hover use solid **`bg-accent`** +
  `text-white` (`ToolButton`, `MobileToolButton`, `ShapeMenuItem`, `CanvasContextMenu`).
- **Selected** layer rows and the active panel-nav icon use the **`bg-accent-soft`** tint.
- Reuse these — don't invent one-off active/selected styles. In-panel segmented controls (grid type,
  export scope/format) intentionally stay `bg-chip` (a quieter inset look).

## Panels (stack model)

- One unified `PanelsContainer.jsx` for desktop (right-side) and mobile (top sheet). Open panels
  share a single card; `PANELS_CONFIG` carries each panel's `icon`.
- **≥2 open:** a top icon-nav row switches the active view (`expandedPanel`); hovering an icon shows a
  ×-circle that removes it (`removePanel`, advances to the next open); clicking the active icon
  collapses to icons-only.
- **1 open:** an icon + label pill on the left, ×-circle on the right.
- Long content (the layers list) scrolls with `.panel-scroll`.

## Squircle

**Not implemented.** Corners use Tailwind `rounded-*`. Any "squircle" chrome is future work
(`TASKS.md` M2), not a current contract — don't document it as if it exists.

## Forbidden design patterns

- Never hardcode accent / colors / radii / shadows in JSX when a token exists.
- Never define a one-off color / shadow / radius in a component.
- Never duplicate selected-row / active styling across class strings — reuse the shared pattern.
- Never let the `theme.js` ↔ `index.css` palette drift out of sync.
- Never apply heavy/squircle chrome to tiny inputs or chips.

See `docs/ux-conventions.md` for naming + keyboard conventions, and the maintainer's visual
references in `references.local/` (git-ignored; convention documented in its README).
