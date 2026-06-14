# UX conventions

The editor follows **Figma** conventions so users coming from Figma feel at home. This is the
contract for **naming, keyboard shortcuts, and interaction behavior**. Source of truth for the
keymap is `src/hooks/useKeyboardShortcuts.js`.

## Terminology

| Concept | We say | Note |
|---|---|---|
| Artboard / canvas region | **Frame** | Figma term; internally `frame` objects (= artboard) |
| Selection / move tool | **Move** | internal `mode: 'edit'` |
| Pen tool | **Pen** | internal `mode: 'draw'` |
| Freehand tool | **Pencil** | internal `mode: 'pencil'` |
| Pan tool | **Hand** | internal `mode: 'pan'` |
| Inspector | **Design** (panel title) | `PANELS_CONFIG` |
| Background-grid panel | **Canvas Grid** | |
| Stroke width | **Weight** | inspector wording |
| Stroke alignment | **Position** | inspector wording |

Internal `mode` values (`edit` / `draw` / `pencil` / `pan`) differ from user-facing labels
(Move / Pen / Pencil / Hand) — keep UI labels Figma-aligned even where the code names differ.

## Keyboard shortcuts (current — Figma-aligned)

Single-letter keys are ignored while Ctrl/Cmd is held, so they never clash with browser/app combos.

| Key | Action |
|---|---|
| `V` | Move (select / edit) |
| `P` / `⇧P` | Pen / Pencil |
| `F` | Frame |
| `H` | Hand (pan) |
| `R` / `O` / `L` | Rectangle / Ellipse / Line |
| `T` | Text |
| `U` | Place image (file picker) |
| `N` | Toggle node visibility (in Pencil: switch to Move + show nodes) |
| `Space` (hold) | Temporary Hand/pan; restores the previous tool on release |
| `Esc` | Finish/cancel the current action, else deselect |
| `Delete` / `Backspace` | Delete the selection |
| `Ctrl/Cmd+C` / `+X` | Copy / Cut (Move mode, with a selection) |
| `Ctrl/Cmd+Z` / `+⇧Z` or `+Y` | Undo / Redo |
| `Ctrl/Cmd+\` | Show / Hide UI (quiet mode) |

## Interaction conventions

- `Shift` constrains — segment angle while drawing; proportions while dragging shapes.
- Double-click a frame's title label to rename it.
- Right-click (desktop) / long-press (mobile) opens the canvas context menu.
- Pinch-zoom + two-finger pan on touch; one-finger draws with the active tool.

## Alignment status

Shortcuts and core terminology already match Figma. New divergences (if any appear) are tracked in
`TASKS.md` (M3). When adding a tool, give it a Figma-consistent name + key here first.
