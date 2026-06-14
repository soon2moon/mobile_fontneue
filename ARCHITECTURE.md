# ARCHITECTURE.md

"What exists and where." Indexes + rules, not explanations. Skim in ~2 min; detail lives in code.
The session protocol lives in `CLAUDE.md`.

## Module map

| Path | Owns | Must not own |
|---|---|---|
| `src/App.jsx` | Top-level composition, context assembly, top-level `useState` (active tool, style defaults) | Reusable UI; domain math |
| `src/state/EditorContext.jsx` | `EditorProvider` + `useEditor()` that distribute state | Business logic |
| `src/hooks/` | Stateful reusable logic (objects, selection, layers, history, persistence, pointer interaction, UI shell, keyboard) | Presentational markup |
| `src/lib/` | Pure domain logic (geometry, paths, shapes, hitTest, stroke, svg, export, objectModel, …) | React/JSX, component state |
| `src/components/Canvas/` | SVG canvas render + on-canvas editors | Panel/toolbar chrome |
| `src/components/Inspector/` | "Design" inspector sections (Fill/Stroke/Text/Transform/Frame) | Global tokens; tool state |
| `src/components/Panels/` | Desktop panel container/accordion | Token defs; toolbar logic |
| `src/components/Toolbar/` | Desktop + mobile tool selection UI | Panel/layer state |
| `src/components/Overlays/` | Context menu, quick layer reorder, floating UI | Canvas render |
| `src/ui/` (+ `src/ui/inputs/`) | Shared presentational primitives (buttons, popover, tooltip, inputs) | Panel/canvas business logic |
| `src/config/panels.js` | `PANELS_CONFIG` registry | Per-panel UI |
| `src/index.css` + `tailwind.config.js` | Token defs + shared CSS utilities | Component logic |
| `src/theme.js` | Canvas/SVG colors (SVG can't read CSS vars) | UI chrome colors (those are tokens) |

## State sources of truth

Components read canonical state; they must not shadow it in local state. Everything is assembled in
`App.jsx` and distributed via `EditorContext`.

| State | Owner |
|---|---|
| Active tool (`mode`: edit/draw/pencil/shape/frame/text/pan), `shapeType`, `pathStyleDefaults` | `useState` in `src/App.jsx` |
| Document content (`paths`, `images`, `texts`, `frames`, `currentPath`) | `src/hooks/useObjects.js` |
| Selection (`selectedPoints`, `selectedImageIds`, `selectedTextIds`, `selectedFrameIds`, `activePathEditId`) | `src/hooks/useSelection.js` |
| Layers (`layers`, `selectedLayerIds`, drag/drop, per-layer visibility/lock) | `src/hooks/useLayers.js` |
| Path stroke/fill resolution | `src/hooks/usePathStyles.js` + `src/lib/paths.js` |
| Selection-aware inspector model | `src/hooks/useInspectorModel.js` |
| Panel stack (`openPanels`, `expandedPanel`, `togglePanel` / `removePanel`), context menu, quiet-UI (`canvasContextMenu`, `uiHidden`), mobile sheet | `src/hooks/useUIShell.js` |
| Undo/redo | `src/hooks/useHistory.js` |
| Load/save the JSON scene | `src/hooks/useSessionPersistence.js` |

## Document model & normalizer contract (load-bearing)

- The whole scene is plain serializable JSON: `useSessionPersistence` does
  `JSON.stringify({ layers, paths, images, texts, frames, currentPath, currentPathInfo,
  pathStyleDefaults, gridConfig, showBackgroundAids, activeLayerId })` on every change.
- `src/lib/objectModel.js` provides factories (`createTextObject`, `createFrameObject`) and
  **normalizers** (`normalizeTextObject`, `normalizeFrameObject`) that validate raw objects from
  **persisted sessions and clipboard payloads**, returning `null` on bad input.
- **Rule:** every producer of document objects (session load, clipboard paste, any future import)
  validates through these normalizers and mutates the existing state setters. **No parallel object
  model or second document format.**

## Reusable primitives index

Check this before creating a new primitive.

| Name | Path | Reuse when |
|---|---|---|
| `ToolButton` | `src/ui/ToolButton.jsx` | A desktop toolbar tool/control button |
| `MobileToolButton` | `src/ui/MobileToolButton.jsx` | A mobile toolbar/drawer button |
| `ShapeMenuItem` | `src/ui/ShapeMenuItem.jsx` | A shape-picker menu row |
| `Popover` | `src/ui/Popover.jsx` | Any floating/anchored panel (`@floating-ui`) |
| `Tooltip` | `src/ui/Tooltip.jsx` | Hover label (+ optional hotkey) on a control |
| `ColorControl` | `src/ui/ColorControl.jsx` | Swatch + hex color input |
| `LayerIcon` | `src/ui/LayerIcon.jsx` | Layer-type icon |
| `ConfigInput`, `ScrubbableNumberInput`, `OpacityField`, `Toggle` | `src/ui/inputs/` | Inspector/config fields (number, drag-scrub, opacity %, on/off) |
| `PANELS_CONFIG` | `src/config/panels.js` | Adding/ordering a panel (carries `id`, `title`, `icon`) |

Reusable hooks (reach for these before adding state): `useObjects`, `useSelection`, `useLayers`,
`useHistory`, `useClipboard`, `useObjectActions`, `useInspectorModel`, `usePathStyles`, `useUIShell`,
`useSessionPersistence`, `useKeyboardShortcuts`, `usePointerInteraction`, `useExport`,
`useViewport` / `useViewportSize` (+ others in `src/hooks/`).

## Placement rules

- **New panel:** register it in `PANELS_CONFIG`; put content under `src/components/Panels/` (or an
  Inspector section); reuse the panel chrome — don't hand-roll a parallel container.
- **New shared visual style:** add a token-backed utility (see `DESIGN.md`); don't hardcode raw
  values in JSX class strings.
- **New stateful logic:** add/extend a hook in `src/hooks/`; don't duplicate canonical state locally.
- **New domain math:** pure functions in `src/lib/`; keep React out of them.

## Boundaries

- `src/ui/*` primitives must not import panel/canvas business logic.
- Toolbar components don't own panel or layer state.
- `src/lib/*` and `src/theme.js` / token files don't import React components.
- Mobile panel behavior is not changed as a side effect of desktop panel work.

## Forbidden patterns

- Don't duplicate canonical state in local component state.
- Don't create a new primitive/util/hook before checking the indexes above.
- Don't hardcode colors/radii/shadows in JSX when a token exists (`DESIGN.md`).
- Don't add a new tool/panel when refining an existing one achieves the goal (**refine, don't accrete**).
- Don't introduce a second document format / parallel object model.
- Don't leave replaced code behind as dead code.
