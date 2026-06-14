# Smoke checklist

Run after every refactor/feature step (`npm run dev`, desktop viewport + ≤900px mobile viewport).
The app must pass every item before a phase is considered done.

## Core drawing

- [ ] Pen tool: click to place corner points, click-drag to create curve handles, close a path.
- [ ] Pen tool: Shift constrains segment angle while placing points.
- [ ] Shapes: draw all 5 shapes (rect, ellipse, polygon, star, line) by dragging; Shift constrains proportions.
- [ ] Pencil: freehand stroke gets simplified + bezier-fit on release and stays node-editable.
- [ ] Node edit: enter edit mode on a path, move anchors/handles, toggle corner/smooth.

## Objects

- [ ] Insert image (file picker): lands centered in the viewport at expected opacity.
- [ ] Insert text: text appears on canvas and is selectable/movable.
- [ ] Multi-select (marquee + shift-click): move, rotate selection.
- [ ] Copy/paste paths (clipboard round-trip), duplicate, delete.
- [ ] Frame tool (F): drag a board, or pick a Design-panel preset; rename + recolor it in Design; click-select, body-drag move, corner resize (W/H), Delete + undo; export scope "Frame" crops to the board.

## State

- [ ] Undo/redo several times across draw + move + style operations (no transient UI stuck).
- [ ] Reload the page: session restores (paths, images, layers, grid config, panel state).
- [ ] Layers: create, rename, reorder (drag), toggle visibility, toggle lock; objects respect both.

## Styling & theme

- [ ] Stroke weight/color/position edits apply to selection and to next-drawn defaults.
- [ ] Grid: toggle types (square/dot/iso/circular), change spacing, grid snap on/off works while drawing.
- [ ] Export: SVG, PNG, JPG produce correct output incl. images/text (JPG uses the light canvas bg #f5f5f5).
- [ ] Light canvas (#f5f5f5) with #2c2c2c chrome and #007eea accent; new shapes default to dark ink (stroke/text #1e1e1e, fill #d9d9d9); pre-existing (legacy) art keeps #344054.

## Tools, shortcuts & layout

- [ ] Figma hotkeys: V Move, H Hand, P Pen, ⇧P Pencil, R/O/L shapes, F Frame, T Text, U Place Image; Ctrl+letter never switches tools.
- [ ] Quiet UI: Ctrl+\ hides/restores all chrome (canvas still works); panels fade while drawing/dragging.
- [ ] Right-click canvas: object → Copy/Cut/Duplicate/Delete/Bring forward/Send backward; empty/board → Paste here (at the point).
- [ ] Tooltips on every toolbar button; the Inspector ("Design") panel never clips its inputs.

## Mobile (≤900px or touch emulation)

- [ ] Pinch zoom + two-finger pan.
- [ ] One-finger draw with the active tool; rollback on multi-touch (no stray strokes).
- [ ] Long-press opens the context menu; menu stays on-screen near edges.
- [ ] Bottom toolbar + tools drawer: every tool reachable, no stuck highlight after tap.
- [ ] Panels open as bottom sheet; same capabilities as desktop panels.

## Console

- [ ] No new console errors/warnings during any of the above.
