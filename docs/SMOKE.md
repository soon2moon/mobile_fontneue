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

## State

- [ ] Undo/redo several times across draw + move + style operations (no transient UI stuck).
- [ ] Reload the page: session restores (paths, images, layers, grid config, panel state).
- [ ] Layers: create, rename, reorder (drag), toggle visibility, toggle lock; objects respect both.

## Styling

- [ ] Stroke width/color/alignment edits apply to selection and to next-drawn defaults.
- [ ] Grid: toggle types (square/dot/iso/circular), change spacing, grid snap on/off works while drawing.
- [ ] Export: SVG, PNG, JPG produce correct output incl. images/text.

## Mobile (≤900px or touch emulation)

- [ ] Pinch zoom + two-finger pan.
- [ ] One-finger draw with the active tool; rollback on multi-touch (no stray strokes).
- [ ] Long-press opens the context menu; menu stays on-screen near edges.
- [ ] Bottom toolbar + tools drawer: every tool reachable, no stuck highlight after tap.
- [ ] Panels open as bottom sheet; same capabilities as desktop panels.

## Console

- [ ] No new console errors/warnings during any of the above.
