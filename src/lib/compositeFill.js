import { pointsToPath, getPathFillStyle } from './paths';

// Group every closed, fill-enabled, visible path into one path-data blob per
// fill color, in canvas paint order: layers bottom-up (the layers array is
// top-first, so reversed), paths in array order within each layer. Groups are
// returned in first-encounter order, so a single-color document yields exactly
// one group that renders identically to the old single composite path —
// cross-path winding holes (fillRule="nonzero" + lib/pathDirection.js) only
// ever existed within one color and are preserved per group.
export function buildCompositeFillGroups({ paths, layers, isPathVisible }) {
  const groupIndexByKey = new Map();
  const groups = [];

  [...layers].reverse().forEach(layer => {
    paths.forEach(path => {
      if (path.layerId !== layer.id) return;
      if (!path.isClosed || !path.fillEnabled || !isPathVisible(path)) return;
      const d = pointsToPath(path.points, path.isClosed);
      if (!d) return;
      const { fillColor, fillOpacity } = getPathFillStyle(path);
      // Key by color AND opacity so semi-transparent fills don't merge into
      // an opaque sibling's group (winding holes still only matter per-group).
      const key = `${fillColor}@${fillOpacity}`;
      if (groupIndexByKey.has(key)) {
        const group = groups[groupIndexByKey.get(key)];
        group.d += ` ${d}`;
      } else {
        groupIndexByKey.set(key, groups.length);
        groups.push({ key, color: fillColor, opacity: fillOpacity, d });
      }
    });
  });

  return groups;
}
