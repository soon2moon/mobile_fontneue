import {
  normalizeStrokeWidth,
  normalizeStrokeColor,
  normalizeStrokeAlign
} from './stroke';
import { DEFAULT_FILL_COLOR } from '../constants';

export const pointsToPath = (points, isClosed) => {
  if (!points || points.length === 0) return '';
  if (points.length === 1) {
    const point = points[0];
    // Render a short segment so single-point paths stay visible outside edit mode.
    return `M ${point.x} ${point.y} L ${point.x + 1.5} ${point.y}`;
  }
  let d = `M ${points[0].x} ${points[0].y}`;

  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cp1 = prev.hOut || { x: prev.x, y: prev.y };
    const cp2 = curr.hIn || { x: curr.x, y: curr.y };
    d += ` C ${cp1.x} ${cp1.y}, ${cp2.x} ${cp2.y}, ${curr.x} ${curr.y}`;
  }

  if (isClosed && points.length > 2) {
    const prev = points[points.length - 1];
    const curr = points[0];
    const cp1 = prev.hOut || { x: prev.x, y: prev.y };
    const cp2 = curr.hIn || { x: curr.x, y: curr.y };
    d += ` C ${cp1.x} ${cp1.y}, ${cp2.x} ${cp2.y}, ${curr.x} ${curr.y} Z`;
  }
  return d;
};

export const isCorner = (p) => {
  const dIn = p.hIn ? Math.hypot(p.hIn.x - p.x, p.hIn.y - p.y) : 0;
  const dOut = p.hOut ? Math.hypot(p.hOut.x - p.x, p.hOut.y - p.y) : 0;
  return dIn < 0.1 && dOut < 0.1;
};

export const clonePoint = (pt) => ({
  ...pt,
  hIn: pt.hIn ? { ...pt.hIn } : undefined,
  hOut: pt.hOut ? { ...pt.hOut } : undefined
});

export const reversePathPoints = (pointsArray) => (
  [...pointsArray].reverse().map(pt => ({
    ...pt,
    hIn: pt.hOut ? { ...pt.hOut } : undefined,
    hOut: pt.hIn ? { ...pt.hIn } : undefined
  }))
);

export const simplifyPolylinePoints = (pointsArray, tolerance = 0) => {
  if (!Array.isArray(pointsArray) || pointsArray.length <= 2) {
    return pointsArray.map(clonePoint);
  }

  const tol = Math.max(0, Number(tolerance) || 0);
  if (tol <= 0.0001) {
    return pointsArray.map(clonePoint);
  }

  const keep = new Array(pointsArray.length).fill(false);
  keep[0] = true;
  keep[pointsArray.length - 1] = true;

  const pointSegmentDistance = (point, a, b) => {
    const l2 = (b.x - a.x) ** 2 + (b.y - a.y) ** 2;
    if (l2 === 0) return Math.hypot(point.x - a.x, point.y - a.y);
    let t = ((point.x - a.x) * (b.x - a.x) + (point.y - a.y) * (b.y - a.y)) / l2;
    t = Math.max(0, Math.min(1, t));
    const projX = a.x + t * (b.x - a.x);
    const projY = a.y + t * (b.y - a.y);
    return Math.hypot(point.x - projX, point.y - projY);
  };

  const simplifyRange = (startIdx, endIdx) => {
    if (endIdx <= startIdx + 1) return;
    let maxDist = 0;
    let index = -1;
    const a = pointsArray[startIdx];
    const b = pointsArray[endIdx];
    for (let i = startIdx + 1; i < endIdx; i++) {
      const dist = pointSegmentDistance(pointsArray[i], a, b);
      if (dist > maxDist) {
        maxDist = dist;
        index = i;
      }
    }
    if (index !== -1 && maxDist > tol) {
      keep[index] = true;
      simplifyRange(startIdx, index);
      simplifyRange(index, endIdx);
    }
  };

  simplifyRange(0, pointsArray.length - 1);

  const simplified = [];
  for (let i = 0; i < pointsArray.length; i++) {
    if (!keep[i]) continue;
    const p = pointsArray[i];
    simplified.push({
      x: p.x,
      y: p.y,
      hIn: { x: p.x, y: p.y },
      hOut: { x: p.x, y: p.y }
    });
  }

  if (simplified.length < 2) {
    return [clonePoint(pointsArray[0]), clonePoint(pointsArray[pointsArray.length - 1])];
  }
  return simplified;
};

export const clonePaths = (pathsArray) => {
  return pathsArray.map(p => ({
    ...p,
    points: p.points.map(clonePoint)
  }));
};

export const cloneState = (pathsArray, currentPathArray, imagesArray, layersArray, textsArray) => ({
  paths: clonePaths(pathsArray),
  currentPath: currentPathArray.map(clonePoint),
  images: imagesArray ? imagesArray.map(img => ({ ...img })) : [],
  layers: layersArray ? layersArray.map(l => ({ ...l })) : [],
  texts: textsArray ? textsArray.map(t => ({ ...t })) : []
});

// Stroke resolution falls back to the fixed legacy defaults (the normalize
// helpers default to DEFAULT_STROKE_*), NOT the live next-path defaults, so
// canvas, thumbnails, and export always agree and paths from before style
// stamping keep rendering the original ink — mirrors getPathFillStyle.
export const getPathStrokeStyle = (path) => ({
  strokeEnabled: path?.strokeEnabled !== false,
  strokeWidth: normalizeStrokeWidth(path?.strokeWidth),
  strokeColor: normalizeStrokeColor(path?.strokeColor),
  strokeAlign: normalizeStrokeAlign(path?.strokeAlign)
});

// Fill resolution falls back to the fixed DEFAULT_FILL_COLOR (not the live
// next-path defaults) so canvas, export, and layer previews always agree and
// paths from before fillColor existed keep rendering the original color.
export const getPathFillStyle = (path) => ({
  fillEnabled: !!path?.fillEnabled,
  fillColor: normalizeStrokeColor(path?.fillColor, DEFAULT_FILL_COLOR)
});

export const resolvePathEditGroupId = (path) => (
  path?.editGroupId ?? (path?.id != null ? `path-${path.id}` : null)
);

// Grow a point selection so that every path sharing an edit group with a
// selected path is fully selected (whole-object semantics outside focus mode).
export const expandPathSelectionToGroups = (paths, selectionPointsInput = []) => {
  if (!Array.isArray(selectionPointsInput) || selectionPointsInput.length === 0) return [];
  const selectedPathIndexSet = new Set(
    selectionPointsInput
      .map(sp => sp.pathIndex)
      .filter(idx => Number.isInteger(idx) && idx >= 0 && idx < paths.length)
  );
  if (selectedPathIndexSet.size === 0) return [];

  const selectedGroupIds = new Set();
  selectedPathIndexSet.forEach((pathIndex) => {
    const path = paths[pathIndex];
    if (!path) return;
    const groupId = resolvePathEditGroupId(path);
    if (groupId != null) {
      selectedGroupIds.add(groupId);
    }
  });
  if (selectedGroupIds.size === 0) {
    return [...selectionPointsInput];
  }

  const expandedSelection = [];
  paths.forEach((path, pathIndex) => {
    const groupId = resolvePathEditGroupId(path);
    if (!selectedGroupIds.has(groupId)) return;
    path.points.forEach((_, pointIndex) => {
      expandedSelection.push({ pathIndex, pointIndex });
    });
  });

  return expandedSelection;
};
