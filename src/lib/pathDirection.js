import { getBezierPoint } from './geometry';

// Normalize winding direction. With a selection: blindly reverse the selected
// paths. Without: set every visible closed path so that fill parity works out
// (outermost clockwise, holes counter-clockwise), using flattened polygons
// for containment-depth and signed-area tests.
export const correctPathDirectionsTransform = (prev, selectedPoints, isPathVisible, isPathLocked) => {
  const newPaths = prev.map(p => ({ ...p, points: [...p.points] }));

  const selectedPathIndices = new Set(selectedPoints.map(sp => sp.pathIndex));
  const processAll = selectedPathIndices.size === 0;

  if (!processAll) {
    selectedPathIndices.forEach(idx => {
      const path = newPaths[idx];
      if (path) {
        const revPts = [...path.points].reverse();
        path.points = revPts.map(p => ({
          ...p,
          hIn: p.hOut ? { ...p.hOut } : undefined,
          hOut: p.hIn ? { ...p.hIn } : undefined
        }));
      }
    });
    return newPaths;
  }

  const allClosedPaths = newPaths.map((p, i) => ({
    path: p,
    index: i,
    isClosed: p.isClosed
  })).filter(item => item.isClosed && isPathVisible(item.path) && !isPathLocked(item.path));

  const pathData = allClosedPaths.map(item => {
    const poly = [];
    const pts = item.path.points;
    for (let i = 0; i < pts.length; i++) {
      const p0 = pts[i];
      const p3 = pts[(i + 1) % pts.length];
      const p1 = p0.hOut || p0;
      const p2 = p3.hIn || p3;
      for (let step = 0; step < 20; step++) {
        poly.push(getBezierPoint(p0, p1, p2, p3, step / 20));
      }
    }

    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    let area = 0;
    for (let i = 0; i < poly.length; i++) {
      const p = poly[i];
      minX = Math.min(minX, p.x); minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x); maxY = Math.max(maxY, p.y);

      const j = (i + 1) % poly.length;
      area += (poly[i].x * poly[j].y) - (poly[j].x * poly[i].y);
    }
    area = area / 2;

    return { ...item, poly, bbox: { minX, minY, maxX, maxY }, area };
  });

  pathData.forEach((pd, i) => {
    let depth = 0;
    pathData.forEach((otherPd, j) => {
      if (i === j) return;
      const intersectsBBox = !(pd.bbox.maxX < otherPd.bbox.minX ||
                               pd.bbox.minX > otherPd.bbox.maxX ||
                               pd.bbox.maxY < otherPd.bbox.minY ||
                               pd.bbox.minY > otherPd.bbox.maxY);

      if (intersectsBBox) {
        const point = pd.poly[0];
        const poly = otherPd.poly;
        let inside = false;
        for (let k = 0, l = poly.length - 1; k < poly.length; l = k++) {
          const xk = poly[k].x, yk = poly[k].y;
          const xl = poly[l].x, yl = poly[l].y;
          const intersect = ((yk > point.y) !== (yl > point.y))
              && (point.x < (xl - xk) * (point.y - yk) / (yl - yk) + xk);
          if (intersect) inside = !inside;
        }
        if (inside) depth++;
      }
    });
    pd.depth = depth;
  });

  pathData.forEach(pd => {
    const parity = pd.depth % 2;
    const isCW = pd.area > 0;
    const targetCW = parity === 0;

    if (isCW !== targetCW) {
      const revPts = [...pd.path.points].reverse();
      newPaths[pd.index].points = revPts.map(p => ({
        ...p,
        hIn: p.hOut ? { ...p.hOut } : undefined,
        hOut: p.hIn ? { ...p.hIn } : undefined
      }));
    }
  });

  return newPaths;
};
