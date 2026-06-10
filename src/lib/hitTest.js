import { SNAP_RADIUS } from '../constants';
import { getBezierPoint, distToBezier } from './geometry';

// World-space hit radii. Scaled up on touch devices and divided by zoom so
// the on-screen target size stays constant. Shared by the pointer handlers
// (hit testing) and the canvas render (handle/anchor visuals).
export const computeHitRadii = (isMobile, zoom) => {
  const touchHitScale = isMobile ? 1.65 : 1;
  return {
    touchHitScale,
    scaleHandleHitRadius: (8 * touchHitScale) / zoom,
    rotateHandleHitRadius: (24 * touchHitScale) / zoom,
    handleHitRadius: (8 * touchHitScale) / zoom,
    pointHitRadius: (10 * touchHitScale) / zoom,
    segmentHitRadius: (10 * touchHitScale) / zoom,
    snapHitRadius: (SNAP_RADIUS * touchHitScale) / zoom,
    closePathHitRadius: (SNAP_RADIUS * (isMobile ? 2.4 : 1.2)) / zoom,
    pencilSamplingDistance: (isMobile ? 12 : 8) / zoom,
    touchDragThresholdPx: isMobile ? 10 : 0
  };
};

// Topmost image interaction under the cursor: scale/rotate corner handles
// (when it is the single selected image) or body move. Skips hidden/locked.
export const getBgHit = (testCoords, { images, layers, selectedImageIds, scaleHandleHitRadius, rotateHandleHitRadius }) => {
  for (let i = images.length - 1; i >= 0; i--) {
    const img = images[i];
    const layer = layers.find(l => l.id === img.layerId);
    if (!layer || !layer.visible || layer.locked) continue;
    if (img.locked) continue;

    const dx = testCoords.x - img.x;
    const dy = testCoords.y - img.y;
    const angleRad = -img.rotation * Math.PI / 180;

    const lx = dx * Math.cos(angleRad) - dy * Math.sin(angleRad);
    const ly = dx * Math.sin(angleRad) + dy * Math.cos(angleRad);

    const sw2 = (img.width * img.scale) / 2;
    const sh2 = (img.height * img.scale) / 2;

    if (selectedImageIds.length === 1 && selectedImageIds[0] === img.id) {
      const corners = [
        { id: 'nw', x: -sw2, y: -sh2, angle: 225 },
        { id: 'ne', x: sw2, y: -sh2, angle: 315 },
        { id: 'se', x: sw2, y: sh2, angle: 45 },
        { id: 'sw', x: -sw2, y: sh2, angle: 135 }
      ];
      for (const c of corners) {
        const dist = Math.hypot(lx - c.x, ly - c.y);
        if (dist <= scaleHandleHitRadius) return { action: `scale-${c.id}`, cursorAngle: c.angle, imageId: img.id };
        if (dist <= rotateHandleHitRadius) return { action: `rotate-${c.id}`, cursorAngle: null, imageId: img.id };
      }
    }

    if (Math.abs(lx) <= sw2 && Math.abs(ly) <= sh2) {
      return { action: 'move', cursorAngle: null, imageId: img.id };
    }
  }
  return null;
};

export const findTopImageAtCoords = (testCoords, { images, layers }) => {
  for (let i = images.length - 1; i >= 0; i--) {
    const img = images[i];
    const layer = layers.find(l => l.id === img.layerId);
    if (!layer || !layer.visible || layer.locked || img.locked) continue;

    const dx = testCoords.x - img.x;
    const dy = testCoords.y - img.y;
    const angleRad = -img.rotation * Math.PI / 180;
    const lx = dx * Math.cos(angleRad) - dy * Math.sin(angleRad);
    const ly = dx * Math.sin(angleRad) + dy * Math.cos(angleRad);

    const sw2 = (img.width * img.scale) / 2;
    const sh2 = (img.height * img.scale) / 2;
    if (Math.abs(lx) <= sw2 && Math.abs(ly) <= sh2) {
      return img;
    }
  }
  return null;
};

// Topmost path under the cursor: nearest bezier segment within radius, or
// interior of a closed filled path (even-odd test over a flattened polygon).
export const findTopPathAtCoords = (testCoords, { paths, isPathVisible, isPathLocked, pointHitRadius, segmentHitRadius }) => {
  let bestPath = null;
  let bestIndex = -1;
  let bestDist = Infinity;

  const isPointInsidePath = (path) => {
    if (!path.isClosed || path.points.length < 3) return false;
    const poly = [];
    for (let j = 0; j < path.points.length; j++) {
      const p0 = path.points[j];
      const p3 = path.points[(j + 1) % path.points.length];
      const p1 = p0.hOut || p0;
      const p2 = p3.hIn || p3;
      for (let step = 0; step < 16; step++) {
        poly.push(getBezierPoint(p0, p1, p2, p3, step / 16));
      }
    }
    let inside = false;
    for (let k = 0, l = poly.length - 1; k < poly.length; l = k++) {
      const xk = poly[k].x;
      const yk = poly[k].y;
      const xl = poly[l].x;
      const yl = poly[l].y;
      const intersects = ((yk > testCoords.y) !== (yl > testCoords.y))
        && (testCoords.x < (xl - xk) * (testCoords.y - yk) / (yl - yk) + xk);
      if (intersects) inside = !inside;
    }
    return inside;
  };

  for (let i = paths.length - 1; i >= 0; i--) {
    const path = paths[i];
    if (!isPathVisible(path) || isPathLocked(path)) continue;

    if (path.points.length === 1) {
      const dist = Math.hypot(path.points[0].x - testCoords.x, path.points[0].y - testCoords.y);
      if (dist < pointHitRadius && dist < bestDist) {
        bestDist = dist;
        bestPath = path;
        bestIndex = i;
      }
      continue;
    }

    let localBest = Infinity;
    const segCount = path.isClosed ? path.points.length : path.points.length - 1;
    for (let j = 1; j <= segCount; j++) {
      const currIndex = path.isClosed ? (j % path.points.length) : j;
      const prevIndex = currIndex === 0 ? path.points.length - 1 : currIndex - 1;
      const prevP = path.points[prevIndex];
      const currP = path.points[currIndex];
      const hit = distToBezier(testCoords, prevP, prevP.hOut || prevP, currP.hIn || currP, currP);
      localBest = Math.min(localBest, hit.dist);
    }

    const filledHit = path.fillEnabled && isPointInsidePath(path);
    if (filledHit || localBest < segmentHitRadius) {
      if (localBest < bestDist || bestPath == null) {
        bestPath = path;
        bestIndex = i;
        bestDist = localBest;
      }
    }
  }

  if (!bestPath) return null;
  return { path: bestPath, pathIndex: bestIndex };
};
