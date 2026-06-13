import { SNAP_RADIUS } from '../constants';
import { getBezierPoint, distToBezier } from './geometry';
import { getTextLocalLayout } from './textMeasure';

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

// Rotated-rect adapters shared by the background hit tests. Texts are
// appended AFTER images and the scan walks from the end, so texts hit above
// images at the same spot.
const collectBgObjects = (images, texts) => {
  const objects = images.map(img => ({
    kind: 'image',
    id: img.id,
    x: img.x,
    y: img.y,
    rotation: img.rotation || 0,
    locked: img.locked,
    layerId: img.layerId,
    halfW: (img.width * img.scale) / 2,
    halfH: (img.height * img.scale) / 2
  }));
  texts.forEach(text => {
    const { halfW, halfH } = getTextLocalLayout(text);
    objects.push({
      kind: 'text',
      id: text.id,
      x: text.x,
      y: text.y,
      rotation: text.rotation || 0,
      locked: text.locked,
      layerId: text.layerId,
      halfW,
      halfH
    });
  });
  return objects;
};

// Topmost background object (image or text) interaction under the cursor:
// scale/rotate corner handles (only when it is the single selected background
// object overall) or body move. Skips hidden/locked.
export const getBgHit = (testCoords, { images, texts = [], layers, selectedImageIds, selectedTextIds = [], scaleHandleHitRadius, rotateHandleHitRadius }) => {
  const objects = collectBgObjects(images, texts);
  const singleSelectedId = selectedImageIds.length + selectedTextIds.length === 1
    ? (selectedImageIds[0] ?? selectedTextIds[0])
    : null;

  for (let i = objects.length - 1; i >= 0; i--) {
    const obj = objects[i];
    const layer = layers.find(l => l.id === obj.layerId);
    if (!layer || !layer.visible || layer.locked) continue;
    if (obj.locked) continue;

    const dx = testCoords.x - obj.x;
    const dy = testCoords.y - obj.y;
    const angleRad = -obj.rotation * Math.PI / 180;

    const lx = dx * Math.cos(angleRad) - dy * Math.sin(angleRad);
    const ly = dx * Math.sin(angleRad) + dy * Math.cos(angleRad);

    if (singleSelectedId === obj.id) {
      const corners = [
        { id: 'nw', x: -obj.halfW, y: -obj.halfH, angle: 225 },
        { id: 'ne', x: obj.halfW, y: -obj.halfH, angle: 315 },
        { id: 'se', x: obj.halfW, y: obj.halfH, angle: 45 },
        { id: 'sw', x: -obj.halfW, y: obj.halfH, angle: 135 }
      ];
      for (const c of corners) {
        const dist = Math.hypot(lx - c.x, ly - c.y);
        if (dist <= scaleHandleHitRadius) return { action: `scale-${c.id}`, cursorAngle: c.angle, kind: obj.kind, id: obj.id, rotation: obj.rotation };
        if (dist <= rotateHandleHitRadius) return { action: `rotate-${c.id}`, cursorAngle: null, kind: obj.kind, id: obj.id, rotation: obj.rotation };
      }
    }

    if (Math.abs(lx) <= obj.halfW && Math.abs(ly) <= obj.halfH) {
      return { action: 'move', cursorAngle: null, kind: obj.kind, id: obj.id, rotation: obj.rotation };
    }
  }
  return null;
};

export const findTopTextAtCoords = (testCoords, { texts, layers }) => {
  for (let i = texts.length - 1; i >= 0; i--) {
    const text = texts[i];
    const layer = layers.find(l => l.id === text.layerId);
    if (!layer || !layer.visible || layer.locked || text.locked) continue;

    const dx = testCoords.x - text.x;
    const dy = testCoords.y - text.y;
    const angleRad = -(text.rotation || 0) * Math.PI / 180;
    const lx = dx * Math.cos(angleRad) - dy * Math.sin(angleRad);
    const ly = dx * Math.sin(angleRad) + dy * Math.cos(angleRad);

    const { halfW, halfH } = getTextLocalLayout(text);
    if (Math.abs(lx) <= halfW && Math.abs(ly) <= halfH) {
      return text;
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

// --- Frames ---
// Boards select on plain click / label / handles only; their body never
// joins the generic bg-hit chain so content above stays marquee-able.
export const findTopFrameAtCoords = (coords, { frames, layers }) => {
  for (let i = frames.length - 1; i >= 0; i--) {
    const frame = frames[i];
    const layer = layers.find(l => l.id === frame.layerId);
    if (!layer || !layer.visible || layer.locked || frame.locked) continue;
    if (Math.abs(coords.x - frame.x) <= frame.width / 2 && Math.abs(coords.y - frame.y) <= frame.height / 2) {
      return frame;
    }
  }
  return null;
};

export const getFrameHandleHit = (coords, frame, scaleHandleHitRadius) => {
  const halfW = frame.width / 2;
  const halfH = frame.height / 2;
  const corners = [
    { id: 'scale-nw', x: frame.x - halfW, y: frame.y - halfH },
    { id: 'scale-ne', x: frame.x + halfW, y: frame.y - halfH },
    { id: 'scale-se', x: frame.x + halfW, y: frame.y + halfH },
    { id: 'scale-sw', x: frame.x - halfW, y: frame.y + halfH }
  ];
  for (const corner of corners) {
    if (Math.hypot(coords.x - corner.x, coords.y - corner.y) <= scaleHandleHitRadius) {
      return corner.id;
    }
  }
  return null;
};

// The name strip drawn above the frame's top-left corner (screen-sized).
export const getFrameLabelHit = (coords, frame, zoom) => {
  const left = frame.x - frame.width / 2;
  const top = frame.y - frame.height / 2;
  const labelWidth = Math.min(frame.width, Math.max(40 / zoom, ((frame.name || '').length || 5) * 7 / zoom));
  return coords.x >= left && coords.x <= left + labelWidth
    && coords.y >= top - 18 / zoom && coords.y <= top;
};

// --- Frame containment (nesting) ---
// An object "belongs to" a frame when its center sits inside the frame's rect
// (Figma's drop rule). Membership is derived from position — nothing stored —
// and drives move-together (drag a frame and its children follow) and frame
// export (a frame's children are what gets exported).
export const isCenterInsideFrame = (cx, cy, frame) => (
  Math.abs(cx - frame.x) <= frame.width / 2 && Math.abs(cy - frame.y) <= frame.height / 2
);

export const getPathCenter = (path) => {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  (path?.points || []).forEach(pt => {
    minX = Math.min(minX, pt.x); minY = Math.min(minY, pt.y);
    maxX = Math.max(maxX, pt.x); maxY = Math.max(maxY, pt.y);
    if (pt.hIn) { minX = Math.min(minX, pt.hIn.x); minY = Math.min(minY, pt.hIn.y); maxX = Math.max(maxX, pt.hIn.x); maxY = Math.max(maxY, pt.hIn.y); }
    if (pt.hOut) { minX = Math.min(minX, pt.hOut.x); minY = Math.min(minY, pt.hOut.y); maxX = Math.max(maxX, pt.hOut.x); maxY = Math.max(maxY, pt.hOut.y); }
  });
  if (minX === Infinity) return null;
  return { x: (minX + maxX) / 2, y: (minY + maxY) / 2 };
};

// Objects on visible layers whose center lies inside the frame.
export const collectFrameChildren = (frame, { paths = [], images = [], texts = [], layers = [] }) => {
  const visible = new Set(layers.filter(l => l.visible).map(l => l.id));
  const childImages = images.filter(img => visible.has(img.layerId) && isCenterInsideFrame(img.x, img.y, frame));
  const childTexts = texts.filter(t => visible.has(t.layerId) && isCenterInsideFrame(t.x, t.y, frame));
  const childPaths = paths.filter(p => {
    if (!visible.has(p.layerId)) return false;
    const c = getPathCenter(p);
    return c && isCenterInsideFrame(c.x, c.y, frame);
  });
  return { childImages, childTexts, childPaths };
};
