export const distToSegmentSquared = (p, v, w) => {
  const l2 = (w.x - v.x)**2 + (w.y - v.y)**2;
  if (l2 === 0) return (p.x - v.x)**2 + (p.y - v.y)**2;
  let t = ((p.x - v.x) * (w.x - v.x) + (p.y - v.y) * (w.y - v.y)) / l2;
  t = Math.max(0, Math.min(1, t));
  return (p.x - (v.x + t * (w.x - v.x)))**2 + (p.y - (v.y + t * (w.y - v.y)))**2;
};
export const distToSegment = (p, v, w) => Math.sqrt(distToSegmentSquared(p, v, w));

export const getBezierPoint = (p0, p1, p2, p3, t) => {
  const u = 1 - t;
  const tt = t * t;
  const uu = u * u;
  const uuu = uu * u;
  const ttt = tt * t;
  return {
    x: uuu * p0.x + 3 * uu * t * p1.x + 3 * u * tt * p2.x + ttt * p3.x,
    y: uuu * p0.y + 3 * uu * t * p1.y + 3 * u * tt * p2.y + ttt * p3.y
  };
};

export const distToBezier = (point, p0, p1, p2, p3) => {
  let minDist = Infinity;
  let bestT = 0;
  let prevPoint = p0;
  const steps = 20;
  for (let i = 1; i <= steps; i++) {
    const tCurr = i / steps;
    const currPoint = getBezierPoint(p0, p1, p2, p3, tCurr);

    const l2 = (currPoint.x - prevPoint.x)**2 + (currPoint.y - prevPoint.y)**2;
    let tSeg = 0;
    if (l2 !== 0) {
      tSeg = ((point.x - prevPoint.x) * (currPoint.x - prevPoint.x) + (point.y - prevPoint.y) * (currPoint.y - prevPoint.y)) / l2;
      tSeg = Math.max(0, Math.min(1, tSeg));
    }
    const projX = prevPoint.x + tSeg * (currPoint.x - prevPoint.x);
    const projY = prevPoint.y + tSeg * (currPoint.y - prevPoint.y);
    const d = Math.sqrt((point.x - projX)**2 + (point.y - projY)**2);

    if (d < minDist) {
      minDist = d;
      bestT = (i - 1) / steps + tSeg * (1 / steps);
    }
    prevPoint = currPoint;
  }
  return { dist: minDist, t: bestT };
};

export const splitBezier = (p0, p1, p2, p3, t) => {
  const lerp = (a, b, t) => ({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t });
  const isStraight = Math.hypot(p1.x - p0.x, p1.y - p0.y) < 0.1 && Math.hypot(p3.x - p2.x, p3.y - p2.y) < 0.1;

  if (isStraight) {
    const b = lerp(p0, p3, t);
    return {
      left: { hOut: p0 },
      right: { hIn: p3 },
      newPoint: { x: b.x, y: b.y, hIn: { ...b }, hOut: { ...b } }
    };
  }

  const q0 = lerp(p0, p1, t);
  const q1 = lerp(p1, p2, t);
  const q2 = lerp(p2, p3, t);
  const r0 = lerp(q0, q1, t);
  const r1 = lerp(q1, q2, t);
  const b = lerp(r0, r1, t);

  return {
    left: { hOut: q0 },
    right: { hIn: q2 },
    newPoint: { x: b.x, y: b.y, hIn: r0, hOut: r1 }
  };
};

export const reflectPointAcrossPerpBisector = (p, p1, p2) => {
  const m = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
  const dx = p2.x - p1.x;
  const dy = p2.y - p1.y;
  const dotDD = dx * dx + dy * dy;
  if (dotDD === 0) return { ...p };
  const vx = p.x - m.x;
  const vy = p.y - m.y;
  const dotVD = vx * dx + vy * dy;
  return {
    x: p.x - 2 * (dotVD / dotDD) * dx,
    y: p.y - 2 * (dotVD / dotDD) * dy
  };
};

export const applyShiftSnap = (currentCoords, refPoint, shiftKey) => {
  if (!shiftKey || !refPoint) return currentCoords;
  const dx = currentCoords.x - refPoint.x;
  const dy = currentCoords.y - refPoint.y;
  const angle = Math.atan2(dy, dx);
  const snappedAngle = Math.round(angle / (Math.PI / 12)) * (Math.PI / 12);
  const dist = Math.hypot(dx, dy);
  return {
    x: refPoint.x + Math.cos(snappedAngle) * dist,
    y: refPoint.y + Math.sin(snappedAngle) * dist
  };
};

export const shortestDeltaDeg = (current, previous) => {
  let delta = current - previous;
  if (delta > 180) delta -= 360;
  if (delta < -180) delta += 360;
  return delta;
};

export const normalizeAngleDeg = (angle) => {
  let normalized = ((angle + 180) % 360 + 360) % 360 - 180;
  if (Object.is(normalized, -0)) normalized = 0;
  return normalized;
};

// Relative corner-scale for a rotated, center-anchored object: the corner
// diagonally opposite `cornerId` stays fixed in world space while the pointer
// drives the dragged corner. halfW/halfH are the object's CURRENT world
// half-extents, so the returned factor s is relative (1 = corner unmoved);
// callers multiply their own size field (image scale, text fontSize) by s.
export const computeCornerScale = ({ coords, cornerId, center, rotation, halfW, halfH, minScale = 0.01 }) => {
  let localCorner, localOpposite;
  if (cornerId === 'nw') { localCorner = { x: -halfW, y: -halfH }; localOpposite = { x: halfW, y: halfH }; }
  if (cornerId === 'ne') { localCorner = { x: halfW, y: -halfH }; localOpposite = { x: -halfW, y: halfH }; }
  if (cornerId === 'se') { localCorner = { x: halfW, y: halfH }; localOpposite = { x: -halfW, y: -halfH }; }
  if (cornerId === 'sw') { localCorner = { x: -halfW, y: halfH }; localOpposite = { x: halfW, y: -halfH }; }
  if (!localCorner) return { s: 1, newCenter: { x: center.x, y: center.y } };

  const theta = rotation * Math.PI / 180;
  const rotateVec = (v) => ({
    x: v.x * Math.cos(theta) - v.y * Math.sin(theta),
    y: v.x * Math.sin(theta) + v.y * Math.cos(theta)
  });

  const fixedOffset = rotateVec(localOpposite);
  const fixedPt = { x: center.x + fixedOffset.x, y: center.y + fixedOffset.y };

  const diagVec = { x: localCorner.x - localOpposite.x, y: localCorner.y - localOpposite.y };
  const diagLen = Math.hypot(diagVec.x, diagVec.y);
  if (!(diagLen > 0)) return { s: 1, newCenter: { x: center.x, y: center.y } };
  const u = rotateVec({ x: diagVec.x / diagLen, y: diagVec.y / diagLen });

  const v = { x: coords.x - fixedPt.x, y: coords.y - fixedPt.y };
  const s = Math.max(minScale, (v.x * u.x + v.y * u.y) / diagLen);

  const newOppositeOffset = rotateVec({ x: s * localOpposite.x, y: s * localOpposite.y });
  return { s, newCenter: { x: fixedPt.x - newOppositeOffset.x, y: fixedPt.y - newOppositeOffset.y } };
};
