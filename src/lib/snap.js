import {
  GRID_SIZE,
  MIN_GRID_SIZE,
  MIN_CIRCULAR_STEP,
  MAX_CIRCULAR_STEP,
  DEFAULT_CIRCULAR_STEP
} from '../constants';

export const applyGridSnap = (point, config) => {
  if (!config.snapToGrid) return point;
  if (config.type === 'none') return point;
  const s = Math.max(MIN_GRID_SIZE, Number(config.size) || GRID_SIZE);

  if (config.type === 'dots' || (config.type === 'lines' && config.edges === 4)) {
    return {
      x: Math.round(point.x / s) * s,
      y: Math.round(point.y / s) * s
    };
  } else if (config.type === 'lines' && config.edges === 3) {
    const w = s;
    const h = s * Math.sqrt(3);
    const j = Math.round(point.y / (h / 2));
    const offsetX = (Math.abs(j) % 2 === 1) ? w / 2 : 0;
    const i = Math.round((point.x - offsetX) / w);
    return {
      x: i * w + offsetX,
      y: j * (h / 2)
    };
  } else if (config.type === 'lines' && config.edges === 6) {
     const w = s * Math.sqrt(3);
     return {
       x: Math.round(point.x / (w/2)) * (w/2),
       y: Math.round(point.y / (s/2)) * (s/2)
     };
  } else if (config.type === 'circular') {
    const r = Math.hypot(point.x, point.y);
    const angle = Math.atan2(point.y, point.x);
    const snapR = Math.round(r / s) * s;
    const circularStepDeg = Math.max(
      MIN_CIRCULAR_STEP,
      Math.min(MAX_CIRCULAR_STEP, Number(config.circularStep) || DEFAULT_CIRCULAR_STEP)
    );
    const circularStepRad = circularStepDeg * (Math.PI / 180);
    const snapAngle = Math.round(angle / circularStepRad) * circularStepRad;
    return {
      x: snapR * Math.cos(snapAngle),
      y: snapR * Math.sin(snapAngle)
    };
  } else if (config.type === 'circles') {
    const cx = Math.floor(point.x / s) * s + s / 2;
    const cy = Math.floor(point.y / s) * s + s / 2;
    return { x: cx, y: cy };
  }
  return point;
};
