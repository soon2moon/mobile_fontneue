import {
  GRID_SIZE,
  MIN_GRID_SIZE,
  MIN_CIRCULAR_STEP,
  MAX_CIRCULAR_STEP,
  DEFAULT_CIRCULAR_STEP
} from '../constants';

// Snap a world point to the grid of the frame that contains it. The design grid
// now lives inside frames (origin = the frame's top-left; circular about the
// frame center), so snapping is frame-relative — a point outside every frame
// does not snap. `frame` is the containing frame (or null).
export const applyGridSnap = (point, config, frame = null) => {
  if (!config.snapToGrid) return point;
  if (config.type === 'none') return point;
  if (!frame) return point;
  const s = Math.max(MIN_GRID_SIZE, Number(config.size) || GRID_SIZE);

  // Frame-local origin (top-left) for axis grids.
  const ox = frame.x - frame.width / 2;
  const oy = frame.y - frame.height / 2;
  const lx = point.x - ox;
  const ly = point.y - oy;

  if (config.type === 'dots' || (config.type === 'lines' && config.edges === 4)) {
    return { x: ox + Math.round(lx / s) * s, y: oy + Math.round(ly / s) * s };
  } else if (config.type === 'lines' && config.edges === 3) {
    const w = s;
    const h = s * Math.sqrt(3);
    const j = Math.round(ly / (h / 2));
    const offsetX = (Math.abs(j) % 2 === 1) ? w / 2 : 0;
    const i = Math.round((lx - offsetX) / w);
    return { x: ox + i * w + offsetX, y: oy + j * (h / 2) };
  } else if (config.type === 'lines' && config.edges === 6) {
    const w = s * Math.sqrt(3);
    return { x: ox + Math.round(lx / (w / 2)) * (w / 2), y: oy + Math.round(ly / (s / 2)) * (s / 2) };
  } else if (config.type === 'circular') {
    // Circular grid is centered on the frame.
    const dx = point.x - frame.x;
    const dy = point.y - frame.y;
    const r = Math.hypot(dx, dy);
    const angle = Math.atan2(dy, dx);
    const snapR = Math.round(r / s) * s;
    const circularStepDeg = Math.max(
      MIN_CIRCULAR_STEP,
      Math.min(MAX_CIRCULAR_STEP, Number(config.circularStep) || DEFAULT_CIRCULAR_STEP)
    );
    const circularStepRad = circularStepDeg * (Math.PI / 180);
    const snapAngle = Math.round(angle / circularStepRad) * circularStepRad;
    return { x: frame.x + snapR * Math.cos(snapAngle), y: frame.y + snapR * Math.sin(snapAngle) };
  } else if (config.type === 'circles') {
    return {
      x: ox + Math.floor(lx / s) * s + s / 2,
      y: oy + Math.floor(ly / s) * s + s / 2
    };
  }
  return point;
};
