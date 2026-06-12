import { getTextLocalLayout } from './textMeasure';

// World-space AABB of a clipboard payload (paths incl. handles, images and
// texts via rotated corners — same math as the export bounds). Returns
// { minX, minY, maxX, maxY, centerX, centerY } or null when empty.
export function computePayloadBounds({ paths = [], images = [], texts = [] }) {
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;
  const extend = (x, y) => {
    minX = Math.min(minX, x);
    minY = Math.min(minY, y);
    maxX = Math.max(maxX, x);
    maxY = Math.max(maxY, y);
  };

  paths.forEach(path => {
    (path.points || []).forEach(point => {
      extend(point.x, point.y);
      if (point.hIn) extend(point.hIn.x, point.hIn.y);
      if (point.hOut) extend(point.hOut.x, point.hOut.y);
    });
  });

  const extendRotatedBox = (cx, cy, halfW, halfH, rotation) => {
    const rad = (rotation || 0) * Math.PI / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);
    [
      { x: -halfW, y: -halfH },
      { x: halfW, y: -halfH },
      { x: halfW, y: halfH },
      { x: -halfW, y: halfH }
    ].forEach(corner => {
      extend(cx + (corner.x * cos - corner.y * sin), cy + (corner.x * sin + corner.y * cos));
    });
  };

  images.forEach(img => {
    extendRotatedBox(img.x, img.y, (img.width * img.scale) / 2, (img.height * img.scale) / 2, img.rotation);
  });

  texts.forEach(text => {
    const { halfW, halfH } = getTextLocalLayout(text);
    extendRotatedBox(text.x, text.y, halfW, halfH, text.rotation);
  });

  if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(maxX) || !Number.isFinite(maxY)) {
    return null;
  }
  return { minX, minY, maxX, maxY, centerX: (minX + maxX) / 2, centerY: (minY + maxY) / 2 };
}
