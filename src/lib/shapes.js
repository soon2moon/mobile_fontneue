// --- SHAPE GENERATION HELPER ---
export const generateShapePath = (startX, startY, endX, endY, type, shiftKey) => {
  let minX = Math.min(startX, endX);
  let minY = Math.min(startY, endY);
  let maxX = Math.max(startX, endX);
  let maxY = Math.max(startY, endY);

  if (shiftKey && type !== 'line') {
      const size = Math.max(maxX - minX, maxY - minY);
      maxX = startX < endX ? startX + size : startX;
      minX = startX < endX ? startX : startX - size;
      maxY = startY < endY ? startY + size : startY;
      minY = startY < endY ? startY : startY - size;
  }

  const w = maxX - minX;
  const h = maxY - minY;
  const cx = minX + w / 2;
  const cy = minY + h / 2;

  if (type === 'rectangle') {
      return {
          isClosed: true,
          points: [
              { x: minX, y: minY, hIn: {x: minX, y: minY}, hOut: {x: minX, y: minY} },
              { x: maxX, y: minY, hIn: {x: maxX, y: minY}, hOut: {x: maxX, y: minY} },
              { x: maxX, y: maxY, hIn: {x: maxX, y: maxY}, hOut: {x: maxX, y: maxY} },
              { x: minX, y: maxY, hIn: {x: minX, y: maxY}, hOut: {x: minX, y: maxY} }
          ]
      };
  }
  if (type === 'ellipse') {
      const rx = w / 2;
      const ry = h / 2;
      const kappa = 0.5522847498;
      const kx = rx * kappa;
      const ky = ry * kappa;
      return {
          isClosed: true,
          points: [
              { x: cx, y: minY, hIn: {x: cx - kx, y: minY}, hOut: {x: cx + kx, y: minY} },
              { x: maxX, y: cy, hIn: {x: maxX, y: cy - ky}, hOut: {x: maxX, y: cy + ky} },
              { x: cx, y: maxY, hIn: {x: cx + kx, y: maxY}, hOut: {x: cx - kx, y: maxY} },
              { x: minX, y: cy, hIn: {x: minX, y: cy + ky}, hOut: {x: minX, y: cy - ky} }
          ]
      };
  }
  if (type === 'line') {
      let p2x = endX;
      let p2y = endY;
      if (shiftKey) {
          const angle = Math.atan2(endY - startY, endX - startX);
          const snappedAngle = Math.round(angle / (Math.PI / 12)) * (Math.PI / 12);
          const dist = Math.hypot(endX - startX, endY - startY);
          p2x = startX + Math.cos(snappedAngle) * dist;
          p2y = startY + Math.sin(snappedAngle) * dist;
      }
      return {
          isClosed: false,
          points: [
              { x: startX, y: startY, hIn: {x: startX, y: startY}, hOut: {x: startX, y: startY} },
              { x: p2x, y: p2y, hIn: {x: p2x, y: p2y}, hOut: {x: p2x, y: p2y} }
          ]
      };
  }
  if (type === 'polygon') {
      return {
          isClosed: true,
          points: [
              { x: cx, y: minY, hIn: {x: cx, y: minY}, hOut: {x: cx, y: minY} },
              { x: maxX, y: maxY, hIn: {x: maxX, y: maxY}, hOut: {x: maxX, y: maxY} },
              { x: minX, y: maxY, hIn: {x: minX, y: maxY}, hOut: {x: minX, y: maxY} }
          ]
      };
  }
  if (type === 'star') {
      const points = [];
      const outerRadius = Math.min(w, h) / 2;
      const innerRadius = outerRadius * 0.382;
      for (let i = 0; i < 10; i++) {
          const radius = i % 2 === 0 ? outerRadius : innerRadius;
          const angle = (i * Math.PI) / 5 - Math.PI / 2;
          const px = cx + Math.cos(angle) * radius;
          const py = cy + Math.sin(angle) * radius;
          points.push({ x: px, y: py, hIn: {x: px, y: py}, hOut: {x: px, y: py} });
      }
      return { isClosed: true, points };
  }
  return { isClosed: false, points: [] };
};
