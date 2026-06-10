// Bounding box (with handles) around a multi-point / mixed selection in edit
// mode. Frozen to the action's stored bbox while a scale/rotate is in
// progress so the box doesn't chase its own transform.
export const computeSelectionBBox = ({
  mode,
  activePathEditId,
  selectedPoints,
  selectedImageIds,
  pointAction,
  paths,
  images,
  layers,
  zoom,
  isPathVisible
}) => {
  const hasMixedSelection = selectedPoints.length > 0 && selectedImageIds.length > 0;
  if (!(mode === 'edit' && !activePathEditId && (selectedPoints.length > 1 || hasMixedSelection))) {
    return null;
  }

  if (pointAction && pointAction.bbox) {
    return pointAction.bbox;
  }

  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

  selectedPoints.forEach(sp => {
    const path = paths[sp.pathIndex];
    if (!path || !isPathVisible(path)) return;
    const pt = path.points[sp.pointIndex];
    if (pt) {
      minX = Math.min(minX, pt.x); minY = Math.min(minY, pt.y);
      maxX = Math.max(maxX, pt.x); maxY = Math.max(maxY, pt.y);
      if (pt.hIn) {
        minX = Math.min(minX, pt.hIn.x); minY = Math.min(minY, pt.hIn.y);
        maxX = Math.max(maxX, pt.hIn.x); maxY = Math.max(maxY, pt.hIn.y);
      }
      if (pt.hOut) {
        minX = Math.min(minX, pt.hOut.x); minY = Math.min(minY, pt.hOut.y);
        maxX = Math.max(maxX, pt.hOut.x); maxY = Math.max(maxY, pt.hOut.y);
      }
    }
  });

  if (hasMixedSelection) {
    selectedImageIds.forEach(imgId => {
      const img = images.find(i => i.id === imgId);
      if (!img) return;
      const layer = layers.find(l => l.id === img.layerId);
      if (!layer || !layer.visible) return;

      const halfW = (img.width * img.scale) / 2;
      const halfH = (img.height * img.scale) / 2;
      const rad = img.rotation * Math.PI / 180;
      const cos = Math.cos(rad);
      const sin = Math.sin(rad);

      const corners = [
        { x: -halfW, y: -halfH },
        { x: halfW, y: -halfH },
        { x: halfW, y: halfH },
        { x: -halfW, y: halfH }
      ];

      corners.forEach(corner => {
        const worldX = img.x + (corner.x * cos - corner.y * sin);
        const worldY = img.y + (corner.x * sin + corner.y * cos);
        minX = Math.min(minX, worldX); minY = Math.min(minY, worldY);
        maxX = Math.max(maxX, worldX); maxY = Math.max(maxY, worldY);
      });
    });
  }

  if (minX === Infinity) return null;
  const pad = 10 / zoom;
  return { minX: minX - pad, minY: minY - pad, maxX: maxX + pad, maxY: maxY + pad };
};
