// --- LAYER HELPER ---
import { getTextLocalLayout } from './textMeasure';

export const generateLayerId = () => `layer-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

export const createLayer = (type, existingCount) => {
   let name = "Vector";
   if (type === 'image') name = "Image";
   else if (type === 'text') name = "Text";
   else if (type === 'rectangle') name = "Rectangle";
   else if (type === 'ellipse') name = "Ellipse";
   else if (type === 'polygon') name = "Polygon";
   else if (type === 'star') name = "Star";
   else if (type === 'line') name = "Line";

   return {
       id: generateLayerId(),
       name: `${name} ${existingCount + 1}`,
       visible: true,
       locked: false,
       itemType: type || 'vector'
   };
};

// Group document content by owning layer, with counts, for the layer panels.
export const groupContentByLayer = (paths, images, texts = []) => {
  const pathsByLayerId = {};
  paths.forEach(path => {
    if (!pathsByLayerId[path.layerId]) pathsByLayerId[path.layerId] = [];
    pathsByLayerId[path.layerId].push(path);
  });
  const imagesByLayerId = {};
  images.forEach(image => {
    if (!imagesByLayerId[image.layerId]) imagesByLayerId[image.layerId] = [];
    imagesByLayerId[image.layerId].push(image);
  });
  const textsByLayerId = {};
  texts.forEach(text => {
    if (!textsByLayerId[text.layerId]) textsByLayerId[text.layerId] = [];
    textsByLayerId[text.layerId].push(text);
  });
  const pathCountByLayerId = {};
  paths.forEach(path => {
    pathCountByLayerId[path.layerId] = (pathCountByLayerId[path.layerId] || 0) + 1;
  });
  const imageCountByLayerId = {};
  images.forEach(image => {
    imageCountByLayerId[image.layerId] = (imageCountByLayerId[image.layerId] || 0) + 1;
  });
  const textCountByLayerId = {};
  texts.forEach(text => {
    textCountByLayerId[text.layerId] = (textCountByLayerId[text.layerId] || 0) + 1;
  });
  return { pathsByLayerId, imagesByLayerId, textsByLayerId, pathCountByLayerId, imageCountByLayerId, textCountByLayerId };
};

// Padded world-space bounds of a layer's content, for thumbnail previews.
// Returns null when the layer is empty.
export const getLayerPreviewBounds = (layerPaths, layerImages, layerTexts = []) => {
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;

  layerPaths.forEach(path => {
    (path.points || []).forEach(point => {
      minX = Math.min(minX, point.x);
      minY = Math.min(minY, point.y);
      maxX = Math.max(maxX, point.x);
      maxY = Math.max(maxY, point.y);
      if (point.hIn) {
        minX = Math.min(minX, point.hIn.x);
        minY = Math.min(minY, point.hIn.y);
        maxX = Math.max(maxX, point.hIn.x);
        maxY = Math.max(maxY, point.hIn.y);
      }
      if (point.hOut) {
        minX = Math.min(minX, point.hOut.x);
        minY = Math.min(minY, point.hOut.y);
        maxX = Math.max(maxX, point.hOut.x);
        maxY = Math.max(maxY, point.hOut.y);
      }
    });
  });

  layerImages.forEach(img => {
    const scale = Number.isFinite(img.scale) ? img.scale : 1;
    const halfW = (img.width * scale) / 2;
    const halfH = (img.height * scale) / 2;
    const rad = (img.rotation || 0) * Math.PI / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);
    [
      { x: -halfW, y: -halfH },
      { x: halfW, y: -halfH },
      { x: halfW, y: halfH },
      { x: -halfW, y: halfH }
    ].forEach(corner => {
      const worldX = img.x + (corner.x * cos - corner.y * sin);
      const worldY = img.y + (corner.x * sin + corner.y * cos);
      minX = Math.min(minX, worldX);
      minY = Math.min(minY, worldY);
      maxX = Math.max(maxX, worldX);
      maxY = Math.max(maxY, worldY);
    });
  });

  layerTexts.forEach(text => {
    const { halfW, halfH } = getTextLocalLayout(text);
    const rad = (text.rotation || 0) * Math.PI / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);
    [
      { x: -halfW, y: -halfH },
      { x: halfW, y: -halfH },
      { x: halfW, y: halfH },
      { x: -halfW, y: halfH }
    ].forEach(corner => {
      const worldX = text.x + (corner.x * cos - corner.y * sin);
      const worldY = text.y + (corner.x * sin + corner.y * cos);
      minX = Math.min(minX, worldX);
      minY = Math.min(minY, worldY);
      maxX = Math.max(maxX, worldX);
      maxY = Math.max(maxY, worldY);
    });
  });

  if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(maxX) || !Number.isFinite(maxY)) {
    return null;
  }

  const padding = 8;
  minX -= padding;
  minY -= padding;
  maxX += padding;
  maxY += padding;
  const width = Math.max(1, maxX - minX);
  const height = Math.max(1, maxY - minY);
  return { minX, minY, width, height };
};
