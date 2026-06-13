import { THEME } from '../theme';
import { DEFAULT_STROKE_WIDTH, DEFAULT_STROKE_COLOR, DEFAULT_FILL_COLOR } from '../constants';
import { pointsToPath } from './paths';
import { buildCompositeFillGroups } from './compositeFill';
import { normalizeStrokeWidth, normalizeStrokeColor, normalizeOpacity } from './stroke';
import { escapeXml } from './svg';
import { getTextLocalLayout } from './textMeasure';

// Resolve which paths/images/texts an export covers: the current selection or
// the whole canvas — hidden layers are excluded either way.
export function collectExportItems(scope, { layers, paths, images, texts = [], selectedPoints, selectedImageIds, selectedTextIds = [] }) {
  const visibleLayerIdSet = new Set(layers.filter(layer => layer.visible).map(layer => layer.id));

  // Frame export covers all visible content (cropped to the frame rect by
  // the caller via explicit bounds), like the whole-canvas scope.
  if (scope === 'selection') {
    const selectedPathIndexSet = new Set(selectedPoints.map(point => point.pathIndex));
    const scopedPaths = [...selectedPathIndexSet]
      .map(index => paths[index])
      .filter(path => path && visibleLayerIdSet.has(path.layerId));
    const selectedImageIdSet = new Set(selectedImageIds);
    const scopedImages = images.filter(img => selectedImageIdSet.has(img.id) && visibleLayerIdSet.has(img.layerId));
    const selectedTextIdSet = new Set(selectedTextIds);
    const scopedTexts = texts.filter(text => selectedTextIdSet.has(text.id) && visibleLayerIdSet.has(text.layerId));
    return { exportPaths: scopedPaths, exportImages: scopedImages, exportTexts: scopedTexts };
  }

  return {
    exportPaths: paths.filter(path => visibleLayerIdSet.has(path.layerId)),
    exportImages: images.filter(img => visibleLayerIdSet.has(img.layerId)),
    exportTexts: texts.filter(text => visibleLayerIdSet.has(text.layerId))
  };
}

// Build a standalone SVG document tightly cropped around the given items.
// Returns { svg, width, height } or null when there is nothing to export.
// Stacking matches the canvas: per-color composite fills at the bottom, then
// images, texts, and stroke-only path outlines on top.
export function buildExportSvgBundle({ exportPaths, exportImages, exportTexts = [], layers = [], bounds = null, background = null }) {
  if (exportPaths.length === 0 && exportImages.length === 0 && exportTexts.length === 0 && !bounds) return null;

  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;

  exportPaths.forEach(path => {
    path.points.forEach(point => {
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

  exportImages.forEach(img => {
    const halfW = (img.width * img.scale) / 2;
    const halfH = (img.height * img.scale) / 2;
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

  exportTexts.forEach(text => {
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

  // Explicit bounds (frame export) crop to the rect verbatim — no measured
  // content bbox, no padding. Otherwise crop tight around the content.
  if (bounds) {
    minX = bounds.minX;
    minY = bounds.minY;
    maxX = bounds.maxX;
    maxY = bounds.maxY;
  } else {
    if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(maxX) || !Number.isFinite(maxY)) {
      return null;
    }
    const padding = 12;
    minX -= padding;
    minY -= padding;
    maxX += padding;
    maxY += padding;
  }
  const width = Math.max(1, Math.ceil(maxX - minX));
  const height = Math.max(1, Math.ceil(maxY - minY));

  const imageMarkup = exportImages.map(img => {
    const renderWidth = img.width * img.scale;
    const renderHeight = img.height * img.scale;
    const x = img.x - renderWidth / 2;
    const y = img.y - renderHeight / 2;
    const opacity = Number.isFinite(img.opacity) ? Math.max(0, Math.min(1, img.opacity)) : 1;
    const rotation = Number.isFinite(img.rotation) ? img.rotation : 0;
    return `<image href="${escapeXml(img.url)}" x="${x}" y="${y}" width="${renderWidth}" height="${renderHeight}" opacity="${opacity}" transform="rotate(${rotation} ${img.x} ${img.y})" />`;
  }).join('');

  // Same local layout as the canvas renderer, so exports stay WYSIWYG.
  const textMarkup = exportTexts.map(text => {
    const layout = getTextLocalLayout(text);
    const opacity = Number.isFinite(text.opacity) ? Math.max(0, Math.min(1, text.opacity)) : 1;
    const rotation = Number.isFinite(text.rotation) ? text.rotation : 0;
    const fill = normalizeStrokeColor(text.fill, DEFAULT_FILL_COLOR);
    const tspans = layout.lines.map(line => (
      `<tspan x="${line.x}" y="${line.y}">${escapeXml(line.text)}</tspan>`
    )).join('');
    return `<text font-family="${escapeXml(text.fontFamily)}" font-size="${text.fontSize}" font-weight="${text.fontWeight}" fill="${fill}" opacity="${opacity}" xml:space="preserve" transform="translate(${text.x} ${text.y}) rotate(${rotation})">${tspans}</text>`;
  }).join('');

  // Same per-color winding groups as the canvas, so donut holes survive and
  // multi-color stacking matches what the user sees.
  const fillMarkup = buildCompositeFillGroups({ paths: exportPaths, layers, isPathVisible: () => true })
    .map(group => `<path d="${escapeXml(group.d)}" fill="${group.color}" fill-opacity="${group.opacity}" fill-rule="nonzero" />`)
    .join('');

  const pathMarkup = exportPaths.map(path => {
    if (path.strokeEnabled === false) return '';
    const d = pointsToPath(path.points, path.isClosed);
    const strokeColor = normalizeStrokeColor(path.strokeColor, DEFAULT_STROKE_COLOR);
    const strokeWidthValue = normalizeStrokeWidth(path.strokeWidth, DEFAULT_STROKE_WIDTH);
    const strokeOpacityValue = normalizeOpacity(path.strokeOpacity);
    return `<path d="${escapeXml(d)}" fill="none" stroke="${strokeColor}" stroke-width="${strokeWidthValue}" stroke-opacity="${strokeOpacityValue}" stroke-linejoin="round" stroke-linecap="round" />`;
  }).join('');

  // Frame background rect spans the whole cropped viewBox, painted first.
  const backgroundMarkup = background
    ? `<rect x="${minX}" y="${minY}" width="${width}" height="${height}" fill="${background}" />`
    : '';

  const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}"><g transform="translate(${-minX} ${-minY})">${backgroundMarkup}${fillMarkup}${imageMarkup}${textMarkup}${pathMarkup}</g></svg>`;
  return { svg, width, height };
}

export function downloadBlob(blob, filename) {
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

// Rasterize an SVG bundle through an offscreen <img> + canvas and trigger a
// PNG/JPG download (JPG gets the canvas background since it has no alpha).
export async function rasterizeAndDownloadBundle(bundle, format, baseName) {
  const svgBlob = new Blob([bundle.svg], { type: 'image/svg+xml;charset=utf-8' });
  const svgUrl = URL.createObjectURL(svgBlob);
  try {
    const svgImage = await new Promise((resolve, reject) => {
      const img = new window.Image();
      img.onload = () => resolve(img);
      img.onerror = reject;
      img.src = svgUrl;
    });

    const canvas = document.createElement('canvas');
    canvas.width = Math.max(1, Math.round(bundle.width));
    canvas.height = Math.max(1, Math.round(bundle.height));
    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    if (format === 'jpg') {
      ctx.fillStyle = THEME.bg;
      ctx.fillRect(0, 0, canvas.width, canvas.height);
    } else {
      ctx.clearRect(0, 0, canvas.width, canvas.height);
    }

    ctx.drawImage(svgImage, 0, 0, canvas.width, canvas.height);
    const mime = format === 'jpg' ? 'image/jpeg' : 'image/png';
    const dataUrl = canvas.toDataURL(mime, format === 'jpg' ? 0.92 : undefined);
    const link = document.createElement('a');
    link.href = dataUrl;
    link.download = `${baseName}.${format === 'jpg' ? 'jpg' : 'png'}`;
    document.body.appendChild(link);
    link.click();
    link.remove();
  } finally {
    URL.revokeObjectURL(svgUrl);
  }
}
