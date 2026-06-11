import { useRef, useCallback } from 'react';
import { DEFAULT_STROKE_COLOR } from '../constants';
import { normalizeStrokeColor } from '../lib/stroke';
import { escapeXml } from '../lib/svg';
import { createLayer } from '../lib/layers';

// Image (and prompt-text) insertion: file → object URL → centered, fit-scaled
// image on a fresh layer, plus the hidden file-input plumbing.
export function useImageImport({
  activeLayerId, setActiveLayerId,
  lockedLayerIds,
  layers, setLayers,
  paths, currentPath,
  images, setImages,
  texts,
  commitHistory,
  setSelectedImageIds, setSelectedPoints,
  setOpenPanels, setExpandedPanel,
  viewportSize, panRef, zoomRef,
  pathStyleDefaults
}) {
  const fileInputRef = useRef(null);

  const insertImageFromFile = useCallback((file, options = {}) => {
    if (!file) return false;
    if (activeLayerId && lockedLayerIds.has(activeLayerId)) return false;

    const layerType = options.layerType || 'image';
    const initialOpacity = Number.isFinite(options.opacity)
      ? Math.max(0, Math.min(1, options.opacity))
      : 1;
    const shouldOpenImagePanel = options.openImagePanel !== false;
    const url = URL.createObjectURL(file);
    const img = new window.Image();
    img.onload = () => {
      commitHistory({ paths, currentPath, images, layers, texts });
      const count = layers.filter(l => l.itemType === layerType).length;
      const newLayer = createLayer(layerType, count);
      setLayers(prev => [newLayer, ...prev]);
      setActiveLayerId(newLayer.id);

      const newImg = {
        id: Date.now(),
        url,
        width: img.width,
        height: img.height,
        x: (viewportSize.width / 2 - panRef.current.x) / zoomRef.current,
        y: (viewportSize.height / 2 - panRef.current.y) / zoomRef.current,
        scale: (() => {
          const viewWorldWidth = viewportSize.width / zoomRef.current;
          const viewWorldHeight = viewportSize.height / zoomRef.current;
          const maxWidth = viewWorldWidth * 0.72;
          const maxHeight = viewWorldHeight * 0.58;
          const widthScale = maxWidth / img.width;
          const heightScale = maxHeight / img.height;
          const fitScale = Math.min(widthScale, heightScale, 1);
          return Number.isFinite(fitScale) && fitScale > 0 ? fitScale : 1;
        })(),
        rotation: 0,
        opacity: initialOpacity,
        locked: false,
        layerId: newLayer.id
      };
      setImages(prev => [...prev, newImg]);
      setSelectedImageIds([newImg.id]);
      setSelectedPoints([]);
      if (shouldOpenImagePanel) {
        setOpenPanels(prev => ({ ...prev, image: true }));
        setExpandedPanel('image');
      }
    };
    img.src = url;
    return true;
  }, [activeLayerId, lockedLayerIds, commitHistory, paths, currentPath, images, texts, layers, viewportSize.width, viewportSize.height]);

  const insertTextFromPrompt = useCallback(() => {
    if (activeLayerId && lockedLayerIds.has(activeLayerId)) return false;
    const rawText = window.prompt('Enter text', 'Text');
    if (rawText == null) return false;

    const normalizedLines = rawText
      .split(/\r?\n/)
      .map(line => line.trimEnd())
      .filter((line, lineIndex, lines) => line.trim().length > 0 || (lines.length === 1 && lineIndex === 0));
    if (normalizedLines.length === 0) return false;

    const fontSize = 96;
    const lineHeight = Math.round(fontSize * 1.14);
    const padding = 24;
    const maxCharCount = normalizedLines.reduce((maxChars, line) => Math.max(maxChars, line.length), 1);
    const width = Math.max(96, Math.ceil(maxCharCount * fontSize * 0.62) + padding * 2);
    const height = Math.max(fontSize + padding * 2, normalizedLines.length * lineHeight + padding * 2);
    const fillColor = normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR);
    const baseline = padding + fontSize;
    const tspans = normalizedLines.map((line, index) => (
      `<tspan x="${padding}" dy="${index === 0 ? 0 : lineHeight}">${escapeXml(line || ' ')}</tspan>`
    )).join('');

    const svgMarkup = `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}"><text x="${padding}" y="${baseline}" font-size="${fontSize}" font-family="Arial, sans-serif" fill="${fillColor}">${tspans}</text></svg>`;
    const file = new File(
      [new Blob([svgMarkup], { type: 'image/svg+xml;charset=utf-8' })],
      `text-${Date.now()}.svg`,
      { type: 'image/svg+xml' }
    );

    return insertImageFromFile(file, { layerType: 'text', opacity: 1 });
  }, [activeLayerId, lockedLayerIds, pathStyleDefaults.strokeColor, insertImageFromFile]);

  const handleImageUpload = (e) => {
    const file = e.target.files?.[0];
    if (file) {
      insertImageFromFile(file);
    }
    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }
  };

  return {
    fileInputRef,
    insertImageFromFile,
    insertTextFromPrompt,
    handleImageUpload
  };
}
