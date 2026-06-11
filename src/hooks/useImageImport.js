import { useRef, useCallback } from 'react';
import { createLayer } from '../lib/layers';

// Image insertion: file → object URL → centered, fit-scaled image on a fresh
// layer, plus the hidden file-input plumbing.
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
  viewportSize, panRef, zoomRef
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
    handleImageUpload
  };
}
