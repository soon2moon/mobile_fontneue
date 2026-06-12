import { useRef, useCallback, useEffect } from 'react';
import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN,
  DEFAULT_FILL_COLOR,
  CLIPBOARD_PAYLOAD_TYPE
} from '../constants';
import { clonePoint, resolvePathEditGroupId, expandPathSelectionToGroups } from '../lib/paths';
import { normalizeStrokeWidth, normalizeStrokeColor, normalizeStrokeAlign } from '../lib/stroke';
import { generateEditGroupId } from '../lib/svg';
import { createLayer } from '../lib/layers';
import { normalizeTextObject } from '../lib/objectModel';

// Copy/cut/paste/duplicate for paths + images + texts. Payloads live in an
// in-memory ref (primary) and round-trip through the system clipboard as JSON
// text; pasting external image data goes through insertImageFromFile. Outside
// path focus mode, copies expand to whole edit groups.
export function useClipboard({
  paths, setPaths,
  images, setImages,
  texts, setTexts,
  layers, setLayers,
  currentPath,
  commitHistory,
  selectedPoints, setSelectedPoints,
  selectedImageIds, setSelectedImageIds,
  selectedTextIds, setSelectedTextIds,
  activePathEditId, setActivePathEditId,
  activeLayerId, setActiveLayerId,
  lockedLayerIds,
  setActiveHandle,
  setSelectionBox,
  setPointAction,
  setBgAction,
  setBgInitialState,
  deleteSelectedItems,
  insertImageFromFile,
  closeMobileContextMenu
}) {
  const copiedContentRef = useRef(null);

  const buildClipboardPayload = useCallback((selectionPoints = selectedPoints, selectionImages = selectedImageIds, selectionTexts = selectedTextIds) => {
    const pathIndices = [...new Set(selectionPoints.map(sp => sp.pathIndex))]
      .filter(idx => idx >= 0 && idx < paths.length);
    const clipboardPaths = pathIndices.map(idx => {
      const path = paths[idx];
      return {
        ...path,
        points: path.points.map(clonePoint)
      };
    });
    const imageIdSet = new Set(selectionImages);
    const clipboardImages = images
      .filter(img => imageIdSet.has(img.id))
      .map(img => ({ ...img }));
    const textIdSet = new Set(selectionTexts);
    const clipboardTexts = texts
      .filter(text => textIdSet.has(text.id))
      .map(text => ({ ...text }));

    if (clipboardPaths.length === 0 && clipboardImages.length === 0 && clipboardTexts.length === 0) return null;
    return {
      type: CLIPBOARD_PAYLOAD_TYPE,
      paths: clipboardPaths,
      images: clipboardImages,
      texts: clipboardTexts
    };
  }, [selectedPoints, selectedImageIds, selectedTextIds, paths, images, texts]);

  const writeClipboardPayload = useCallback((payload) => {
    if (!payload) return false;
    copiedContentRef.current = payload;
    return true;
  }, []);

  const removeObjectsByIds = useCallback((pathIds = [], imageIds = [], textIds = []) => {
    const pathIdSet = new Set(pathIds);
    const imageIdSet = new Set(imageIds);
    const textIdSet = new Set(textIds);
    if (pathIdSet.size === 0 && imageIdSet.size === 0 && textIdSet.size === 0) return false;

    commitHistory({ paths, currentPath, images, layers, texts });
    const nextPaths = paths.filter(path => !pathIdSet.has(path.id));
    const nextImages = images.filter(img => !imageIdSet.has(img.id));
    const nextTexts = texts.filter(text => !textIdSet.has(text.id));
    const usedLayerIds = new Set([
      ...nextPaths.map(path => path.layerId),
      ...nextImages.map(img => img.layerId),
      ...nextTexts.map(text => text.layerId)
    ]);

    setPaths(nextPaths);
    setImages(nextImages);
    setTexts(nextTexts);
    setLayers(prevLayers => prevLayers.filter(layer => usedLayerIds.has(layer.id)));
    setSelectedPoints([]);
    setSelectedImageIds([]);
    setSelectedTextIds([]);
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setBgAction(null);
    setBgInitialState(null);

    if (activeLayerId && !usedLayerIds.has(activeLayerId)) {
      const nextLayer = layers.find(layer => usedLayerIds.has(layer.id));
      setActiveLayerId(nextLayer ? nextLayer.id : null);
    }
    return true;
  }, [paths, images, texts, layers, currentPath, commitHistory, activeLayerId]);

  const copyCurrentSelection = useCallback(() => {
    const effectiveSelection = activePathEditId ? selectedPoints : expandPathSelectionToGroups(paths, selectedPoints);
    const payload = buildClipboardPayload(effectiveSelection, selectedImageIds);
    return writeClipboardPayload(payload);
  }, [activePathEditId, selectedPoints, selectedImageIds, paths, buildClipboardPayload, writeClipboardPayload]);

  const cutCurrentSelection = useCallback(() => {
    const effectiveSelection = activePathEditId ? selectedPoints : expandPathSelectionToGroups(paths, selectedPoints);
    const payload = buildClipboardPayload(effectiveSelection, selectedImageIds);
    if (!payload) return false;
    writeClipboardPayload(payload);
    const selectedPointsByPath = new Map();
    effectiveSelection.forEach(point => {
      selectedPointsByPath.set(point.pathIndex, (selectedPointsByPath.get(point.pathIndex) || 0) + 1);
    });

    let hasPartialPointSelection = false;
    const fullySelectedPathIds = [];
    selectedPointsByPath.forEach((count, pathIndex) => {
      const path = paths[pathIndex];
      if (!path) return;
      if (count === path.points.length) {
        fullySelectedPathIds.push(path.id);
      } else {
        hasPartialPointSelection = true;
      }
    });

    if (hasPartialPointSelection) {
      deleteSelectedItems();
      return true;
    }

    removeObjectsByIds(fullySelectedPathIds, selectedImageIds, selectedTextIds);
    return true;
  }, [activePathEditId, selectedPoints, selectedImageIds, selectedTextIds, paths, buildClipboardPayload, writeClipboardPayload, deleteSelectedItems, removeObjectsByIds]);

  const insertClipboardPayload = useCallback((parsedPayload) => {
    if (!parsedPayload || parsedPayload.type !== CLIPBOARD_PAYLOAD_TYPE) return false;
    const sourcePaths = Array.isArray(parsedPayload.paths) ? parsedPayload.paths : [];
    const sourceImages = Array.isArray(parsedPayload.images) ? parsedPayload.images : [];
    const sourceTexts = Array.isArray(parsedPayload.texts)
      ? parsedPayload.texts.map(normalizeTextObject).filter(Boolean)
      : [];
    if (sourcePaths.length === 0 && sourceImages.length === 0 && sourceTexts.length === 0) return false;
    if (activeLayerId && lockedLayerIds.has(activeLayerId)) return false;

    commitHistory({ paths, currentPath, images, layers, texts });

    const newLayers = [];
    const newPaths = [];
    const newImages = [];
    const newTexts = [];
    const groupIdMap = new Map();

    sourcePaths.forEach(path => {
      const layerType = path.itemType || 'vector';
      const count = layers.filter(layer => layer.itemType === layerType).length
        + newLayers.filter(layer => layer.itemType === layerType).length;
      const layer = createLayer(layerType, count);
      newLayers.push(layer);
      const sourceGroupId = resolvePathEditGroupId(path);
      if (!groupIdMap.has(sourceGroupId)) {
        groupIdMap.set(sourceGroupId, generateEditGroupId());
      }
      newPaths.push({
        ...path,
        id: Date.now() + Math.random(),
        layerId: layer.id,
        itemType: layerType,
        points: (path.points || []).map(clonePoint),
        fillEnabled: !!path.fillEnabled,
        fillColor: normalizeStrokeColor(path.fillColor, DEFAULT_FILL_COLOR),
        strokeEnabled: path.strokeEnabled !== false,
        strokeWidth: normalizeStrokeWidth(path.strokeWidth, DEFAULT_STROKE_WIDTH),
        strokeColor: normalizeStrokeColor(path.strokeColor, DEFAULT_STROKE_COLOR),
        strokeAlign: normalizeStrokeAlign(path.strokeAlign, DEFAULT_STROKE_ALIGN),
        editGroupId: groupIdMap.get(sourceGroupId)
      });
    });

    sourceImages.forEach(img => {
      const count = layers.filter(layer => layer.itemType === 'image').length
        + newLayers.filter(layer => layer.itemType === 'image').length;
      const layer = createLayer('image', count);
      newLayers.push(layer);
      newImages.push({
        ...img,
        id: Date.now() + Math.random(),
        layerId: layer.id
      });
    });

    sourceTexts.forEach(text => {
      const count = layers.filter(layer => layer.itemType === 'text').length
        + newLayers.filter(layer => layer.itemType === 'text').length;
      const layer = createLayer('text', count);
      newLayers.push(layer);
      newTexts.push({
        ...text,
        id: crypto.randomUUID(),
        layerId: layer.id
      });
    });

    const nextLayers = [...newLayers, ...layers];
    const nextPaths = [...paths, ...newPaths];
    const nextImages = [...images, ...newImages];
    const nextTexts = [...texts, ...newTexts];
    setLayers(nextLayers);
    setPaths(nextPaths);
    setImages(nextImages);
    setTexts(nextTexts);
    if (newLayers.length > 0) {
      setActiveLayerId(newLayers[0].id);
    }

    const selectedPathPoints = [];
    const basePathIndex = paths.length;
    newPaths.forEach((path, pathOffset) => {
      path.points.forEach((_, pointIndex) => {
        selectedPathPoints.push({ pathIndex: basePathIndex + pathOffset, pointIndex });
      });
    });
    setSelectedPoints(selectedPathPoints);
    setSelectedImageIds(newImages.map(img => img.id));
    setSelectedTextIds(newTexts.map(text => text.id));
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setBgAction(null);
    setBgInitialState(null);
    return true;
  }, [activeLayerId, lockedLayerIds, commitHistory, paths, currentPath, images, texts, layers]);

  const duplicateCurrentSelection = useCallback(() => {
    const effectiveSelection = activePathEditId ? selectedPoints : expandPathSelectionToGroups(paths, selectedPoints);
    const payload = buildClipboardPayload(effectiveSelection, selectedImageIds);
    if (!payload) return false;
    copiedContentRef.current = payload;
    return insertClipboardPayload(payload);
  }, [activePathEditId, selectedPoints, selectedImageIds, paths, buildClipboardPayload, insertClipboardPayload]);

  const pasteFromAvailableClipboard = useCallback(async () => {
    if (copiedContentRef.current && insertClipboardPayload(copiedContentRef.current)) {
      return true;
    }

    if (navigator.clipboard?.read) {
      try {
        const clipboardItems = await navigator.clipboard.read();
        for (const item of clipboardItems) {
          const imageType = item.types.find(type => type.startsWith('image/'));
          if (!imageType) continue;
          const blob = await item.getType(imageType);
          const ext = imageType.split('/')[1] || 'png';
          const file = new File([blob], `pasted-${Date.now()}.${ext}`, { type: imageType });
          if (insertImageFromFile(file)) {
            return true;
          }
        }
      } catch (err) {
        // Permission or platform clipboard limitation; continue to text fallback.
      }
    }

    if (navigator.clipboard?.readText) {
      try {
        const textData = await navigator.clipboard.readText();
        if (textData) {
          const parsed = JSON.parse(textData);
          if (insertClipboardPayload(parsed)) {
            return true;
          }
        }
      } catch (err) {
        // Clipboard text unavailable or not our payload.
      }
    }

    return false;
  }, [insertClipboardPayload, insertImageFromFile]);

  const handleMobileContextPaste = useCallback(async () => {
    const didPaste = await pasteFromAvailableClipboard();
    if (didPaste) {
      closeMobileContextMenu();
    }
  }, [pasteFromAvailableClipboard, closeMobileContextMenu]);

  // Document-level paste: editor payload first (JSON text), then raw images.
  useEffect(() => {
    const handlePaste = (e) => {
      const target = e.target;
      const tagName = target?.tagName?.toUpperCase();
      if (tagName === 'INPUT' || tagName === 'TEXTAREA' || target?.isContentEditable) return;

      // 1. Try to paste editor payload first
      try {
        const textData = e.clipboardData?.getData('text/plain');
        if (textData) {
          const parsed = JSON.parse(textData);
          if (insertClipboardPayload(parsed)) {
            copiedContentRef.current = parsed;
            e.preventDefault();
            return;
          }
        }
      } catch (err) {
        // Not our JSON payload, continue to image paste check.
      }

      // 2. Fallback to image paste
      const items = e.clipboardData?.items;
      if (items) {
        for (let i = 0; i < items.length; i++) {
          if (items[i].type?.indexOf('image') !== -1) {
            const file = items[i].getAsFile();
            if (file && insertImageFromFile(file)) {
              e.preventDefault();
            }
            return;
          }
        }
      }

      const fallbackImage = Array.from(e.clipboardData?.files || []).find(file => file.type?.startsWith('image/'));
      if (fallbackImage && insertImageFromFile(fallbackImage)) {
        e.preventDefault();
      }
    };

    document.addEventListener('paste', handlePaste, true);
    return () => document.removeEventListener('paste', handlePaste, true);
  }, [insertClipboardPayload, insertImageFromFile]);

  return {
    copyCurrentSelection,
    cutCurrentSelection,
    duplicateCurrentSelection,
    pasteFromAvailableClipboard,
    handleMobileContextPaste
  };
}
