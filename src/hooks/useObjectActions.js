import { useCallback } from 'react';
import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN,
  DEFAULT_FILL_COLOR
} from '../constants';
import { clonePoint, reversePathPoints, resolvePathEditGroupId } from '../lib/paths';
import {
  normalizeStrokeWidth,
  normalizeStrokeColor,
  normalizeStrokeAlign
} from '../lib/stroke';
import { createLayer } from '../lib/layers';
import { correctPathDirectionsTransform } from '../lib/pathDirection';

// Document-level object actions: delete the current selection (auto-pruning
// emptied layers), clear the canvas, fix winding direction, and commit the
// in-progress pen/pencil path as a real path object (finishPath) — optionally
// dropping straight into focused node editing.
export function useObjectActions({
  paths, setPaths,
  currentPath, setCurrentPath,
  currentPathInfo, setCurrentPathInfo,
  images, setImages,
  texts, setTexts,
  frames, setFrames,
  layers, setLayers,
  commitHistory,
  selectedPoints, setSelectedPoints,
  selectedImageIds, setSelectedImageIds,
  selectedTextIds, setSelectedTextIds,
  selectedFrameIds, setSelectedFrameIds,
  activeLayerId, setActiveLayerId,
  setActivePathEditId,
  setActiveHandle,
  setSelectionBox,
  setPointAction,
  setBgAction,
  setBgInitialState,
  setMode,
  setShowNodes,
  pathStyleDefaults,
  setGhostPoint,
  setHoveredStartPoint,
  setIsDrawingCurve,
  setSnapState,
  setDrawHover,
  setHoveredHandle,
  setDrawingShape,
  clearPendingTouchDrawAction,
  isPathVisible,
  isPathLocked
}) {
  const deleteSelectedItems = useCallback(() => {
    if (selectedPoints.length === 0 && selectedImageIds.length === 0 && selectedTextIds.length === 0 && selectedFrameIds.length === 0) return;
    commitHistory({ paths, currentPath, images, layers, texts, frames });

    let layerIdsToCheck = new Set();
    let newPaths = paths.map(p => ({ ...p, points: [...p.points] }));

    // Delete points
    if (selectedPoints.length > 0) {
        const toDelete = {};
        selectedPoints.forEach(sp => {
            if (!toDelete[sp.pathIndex]) toDelete[sp.pathIndex] = [];
            if (!toDelete[sp.pathIndex].includes(sp.pointIndex)) {
                toDelete[sp.pathIndex].push(sp.pointIndex);
            }
        });

        Object.keys(toDelete).forEach(pathIdxStr => {
            const pathIdx = parseInt(pathIdxStr, 10);
            const indices = toDelete[pathIdx].sort((a, b) => b - a);
            indices.forEach(idx => {
                newPaths[pathIdx].points.splice(idx, 1);
            });

            if (newPaths[pathIdx].isClosed && newPaths[pathIdx].points.length < 3) {
                newPaths[pathIdx].isClosed = false;
            }

            if (newPaths[pathIdx].points.length === 0) {
                layerIdsToCheck.add(newPaths[pathIdx].layerId);
            }
        });
    }

    // Delete images
    if (selectedImageIds.length > 0) {
        images.forEach(img => {
            if (selectedImageIds.includes(img.id)) {
                layerIdsToCheck.add(img.layerId);
            }
        });
        setImages(prev => prev.filter(img => !selectedImageIds.includes(img.id)));
    }

    // Delete texts
    if (selectedTextIds.length > 0) {
        texts.forEach(text => {
            if (selectedTextIds.includes(text.id)) {
                layerIdsToCheck.add(text.layerId);
            }
        });
        setTexts(prev => prev.filter(text => !selectedTextIds.includes(text.id)));
    }

    // Delete frames
    if (selectedFrameIds.length > 0) {
        frames.forEach(frame => {
            if (selectedFrameIds.includes(frame.id)) {
                layerIdsToCheck.add(frame.layerId);
            }
        });
        setFrames(prev => prev.filter(frame => !selectedFrameIds.includes(frame.id)));
    }

    const finalPaths = newPaths.filter(p => p.points.length > 0);
    setPaths(finalPaths);

    // Completely empty layers are automatically deleted
    if (layerIdsToCheck.size > 0) {
        setLayers(prevLayers => {
            const remainingLayers = prevLayers.filter(l => {
                if (!layerIdsToCheck.has(l.id)) return true;
                const hasPaths = finalPaths.some(p => p.layerId === l.id);
                const hasImages = images.some(img => img.layerId === l.id && !selectedImageIds.includes(img.id));
                const hasTexts = texts.some(text => text.layerId === l.id && !selectedTextIds.includes(text.id));
                const hasFrames = frames.some(frame => frame.layerId === l.id && !selectedFrameIds.includes(frame.id));
                return hasPaths || hasImages || hasTexts || hasFrames;
            });
            if (activeLayerId && layerIdsToCheck.has(activeLayerId) && !remainingLayers.some(l => l.id === activeLayerId)) {
                setActiveLayerId(remainingLayers.length > 0 ? remainingLayers[0].id : null);
            }
            return remainingLayers;
        });
    }

    setSelectedPoints([]);
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setSelectedImageIds([]);
    setSelectedTextIds([]);
    setSelectedFrameIds([]);
  }, [paths, currentPath, images, texts, frames, layers, selectedPoints, selectedImageIds, selectedTextIds, selectedFrameIds, activeLayerId, commitHistory]);

  const activatePathEditSession = (nextPaths, pathId) => {
    const pathIndex = nextPaths.findIndex(p => p.id === pathId);
    if (pathIndex === -1) return;
    const path = nextPaths[pathIndex];
    setMode('edit');
    setShowNodes(true);
    setActivePathEditId(pathId);
    setSelectedImageIds([]);
    setSelectedTextIds([]);
    setSelectedFrameIds([]);
    setSelectedPoints([]);
    setActiveLayerId(path.layerId);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setBgAction(null);
    setBgInitialState(null);
  };

  const finishPath = (isClosed = false, enterDirectEdit = false) => {
    if (currentPath.length > 0) {
      commitHistory({ paths, currentPath, images, layers, texts, frames });
      let targetLayerId = currentPathInfo?.layerId;
      let layerType = currentPathInfo?.itemType || 'vector';

      if (!targetLayerId) {
          const count = layers.filter(l => l.itemType === layerType).length;
          const newLayer = createLayer(layerType, count);
          setLayers(prev => [newLayer, ...prev]);
          targetLayerId = newLayer.id;
      }
      const pointsToSave = currentPathInfo?.resumeReverseOnSave
        ? reversePathPoints(currentPath)
        : currentPath.map(clonePoint);
      const resumePathId = currentPathInfo?.resumePathId;
      const resumeSourcePath = resumePathId != null
        ? paths.find(path => path.id === resumePathId)
        : null;
      const finalPathId = resumePathId ?? Date.now();
      const finalEditGroupId = currentPathInfo?.editGroupId
        || resolvePathEditGroupId(resumeSourcePath)
        || `path-${finalPathId}`;
      const newPath = {
        id: finalPathId,
        points: pointsToSave,
        isClosed,
        layerId: targetLayerId,
        itemType: layerType,
        fillEnabled: currentPathInfo?.fillEnabled ?? pathStyleDefaults.fillEnabled,
        fillOpacity: currentPathInfo?.fillOpacity ?? pathStyleDefaults.fillOpacity,
        fillColor: normalizeStrokeColor(
          currentPathInfo?.fillColor,
          normalizeStrokeColor(pathStyleDefaults.fillColor, DEFAULT_FILL_COLOR)
        ),
        strokeEnabled: currentPathInfo?.strokeEnabled ?? pathStyleDefaults.strokeEnabled,
        strokeOpacity: currentPathInfo?.strokeOpacity ?? pathStyleDefaults.strokeOpacity,
        strokeWidth: normalizeStrokeWidth(
          currentPathInfo?.strokeWidth,
          normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH)
        ),
        strokeColor: normalizeStrokeColor(
          currentPathInfo?.strokeColor,
          normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR)
        ),
        strokeAlign: normalizeStrokeAlign(
          currentPathInfo?.strokeAlign,
          normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN)
        ),
        editGroupId: finalEditGroupId
      };
      let nextPaths = [...paths, newPath];
      if (resumePathId != null) {
        const existingIndex = paths.findIndex(p => p.id === resumePathId);
        if (existingIndex !== -1) {
          nextPaths = paths.map((p, idx) => (idx === existingIndex ? newPath : p));
        } else if (Number.isInteger(currentPathInfo?.resumePathIndex)) {
          nextPaths = [...paths];
          const insertIndex = Math.max(0, Math.min(currentPathInfo.resumePathIndex, nextPaths.length));
          nextPaths.splice(insertIndex, 0, newPath);
        } else {
          nextPaths = [...paths, newPath];
        }
      }
      setPaths(nextPaths);
      setActiveLayerId(targetLayerId);
      if (enterDirectEdit) {
        activatePathEditSession(nextPaths, newPath.id);
      } else {
        setActivePathEditId(null);
        setSelectedPoints([]);
        setSelectedImageIds([]);
        setSelectedTextIds([]);
        setActiveHandle(null);
        setSelectionBox(null);
        setPointAction(null);
        setBgAction(null);
        setBgInitialState(null);
      }
    }
    setCurrentPath([]);
    setCurrentPathInfo(null);
    setGhostPoint(null);
    setHoveredStartPoint(false);
    setIsDrawingCurve(false);
    setSnapState({ endpoint: null, segment: null });
    clearPendingTouchDrawAction();
  };

  const clearCanvas = () => {
    commitHistory({ paths, currentPath, images, layers, texts, frames });
    setPaths([]);
    setCurrentPath([]);
    setImages([]);
    setTexts([]);
    setFrames([]);
    setLayers([]);
    setGhostPoint(null);
    setActivePathEditId(null);
    setSelectedPoints([]);
    setActiveHandle(null);
    setIsDrawingCurve(false);
    setDrawHover(null);
    setHoveredHandle(null);
    setPointAction(null);
    setDrawingShape(null);
    setCurrentPathInfo(null);
    setSelectedImageIds([]);
    setSelectedTextIds([]);
    setSelectedFrameIds([]);
    clearPendingTouchDrawAction();
  };

  const correctPathDirections = () => {
    commitHistory({ paths, currentPath, images, layers, texts, frames });
    setPaths(prev => correctPathDirectionsTransform(prev, selectedPoints, isPathVisible, isPathLocked));
  };

  return {
    deleteSelectedItems,
    finishPath,
    clearCanvas,
    correctPathDirections
  };
}
