import { useState, useCallback } from 'react';
import { cloneState } from '../lib/paths';

// Undo/redo over the document state (paths/currentPath/images/layers/texts/frames).
// Undo while actively drawing instead retracts in-progress pen/pencil input,
// and both undo and redo clear transient interaction UI via injected setters.
export function useHistory({
  mode,
  paths, setPaths,
  currentPath, setCurrentPath,
  images, setImages,
  texts, setTexts,
  frames, setFrames,
  layers, setLayers,
  setIsDrawingCurve,
  setDrawHover,
  setHoveredStartPoint,
  setGhostPoint,
  setSelectedPoints,
  setActivePathEditId,
  setActiveHandle,
  setSelectionBox,
  setPointAction,
  setDrawingShape
}) {
  const [pastPaths, setPastPaths] = useState([]);
  const [futurePaths, setFuturePaths] = useState([]);

  const commitHistory = useCallback((stateToSave) => {
    setPastPaths(prev => [...prev, cloneState(stateToSave.paths, stateToSave.currentPath, stateToSave.images, stateToSave.layers, stateToSave.texts, stateToSave.frames)]);
    setFuturePaths([]);
  }, []);

  const handleUndo = useCallback(() => {
    if (mode === 'draw' && currentPath.length > 0) {
      setCurrentPath(prev => prev.slice(0, -1));
      if (currentPath.length <= 1) {
          setIsDrawingCurve(false);
          setDrawHover(null);
          setHoveredStartPoint(false);
          setGhostPoint(null);
      }
      return;
    }
    if (mode === 'pencil' && currentPath.length > 0) {
      setCurrentPath([]);
      return;
    }

    if (pastPaths.length === 0) return;

    const previous = pastPaths[pastPaths.length - 1];
    const newPast = pastPaths.slice(0, -1);

    setFuturePaths(prev => [cloneState(paths, currentPath, images, layers, texts, frames), ...prev]);
    setPaths(previous.paths);
    setCurrentPath(previous.currentPath);
    setImages(previous.images || []);
    setLayers(previous.layers || []);
    setTexts(previous.texts || []);
    setFrames(previous.frames || []);
    setPastPaths(newPast);

    setIsDrawingCurve(false);
    setDrawHover(null);
    setHoveredStartPoint(false);
    setGhostPoint(null);

    setSelectedPoints([]);
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setDrawingShape(null);
  }, [pastPaths, futurePaths, paths, currentPath, images, layers, texts, frames, mode]);

  const handleRedo = useCallback(() => {
    if ((mode === 'draw' || mode === 'pencil') && currentPath.length > 0) return;
    if (futurePaths.length === 0) return;

    const next = futurePaths[0];
    const newFuture = futurePaths.slice(1);

    setPastPaths(prev => [...prev, cloneState(paths, currentPath, images, layers, texts, frames)]);
    setPaths(next.paths);
    setCurrentPath(next.currentPath);
    setImages(next.images || []);
    setLayers(next.layers || []);
    setTexts(next.texts || []);
    setFrames(next.frames || []);
    setFuturePaths(newFuture);

    setIsDrawingCurve(false);
    setDrawHover(null);
    setHoveredStartPoint(false);
    setGhostPoint(null);

    setSelectedPoints([]);
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setDrawingShape(null);
  }, [pastPaths, futurePaths, paths, currentPath, images, layers, texts, frames, mode]);

  return { pastPaths, futurePaths, commitHistory, handleUndo, handleRedo };
}
