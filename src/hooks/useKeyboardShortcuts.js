import { useRef, useEffect } from 'react';

// Global hotkeys, Figma-aligned: tools (P pen, Shift+P pencil, V move, F frame,
// H hand, R/O/L shapes, T text, N nodes, U place image), copy/cut,
// undo/redo, Escape (finish/cancel/deselect), Delete, and hold-Space
// temporary panning (restores the previous mode on release/blur).
//
// The dependency list deliberately tracks the *data* the handlers read; the
// per-render callbacks (changeMode, finishPath, setters) are
// re-captured whenever that data changes, matching the original behavior.
export function useKeyboardShortcuts({
  mode, setMode,
  changeMode,
  fileInputRef,
  selectedPoints, setSelectedPoints,
  selectedImageIds, setSelectedImageIds,
  selectedTextIds, setSelectedTextIds,
  selectedFrameIds, setSelectedFrameIds,
  currentPath, setCurrentPath,
  pastPaths, futurePaths,
  paths, images, layers,
  handleUndo, handleRedo,
  commitHistory,
  deleteSelectedItems,
  copyCurrentSelection,
  cutCurrentSelection,
  editingLayerId,
  activePathEditId, setActivePathEditId,
  lastFocusedPathEditIdRef,
  finishPath,
  setGhostPoint,
  setHoveredStartPoint,
  setIsDrawingCurve,
  setDrawHover,
  setCurrentPathInfo,
  setDrawingShape,
  setDrawingFrame,
  toggleUiHidden,
  setActiveHandle,
  setSelectionBox,
  setHoveredHandle,
  setPointAction,
  setShapeType,
  setShowNodes,
  setIsPanning
}) {
  const spacePanRef = useRef({ active: false, prevMode: null });

  useEffect(() => {
    const handleKeyDown = (e) => {
      if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;

      // Show/Hide UI (Figma's Ctrl+\)
      if ((e.ctrlKey || e.metaKey) && e.key === '\\') {
        e.preventDefault();
        toggleUiHidden();
        return;
      }

      // Copy
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'c' && mode === 'edit') {
        if (selectedPoints.length > 0 || selectedImageIds.length > 0 || selectedTextIds.length > 0) {
          e.preventDefault();
          copyCurrentSelection();
        }
        return;
      }

      // Cut
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'x' && mode === 'edit') {
        if (selectedPoints.length > 0 || selectedImageIds.length > 0 || selectedTextIds.length > 0) {
          e.preventDefault();
          cutCurrentSelection();
        }
        return;
      }

      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
        e.preventDefault();
        if (e.shiftKey) {
          handleRedo();
        } else {
          handleUndo();
        }
        return;
      }

      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'y') {
        e.preventDefault();
        handleRedo();
        return;
      }

      if (e.key.toLowerCase() === 'p' && !e.ctrlKey && !e.metaKey) {
        changeMode(e.shiftKey ? 'pencil' : 'draw');
        return;
      }
      if (e.key.toLowerCase() === 'v' && !e.ctrlKey && !e.metaKey) {
        changeMode('edit');
        return;
      }
      if (e.key.toLowerCase() === 'f' && !e.ctrlKey && !e.metaKey) {
        changeMode('frame');
        return;
      }
      if (e.key.toLowerCase() === 'h' && !e.ctrlKey && !e.metaKey) {
        changeMode('pan');
        return;
      }
      if (e.key.toLowerCase() === 'r' && !e.ctrlKey && !e.metaKey) {
        changeMode('shape');
        setShapeType('rectangle');
        return;
      }
      if (e.key.toLowerCase() === 'o' && !e.ctrlKey && !e.metaKey) {
        changeMode('shape');
        setShapeType('ellipse');
        return;
      }
      if (e.key.toLowerCase() === 't' && !e.ctrlKey && !e.metaKey) {
        changeMode('text');
        return;
      }
      if (e.code === 'Space') {
        e.preventDefault();
        if (!spacePanRef.current.active) {
          spacePanRef.current = { active: true, prevMode: mode === 'pan' ? null : mode };
          if (mode !== 'pan') {
            setMode('pan');
          }
        }
        return;
      }
      if (e.key.toLowerCase() === 'n' && !e.ctrlKey && !e.metaKey) {
        if (mode === 'pencil') {
          changeMode('edit');
          setShowNodes(true);
        } else {
          setShowNodes(prev => !prev);
        }
        return;
      }
      if (e.key.toLowerCase() === 'l' && !e.ctrlKey && !e.metaKey) {
        changeMode('shape');
        setShapeType('line');
        return;
      }
      if (e.key.toLowerCase() === 'u' && !e.ctrlKey && !e.metaKey) {
        fileInputRef.current?.click();
        return;
      }
      if (e.key === 'Escape') {
        if (mode === 'draw' || mode === 'pencil') {
          if (currentPath.length > 0) {
            finishPath(false);
          } else {
            setCurrentPath([]);
            setGhostPoint(null);
            setHoveredStartPoint(false);
            setIsDrawingCurve(false);
            setDrawHover(null);
            setCurrentPathInfo(null);
          }
        } else if (mode === 'shape') {
          setDrawingShape(null);
        } else if (mode === 'frame') {
          setDrawingFrame(null);
          changeMode('edit');
        } else if (mode === 'text') {
          changeMode('edit');
        } else if (mode === 'edit') {
          if (activePathEditId) {
            setActivePathEditId(null);
            lastFocusedPathEditIdRef.current = null;
            setActiveHandle(null);
            setSelectionBox(null);
            setHoveredHandle(null);
            return;
          }
          setSelectedPoints([]);
          setActiveHandle(null);
          setSelectionBox(null);
          setSelectedImageIds([]);
          setSelectedTextIds([]);
          setSelectedFrameIds([]);
          setPointAction(null);
        }
        return;
      }

      if ((e.key === 'Backspace' || e.key === 'Delete')) {
        if (editingLayerId) return;
        if (selectedPoints.length > 0 || selectedImageIds.length > 0 || selectedTextIds.length > 0 || selectedFrameIds.length > 0) {
          e.preventDefault();
          deleteSelectedItems();
        }
      }
    };

    const handleKeyUp = (e) => {
      if (e.code !== 'Space') return;
      if (!spacePanRef.current.active) return;
      e.preventDefault();

      const { prevMode } = spacePanRef.current;
      spacePanRef.current = { active: false, prevMode: null };
      setIsPanning(false);

      if (prevMode && mode === 'pan') {
        setMode(prevMode);
      }
    };

    const handleWindowBlur = () => {
      if (!spacePanRef.current.active) return;
      const { prevMode } = spacePanRef.current;
      spacePanRef.current = { active: false, prevMode: null };
      setIsPanning(false);

      if (prevMode && mode === 'pan') {
        setMode(prevMode);
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    window.addEventListener('keyup', handleKeyUp);
    window.addEventListener('blur', handleWindowBlur);
    return () => {
      window.removeEventListener('keydown', handleKeyDown);
      window.removeEventListener('keyup', handleKeyUp);
      window.removeEventListener('blur', handleWindowBlur);
    };
  }, [mode, selectedPoints, selectedImageIds, selectedTextIds, selectedFrameIds, currentPath, pastPaths, futurePaths, paths, images, layers, handleUndo, handleRedo, commitHistory, deleteSelectedItems, copyCurrentSelection, cutCurrentSelection, editingLayerId, activePathEditId]);
}
