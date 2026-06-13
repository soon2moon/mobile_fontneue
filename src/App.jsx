import React, { useState, useRef, useEffect, useCallback } from 'react';
import { Square, Circle, Triangle, Star, Minus } from 'lucide-react';

import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_ALIGN,
  NEW_SHAPE_FILL_COLOR,
  NEW_SHAPE_STROKE_COLOR,
  GRID_SIZE,
  MIN_GRID_SIZE,
  MIN_CIRCULAR_STEP,
  MAX_CIRCULAR_STEP,
  DEFAULT_CIRCULAR_STEP
} from './constants';
import { resolvePathEditGroupId } from './lib/paths';
import { buildCompositeFillGroups } from './lib/compositeFill';
import {
  computeHitRadii,
  getBgHit as getBgHitAtCoords,
  findTopImageAtCoords as findTopImageAt,
  findTopTextAtCoords as findTopTextAt,
  findTopPathAtCoords as findTopPathAt
} from './lib/hitTest';
import { computeSelectionBBox } from './lib/selectionBounds';
import { computeDynamicCursor } from './lib/cursor';
import { groupContentByLayer, getLayerPreviewBounds } from './lib/layers';

import { useViewportSize } from './hooks/useViewportSize';
import { useViewport } from './hooks/useViewport';
import { useHistory } from './hooks/useHistory';
import { useObjects } from './hooks/useObjects';
import { useSelection } from './hooks/useSelection';
import { useSessionPersistence } from './hooks/useSessionPersistence';
import { useLayers } from './hooks/useLayers';
import { useExport } from './hooks/useExport';
import { useImageImport } from './hooks/useImageImport';
import { useClipboard } from './hooks/useClipboard';
import { useKeyboardShortcuts } from './hooks/useKeyboardShortcuts';
import { usePendingTouchDraw } from './hooks/usePendingTouchDraw';
import { useUIShell } from './hooks/useUIShell';
import { useObjectActions } from './hooks/useObjectActions';
import { usePathStyles } from './hooks/usePathStyles';
import { useInspectorModel } from './hooks/useInspectorModel';
import { useTextEditing } from './hooks/useTextEditing';
import { usePointerInteraction } from './hooks/usePointerInteraction';
import { EditorProvider } from './state/EditorContext';
import DesktopToolbar from './components/Toolbar/DesktopToolbar';
import PanelsContainer from './components/Panels/PanelsContainer';
import QuickLayerReorder from './components/Overlays/QuickLayerReorder';
import CanvasContextMenu from './components/Overlays/CanvasContextMenu';
import MobileControls from './components/Toolbar/MobileControls';
import Canvas from './components/Canvas/Canvas';
import TextEditorOverlay from './components/Canvas/TextEditorOverlay';

// --- MAIN APP COMPONENT ---
export default function App() {
  // Canvas State
  const svgRef = useRef(null);
  const { viewportSize, isMobile, mobileBottomInset } = useViewportSize();
  const {
    pan, setPan,
    zoom, setZoom,
    isPanning, setIsPanning,
    panRef, zoomRef,
    getCanvasCoords,
    zoomAtScreenPoint,
    stepZoom
  } = useViewport(svgRef);
  const uiShell = useUIShell({ isMobile, viewportSize, mobileBottomInset });
  const {
    setOpenPanels, setExpandedPanel,
    togglePanel,
    closeAllPanels,
    uiHidden, toggleUiHidden,
    setMobileToolsOpen,
    mobileShapePanelOpen, setMobileShapePanelOpen,
    canvasContextMenu, setCanvasContextMenu,
    closeCanvasContextMenu,
    mobileLongPressRef,
    clearMobileLongPress
  } = uiShell;
  
  // Tool State
  const [mode, setMode] = useState('pan'); 
  const [showNodes, setShowNodes] = useState(true);
  const [pathStyleDefaults, setPathStyleDefaults] = useState({
    fillEnabled: true,
    fillColor: NEW_SHAPE_FILL_COLOR,
    strokeEnabled: true,
    strokeWidth: DEFAULT_STROKE_WIDTH,
    strokeColor: NEW_SHAPE_STROKE_COLOR,
    strokeAlign: DEFAULT_STROKE_ALIGN
  });
  // Quiet UI: true while a non-pan pointer gesture is working the canvas.
  const [isCanvasWorking, setIsCanvasWorking] = useState(false);
  // Stable forwarder so hooks created before changeMode's declaration can
  // switch modes (same pattern as commitTextEditingRef).
  const changeModeRef = useRef(null);
  const changeModeStable = useCallback((nextMode) => changeModeRef.current?.(nextMode), []);
  
  // Shape Tool State
  const [shapeType, setShapeType] = useState('rectangle');
  const [showShapeMenu, setShowShapeMenu] = useState(false);
  const [drawingShape, setDrawingShape] = useState(null);

  // Frame Tool State
  const [drawingFrame, setDrawingFrame] = useState(null);
  
  // Grid State
  const [gridConfig, setGridConfig] = useState({
    type: 'none',
    edges: 4,
    snapToGrid: false,
    size: GRID_SIZE,
    circularStep: DEFAULT_CIRCULAR_STEP
  });

  const [showBackgroundAids, setShowBackgroundAids] = useState(true);

  // Layers & Objects State
  const [layers, setLayers] = useState([]);
  const [activeLayerId, setActiveLayerId] = useState(null);

  // Drawing & Editing State
  const {
    paths, setPaths,
    images, setImages,
    texts, setTexts,
    frames, setFrames,
    currentPath, setCurrentPath,
    currentPathInfo, setCurrentPathInfo
  } = useObjects();
  const [ghostPoint, setGhostPoint] = useState(null);
  const [isDrawingCurve, setIsDrawingCurve] = useState(false);
  const [snapState, setSnapState] = useState({ endpoint: null, segment: null });

  const {
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
    selectedTextIds, setSelectedTextIds,
    selectedFrameIds, setSelectedFrameIds,
    activePathEditId, setActivePathEditId
  } = useSelection();
  const [activeHandle, setActiveHandle] = useState(null);
  const [selectionBox, setSelectionBox] = useState(null);
  const [isDraggingPoints, setIsDraggingPoints] = useState(false);
  const [hoveredStartPoint, setHoveredStartPoint] = useState(false);
  const [drawHover, setDrawHover] = useState(null);
  const [hoveredHandle, setHoveredHandle] = useState(null); // { pathIndex, pointIndex, type: 'hIn' | 'hOut' }

  // Transform States
  const [pointAction, setPointAction] = useState(null);
  const [bgAction, setBgAction] = useState(null);
  const [bgInitialState, setBgInitialState] = useState(null);
  const [bgHoverAction, setBgHoverAction] = useState(null);

  // History State (Undo/Redo)
  const { pastPaths, futurePaths, commitHistory, handleUndo, handleRedo } = useHistory({
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
  });

  const { sessionLoaded } = useSessionPersistence({
    layers, setLayers,
    paths, setPaths,
    images, setImages,
    texts, setTexts,
    frames, setFrames,
    currentPath, setCurrentPath,
    currentPathInfo, setCurrentPathInfo,
    pathStyleDefaults, setPathStyleDefaults,
    gridConfig, setGridConfig,
    showBackgroundAids, setShowBackgroundAids,
    activeLayerId, setActiveLayerId
  });
  const lastFocusedPathEditIdRef = useRef(null);

  const visibleLayerIds = new Set(layers.filter(l => l.visible).map(l => l.id));
  const lockedLayerIds = new Set(layers.filter(l => l.locked).map(l => l.id));
  const isPathVisible = (path) => visibleLayerIds.has(path.layerId);
  const isPathLocked = (path) => lockedLayerIds.has(path.layerId);
  const resolveEditContextLayerId = useCallback(() => {
    if (!activePathEditId) return null;
    const contextPath = paths.find(candidate => candidate.id === activePathEditId);
    if (!contextPath) return null;
    const layer = layers.find(candidate => candidate.id === contextPath.layerId);
    if (!layer || !layer.visible || layer.locked) return null;
    return layer.id;
  }, [activePathEditId, paths, layers]);
  const {
    pendingTouchDrawActionRef,
    clearPendingTouchDrawAction,
    beginPendingTouchDrawAction,
    rollbackPendingTouchDrawAction
  } = usePendingTouchDraw({
    setPaths,
    setLayers,
    setActiveLayerId,
    setCurrentPath,
    setCurrentPathInfo,
    setIsDrawingCurve,
    setGhostPoint,
    setDrawHover,
    setHoveredStartPoint,
    setSnapState
  });

  // Hit radii are shared by the pointer handlers (hit testing) and the
  // canvas render (handle/anchor visuals), so they live here.
  const {
    scaleHandleHitRadius,
    rotateHandleHitRadius,
    handleHitRadius,
    pointHitRadius,
    segmentHitRadius,
    snapHitRadius,
    closePathHitRadius,
    pencilSamplingDistance,
    touchDragThresholdPx
  } = computeHitRadii(isMobile, zoom);

  // Exit path-focus edit if the path disappears, is hidden, or becomes locked.
  useEffect(() => {
    if (activePathEditId) {
      lastFocusedPathEditIdRef.current = activePathEditId;
    }
  }, [activePathEditId]);

  useEffect(() => {
    if (showNodes || !activePathEditId) return;
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
  }, [showNodes, activePathEditId]);

  useEffect(() => {
    if (!activePathEditId) return;
    const activePath = paths.find(p => p.id === activePathEditId);
    if (!activePath) {
      setActivePathEditId(null);
      lastFocusedPathEditIdRef.current = null;
      return;
    }
    const layer = layers.find(l => l.id === activePath.layerId);
    if (!layer || !layer.visible || layer.locked) {
      setActivePathEditId(null);
      lastFocusedPathEditIdRef.current = null;
    }
  }, [activePathEditId, paths, layers]);

  useEffect(() => {
    if (activePathEditId) return;
    setActiveHandle(null);
    setHoveredHandle(null);
  }, [activePathEditId]);

  const activeEditPath = activePathEditId
    ? paths.find(path => path.id === activePathEditId) || null
    : null;
  const activeEditGroupId = activeEditPath
    ? resolvePathEditGroupId(activeEditPath)
    : null;
  const isPathInActiveEditContext = useCallback((path) => {
    if (!path || activeEditGroupId == null) return false;
    return resolvePathEditGroupId(path) === activeEditGroupId;
  }, [activeEditGroupId]);

  const selBBox = computeSelectionBBox({
    mode,
    activePathEditId,
    selectedPoints,
    selectedImageIds,
    selectedTextIds,
    pointAction,
    paths,
    images,
    texts,
    layers,
    zoom,
    isPathVisible
  });

  const getBgHit = useCallback((testCoords) => (
    getBgHitAtCoords(testCoords, { images, texts, layers, selectedImageIds, selectedTextIds, scaleHandleHitRadius, rotateHandleHitRadius })
  ), [images, texts, selectedImageIds, selectedTextIds, layers, scaleHandleHitRadius, rotateHandleHitRadius]);

  const findTopImageAtCoords = useCallback((testCoords) => (
    findTopImageAt(testCoords, { images, layers })
  ), [images, layers]);

  const findTopTextAtCoords = useCallback((testCoords) => (
    findTopTextAt(testCoords, { texts, layers })
  ), [texts, layers]);

  const {
    editingText,
    editingTextId,
    beginNewTextAt,
    beginEditingText,
    updateDraft,
    commitTextEditing,
    commitTextEditingRef
  } = useTextEditing({
    paths, currentPath,
    images,
    texts, setTexts,
    frames,
    layers, setLayers,
    commitHistory,
    activeLayerId, setActiveLayerId,
    setMode,
    setSelectedTextIds,
    setSelectedPoints,
    setSelectedImageIds,
    setActivePathEditId
  });

  const objectActions = useObjectActions({
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
  });
  const { deleteSelectedItems, finishPath } = objectActions;

  const getPathSelection = useCallback((pathIndex) => {
    const path = paths[pathIndex];
    if (!path) return [];
    return path.points.map((_, pointIndex) => ({ pathIndex, pointIndex }));
  }, [paths]);

  const findTopPathAtCoords = useCallback((testCoords) => (
    findTopPathAt(testCoords, { paths, isPathVisible, isPathLocked, pointHitRadius, segmentHitRadius })
  ), [paths, isPathVisible, isPathLocked, pointHitRadius, segmentHitRadius]);

  // --- EVENT HANDLERS ---

  const handleCanvasContextMenu = useCallback((e) => {
    const coords = getCanvasCoords(e.clientX, e.clientY);
    const hitText = findTopTextAtCoords(coords);
    const hitImage = hitText ? null : findTopImageAtCoords(coords);
    const hitPath = hitText || hitImage ? null : findTopPathAtCoords(coords);

    e.preventDefault();
    clearMobileLongPress();
    if (hitText) {
      setSelectedTextIds([hitText.id]);
      setSelectedImageIds([]);
      setSelectedPoints([]);
      setActivePathEditId(null);
    } else if (hitImage) {
      setSelectedImageIds([hitImage.id]);
      setSelectedTextIds([]);
      setSelectedPoints([]);
      setActivePathEditId(null);
    } else if (hitPath) {
      setSelectedPoints(getPathSelection(hitPath.pathIndex));
      setSelectedImageIds([]);
      setSelectedTextIds([]);
      setActivePathEditId(null);
    }

    setCanvasContextMenu({
      type: hitText || hitImage || hitPath ? 'actions' : 'paste',
      x: e.clientX,
      y: e.clientY,
      worldX: coords.x,
      worldY: coords.y,
      targetLayerId: hitText?.layerId
        ?? hitImage?.layerId
        ?? (hitPath ? paths[hitPath.pathIndex]?.layerId ?? null : null)
    });

    setActiveHandle(null);
    setSelectionBox(null);
    setBgAction(null);
    setPointAction(null);
    setIsDraggingPoints(false);
  }, [getCanvasCoords, findTopTextAtCoords, findTopImageAtCoords, findTopPathAtCoords, clearMobileLongPress, getPathSelection, paths]);

  const { handlePointerDown, handlePointerMove, handlePointerUp } = usePointerInteraction({
    activeEditGroupId,
    activeHandle,
    activeLayerId,
    activePathEditId,
    frames,
    setFrames,
    selectedFrameIds,
    drawingFrame,
    setDrawingFrame,
    setSelectedFrameIds,
    changeMode: changeModeStable,
    beginEditingText,
    beginNewTextAt,
    beginPendingTouchDrawAction,
    bgAction,
    bgInitialState,
    clearMobileLongPress,
    clearPendingTouchDrawAction,
    closePathHitRadius,
    handleHitRadius,
    pencilSamplingDistance,
    pointHitRadius,
    rotateHandleHitRadius,
    scaleHandleHitRadius,
    segmentHitRadius,
    snapHitRadius,
    touchDragThresholdPx,
    commitHistory,
    currentPath,
    currentPathInfo,
    drawHover,
    drawingShape,
    findTopImageAtCoords,
    findTopPathAtCoords,
    findTopTextAtCoords,
    finishPath,
    getBgHit,
    getCanvasCoords,
    getPathSelection,
    ghostPoint,
    gridConfig,
    hoveredStartPoint,
    images,
    isDraggingPoints,
    isDrawingCurve,
    isMobile,
    isPanning,
    isPathInActiveEditContext,
    isPathLocked,
    isPathVisible,
    lastFocusedPathEditIdRef,
    layers,
    lockedLayerIds,
    canvasContextMenu,
    mobileLongPressRef,
    mode,
    panRef,
    pathStyleDefaults,
    paths,
    pendingTouchDrawActionRef,
    pointAction,
    resolveEditContextLayerId,
    rollbackPendingTouchDrawAction,
    selBBox,
    selectedImageIds,
    selectedPoints,
    selectedTextIds,
    selectionBox,
    setActiveHandle,
    setActiveLayerId,
    setActivePathEditId,
    setBgAction,
    setBgHoverAction,
    setBgInitialState,
    setCurrentPath,
    setCurrentPathInfo,
    setDrawHover,
    setDrawingShape,
    setGhostPoint,
    setHoveredHandle,
    setHoveredStartPoint,
    setImages,
    setIsDraggingPoints,
    setIsDrawingCurve,
    setIsPanning,
    setLayers,
    setCanvasContextMenu,
    setPan,
    setPaths,
    setPointAction,
    setSelectedImageIds,
    setSelectedPoints,
    setSelectedTextIds,
    setSelectionBox,
    setIsCanvasWorking,
    setShowNodes,
    setSnapState,
    setTexts,
    setZoom,
    shapeType,
    showNodes,
    snapState,
    svgRef,
    texts,
    viewportSize,
    zoom,
    zoomRef
  });


  const changeMode = (newMode) => {
    const targetMode = newMode;

    commitTextEditingRef.current?.();
    if ((mode === 'draw' || mode === 'pencil') && targetMode !== mode && currentPath.length > 0) {
      finishPath(false, false);
    }
    setCanvasContextMenu(null);
    clearMobileLongPress();
    clearPendingTouchDrawAction();
    setMode(targetMode);
    setDrawHover(null);
    setHoveredHandle(null);
    
    // Always close the shape menu when transitioning modes
    setShowShapeMenu(false);
    if (isMobile) {
      setMobileToolsOpen(false);
      if (targetMode !== 'shape') {
        setMobileShapePanelOpen(false);
      }
    }

    if (targetMode !== 'shape') {
      setDrawingShape(null);
    }

    if (targetMode === 'edit' && ['draw', 'pencil', 'shape'].includes(mode)) {
      setActivePathEditId(null);
    }

    if (targetMode !== 'edit') {
      if (!['draw', 'shape', 'pencil'].includes(targetMode)) {
        setActivePathEditId(null);
      }
      setSelectedPoints([]);
      setActiveHandle(null);
      setSelectionBox(null);
      setSelectedImageIds([]);
      setSelectedFrameIds([]);
      setSelectedTextIds([]);
      setBgAction(null);
      setPointAction(null);
    }
  };
  changeModeRef.current = changeMode;

  const {
    fileInputRef,
    insertImageFromFile,
    handleImageUpload
  } = useImageImport({
    activeLayerId, setActiveLayerId,
    lockedLayerIds,
    layers, setLayers,
    paths, currentPath,
    images, setImages,
    texts,
    frames,
    commitHistory,
    setSelectedImageIds, setSelectedPoints,
    setOpenPanels, setExpandedPanel,
    viewportSize, panRef, zoomRef
  });

  const {
    copyCurrentSelection,
    cutCurrentSelection,
    duplicateCurrentSelection,
    handleContextPaste
  } = useClipboard({
    paths, setPaths,
    images, setImages,
    texts, setTexts,
    frames,
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
    closeCanvasContextMenu
  });

  // --- LAYER MANAGEMENT ---
  const layersApi = useLayers({
    layers, setLayers,
    paths, setPaths,
    images, setImages,
    texts, setTexts,
    frames, setFrames,
    currentPath,
    commitHistory,
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
    selectedTextIds, setSelectedTextIds,
    selectedFrameIds, setSelectedFrameIds,
    activeLayerId, setActiveLayerId,
    setActivePathEditId,
    mode, changeMode,
    isMobile
  });
  const { editingLayerId, selectedLayerIds } = layersApi;


  const {
    exportScope, setExportScope,
    exportFormat, setExportFormat,
    isExporting,
    handleExport
  } = useExport({ layers, paths, images, texts, selectedPoints, selectedImageIds, selectedTextIds });

  useKeyboardShortcuts({
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
  });

  const pathStyles = usePathStyles({
    paths, setPaths,
    currentPath,
    currentPathInfo,
    images,
    texts,
    frames,
    layers,
    selectedPoints,
    commitHistory,
    pathStyleDefaults, setPathStyleDefaults,
    zoom
  });

  const dynamicCursor = computeDynamicCursor({
    mode,
    isPanning,
    pointAction,
    bgAction,
    bgInitialState,
    bgHoverAction
  });
  
  // --- DYNAMIC PATTERN GENERATION ---
  const effectiveGridSize = Math.max(MIN_GRID_SIZE, Number(gridConfig.size) || GRID_SIZE);
  const effectiveCircularStep = Math.max(
    MIN_CIRCULAR_STEP,
    Math.min(MAX_CIRCULAR_STEP, Number(gridConfig.circularStep) || DEFAULT_CIRCULAR_STEP)
  );

  // --- UI STATE ---
  const activeImage = images.find(img => selectedImageIds.includes(img.id));
  const updateActiveImage = (updates) => {
    if (!activeImage) return;
    setImages(prev => prev.map(img => img.id === activeImage.id ? { ...img, ...updates } : img));
  };
  const activeText = texts.find(text => selectedTextIds.includes(text.id));
  const updateActiveText = (updates) => {
    if (!activeText) return;
    setTexts(prev => prev.map(text => text.id === activeText.id ? { ...text, ...updates } : text));
  };
  const activeFrame = frames.find(frame => selectedFrameIds.includes(frame.id));
  const updateActiveFrame = (updates) => {
    if (!activeFrame) return;
    setFrames(prev => prev.map(frame => frame.id === activeFrame.id ? { ...frame, ...updates } : frame));
  };

  const inspector = useInspectorModel({
    selectedPathObjects: pathStyles.selectedPathObjects,
    selectedImageIds,
    selectedTextIds,
    pathStyleDefaults,
    applyPathStyle: pathStyles.applyPathStyle,
    activeImage,
    updateActiveImage,
    activeText,
    updateActiveText
  });

  const hasActiveSelection = selectedPoints.length > 0 || selectedImageIds.length > 0 || selectedTextIds.length > 0 || selectedFrameIds.length > 0;
  const canExportSelection = hasActiveSelection;
  const selectedLayersInStackOrder = layers.filter(layer => selectedLayerIds.has(layer.id));
  const layerIndexById = new Map(layers.map((layer, index) => [layer.id, index]));
  const { pathsByLayerId, imagesByLayerId, textsByLayerId, framesByLayerId, pathCountByLayerId, imageCountByLayerId, textCountByLayerId, frameCountByLayerId } = groupContentByLayer(paths, images, texts, frames);
  const compositeFillGroups = buildCompositeFillGroups({
    paths,
    layers,
    isPathVisible: path => visibleLayerIds.has(path.layerId)
  });
  const toggleMobileShapePanel = () => {
    const shouldOpen = mode !== 'shape' || !mobileShapePanelOpen;
    closeAllPanels();
    changeMode('shape');
    if (shouldOpen) {
      setMobileShapePanelOpen(true);
    }
  };
  const selectMobileShape = (nextShape) => {
    setShapeType(nextShape);
    changeMode('shape');
    setMobileShapePanelOpen(false);
  };
  const getShapeToolIcon = (size = 16) => {
    if (shapeType === 'ellipse') return <Circle size={size} />;
    if (shapeType === 'polygon') return <Triangle size={size} />;
    if (shapeType === 'star') return <Star size={size} />;
    if (shapeType === 'line') return <Minus size={size} />;
    return <Square size={size} />;
  };
  const resetZoomToHundred = () => {
    const currentZoom = zoomRef.current;
    if (Math.abs(currentZoom - 1) < 0.0001) return;
    zoomAtScreenPoint(1 / currentZoom, viewportSize.width / 2, viewportSize.height / 2);
  };

  const editor = {
    ...uiShell,
    ...layersApi,
    ...pathStyles,
    ...objectActions,
    activeEditGroupId,
    activeImage,
    activeLayerId,
    activeFrame,
    activeText,
    beginEditingText,
    canExportSelection,
    changeMode,
    commitTextEditing,
    compositeFillGroups,
    copyCurrentSelection,
    currentPath,
    currentPathInfo,
    cutCurrentSelection,
    drawHover,
    editingText,
    editingTextId,
    drawingFrame,
    drawingShape,
    duplicateCurrentSelection,
    dynamicCursor,
    effectiveCircularStep,
    exportFormat,
    exportScope,
    effectiveGridSize,
    fileInputRef,
    getLayerPreviewBounds,
    getShapeToolIcon,
    ghostPoint,
    gridConfig,
    handleCanvasContextMenu,
    handleExport,
    handleContextPaste,
    handlePointerDown,
    handlePointerMove,
    handlePointerUp,
    handleRedo,
    handleUndo,
    hasActiveSelection,
    hoveredHandle,
    hoveredStartPoint,
    imageCountByLayerId,
    images,
    imagesByLayerId,
    inspector,
    isCanvasWorking,
    isDrawingCurve,
    isExporting,
    isMobile,
    isPathInActiveEditContext,
    layerIndexById,
    layers,
    mobileBottomInset,
    mode,
    pan,
    pathCountByLayerId,
    pathStyleDefaults,
    paths,
    pathsByLayerId,
    pointAction,
    resetZoomToHundred,
    selBBox,
    selectMobileShape,
    selectedImageIds,
    selectedLayersInStackOrder,
    selectedPoints,
    selectedFrameIds,
    selectedTextIds,
    selectionBox,
    setActiveLayerId,
    setSelectedFrameIds,
    setGridConfig,
    setExportFormat,
    setExportScope,
    setHoveredHandle,
    setPan,
    setShapeType,
    setShowBackgroundAids,
    setShowNodes,
    setShowShapeMenu,
    shapeType,
    showBackgroundAids,
    showNodes,
    showShapeMenu,
    stepZoom,
    svgRef,
    textCountByLayerId,
    texts,
    textsByLayerId,
    frameCountByLayerId,
    frames,
    framesByLayerId,
    toggleMobileShapePanel,
    updateActiveFrame,
    updateActiveImage,
    updateActiveText,
    updateDraft,
    viewportSize,
    zoom
  };

  return (
    <EditorProvider value={editor}>
    <div className="w-screen h-screen bg-canvas overflow-hidden select-none font-sans text-ink flex flex-col fixed inset-0 touch-none">
      
      {/* CANVAS */}
      <Canvas />

      {/* In-place text editing session (textarea + commit backdrop) */}
      <TextEditorOverlay />

      {/* --- UI OVERLAYS --- */}

      {/* Hidden File Input for Sketch Upload */}
      <input 
        type="file" 
        accept="image/*" 
        ref={fileInputRef} 
        onChange={handleImageUpload} 
        className="hidden" 
      />

      {/* Shared right-click / long-press canvas menu (desktop + mobile) */}
      <CanvasContextMenu />

      {!uiHidden && <QuickLayerReorder />}

      {isMobile && !uiHidden && <MobileControls />}


      {/* Right-Side Panels Container */}
      {!uiHidden && <PanelsContainer />}

      {/* Bottom Toolbar (Desktop Tools) */}
      {!isMobile && !uiHidden && <DesktopToolbar />}

      {/* Quiet-UI escape hatch on touch (no Ctrl+\ there) */}
      {isMobile && uiHidden && (
        <button
          type="button"
          onClick={toggleUiHidden}
          className="absolute bottom-6 left-1/2 -translate-x-1/2 z-40 h-9 px-4 rounded-full bg-raised/90 border border-edge text-secondary text-xs font-semibold shadow-menu"
        >
          Show UI
        </button>
      )}

    </div>
    </EditorProvider>
  );
}
