import React, { useState, useRef, useEffect, useCallback } from 'react';
import { Square, Circle, Triangle, Star, Minus } from 'lucide-react';

import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN,
  GRID_SIZE,
  MIN_GRID_SIZE,
  MIN_CIRCULAR_STEP,
  MAX_CIRCULAR_STEP,
  DEFAULT_CIRCULAR_STEP
} from './constants';
import { pointsToPath, resolvePathEditGroupId } from './lib/paths';
import {
  computeHitRadii,
  getBgHit as getBgHitAtCoords,
  findTopImageAtCoords as findTopImageAt,
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
import { usePointerInteraction } from './hooks/usePointerInteraction';
import { EditorProvider } from './state/EditorContext';
import DesktopToolbar from './components/Toolbar/DesktopToolbar';
import PanelsContainer from './components/Panels/PanelsContainer';
import QuickLayerReorder from './components/Overlays/QuickLayerReorder';
import MobileControls from './components/Toolbar/MobileControls';
import Canvas from './components/Canvas/Canvas';

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
    setMobileToolsOpen,
    mobileShapePanelOpen, setMobileShapePanelOpen,
    mobileContextMenu, setMobileContextMenu,
    closeMobileContextMenu,
    mobileLongPressRef,
    clearMobileLongPress
  } = uiShell;
  
  // Tool State
  const [mode, setMode] = useState('pan'); 
  const [showNodes, setShowNodes] = useState(true);
  const [pathStyleDefaults, setPathStyleDefaults] = useState({
    fillEnabled: false,
    strokeEnabled: true,
    strokeWidth: DEFAULT_STROKE_WIDTH,
    strokeColor: DEFAULT_STROKE_COLOR,
    strokeAlign: DEFAULT_STROKE_ALIGN
  });
  
  // Shape Tool State
  const [shapeType, setShapeType] = useState('rectangle');
  const [showShapeMenu, setShowShapeMenu] = useState(false);
  const [drawingShape, setDrawingShape] = useState(null);
  const shapeMenuContainerRef = useRef(null);
  
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
    currentPath, setCurrentPath,
    currentPathInfo, setCurrentPathInfo
  } = useObjects();
  const [ghostPoint, setGhostPoint] = useState(null);
  const [isDrawingCurve, setIsDrawingCurve] = useState(false);
  const [snapState, setSnapState] = useState({ endpoint: null, segment: null });

  const {
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
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

  // Click Outside logic for Shape Dropdown
  useEffect(() => {
    const handleClickOutside = (e) => {
      if (showShapeMenu && shapeMenuContainerRef.current && !shapeMenuContainerRef.current.contains(e.target)) {
        setShowShapeMenu(false);
      }
    };
    document.addEventListener('mousedown', handleClickOutside);
    return () => document.removeEventListener('mousedown', handleClickOutside);
  }, [showShapeMenu]);

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
    pointAction,
    paths,
    images,
    layers,
    zoom,
    isPathVisible
  });

  const getBgHit = useCallback((testCoords) => (
    getBgHitAtCoords(testCoords, { images, layers, selectedImageIds, scaleHandleHitRadius, rotateHandleHitRadius })
  ), [images, selectedImageIds, layers, scaleHandleHitRadius, rotateHandleHitRadius]);

  const findTopImageAtCoords = useCallback((testCoords) => (
    findTopImageAt(testCoords, { images, layers })
  ), [images, layers]);

  const objectActions = useObjectActions({
    paths, setPaths,
    currentPath, setCurrentPath,
    currentPathInfo, setCurrentPathInfo,
    images, setImages,
    layers, setLayers,
    commitHistory,
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
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
    if (!isMobile) return;
    const coords = getCanvasCoords(e.clientX, e.clientY);
    const hitImage = findTopImageAtCoords(coords);
    const hitPath = hitImage ? null : findTopPathAtCoords(coords);

    e.preventDefault();
    clearMobileLongPress();
    if (hitImage) {
      setSelectedImageIds([hitImage.id]);
      setSelectedPoints([]);
      setActivePathEditId(null);
    } else if (hitPath) {
      setSelectedPoints(getPathSelection(hitPath.pathIndex));
      setSelectedImageIds([]);
      setActivePathEditId(null);
    }

    setMobileContextMenu({
      type: hitImage || hitPath ? 'actions' : 'paste',
      x: Math.min(Math.max(12, e.clientX), Math.max(12, viewportSize.width - 140)),
      y: Math.min(Math.max(12, e.clientY), Math.max(12, viewportSize.height - 56))
    });

    setActiveHandle(null);
    setSelectionBox(null);
    setBgAction(null);
    setPointAction(null);
    setIsDraggingPoints(false);
  }, [isMobile, getCanvasCoords, findTopImageAtCoords, findTopPathAtCoords, clearMobileLongPress, getPathSelection, viewportSize.width, viewportSize.height]);

  const { handlePointerDown, handlePointerMove, handlePointerUp } = usePointerInteraction({
    activeEditGroupId,
    activeHandle,
    activeLayerId,
    activePathEditId,
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
    mobileContextMenu,
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
    setMobileContextMenu,
    setPan,
    setPaths,
    setPointAction,
    setSelectedImageIds,
    setSelectedPoints,
    setSelectionBox,
    setShowNodes,
    setShowShapeMenu,
    setSnapState,
    setZoom,
    shapeType,
    showNodes,
    showShapeMenu,
    snapState,
    svgRef,
    viewportSize,
    zoom,
    zoomRef
  });


  const changeMode = (newMode) => {
    const targetMode = newMode;

    if ((mode === 'draw' || mode === 'pencil') && targetMode !== mode && currentPath.length > 0) {
      finishPath(false, false);
    }
    setMobileContextMenu(null);
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
      setBgAction(null);
      setPointAction(null);
    }
  };

  const {
    fileInputRef,
    insertImageFromFile,
    insertTextFromPrompt,
    handleImageUpload
  } = useImageImport({
    activeLayerId, setActiveLayerId,
    lockedLayerIds,
    layers, setLayers,
    paths, currentPath,
    images, setImages,
    commitHistory,
    setSelectedImageIds, setSelectedPoints,
    setOpenPanels, setExpandedPanel,
    viewportSize, panRef, zoomRef,
    pathStyleDefaults
  });

  const {
    copyCurrentSelection,
    cutCurrentSelection,
    duplicateCurrentSelection,
    handleMobileContextPaste
  } = useClipboard({
    paths, setPaths,
    images, setImages,
    layers, setLayers,
    currentPath,
    commitHistory,
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
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
  });

  // --- LAYER MANAGEMENT ---
  const layersApi = useLayers({
    layers, setLayers,
    paths, setPaths,
    images, setImages,
    currentPath,
    commitHistory,
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
    activeLayerId, setActiveLayerId,
    setActivePathEditId,
    mode, changeMode,
    isMobile
  });
  const { editingLayerId, selectedLayerIds } = layersApi;


  const {
    exportScope: mobileExportScope, setExportScope: setMobileExportScope,
    exportFormat: mobileExportFormat, setExportFormat: setMobileExportFormat,
    isExporting,
    handleExport
  } = useExport({ layers, paths, images, selectedPoints, selectedImageIds });

  useKeyboardShortcuts({
    mode, setMode,
    changeMode,
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
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
    setShowShapeMenu,
    setActiveHandle,
    setSelectionBox,
    setHoveredHandle,
    setPointAction,
    setShapeType,
    setShowNodes,
    togglePanel,
    setIsPanning
  });

  const pathStyles = usePathStyles({
    paths, setPaths,
    currentPath,
    currentPathInfo,
    images,
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
    bgHoverAction,
    images,
    selectedImageIds
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

  const hasActiveSelection = selectedPoints.length > 0 || selectedImageIds.length > 0;
  const canExportSelection = hasActiveSelection;
  const selectedLayersInStackOrder = layers.filter(layer => selectedLayerIds.has(layer.id));
  const layerIndexById = new Map(layers.map((layer, index) => [layer.id, index]));
  const { pathsByLayerId, imagesByLayerId, pathCountByLayerId, imageCountByLayerId } = groupContentByLayer(paths, images);
  const compositeFillPathD = paths
    .filter(path => path.isClosed && path.fillEnabled && visibleLayerIds.has(path.layerId))
    .map(path => pointsToPath(path.points, path.isClosed))
    .join(' ');
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
  const handleMobileUndo = () => {
    handleUndo();
  };
  const handleMobileRedo = () => {
    handleRedo();
  };
  const handleMobileZoomOut = () => {
    stepZoom(-1);
  };
  const handleMobileZoomIn = () => {
    stepZoom(1);
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
    canExportSelection,
    changeMode,
    compositeFillPathD,
    copyCurrentSelection,
    currentPath,
    currentPathInfo,
    cutCurrentSelection,
    drawHover,
    drawingShape,
    duplicateCurrentSelection,
    dynamicCursor,
    effectiveCircularStep,
    effectiveGridSize,
    fileInputRef,
    getLayerPreviewBounds,
    getShapeToolIcon,
    ghostPoint,
    gridConfig,
    handleCanvasContextMenu,
    handleExport,
    handleMobileContextPaste,
    handleMobileRedo,
    handleMobileUndo,
    handleMobileZoomIn,
    handleMobileZoomOut,
    handlePointerDown,
    handlePointerMove,
    handlePointerUp,
    hasActiveSelection,
    hoveredHandle,
    hoveredStartPoint,
    imageCountByLayerId,
    images,
    imagesByLayerId,
    insertTextFromPrompt,
    isDrawingCurve,
    isExporting,
    isMobile,
    isPathInActiveEditContext,
    layerIndexById,
    layers,
    mobileExportFormat,
    mobileExportScope,
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
    selectionBox,
    setActiveLayerId,
    setGridConfig,
    setHoveredHandle,
    setMobileExportFormat,
    setMobileExportScope,
    setShapeType,
    setShowBackgroundAids,
    setShowNodes,
    setShowShapeMenu,
    shapeMenuContainerRef,
    shapeType,
    showBackgroundAids,
    showNodes,
    showShapeMenu,
    svgRef,
    toggleMobileShapePanel,
    updateActiveImage,
    zoom
  };

  return (
    <EditorProvider value={editor}>
    <div className="w-screen h-screen bg-[#f2f4f7] overflow-hidden select-none font-sans text-slate-800 flex flex-col fixed inset-0 touch-none">
      
      {/* CANVAS */}
      <Canvas />

      {/* --- UI OVERLAYS --- */}

      {/* Hidden File Input for Sketch Upload */}
      <input 
        type="file" 
        accept="image/*" 
        ref={fileInputRef} 
        onChange={handleImageUpload} 
        className="hidden" 
      />

      <QuickLayerReorder />

      {isMobile && <MobileControls />}


      {/* Right-Side Panels Container */}
      <PanelsContainer />

      {/* Bottom Toolbar (Desktop Tools) */}
      {!isMobile && <DesktopToolbar />}

    </div>
    </EditorProvider>
  );
}
