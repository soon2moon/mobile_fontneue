import React, { useState, useRef, useEffect, useCallback } from 'react';
import { 
  PenTool, 
  Pencil,
  MousePointer2, 
  Hand, 
  Menu,
  Eye, 
  EyeOff,
  Trash2, 
  Check,
  CircleDot,
  RefreshCw,
  Layers,
  Plus,
  GripVertical,
  Image as ImageIcon,
  Ruler,
  X,
  Grid,
  Lock,
  Unlock,
  Droplet,
  Square,
  Circle,
  Triangle,
  Star,
  Minus,
  ChevronUp,
  Copy,
  Scissors,
  ClipboardPaste,
  Download,
  Type
} from 'lucide-react';

import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN,
  SNAP_RADIUS,
  GRID_SIZE,
  MIN_GRID_SIZE,
  MAX_GRID_SIZE,
  MIN_CIRCULAR_STEP,
  MAX_CIRCULAR_STEP,
  DEFAULT_CIRCULAR_STEP,
  MIN_ZOOM,
  MAX_ZOOM,
  PIXEL_GRID_MIN_ZOOM,
  SESSION_STORAGE_KEY,
  LEGACY_SESSION_STORAGE_KEY
} from './constants';
import {
  getBezierPoint,
  distToBezier,
  splitBezier,
  reflectPointAcrossPerpBisector,
  applyShiftSnap
} from './lib/geometry';
import {
  computeHitRadii,
  getBgHit as getBgHitAtCoords,
  findTopImageAtCoords as findTopImageAt,
  findTopPathAtCoords as findTopPathAt
} from './lib/hitTest';
import { computeSelectionBBox } from './lib/selectionBounds';
import { computeDynamicCursor } from './lib/cursor';
import { correctPathDirectionsTransform } from './lib/pathDirection';
import { applyGridSnap } from './lib/snap';
import {
  pointsToPath,
  isCorner,
  clonePoint,
  reversePathPoints,
  simplifyPolylinePoints,
  clonePaths,
  cloneState,
  getPathStrokeStyle,
  resolvePathEditGroupId
} from './lib/paths';
import {
  normalizeStrokeWidth,
  normalizeStrokeColor,
  normalizeStrokeAlign
} from './lib/stroke';
import { generateShapePath } from './lib/shapes';
import { createLayer, groupContentByLayer, getLayerPreviewBounds } from './lib/layers';

import LayerIcon from './ui/LayerIcon';
import ConfigInput from './ui/inputs/ConfigInput';
import ScrubbableNumberInput from './ui/inputs/ScrubbableNumberInput';
import ToolButton from './ui/ToolButton';
import MobileToolButton from './ui/MobileToolButton';
import ShapeMenuItem from './ui/ShapeMenuItem';
import { PANELS_CONFIG, CLOSED_PANELS } from './config/panels';
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
  const [strokeWidthInput, setStrokeWidthInput] = useState(String(DEFAULT_STROKE_WIDTH));
  const [strokeColorInput, setStrokeColorInput] = useState(DEFAULT_STROKE_COLOR.replace('#', ''));
  
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

  // --- DELETE HELPER ---
  const deleteSelectedItems = useCallback(() => {
    if (selectedPoints.length === 0 && selectedImageIds.length === 0) return;
    commitHistory({ paths, currentPath, images, layers });
    
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
    
    const finalPaths = newPaths.filter(p => p.points.length > 0);
    setPaths(finalPaths);

    // Completely empty layers are automatically deleted
    if (layerIdsToCheck.size > 0) {
        setLayers(prevLayers => {
            const remainingLayers = prevLayers.filter(l => {
                if (!layerIdsToCheck.has(l.id)) return true;
                const hasPaths = finalPaths.some(p => p.layerId === l.id);
                const hasImages = images.some(img => img.layerId === l.id && !selectedImageIds.includes(img.id));
                return hasPaths || hasImages;
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
  }, [paths, currentPath, images, layers, selectedPoints, selectedImageIds, activeLayerId, commitHistory]);

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

  // --- ACTIONS ---
  const activatePathEditSession = (nextPaths, pathId) => {
    const pathIndex = nextPaths.findIndex(p => p.id === pathId);
    if (pathIndex === -1) return;
    const path = nextPaths[pathIndex];
    setMode('edit');
    setShowNodes(true);
    setActivePathEditId(pathId);
    setSelectedImageIds([]);
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
      commitHistory({ paths, currentPath, images, layers });
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
        strokeEnabled: currentPathInfo?.strokeEnabled ?? pathStyleDefaults.strokeEnabled,
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

  const clearCanvas = () => {
    commitHistory({ paths, currentPath, images, layers });
    setPaths([]);
    setCurrentPath([]);
    setImages([]);
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
    clearPendingTouchDrawAction();
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
  const {
    editingLayerId,
    editingLayerName, setEditingLayerName,
    dragDropTarget,
    draggedLayerId,
    selectedLayerIds,
    toggleLayerVisibility,
    toggleLayerLock,
    deleteLayer,
    startEditingLayer,
    saveLayerName,
    handleLayerNameKeyDown,
    handleLayerDragStart,
    handleLayerDragOver,
    handleLayerDrop,
    handleLayerDragEnd,
    handleLayerSelect,
    moveSelectedLayerQuick
  } = useLayers({
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


  const correctPathDirections = () => {
    commitHistory({ paths, currentPath, images, layers });
    setPaths(prev => correctPathDirectionsTransform(prev, selectedPoints, isPathVisible, isPathLocked));
  };

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

  // --- RENDER HELPERS ---
  const strokeWidth = 1.5 / zoom;
  const defaultStrokeEnabled = pathStyleDefaults.strokeEnabled !== false;
  const defaultStrokeRenderWidth = normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH) / zoom;
  const defaultStrokeRenderColor = normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR);
  const livePathStroke = currentPathInfo
    ? {
        strokeEnabled: currentPathInfo.strokeEnabled !== false,
        strokeWidth: normalizeStrokeWidth(currentPathInfo.strokeWidth, normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH)),
        strokeColor: normalizeStrokeColor(currentPathInfo.strokeColor, normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR))
      }
    : {
        strokeEnabled: defaultStrokeEnabled,
        strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
        strokeColor: defaultStrokeRenderColor
      };
  const livePathStrokeRenderWidth = livePathStroke.strokeWidth / zoom;

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

  const selectedPathIndices = [...new Set(selectedPoints.map(sp => sp.pathIndex))]
    .filter(idx => idx >= 0 && idx < paths.length);
  const selectedPathObjects = selectedPathIndices.map(idx => paths[idx]).filter(Boolean);
  const hasActiveSelection = selectedPoints.length > 0 || selectedImageIds.length > 0;
  const canExportSelection = hasActiveSelection;
  const hasSelectedPaths = selectedPathObjects.length > 0;
  const fillToggleActive = hasSelectedPaths
    ? selectedPathObjects.every(path => !!path.fillEnabled)
    : pathStyleDefaults.fillEnabled;
  const strokeToggleActive = hasSelectedPaths
    ? selectedPathObjects.every(path => path.strokeEnabled !== false)
    : pathStyleDefaults.strokeEnabled;
  const representativePathStroke = hasSelectedPaths
    ? getPathStrokeStyle(selectedPathObjects[0], pathStyleDefaults)
    : null;
  const strokePanelStyle = representativePathStroke || {
    strokeEnabled: pathStyleDefaults.strokeEnabled !== false,
    strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
    strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
    strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN)
  };

  const applyPathStyle = (updates) => {
    const normalizedUpdates = { ...updates };
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'strokeWidth')) {
      normalizedUpdates.strokeWidth = normalizeStrokeWidth(normalizedUpdates.strokeWidth, pathStyleDefaults.strokeWidth);
    }
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'strokeColor')) {
      normalizedUpdates.strokeColor = normalizeStrokeColor(normalizedUpdates.strokeColor, pathStyleDefaults.strokeColor);
    }
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'strokeAlign')) {
      normalizedUpdates.strokeAlign = normalizeStrokeAlign(normalizedUpdates.strokeAlign, pathStyleDefaults.strokeAlign);
    }

    if (hasSelectedPaths) {
      commitHistory({ paths, currentPath, images, layers });
      const selectedSet = new Set(selectedPathIndices);
      setPaths(prev => prev.map((path, idx) => (
        selectedSet.has(idx) ? { ...path, ...normalizedUpdates } : path
      )));
      return;
    }
    setPathStyleDefaults(prev => ({ ...prev, ...normalizedUpdates }));
  };

  useEffect(() => {
    setStrokeWidthInput(String(Number(strokePanelStyle.strokeWidth.toFixed(2))));
    setStrokeColorInput(strokePanelStyle.strokeColor.replace('#', ''));
  }, [strokePanelStyle.strokeWidth, strokePanelStyle.strokeColor]);

  const commitStrokeWidthInput = () => {
    const parsedWidth = normalizeStrokeWidth(strokeWidthInput, strokePanelStyle.strokeWidth);
    setStrokeWidthInput(String(Number(parsedWidth.toFixed(2))));
    applyPathStyle({ strokeWidth: parsedWidth, strokeEnabled: true });
  };

  const handleStrokeWidthInputChange = (value) => {
    const sanitized = value.replace(/[^0-9.]/g, '');
    setStrokeWidthInput(sanitized);
  };

  const commitStrokeColorInput = () => {
    const normalized = normalizeStrokeColor(`#${strokeColorInput}`, strokePanelStyle.strokeColor);
    setStrokeColorInput(normalized.replace('#', ''));
    applyPathStyle({ strokeColor: normalized, strokeEnabled: true });
  };

  const handleStrokeColorInputChange = (value) => {
    const sanitized = value.replace(/[^0-9a-fA-F]/g, '').slice(0, 6).toLowerCase();
    setStrokeColorInput(sanitized);
  };

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
    activeEditGroupId,
    activeImage,
    activeLayerId,
    applyPathStyle,
    canExportSelection,
    changeMode,
    clearCanvas,
    commitStrokeColorInput,
    commitStrokeWidthInput,
    compositeFillPathD,
    copyCurrentSelection,
    correctPathDirections,
    currentPath,
    currentPathInfo,
    cutCurrentSelection,
    defaultStrokeEnabled,
    defaultStrokeRenderColor,
    defaultStrokeRenderWidth,
    deleteLayer,
    deleteSelectedItems,
    dragDropTarget,
    draggedLayerId,
    drawHover,
    drawingShape,
    duplicateCurrentSelection,
    dynamicCursor,
    editingLayerId,
    editingLayerName,
    effectiveCircularStep,
    effectiveGridSize,
    fileInputRef,
    fillToggleActive,
    getLayerPreviewBounds,
    getShapeToolIcon,
    ghostPoint,
    gridConfig,
    handleCanvasContextMenu,
    handleExport,
    handleLayerDragEnd,
    handleLayerDragOver,
    handleLayerDragStart,
    handleLayerDrop,
    handleLayerNameKeyDown,
    handleLayerSelect,
    handleMobileContextPaste,
    handleMobileRedo,
    handleMobileUndo,
    handleMobileZoomIn,
    handleMobileZoomOut,
    handlePointerDown,
    handlePointerMove,
    handlePointerUp,
    handleStrokeColorInputChange,
    handleStrokeWidthInputChange,
    hasActiveSelection,
    hasSelectedPaths,
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
    livePathStroke,
    livePathStrokeRenderWidth,
    mobileExportFormat,
    mobileExportScope,
    mode,
    moveSelectedLayerQuick,
    pan,
    pathCountByLayerId,
    pathStyleDefaults,
    paths,
    pathsByLayerId,
    pointAction,
    resetZoomToHundred,
    saveLayerName,
    selBBox,
    selectMobileShape,
    selectedImageIds,
    selectedLayerIds,
    selectedLayersInStackOrder,
    selectedPoints,
    selectionBox,
    setActiveLayerId,
    setEditingLayerName,
    setGridConfig,
    setHoveredHandle,
    setMobileExportFormat,
    setMobileExportScope,
    setShapeType,
    setShowBackgroundAids,
    setShowNodes,
    setShowShapeMenu,
    setStrokeColorInput,
    shapeMenuContainerRef,
    shapeType,
    showBackgroundAids,
    showNodes,
    showShapeMenu,
    startEditingLayer,
    strokeColorInput,
    strokePanelStyle,
    strokeToggleActive,
    strokeWidth,
    strokeWidthInput,
    svgRef,
    toggleLayerLock,
    toggleLayerVisibility,
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
