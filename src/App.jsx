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
  LEGACY_SESSION_STORAGE_KEY,
  CLIPBOARD_PAYLOAD_TYPE
} from './constants';
import {
  getBezierPoint,
  distToBezier,
  splitBezier,
  reflectPointAcrossPerpBisector,
  applyShiftSnap
} from './lib/geometry';
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
import { generateEditGroupId } from './lib/svg';
import { generateShapePath } from './lib/shapes';
import { createLayer } from './lib/layers';

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
    stepZoom,
    handleWheel
  } = useViewport(svgRef);
  const [mobileToolsOpen, setMobileToolsOpen] = useState(false);
  const [mobilePanelsOpen, setMobilePanelsOpen] = useState(false);
  const [mobileShapePanelOpen, setMobileShapePanelOpen] = useState(false);
  const [mobileToolbarWidth, setMobileToolbarWidth] = useState(0);
  const [mobileContextMenu, setMobileContextMenu] = useState(null);
  const [strokeWidthInput, setStrokeWidthInput] = useState(String(DEFAULT_STROKE_WIDTH));
  const [strokeColorInput, setStrokeColorInput] = useState(DEFAULT_STROKE_COLOR.replace('#', ''));
  const mobileToolbarShellRef = useRef(null);
  const mobileLongPressRef = useRef({ timerId: null, pointerId: null, startX: 0, startY: 0, targetType: null, targetId: null, triggered: false });
  
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
  
  // Panels State (Accordion)
  const [openPanels, setOpenPanels] = useState(CLOSED_PANELS);
  const [expandedPanel, setExpandedPanel] = useState(null);

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
  const spacePanRef = useRef({ active: false, prevMode: null });
  const pendingTouchDrawActionRef = useRef({
    active: false,
    pointerId: null,
    prevPath: [],
    prevInfo: null,
    prevPaths: null,
    prevLayers: null,
    prevActiveLayerId: null,
    prevGhostPoint: null,
    prevDrawHover: null,
    prevHoveredStartPoint: false,
    prevIsDrawingCurve: false,
    prevSnapState: { endpoint: null, segment: null }
  });
  const copiedContentRef = useRef(null);

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
  const clearMobileLongPress = useCallback(() => {
    const longPressState = mobileLongPressRef.current;
    if (longPressState.timerId) {
      clearTimeout(longPressState.timerId);
    }
    mobileLongPressRef.current = {
      timerId: null,
      pointerId: null,
      startX: 0,
      startY: 0,
      targetType: null,
      targetId: null,
      triggered: false
    };
  }, []);

  const clearPendingTouchDrawAction = useCallback(() => {
    pendingTouchDrawActionRef.current = {
      active: false,
      pointerId: null,
      prevPath: [],
      prevInfo: null,
      prevPaths: null,
      prevLayers: null,
      prevActiveLayerId: null,
      prevGhostPoint: null,
      prevDrawHover: null,
      prevHoveredStartPoint: false,
      prevIsDrawingCurve: false,
      prevSnapState: { endpoint: null, segment: null }
    };
  }, []);

  const beginPendingTouchDrawAction = useCallback((pointerId, snapshot = {}) => {
    pendingTouchDrawActionRef.current = {
      active: true,
      pointerId,
      prevPath: (snapshot.path || []).map(clonePoint),
      prevInfo: snapshot.info
        ? {
            ...snapshot.info,
            mergedPathIds: Array.isArray(snapshot.info.mergedPathIds) ? [...snapshot.info.mergedPathIds] : snapshot.info.mergedPathIds
          }
        : null,
      prevPaths: snapshot.paths || null,
      prevLayers: snapshot.layers || null,
      prevActiveLayerId: snapshot.activeLayerId ?? null,
      prevGhostPoint: snapshot.ghostPoint ? { ...snapshot.ghostPoint } : null,
      prevDrawHover: snapshot.drawHover ? { ...snapshot.drawHover } : null,
      prevHoveredStartPoint: !!snapshot.hoveredStartPoint,
      prevIsDrawingCurve: snapshot.isDrawingCurve || false,
      prevSnapState: snapshot.snapState
        ? {
            endpoint: snapshot.snapState.endpoint ? { ...snapshot.snapState.endpoint } : null,
            segment: snapshot.snapState.segment ? { ...snapshot.snapState.segment } : null
          }
        : { endpoint: null, segment: null }
    };
  }, []);

  const rollbackPendingTouchDrawAction = useCallback(() => {
    const pending = pendingTouchDrawActionRef.current;
    if (!pending.active) return false;
    if (pending.prevPaths) {
      setPaths(pending.prevPaths);
    }
    if (pending.prevLayers) {
      setLayers(pending.prevLayers);
    }
    setActiveLayerId(pending.prevActiveLayerId ?? null);
    setCurrentPath((pending.prevPath || []).map(clonePoint));
    setCurrentPathInfo(
      pending.prevInfo
        ? {
            ...pending.prevInfo,
            mergedPathIds: Array.isArray(pending.prevInfo.mergedPathIds)
              ? [...pending.prevInfo.mergedPathIds]
              : pending.prevInfo.mergedPathIds
          }
        : null
    );
    setIsDrawingCurve(pending.prevIsDrawingCurve || false);
    setGhostPoint(pending.prevGhostPoint ? { ...pending.prevGhostPoint } : null);
    setDrawHover(pending.prevDrawHover ? { ...pending.prevDrawHover } : null);
    setHoveredStartPoint(!!pending.prevHoveredStartPoint);
    setSnapState(
      pending.prevSnapState
        ? {
            endpoint: pending.prevSnapState.endpoint ? { ...pending.prevSnapState.endpoint } : null,
            segment: pending.prevSnapState.segment ? { ...pending.prevSnapState.segment } : null
          }
        : { endpoint: null, segment: null }
    );
    clearPendingTouchDrawAction();
    return true;
  }, [clearPendingTouchDrawAction]);

  useEffect(() => {
    if (!isMobile) {
      setMobileToolbarWidth(0);
      return;
    }
    const toolbarShell = mobileToolbarShellRef.current;
    if (!toolbarShell) return;

    const syncMobileToolbarWidth = () => {
      const measured = Math.round(toolbarShell.getBoundingClientRect().width);
      if (measured > 0) {
        setMobileToolbarWidth(prev => (prev === measured ? prev : measured));
      }
    };

    syncMobileToolbarWidth();
    let observer = null;
    if (typeof ResizeObserver !== 'undefined') {
      observer = new ResizeObserver(syncMobileToolbarWidth);
      observer.observe(toolbarShell);
    }

    window.addEventListener('resize', syncMobileToolbarWidth);
    window.visualViewport?.addEventListener('resize', syncMobileToolbarWidth);
    return () => {
      observer?.disconnect();
      window.removeEventListener('resize', syncMobileToolbarWidth);
      window.visualViewport?.removeEventListener('resize', syncMobileToolbarWidth);
    };
  }, [isMobile]);

  useEffect(() => {
    if (!isMobile) {
      setMobileToolsOpen(false);
      setMobilePanelsOpen(false);
      setMobileShapePanelOpen(false);
    }
  }, [isMobile]);

  useEffect(() => {
    if (!isMobile) {
      setMobileContextMenu(null);
      clearMobileLongPress();
    }
  }, [isMobile, clearMobileLongPress]);

  useEffect(() => () => {
    clearMobileLongPress();
  }, [clearMobileLongPress]);

  const shortestDeltaDeg = (current, previous) => {
    let delta = current - previous;
    if (delta > 180) delta -= 360;
    if (delta < -180) delta += 360;
    return delta;
  };

  const normalizeAngleDeg = (angle) => {
    let normalized = ((angle + 180) % 360 + 360) % 360 - 180;
    if (Object.is(normalized, -0)) normalized = 0;
    return normalized;
  };

  // Hit radii are shared by the pointer handlers (hit testing) and the
  // canvas render (handle/anchor visuals), so they live here.
  const touchHitScale = isMobile ? 1.65 : 1;
  const scaleHandleHitRadius = (8 * touchHitScale) / zoom;
  const rotateHandleHitRadius = (24 * touchHitScale) / zoom;
  const handleHitRadius = (8 * touchHitScale) / zoom;
  const pointHitRadius = (10 * touchHitScale) / zoom;
  const segmentHitRadius = (10 * touchHitScale) / zoom;
  const snapHitRadius = (SNAP_RADIUS * touchHitScale) / zoom;
  const closePathHitRadius = (SNAP_RADIUS * (isMobile ? 2.4 : 1.2)) / zoom;
  const pencilSamplingDistance = (isMobile ? 12 : 8) / zoom;
  const touchDragThresholdPx = isMobile ? 10 : 0;

  const togglePanel = (panelId) => {
    if (isMobile) {
      const isSameOpen = openPanels[panelId] && expandedPanel === panelId;
      setMobileToolsOpen(false);
      setMobileShapePanelOpen(false);
      if (isSameOpen) {
        setOpenPanels({ ...CLOSED_PANELS });
        setExpandedPanel(null);
        setMobilePanelsOpen(false);
      } else {
        setOpenPanels({ ...CLOSED_PANELS, [panelId]: true });
        setExpandedPanel(panelId);
        setMobilePanelsOpen(true);
      }
      return;
    }
    setOpenPanels(prev => {
      const isCurrentlyOpen = prev[panelId];
      if (isCurrentlyOpen) {
        if (expandedPanel === panelId) {
          setExpandedPanel(null);
          return { ...prev, [panelId]: false };
        } else {
          setExpandedPanel(panelId);
          return prev;
        }
      } else {
        setExpandedPanel(panelId);
        return { ...prev, [panelId]: true };
      }
    });
  };

  useEffect(() => {
    if (!Object.values(openPanels).some(Boolean)) {
      setMobilePanelsOpen(false);
    }
  }, [openPanels]);

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

  // --- COMPUTE SELECTION BOUNDS ---
  let selBBox = null;
  const hasMixedSelection = selectedPoints.length > 0 && selectedImageIds.length > 0;
  if (mode === 'edit' && !activePathEditId && (selectedPoints.length > 1 || hasMixedSelection)) {
    // Keep bounding box totally fixed if we are actively scaling or rotating points/images
    if (pointAction && pointAction.bbox) {
      selBBox = pointAction.bbox;
    } else {
      let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

      selectedPoints.forEach(sp => {
        const path = paths[sp.pathIndex];
        if (!path || !isPathVisible(path)) return;
        const pt = path.points[sp.pointIndex];
        if (pt) {
          minX = Math.min(minX, pt.x); minY = Math.min(minY, pt.y);
          maxX = Math.max(maxX, pt.x); maxY = Math.max(maxY, pt.y);
          if (pt.hIn) {
            minX = Math.min(minX, pt.hIn.x); minY = Math.min(minY, pt.hIn.y);
            maxX = Math.max(maxX, pt.hIn.x); maxY = Math.max(maxY, pt.hIn.y);
          }
          if (pt.hOut) {
            minX = Math.min(minX, pt.hOut.x); minY = Math.min(minY, pt.hOut.y);
            maxX = Math.max(maxX, pt.hOut.x); maxY = Math.max(maxY, pt.hOut.y);
          }
        }
      });

      if (hasMixedSelection) {
        selectedImageIds.forEach(imgId => {
          const img = images.find(i => i.id === imgId);
          if (!img) return;
          const layer = layers.find(l => l.id === img.layerId);
          if (!layer || !layer.visible) return;

          const halfW = (img.width * img.scale) / 2;
          const halfH = (img.height * img.scale) / 2;
          const rad = img.rotation * Math.PI / 180;
          const cos = Math.cos(rad);
          const sin = Math.sin(rad);

          const corners = [
            { x: -halfW, y: -halfH },
            { x: halfW, y: -halfH },
            { x: halfW, y: halfH },
            { x: -halfW, y: halfH }
          ];

          corners.forEach(corner => {
            const worldX = img.x + (corner.x * cos - corner.y * sin);
            const worldY = img.y + (corner.x * sin + corner.y * cos);
            minX = Math.min(minX, worldX); minY = Math.min(minY, worldY);
            maxX = Math.max(maxX, worldX); maxY = Math.max(maxY, worldY);
          });
        });
      }

      if (minX !== Infinity) {
        const pad = 10 / zoom;
        selBBox = { minX: minX - pad, minY: minY - pad, maxX: maxX + pad, maxY: maxY + pad };
      }
    }
  }

  // --- BG HIT TEST ---
  const getBgHit = useCallback((testCoords) => {
    for (let i = images.length - 1; i >= 0; i--) {
      const img = images[i];
      const layer = layers.find(l => l.id === img.layerId);
      if (!layer || !layer.visible || layer.locked) continue;
      if (img.locked) continue;

      const dx = testCoords.x - img.x;
      const dy = testCoords.y - img.y;
      const angleRad = -img.rotation * Math.PI / 180;
      
      const lx = dx * Math.cos(angleRad) - dy * Math.sin(angleRad);
      const ly = dx * Math.sin(angleRad) + dy * Math.cos(angleRad);

      const sw2 = (img.width * img.scale) / 2;
      const sh2 = (img.height * img.scale) / 2;

      if (selectedImageIds.length === 1 && selectedImageIds[0] === img.id) {
        const corners = [
          { id: 'nw', x: -sw2, y: -sh2, angle: 225 },
          { id: 'ne', x: sw2, y: -sh2, angle: 315 },
          { id: 'se', x: sw2, y: sh2, angle: 45 },
          { id: 'sw', x: -sw2, y: sh2, angle: 135 }
        ];
        for (const c of corners) {
          const dist = Math.hypot(lx - c.x, ly - c.y);
          if (dist <= scaleHandleHitRadius) return { action: `scale-${c.id}`, cursorAngle: c.angle, imageId: img.id };
          if (dist <= rotateHandleHitRadius) return { action: `rotate-${c.id}`, cursorAngle: null, imageId: img.id };
        }
      }

      if (Math.abs(lx) <= sw2 && Math.abs(ly) <= sh2) {
        return { action: 'move', cursorAngle: null, imageId: img.id };
      }
    }
    return null;
  }, [images, selectedImageIds, layers, scaleHandleHitRadius, rotateHandleHitRadius]);

  const findTopImageAtCoords = useCallback((testCoords) => {
    for (let i = images.length - 1; i >= 0; i--) {
      const img = images[i];
      const layer = layers.find(l => l.id === img.layerId);
      if (!layer || !layer.visible || layer.locked || img.locked) continue;

      const dx = testCoords.x - img.x;
      const dy = testCoords.y - img.y;
      const angleRad = -img.rotation * Math.PI / 180;
      const lx = dx * Math.cos(angleRad) - dy * Math.sin(angleRad);
      const ly = dx * Math.sin(angleRad) + dy * Math.cos(angleRad);

      const sw2 = (img.width * img.scale) / 2;
      const sh2 = (img.height * img.scale) / 2;
      if (Math.abs(lx) <= sw2 && Math.abs(ly) <= sh2) {
        return img;
      }
    }
    return null;
  }, [images, layers]);

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

  const closeMobileContextMenu = useCallback(() => {
    setMobileContextMenu(null);
  }, []);

  const getPathSelection = useCallback((pathIndex) => {
    const path = paths[pathIndex];
    if (!path) return [];
    return path.points.map((_, pointIndex) => ({ pathIndex, pointIndex }));
  }, [paths]);

  const findTopPathAtCoords = useCallback((testCoords) => {
    let bestPath = null;
    let bestIndex = -1;
    let bestDist = Infinity;

    const isPointInsidePath = (path) => {
      if (!path.isClosed || path.points.length < 3) return false;
      const poly = [];
      for (let j = 0; j < path.points.length; j++) {
        const p0 = path.points[j];
        const p3 = path.points[(j + 1) % path.points.length];
        const p1 = p0.hOut || p0;
        const p2 = p3.hIn || p3;
        for (let step = 0; step < 16; step++) {
          poly.push(getBezierPoint(p0, p1, p2, p3, step / 16));
        }
      }
      let inside = false;
      for (let k = 0, l = poly.length - 1; k < poly.length; l = k++) {
        const xk = poly[k].x;
        const yk = poly[k].y;
        const xl = poly[l].x;
        const yl = poly[l].y;
        const intersects = ((yk > testCoords.y) !== (yl > testCoords.y))
          && (testCoords.x < (xl - xk) * (testCoords.y - yk) / (yl - yk) + xk);
        if (intersects) inside = !inside;
      }
      return inside;
    };

    for (let i = paths.length - 1; i >= 0; i--) {
      const path = paths[i];
      if (!isPathVisible(path) || isPathLocked(path)) continue;

      if (path.points.length === 1) {
        const dist = Math.hypot(path.points[0].x - testCoords.x, path.points[0].y - testCoords.y);
        if (dist < pointHitRadius && dist < bestDist) {
          bestDist = dist;
          bestPath = path;
          bestIndex = i;
        }
        continue;
      }

      let localBest = Infinity;
      const segCount = path.isClosed ? path.points.length : path.points.length - 1;
      for (let j = 1; j <= segCount; j++) {
        const currIndex = path.isClosed ? (j % path.points.length) : j;
        const prevIndex = currIndex === 0 ? path.points.length - 1 : currIndex - 1;
        const prevP = path.points[prevIndex];
        const currP = path.points[currIndex];
        const hit = distToBezier(testCoords, prevP, prevP.hOut || prevP, currP.hIn || currP, currP);
        localBest = Math.min(localBest, hit.dist);
      }

      const filledHit = path.fillEnabled && isPointInsidePath(path);
      if (filledHit || localBest < segmentHitRadius) {
        if (localBest < bestDist || bestPath == null) {
          bestPath = path;
          bestIndex = i;
          bestDist = localBest;
        }
      }
    }

    if (!bestPath) return null;
    return { path: bestPath, pathIndex: bestIndex };
  }, [paths, isPathVisible, isPathLocked, pointHitRadius, segmentHitRadius]);

  const expandPathSelectionToGroups = useCallback((selectionPointsInput = []) => {
    if (!Array.isArray(selectionPointsInput) || selectionPointsInput.length === 0) return [];
    const selectedPathIndexSet = new Set(
      selectionPointsInput
        .map(sp => sp.pathIndex)
        .filter(idx => Number.isInteger(idx) && idx >= 0 && idx < paths.length)
    );
    if (selectedPathIndexSet.size === 0) return [];

    const selectedGroupIds = new Set();
    selectedPathIndexSet.forEach((pathIndex) => {
      const path = paths[pathIndex];
      if (!path) return;
      const groupId = resolvePathEditGroupId(path);
      if (groupId != null) {
        selectedGroupIds.add(groupId);
      }
    });
    if (selectedGroupIds.size === 0) {
      return [...selectionPointsInput];
    }

    const expandedSelection = [];
    paths.forEach((path, pathIndex) => {
      const groupId = resolvePathEditGroupId(path);
      if (!selectedGroupIds.has(groupId)) return;
      path.points.forEach((_, pointIndex) => {
        expandedSelection.push({ pathIndex, pointIndex });
      });
    });

    return expandedSelection;
  }, [paths]);

  const buildClipboardPayload = useCallback((selectionPoints = selectedPoints, selectionImages = selectedImageIds) => {
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

    if (clipboardPaths.length === 0 && clipboardImages.length === 0) return null;
    return {
      type: CLIPBOARD_PAYLOAD_TYPE,
      paths: clipboardPaths,
      images: clipboardImages
    };
  }, [selectedPoints, selectedImageIds, paths, images]);

  const writeClipboardPayload = useCallback((payload) => {
    if (!payload) return false;
    copiedContentRef.current = payload;
    return true;
  }, []);

  const removeObjectsByIds = useCallback((pathIds = [], imageIds = []) => {
    const pathIdSet = new Set(pathIds);
    const imageIdSet = new Set(imageIds);
    if (pathIdSet.size === 0 && imageIdSet.size === 0) return false;

    commitHistory({ paths, currentPath, images, layers });
    const nextPaths = paths.filter(path => !pathIdSet.has(path.id));
    const nextImages = images.filter(img => !imageIdSet.has(img.id));
    const usedLayerIds = new Set([
      ...nextPaths.map(path => path.layerId),
      ...nextImages.map(img => img.layerId)
    ]);

    setPaths(nextPaths);
    setImages(nextImages);
    setLayers(prevLayers => prevLayers.filter(layer => usedLayerIds.has(layer.id)));
    setSelectedPoints([]);
    setSelectedImageIds([]);
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
  }, [paths, images, layers, currentPath, commitHistory, activeLayerId]);

  const copyCurrentSelection = useCallback(() => {
    const effectiveSelection = activePathEditId ? selectedPoints : expandPathSelectionToGroups(selectedPoints);
    const payload = buildClipboardPayload(effectiveSelection, selectedImageIds);
    return writeClipboardPayload(payload);
  }, [activePathEditId, selectedPoints, selectedImageIds, expandPathSelectionToGroups, buildClipboardPayload, writeClipboardPayload]);

  const cutCurrentSelection = useCallback(() => {
    const effectiveSelection = activePathEditId ? selectedPoints : expandPathSelectionToGroups(selectedPoints);
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

    removeObjectsByIds(fullySelectedPathIds, selectedImageIds);
    return true;
  }, [activePathEditId, selectedPoints, selectedImageIds, expandPathSelectionToGroups, buildClipboardPayload, writeClipboardPayload, paths, deleteSelectedItems, removeObjectsByIds]);

  const insertClipboardPayload = useCallback((parsedPayload) => {
    if (!parsedPayload || parsedPayload.type !== CLIPBOARD_PAYLOAD_TYPE) return false;
    const sourcePaths = Array.isArray(parsedPayload.paths) ? parsedPayload.paths : [];
    const sourceImages = Array.isArray(parsedPayload.images) ? parsedPayload.images : [];
    if (sourcePaths.length === 0 && sourceImages.length === 0) return false;
    if (activeLayerId && lockedLayerIds.has(activeLayerId)) return false;

    commitHistory({ paths, currentPath, images, layers });

    const newLayers = [];
    const newPaths = [];
    const newImages = [];
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

    const nextLayers = [...newLayers, ...layers];
    const nextPaths = [...paths, ...newPaths];
    const nextImages = [...images, ...newImages];
    setLayers(nextLayers);
    setPaths(nextPaths);
    setImages(nextImages);
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
    setActivePathEditId(null);
    setActiveHandle(null);
    setSelectionBox(null);
    setPointAction(null);
    setBgAction(null);
    setBgInitialState(null);
    return true;
  }, [activeLayerId, lockedLayerIds, commitHistory, paths, currentPath, images, layers]);

  const duplicateCurrentSelection = useCallback(() => {
    const effectiveSelection = activePathEditId ? selectedPoints : expandPathSelectionToGroups(selectedPoints);
    const payload = buildClipboardPayload(effectiveSelection, selectedImageIds);
    if (!payload) return false;
    copiedContentRef.current = payload;
    return insertClipboardPayload(payload);
  }, [activePathEditId, selectedPoints, selectedImageIds, expandPathSelectionToGroups, buildClipboardPayload, insertClipboardPayload]);

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
    normalizeAngleDeg,
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
    shortestDeltaDeg,
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

  // --- PASTE HANDLER ---
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
    setPaths(prev => {
      const newPaths = prev.map(p => ({ ...p, points: [...p.points] }));
      
      const selectedPathIndices = new Set(selectedPoints.map(sp => sp.pathIndex));
      const processAll = selectedPathIndices.size === 0;

      if (!processAll) {
        selectedPathIndices.forEach(idx => {
          const path = newPaths[idx];
          if (path) {
            const revPts = [...path.points].reverse();
            path.points = revPts.map(p => ({
              ...p,
              hIn: p.hOut ? { ...p.hOut } : undefined,
              hOut: p.hIn ? { ...p.hIn } : undefined
            }));
          }
        });
        return newPaths;
      }

      const allClosedPaths = newPaths.map((p, i) => ({
        path: p,
        index: i,
        isClosed: p.isClosed
      })).filter(item => item.isClosed && isPathVisible(item.path) && !isPathLocked(item.path));

      const pathData = allClosedPaths.map(item => {
        const poly = [];
        const pts = item.path.points;
        for (let i = 0; i < pts.length; i++) {
          const p0 = pts[i];
          const p3 = pts[(i + 1) % pts.length];
          const p1 = p0.hOut || p0;
          const p2 = p3.hIn || p3;
          for (let step = 0; step < 20; step++) {
            poly.push(getBezierPoint(p0, p1, p2, p3, step / 20));
          }
        }
        
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        let area = 0;
        for (let i = 0; i < poly.length; i++) {
          const p = poly[i];
          minX = Math.min(minX, p.x); minY = Math.min(minY, p.y);
          maxX = Math.max(maxX, p.x); maxY = Math.max(maxY, p.y);
          
          const j = (i + 1) % poly.length;
          area += (poly[i].x * poly[j].y) - (poly[j].x * poly[i].y);
        }
        area = area / 2;

        return { ...item, poly, bbox: { minX, minY, maxX, maxY }, area };
      });

      pathData.forEach((pd, i) => {
        let depth = 0;
        pathData.forEach((otherPd, j) => {
          if (i === j) return;
          const intersectsBBox = !(pd.bbox.maxX < otherPd.bbox.minX || 
                                   pd.bbox.minX > otherPd.bbox.maxX || 
                                   pd.bbox.maxY < otherPd.bbox.minY || 
                                   pd.bbox.minY > otherPd.bbox.maxY);
          
          if (intersectsBBox) {
            const point = pd.poly[0];
            const poly = otherPd.poly;
            let inside = false;
            for (let k = 0, l = poly.length - 1; k < poly.length; l = k++) {
              const xk = poly[k].x, yk = poly[k].y;
              const xl = poly[l].x, yl = poly[l].y;
              const intersect = ((yk > point.y) !== (yl > point.y))
                  && (point.x < (xl - xk) * (point.y - yk) / (yl - yk) + xk);
              if (intersect) inside = !inside;
            }
            if (inside) depth++;
          }
        });
        pd.depth = depth;
      });

      pathData.forEach(pd => {
        const parity = pd.depth % 2;
        const isCW = pd.area > 0;
        const targetCW = parity === 0; 
        
        if (isCW !== targetCW) {
          const revPts = [...pd.path.points].reverse();
          newPaths[pd.index].points = revPts.map(p => ({
            ...p,
            hIn: p.hOut ? { ...p.hOut } : undefined,
            hOut: p.hIn ? { ...p.hIn } : undefined
          }));
        }
      });

      return newPaths;
    });
  };

  const {
    exportScope: mobileExportScope, setExportScope: setMobileExportScope,
    exportFormat: mobileExportFormat, setExportFormat: setMobileExportFormat,
    isExporting,
    handleExport
  } = useExport({ layers, paths, images, selectedPoints, selectedImageIds });

  useEffect(() => {
    const canvas = svgRef.current;
    if (canvas) {
      canvas.addEventListener('wheel', handleWheel, { passive: false });
      return () => canvas.removeEventListener('wheel', handleWheel);
    }
  }, [handleWheel]); 

  // --- KEYBOARD SHORTCUTS ---
  useEffect(() => {
    const handleKeyDown = (e) => {
      if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;

      // Copy
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'c' && mode === 'edit') {
        if (selectedPoints.length > 0 || selectedImageIds.length > 0) {
          e.preventDefault();
          copyCurrentSelection();
        }
        return;
      }

      // Cut
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'x' && mode === 'edit') {
        if (selectedPoints.length > 0 || selectedImageIds.length > 0) {
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

      if (e.key.toLowerCase() === 'p') {
        changeMode('draw');
        return;
      }
      if (e.key.toLowerCase() === 'f') {
        changeMode('pencil');
        return;
      }
      if (e.key.toLowerCase() === 'v') {
        changeMode('edit');
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
      if (e.key.toLowerCase() === 'n') {
        if (mode === 'pencil') {
          changeMode('edit');
          setShowNodes(true);
        } else {
          setShowNodes(prev => !prev);
        }
        return;
      }
      if (e.key.toLowerCase() === 'l') {
        togglePanel('layers');
        return;
      }
      if (e.key.toLowerCase() === 'u') {
        togglePanel('image');
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
          setShowShapeMenu(false);
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
          setPointAction(null);
        }
        return;
      }

      if ((e.key === 'Backspace' || e.key === 'Delete')) {
        if (editingLayerId) return; 
        if (selectedPoints.length > 0 || selectedImageIds.length > 0) {
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
  }, [mode, selectedPoints, selectedImageIds, currentPath, pastPaths, futurePaths, paths, images, layers, handleUndo, handleRedo, commitHistory, deleteSelectedItems, copyCurrentSelection, cutCurrentSelection, editingLayerId, activePathEditId]);

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

  let dynamicCursor = 'cursor-default';
  if (mode === 'pan' || isPanning) dynamicCursor = 'cursor-grab active:cursor-grabbing';
  else if (mode === 'draw') dynamicCursor = 'cursor-pen';
  else if (mode === 'pencil') dynamicCursor = 'cursor-pencil';
  else if (mode === 'shape') dynamicCursor = 'cursor-crosshair';
  else if (mode === 'edit') {
    const activeImgId = bgAction ? selectedImageIds[0] : (bgHoverAction ? bgHoverAction.imageId : null);
    const activeImg = images.find(i => i.id === activeImgId);
    
    let act = null;
    let ang = 0;
    let baseRot = 0;

    if (pointAction) {
        act = pointAction.action;
        ang = pointAction.cursorAngle;
    } else if (bgAction) {
        act = bgAction;
        ang = bgInitialState?.cursorAngle;
        baseRot = activeImg ? activeImg.rotation : 0;
    } else if (bgHoverAction) {
        act = bgHoverAction.action;
        ang = bgHoverAction.cursorAngle;
        if (bgHoverAction.type !== 'point' && activeImg) {
             baseRot = activeImg.rotation;
        }
    }
    
    if (act) {
      if (act === 'move' || act === 'move-points') dynamicCursor = 'cursor-default';
      else if (act.startsWith('rotate')) dynamicCursor = 'cursor-rotate';
      else if (act.startsWith('scale')) {
        let visualAngle = (ang + baseRot) % 180;
        if (visualAngle < 0) visualAngle += 180;
        if (visualAngle > 22.5 && visualAngle <= 112.5) dynamicCursor = 'cursor-nwse';
        else dynamicCursor = 'cursor-nesw';
      }
    }
  }
  
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
  const pathsByLayerId = {};
  paths.forEach(path => {
    if (!pathsByLayerId[path.layerId]) pathsByLayerId[path.layerId] = [];
    pathsByLayerId[path.layerId].push(path);
  });
  const imagesByLayerId = {};
  images.forEach(image => {
    if (!imagesByLayerId[image.layerId]) imagesByLayerId[image.layerId] = [];
    imagesByLayerId[image.layerId].push(image);
  });
  const getLayerPreviewBounds = (layerPaths, layerImages) => {
    let minX = Infinity;
    let minY = Infinity;
    let maxX = -Infinity;
    let maxY = -Infinity;

    layerPaths.forEach(path => {
      (path.points || []).forEach(point => {
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

    layerImages.forEach(img => {
      const scale = Number.isFinite(img.scale) ? img.scale : 1;
      const halfW = (img.width * scale) / 2;
      const halfH = (img.height * scale) / 2;
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

    if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(maxX) || !Number.isFinite(maxY)) {
      return null;
    }

    const padding = 8;
    minX -= padding;
    minY -= padding;
    maxX += padding;
    maxY += padding;
    const width = Math.max(1, maxX - minX);
    const height = Math.max(1, maxY - minY);
    return { minX, minY, width, height };
  };
  const pathCountByLayerId = {};
  paths.forEach(path => {
    pathCountByLayerId[path.layerId] = (pathCountByLayerId[path.layerId] || 0) + 1;
  });
  const imageCountByLayerId = {};
  images.forEach(image => {
    imageCountByLayerId[image.layerId] = (imageCountByLayerId[image.layerId] || 0) + 1;
  });
  const compositeFillPathD = paths
    .filter(path => path.isClosed && path.fillEnabled && visibleLayerIds.has(path.layerId))
    .map(path => pointsToPath(path.points, path.isClosed))
    .join(' ');
  const anyPanelOpen = Object.values(openPanels).some(Boolean);
  const closeAllPanels = () => {
    setMobileContextMenu(null);
    setMobileToolsOpen(false);
    setMobileShapePanelOpen(false);
    setMobilePanelsOpen(false);
    setOpenPanels({ ...CLOSED_PANELS });
    setExpandedPanel(null);
  };
  const openMobilePanel = (panelId) => {
    setMobileContextMenu(null);
    setMobileToolsOpen(false);
    setMobileShapePanelOpen(false);
    setOpenPanels({ ...CLOSED_PANELS, [panelId]: true });
    setExpandedPanel(panelId);
    setMobilePanelsOpen(true);
  };
  const toggleMobileToolsMenu = () => {
    if (mobileToolsOpen) {
      setMobileToolsOpen(false);
      return;
    }
    closeAllPanels();
    setMobileToolsOpen(true);
  };
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
  const clearTapFocus = (event) => {
    if (event?.currentTarget && typeof event.currentTarget.blur === 'function') {
      event.currentTarget.blur();
    }
  };
  const resetZoomToHundred = () => {
    const currentZoom = zoomRef.current;
    if (Math.abs(currentZoom - 1) < 0.0001) return;
    zoomAtScreenPoint(1 / currentZoom, viewportSize.width / 2, viewportSize.height / 2);
  };
  const anyMobileOverlayOpen = mobileToolsOpen || mobileShapePanelOpen || mobilePanelsOpen || anyPanelOpen;
  const mobileControlGapPx = 8;
  const mobileToolbarRowHeightPx = 48;
  const mobilePanelOffsetPx = mobileToolbarRowHeightPx + mobileControlGapPx;
  const mobileToolbarMinimumClearancePx = 44;
  const mobileToolbarDesignGapPx = 16;
  const resolvedMobileInsetPx = Math.max(mobileBottomInset, mobileToolbarMinimumClearancePx);
  const computedBottomInset = `max(env(safe-area-inset-bottom, 0px), ${resolvedMobileInsetPx}px)`;
  const mobileToolbarBottom = `calc(${computedBottomInset} + ${mobileToolbarDesignGapPx}px)`;
  const mobileMenuDrawerBottom = `calc(${mobileToolbarBottom} + ${mobilePanelOffsetPx}px)`;
  const mobileShapePanelBottom = `calc(${mobileToolbarBottom} + ${mobilePanelOffsetPx}px)`;
  const mobileToolbarMaxWidth = Math.max(0, viewportSize.width - 16);
  const measuredMobileToolbarWidth = mobileToolbarWidth > 0
    ? Math.min(mobileToolbarWidth, mobileToolbarMaxWidth)
    : mobileToolbarMaxWidth;
  const mobileToolbarSharedWidthStyle = {
    width: measuredMobileToolbarWidth > 0 ? `${measuredMobileToolbarWidth}px` : 'calc(100vw - 16px)',
    maxWidth: 'calc(100vw - 16px)'
  };
  const mobileTopInset = 'calc(env(safe-area-inset-top, 0px) + 8px)';

  const editor = {
    activeEditGroupId,
    activeImage,
    activeLayerId,
    anyMobileOverlayOpen,
    anyPanelOpen,
    applyPathStyle,
    canExportSelection,
    changeMode,
    clearCanvas,
    clearTapFocus,
    closeAllPanels,
    closeMobileContextMenu,
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
    expandedPanel,
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
    mobileContextMenu,
    mobileExportFormat,
    mobileExportScope,
    mobileMenuDrawerBottom,
    mobilePanelsOpen,
    mobileShapePanelBottom,
    mobileShapePanelOpen,
    mobileToolbarBottom,
    mobileToolbarSharedWidthStyle,
    mobileToolbarShellRef,
    mobileToolsOpen,
    mobileTopInset,
    mode,
    moveSelectedLayerQuick,
    openMobilePanel,
    openPanels,
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
    setExpandedPanel,
    setGridConfig,
    setHoveredHandle,
    setMobileExportFormat,
    setMobileExportScope,
    setOpenPanels,
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
    toggleMobileToolsMenu,
    togglePanel,
    updateActiveImage,
    zoom
  };

  return (
    <EditorProvider value={editor}>
    <div className="w-screen h-screen bg-[#f2f4f7] overflow-hidden select-none font-sans text-slate-800 flex flex-col fixed inset-0 touch-none">
      
      {/* Global Style overrides to hide default number input spinners for cleaner UI */}
      <style>{`
        input[type="number"]::-webkit-inner-spin-button,
        input[type="number"]::-webkit-outer-spin-button {
          -webkit-appearance: none;
          margin: 0;
        }
        input[type="number"] {
          -moz-appearance: textfield;
        }
        button,
        [role='button'] {
          -webkit-tap-highlight-color: transparent;
          tap-highlight-color: transparent;
        }
        .cursor-pen {
          cursor: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='white' stroke='%23344054' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M12 19l7-7 3 3-7 7-3-3z'/%3E%3Cpath d='M18 13l-1.5-7.5L2 2l3.5 14.5L13 18l5-5z'/%3E%3Cpath d='M2 2l7.586 7.586'/%3E%3Ccircle cx='11' cy='11' r='2'/%3E%3C/svg%3E") 2 2, crosshair !important;
        }
        .cursor-pencil {
          cursor: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='white' stroke='%23344054' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M17 3a2.828 2.828 0 1 1 4 4L7.5 20.5 2 22l1.5-5.5L17 3z'/%3E%3C/svg%3E") 2 22, crosshair !important;
        }
        .cursor-rotate {
          cursor: url("data:image/svg+xml,%3Csvg width='20' height='20' viewBox='0 0 20 20' fill='none' xmlns='http://www.w3.org/2000/svg'%3E%3Cg stroke='white' stroke-width='3' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M5 8A7 7 0 0 1 12 15'/%3E%3Cpath d='M8.5 4.5L5 8l3.5 3.5'/%3E%3Cpath d='M8.5 11.5L12 15l3.5-3.5'/%3E%3C/g%3E%3Cg stroke='black' stroke-width='1.2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M5 8A7 7 0 0 1 12 15'/%3E%3Cpath d='M8.5 4.5L5 8l3.5 3.5'/%3E%3Cpath d='M8.5 11.5L12 15l3.5-3.5'/%3E%3C/g%3E%3C/svg%3E") 10 10, crosshair !important;
        }
        .cursor-crosshair { cursor: crosshair !important; }
        .cursor-nwse { cursor: nwse-resize !important; }
        .cursor-nesw { cursor: nesw-resize !important; }
        .cursor-move { cursor: move !important; }
        .cursor-default { cursor: default !important; }
        .cursor-grab { cursor: grab !important; }
        .cursor-grabbing { cursor: grabbing !important; }
        .mobile-drawer {
          transition: opacity 180ms ease, transform 180ms ease;
          will-change: transform, opacity;
        }
        .mobile-drawer-open {
          opacity: 1;
          transform: translateY(0);
          pointer-events: auto;
        }
        .mobile-drawer-closed {
          opacity: 0;
          transform: translateY(10px);
          pointer-events: none;
        }
        .mobile-panels-wrap {
          transition: opacity 200ms ease, transform 200ms ease;
          will-change: transform, opacity;
        }
        .mobile-panels-open {
          opacity: 1;
          transform: translateY(0);
          pointer-events: auto;
        }
        .mobile-panels-closed {
          opacity: 0;
          transform: translateY(-10px);
          pointer-events: none;
        }
      `}</style>

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
