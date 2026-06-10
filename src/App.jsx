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

import { THEME } from './theme';
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
import { escapeXml, toSafeSvgId, generateEditGroupId } from './lib/svg';
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
import { usePointerInteraction } from './hooks/usePointerInteraction';
import { EditorProvider } from './state/EditorContext';
import DesktopToolbar from './components/Toolbar/DesktopToolbar';

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
  const [mobileExportScope, setMobileExportScope] = useState('selection');
  const [mobileExportFormat, setMobileExportFormat] = useState('png');
  const [isExporting, setIsExporting] = useState(false);
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

  const fileInputRef = useRef(null);
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
      commitHistory({ paths, currentPath, images, layers });
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
  }, [activeLayerId, lockedLayerIds, commitHistory, paths, currentPath, images, layers, viewportSize.width, viewportSize.height]);

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

  // --- SKETCH UPLOAD ---
  const handleImageUpload = (e) => {
    const file = e.target.files?.[0];
    if (file) {
      insertImageFromFile(file);
    }
    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }
  };

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

  const collectExportItems = useCallback((scope) => {
    const visibleLayerIdSet = new Set(layers.filter(layer => layer.visible).map(layer => layer.id));

    if (scope === 'selection') {
      const selectedPathIndexSet = new Set(selectedPoints.map(point => point.pathIndex));
      const scopedPaths = [...selectedPathIndexSet]
        .map(index => paths[index])
        .filter(path => path && visibleLayerIdSet.has(path.layerId));
      const selectedImageIdSet = new Set(selectedImageIds);
      const scopedImages = images.filter(img => selectedImageIdSet.has(img.id) && visibleLayerIdSet.has(img.layerId));
      return { exportPaths: scopedPaths, exportImages: scopedImages };
    }

    return {
      exportPaths: paths.filter(path => visibleLayerIdSet.has(path.layerId)),
      exportImages: images.filter(img => visibleLayerIdSet.has(img.layerId))
    };
  }, [layers, selectedPoints, selectedImageIds, paths, images]);

  const buildExportSvgBundle = useCallback((scope) => {
    const { exportPaths, exportImages } = collectExportItems(scope);
    if (exportPaths.length === 0 && exportImages.length === 0) return null;

    let minX = Infinity;
    let minY = Infinity;
    let maxX = -Infinity;
    let maxY = -Infinity;

    exportPaths.forEach(path => {
      path.points.forEach(point => {
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

    exportImages.forEach(img => {
      const halfW = (img.width * img.scale) / 2;
      const halfH = (img.height * img.scale) / 2;
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

    const padding = 12;
    minX -= padding;
    minY -= padding;
    maxX += padding;
    maxY += padding;
    const width = Math.max(1, Math.ceil(maxX - minX));
    const height = Math.max(1, Math.ceil(maxY - minY));

    const imageMarkup = exportImages.map(img => {
      const renderWidth = img.width * img.scale;
      const renderHeight = img.height * img.scale;
      const x = img.x - renderWidth / 2;
      const y = img.y - renderHeight / 2;
      const opacity = Number.isFinite(img.opacity) ? Math.max(0, Math.min(1, img.opacity)) : 1;
      const rotation = Number.isFinite(img.rotation) ? img.rotation : 0;
      return `<image href="${escapeXml(img.url)}" x="${x}" y="${y}" width="${renderWidth}" height="${renderHeight}" opacity="${opacity}" transform="rotate(${rotation} ${img.x} ${img.y})" />`;
    }).join('');

    const pathMarkup = exportPaths.map(path => {
      const d = pointsToPath(path.points, path.isClosed);
      const fill = path.fillEnabled ? THEME.main : 'none';
      const strokeColor = normalizeStrokeColor(path.strokeColor, DEFAULT_STROKE_COLOR);
      const stroke = path.strokeEnabled === false ? 'none' : strokeColor;
      const strokeWidthValue = stroke === 'none' ? 0 : normalizeStrokeWidth(path.strokeWidth, DEFAULT_STROKE_WIDTH);
      return `<path d="${escapeXml(d)}" fill="${fill}" stroke="${stroke}" stroke-width="${strokeWidthValue}" stroke-linejoin="round" stroke-linecap="round" />`;
    }).join('');

    const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}"><g transform="translate(${-minX} ${-minY})">${imageMarkup}${pathMarkup}</g></svg>`;
    return { svg, width, height };
  }, [collectExportItems]);

  const downloadBlob = useCallback((blob, filename) => {
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = filename;
    document.body.appendChild(link);
    link.click();
    link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }, []);

  const handleExport = useCallback(async () => {
    if (isExporting) return;
    const scope = mobileExportScope;
    const format = mobileExportFormat;
    const bundle = buildExportSvgBundle(scope);
    if (!bundle) return;

    setIsExporting(true);
    try {
      const baseName = scope === 'selection' ? 'selection' : 'canvas';
      if (format === 'svg') {
        downloadBlob(new Blob([bundle.svg], { type: 'image/svg+xml;charset=utf-8' }), `${baseName}.svg`);
        return;
      }

      const svgBlob = new Blob([bundle.svg], { type: 'image/svg+xml;charset=utf-8' });
      const svgUrl = URL.createObjectURL(svgBlob);
      try {
        const svgImage = await new Promise((resolve, reject) => {
          const img = new window.Image();
          img.onload = () => resolve(img);
          img.onerror = reject;
          img.src = svgUrl;
        });

        const canvas = document.createElement('canvas');
        canvas.width = Math.max(1, Math.round(bundle.width));
        canvas.height = Math.max(1, Math.round(bundle.height));
        const ctx = canvas.getContext('2d');
        if (!ctx) return;

        if (format === 'jpg') {
          ctx.fillStyle = THEME.bg;
          ctx.fillRect(0, 0, canvas.width, canvas.height);
        } else {
          ctx.clearRect(0, 0, canvas.width, canvas.height);
        }

        ctx.drawImage(svgImage, 0, 0, canvas.width, canvas.height);
        const mime = format === 'jpg' ? 'image/jpeg' : 'image/png';
        const dataUrl = canvas.toDataURL(mime, format === 'jpg' ? 0.92 : undefined);
        const link = document.createElement('a');
        link.href = dataUrl;
        link.download = `${baseName}.${format === 'jpg' ? 'jpg' : 'png'}`;
        document.body.appendChild(link);
        link.click();
        link.remove();
      } finally {
        URL.revokeObjectURL(svgUrl);
      }
    } finally {
      setIsExporting(false);
    }
  }, [isExporting, mobileExportScope, mobileExportFormat, buildExportSvgBundle, downloadBlob]);

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
  const circularRayCount = Math.max(1, Math.ceil(360 / effectiveCircularStep));
  const s = effectiveGridSize;
  let patternW = s;
  let patternH = s;
  let patternContent = null;
  const showPixelGrid = zoom >= PIXEL_GRID_MIN_ZOOM;
  const showBackgroundGridPattern = showBackgroundAids && gridConfig.type !== 'none' && gridConfig.type !== 'circular';
  const showCircularGrid = showBackgroundAids && gridConfig.type === 'circular';
  const showPixelGridOverlay = showBackgroundAids && showPixelGrid;

  if (gridConfig.type === 'dots') {
    patternW = s;
    patternH = s;
    patternContent = <circle cx={1/zoom} cy={1/zoom} r={1.5/zoom} fill="#d0d5dd" />;
  } else if (gridConfig.type === 'circles') {
    patternW = s;
    patternH = s;
    patternContent = <circle cx={s/2} cy={s/2} r={s / 2} fill="none" stroke="#d0d5dd" strokeWidth={1/zoom} />;
  } else if (gridConfig.type === 'lines') {
    if (gridConfig.edges === 4) {
      patternW = s;
      patternH = s;
      patternContent = <path d={`M ${s} 0 L 0 0 L 0 ${s}`} fill="none" stroke="#d0d5dd" strokeWidth={1/zoom} />;
    } else if (gridConfig.edges === 3) {
      patternW = s;
      patternH = s * Math.sqrt(3);
      patternContent = <path d={`M 0 0 L ${patternW} 0 M 0 ${patternH/2} L ${patternW} ${patternH/2} M 0 ${patternH/2} L ${patternW/2} 0 M ${patternW/2} ${patternH} L ${patternW} ${patternH/2} M ${patternW/2} 0 L ${patternW} ${patternH/2} M 0 ${patternH/2} L ${patternW/2} ${patternH}`} fill="none" stroke="#d0d5dd" strokeWidth={1/zoom} />;
    } else if (gridConfig.edges === 6) {
      patternW = s * Math.sqrt(3);
      patternH = s * 3;
      patternContent = <path d={`M 0 ${0.5*s} L ${patternW/2} 0 L ${patternW} ${0.5*s} L ${patternW} ${1.5*s} L ${patternW/2} ${2*s} L 0 ${1.5*s} Z M ${patternW/2} ${2*s} L ${patternW/2} ${3*s}`} fill="none" stroke="#d0d5dd" strokeWidth={1/zoom} />;
    }
  }

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
    applyPathStyle,
    changeMode,
    clearCanvas,
    correctPathDirections,
    fillToggleActive,
    hasSelectedPaths,
    insertTextFromPrompt,
    mode,
    openPanels,
    selectedPoints,
    setShapeType,
    setShowNodes,
    setShowShapeMenu,
    shapeMenuContainerRef,
    shapeType,
    showNodes,
    showShapeMenu,
    togglePanel
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
      <svg 
        ref={svgRef}
        className={`w-full h-full ${dynamicCursor}`}
        onPointerDown={handlePointerDown}
        onPointerMove={handlePointerMove}
        onPointerUp={handlePointerUp}
        onPointerCancel={handlePointerUp}
        onContextMenu={handleCanvasContextMenu}
      >
        <defs>
          {showBackgroundGridPattern && (
            <pattern 
              id="bg-grid" 
              width={patternW * zoom} 
              height={patternH * zoom} 
              patternUnits="userSpaceOnUse" 
              patternTransform={`translate(${pan.x}, ${pan.y})`}
            >
              <g transform={`scale(${zoom})`}>
                {patternContent}
              </g>
            </pattern>
          )}
          {showPixelGridOverlay && (
            <pattern
              id="pixel-grid"
              width={zoom}
              height={zoom}
              patternUnits="userSpaceOnUse"
              patternTransform={`translate(${pan.x}, ${pan.y})`}
            >
              <g transform={`scale(${zoom})`}>
                <path
                  d="M 1 0 L 0 0 L 0 1"
                  fill="none"
                  stroke="#667085"
                  strokeOpacity="0.22"
                  strokeWidth={1 / zoom}
                />
              </g>
            </pattern>
          )}
        </defs>

        {/* Background Grid */}
        {showBackgroundGridPattern && <rect width="100%" height="100%" fill="url(#bg-grid)" />}

        {/* Transform Group for Pan & Zoom */}
        <g transform={`translate(${pan.x}, ${pan.y}) scale(${zoom})`}>
          
          {/* Circular Grid (Drawn inside world coordinates) */}
          {showCircularGrid && (
            <g className="opacity-60 pointer-events-none">
              {Array.from({length: 100}).map((_, i) => (
                <circle key={`circ-${i}`} cx={0} cy={0} r={(i + 1) * s} stroke="#d0d5dd" strokeWidth={1/zoom} fill="none" />
              ))}
              {Array.from({length: circularRayCount}).map((_, i) => {
                 const angle = (i * effectiveCircularStep * Math.PI) / 180;
                 return <line key={`rad-${i}`} x1={-5000 * Math.cos(angle)} y1={-5000 * Math.sin(angle)} x2={5000 * Math.cos(angle)} y2={5000 * Math.sin(angle)} stroke="#d0d5dd" strokeWidth={1/zoom} />
              })}
            </g>
          )}

          {/* Global Composite Fill (winding-based interpolation across all visible layers) */}
          {compositeFillPathD && (
            <path
              d={compositeFillPathD}
              fill={THEME.main}
              fillRule="nonzero"
            />
          )}

          {/* Finished Paths and Layer-bound Images */}
          {layers.slice().reverse().map(layer => {
            if (!layer.visible) return null;

            return (
            <g key={`layer-group-${layer.id}`}>
              
              {/* Layer Images */}
              {images.map(img => {
                if (img.layerId !== layer.id) return null;
                return (
                  <g key={img.id}>
                    <image
                      href={img.url}
                      x={-img.width / 2}
                      y={-img.height / 2}
                      width={img.width}
                      height={img.height}
                      opacity={img.opacity}
                      imageRendering={showPixelGridOverlay ? 'pixelated' : 'auto'}
                      style={showPixelGridOverlay ? { imageRendering: 'pixelated' } : undefined}
                      pointerEvents="none"
                      transform={`translate(${img.x}, ${img.y}) scale(${img.scale}) rotate(${img.rotation})`}
                    />

                    {/* Bounding Box for active edit mode image */}
                    {selectedImageIds.includes(img.id) && !layer.locked && !img.locked && mode === 'edit' && (
                       <g transform={`translate(${img.x}, ${img.y}) rotate(${img.rotation})`} pointerEvents="none">
                           <rect
                               x={-img.width * img.scale / 2}
                               y={-img.height * img.scale / 2}
                               width={img.width * img.scale}
                               height={img.height * img.scale}
                               fill="none"
                               stroke="#3b82f6" 
                               strokeWidth={1.5/zoom}
                           />
                           {selectedImageIds.length === 1 && [
                             {x: -1, y: -1}, {x: 1, y: -1}, {x: 1, y: 1}, {x: -1, y: 1}
                           ].map((c, i) => (
                               <rect
                                 key={i}
                                 x={(c.x * img.width * img.scale / 2) - 4/zoom}
                                 y={(c.y * img.height * img.scale / 2) - 4/zoom}
                                 width={8/zoom}
                                 height={8/zoom}
                                 fill="white"
                                 stroke="#3b82f6"
                                 strokeWidth={1.5/zoom}
                               />
                           ))}
                       </g>
                    )}
                  </g>
                );
              })}

              {/* Layer Paths */}
              {paths.map((path, i) => {
                if (path.layerId !== layer.id) return null;
                if (mode === 'draw' && currentPath.length > 0 && currentPathInfo?.resumePathId === path.id) return null;
                const pathD = pointsToPath(path.points, path.isClosed);
                const isSinglePointPath = path.points.length === 1;
                const pathStroke = getPathStrokeStyle(path, pathStyleDefaults);
                const renderStrokeWidth = pathStroke.strokeWidth / zoom;
                const canOffsetStroke = pathStroke.strokeEnabled && path.isClosed && !isSinglePointPath;
                const effectiveStrokeAlign = canOffsetStroke ? pathStroke.strokeAlign : 'center';
                const strokeRenderIdBase = `stroke-${toSafeSvgId(path.id)}-${i}`;

                return (
                  <g key={path.id}>
                    {isSinglePointPath ? (
                      pathStroke.strokeEnabled ? (
                        <circle
                          cx={path.points[0].x}
                          cy={path.points[0].y}
                          r={Math.max(2, pathStroke.strokeWidth * 1.5) / zoom}
                          fill={pathStroke.strokeColor}
                          stroke={pathStroke.strokeColor}
                          strokeWidth={1 / zoom}
                          vectorEffect="non-scaling-stroke"
                        />
                      ) : null
                    ) : (
                      <>
                        {pathStroke.strokeEnabled && effectiveStrokeAlign === 'inside' && (
                          <>
                            <defs>
                              <clipPath id={`${strokeRenderIdBase}-inside-clip`}>
                                <path d={pathD} />
                              </clipPath>
                            </defs>
                            <path
                              d={pathD}
                              fill="none"
                              stroke={pathStroke.strokeColor}
                              strokeWidth={(renderStrokeWidth * 2)}
                              strokeLinejoin="round"
                              strokeLinecap="round"
                              clipPath={`url(#${strokeRenderIdBase}-inside-clip)`}
                            />
                          </>
                        )}
                        {pathStroke.strokeEnabled && effectiveStrokeAlign === 'outside' && (
                          <>
                            <defs>
                              <mask id={`${strokeRenderIdBase}-outside-mask`}>
                                <rect x="-200000" y="-200000" width="400000" height="400000" fill="white" />
                                <path d={pathD} fill="black" />
                              </mask>
                            </defs>
                            <path
                              d={pathD}
                              fill="none"
                              stroke={pathStroke.strokeColor}
                              strokeWidth={(renderStrokeWidth * 2)}
                              strokeLinejoin="round"
                              strokeLinecap="round"
                              mask={`url(#${strokeRenderIdBase}-outside-mask)`}
                            />
                          </>
                        )}
                        {pathStroke.strokeEnabled && effectiveStrokeAlign === 'center' && (
                          <path
                            d={pathD}
                            fill="none"
                            stroke={pathStroke.strokeColor}
                            strokeWidth={renderStrokeWidth}
                            strokeLinejoin="round"
                            strokeLinecap="round"
                          />
                        )}
                      </>
                    )}
                    
                    {/* Nodes and Handles (controlled by Show Nodes, hidden only in pencil mode, and when unlocked) */}
                    {showNodes && (mode === 'edit' || mode === 'draw') && !layer.locked && activeEditGroupId != null && isPathInActiveEditContext(path) && (
                      <g>
                        {/* Draw Bezier Handles for ALL Points (Persistent) */}
                        {path.points.map((p, j) => {
                          const hasIn = p.hIn && Math.hypot(p.hIn.x - p.x, p.hIn.y - p.y) > 0.1;
                          const hasOut = p.hOut && Math.hypot(p.hOut.x - p.x, p.hOut.y - p.y) > 0.1;
                          const inHovered = hoveredHandle?.pathIndex === i && hoveredHandle?.pointIndex === j && hoveredHandle?.type === 'hIn';
                          const outHovered = hoveredHandle?.pathIndex === i && hoveredHandle?.pointIndex === j && hoveredHandle?.type === 'hOut';
                          
                          return (
                            <g key={`handles-${j}`}>
                              {hasIn && (
                                <g
                                  className="cursor-pointer"
                                  onPointerEnter={() => setHoveredHandle({ pathIndex: i, pointIndex: j, type: 'hIn' })}
                                  onPointerLeave={() => setHoveredHandle(prev => (
                                    prev?.pathIndex === i && prev?.pointIndex === j && prev?.type === 'hIn' ? null : prev
                                  ))}
                                >
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hIn.x}
                                    y2={p.hIn.y}
                                    stroke={inHovered ? "#2563eb" : THEME.main}
                                    strokeWidth={(inHovered ? 1.1 : 0.8) / zoom}
                                    className="transition-all duration-150"
                                  />
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hIn.x}
                                    y2={p.hIn.y}
                                    stroke="rgba(0,0,0,0)"
                                    strokeWidth={(isMobile ? 16 : 10) / zoom}
                                    pointerEvents="stroke"
                                  />
                                  <circle
                                    cx={p.hIn.x}
                                    cy={p.hIn.y}
                                    r={2.5 / zoom}
                                    fill={inHovered ? "white" : THEME.nodeFill}
                                    stroke={inHovered ? "#2563eb" : THEME.main}
                                    strokeWidth={1 / zoom}
                                    className="transition-colors duration-150"
                                  />
                                </g>
                              )}
                              {hasOut && (
                                <g
                                  className="cursor-pointer"
                                  onPointerEnter={() => setHoveredHandle({ pathIndex: i, pointIndex: j, type: 'hOut' })}
                                  onPointerLeave={() => setHoveredHandle(prev => (
                                    prev?.pathIndex === i && prev?.pointIndex === j && prev?.type === 'hOut' ? null : prev
                                  ))}
                                >
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hOut.x}
                                    y2={p.hOut.y}
                                    stroke={outHovered ? "#2563eb" : THEME.main}
                                    strokeWidth={(outHovered ? 1.1 : 0.8) / zoom}
                                    className="transition-all duration-150"
                                  />
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hOut.x}
                                    y2={p.hOut.y}
                                    stroke="rgba(0,0,0,0)"
                                    strokeWidth={(isMobile ? 16 : 10) / zoom}
                                    pointerEvents="stroke"
                                  />
                                  <circle
                                    cx={p.hOut.x}
                                    cy={p.hOut.y}
                                    r={2.5 / zoom}
                                    fill={outHovered ? "white" : THEME.nodeFill}
                                    stroke={outHovered ? "#2563eb" : THEME.main}
                                    strokeWidth={1 / zoom}
                                    className="transition-colors duration-150"
                                  />
                                </g>
                              )}
                            </g>
                          );
                        })}
                        
                        {/* Draw Anchor Points (Squares for corners, Circles for smooth) */}
                        {path.points.map((p, j) => {
                          const isSelected = selectedPoints.some(sp => sp.pathIndex === i && sp.pointIndex === j);
                          const corner = isCorner(p);
                          const fill = isSelected ? THEME.main : THEME.nodeFill;
                          
                          if (corner) {
                            return (
                              <rect 
                                key={`anchor-${j}`} 
                                x={p.x - 3.5/zoom} 
                                y={p.y - 3.5/zoom} 
                                width={7/zoom} 
                                height={7/zoom} 
                                fill={fill} 
                                stroke={THEME.main} 
                                strokeWidth={1.5/zoom}
                                className=""
                              />
                            );
                          } else {
                            return (
                              <circle 
                                key={`anchor-${j}`} 
                                cx={p.x} 
                                cy={p.y} 
                                r={3.5/zoom} 
                                fill={fill} 
                                stroke={THEME.main} 
                                strokeWidth={1.5/zoom}
                                className=""
                              />
                            );
                          }
                        })}
                      </g>
                    )}
                  </g>
                );
              })}
            </g>
          )})}

          {/* Drawing Shape Preview (Live Render) */}
          {mode === 'shape' && drawingShape && (
            <path
              d={pointsToPath(
                 generateShapePath(drawingShape.startX, drawingShape.startY, drawingShape.currentX, drawingShape.currentY, shapeType, drawingShape.shiftKey).points, 
                 shapeType !== 'line'
              )}
              fill="none"
              stroke={defaultStrokeEnabled ? defaultStrokeRenderColor : 'none'}
              strokeWidth={defaultStrokeEnabled ? defaultStrokeRenderWidth : 0}
              strokeLinejoin="round"
              strokeLinecap="round"
            />
          )}

          {/* Selection Box (Draw to select multiple) */}
          {selectionBox && mode === 'edit' && (
            <rect
              x={Math.min(selectionBox.startX, selectionBox.currentX)}
              y={Math.min(selectionBox.startY, selectionBox.currentY)}
              width={Math.abs(selectionBox.currentX - selectionBox.startX)}
              height={Math.abs(selectionBox.currentY - selectionBox.startY)}
              fill="rgba(74, 38, 34, 0.08)"
              stroke={THEME.main}
              strokeWidth={1/zoom}
            />
          )}

          {/* Active Selection Bounding Box (Paths) */}
          {(() => {
             let bboxTransform = "";
             if (selBBox && pointAction) {
                if (pointAction.action.startsWith('rotate-')) {
                   bboxTransform = `rotate(${pointAction.angle || 0} ${(selBBox.minX + selBBox.maxX)/2} ${(selBBox.minY + selBBox.maxY)/2})`;
                } else if (pointAction.action.startsWith('scale-')) {
                   const ox = pointAction.origin?.x || 0;
                   const oy = pointAction.origin?.y || 0;
                   const s = pointAction.scale || 1;
                   bboxTransform = `translate(${ox} ${oy}) scale(${s}) translate(${-ox} ${-oy})`;
                }
             }

             return selBBox && mode === 'edit' && !selectionBox && (
                 <g pointerEvents="none" transform={bboxTransform}>
                   <rect
                       x={selBBox.minX}
                       y={selBBox.minY}
                       width={selBBox.maxX - selBBox.minX}
                       height={selBBox.maxY - selBBox.minY}
                       fill="rgba(59, 130, 246, 0.03)"
                       stroke="#3b82f6"
                       strokeWidth={1.25}
                       strokeDasharray="4 4"
                       vectorEffect="non-scaling-stroke"
                   />
                   {[
                     {x: selBBox.minX, y: selBBox.minY},
                     {x: selBBox.maxX, y: selBBox.minY},
                     {x: selBBox.maxX, y: selBBox.maxY},
                     {x: selBBox.minX, y: selBBox.maxY}
                   ].map((c, i) => (
                       <rect
                         key={`sel-handle-${i}`}
                         x={c.x - 4/zoom}
                         y={c.y - 4/zoom}
                         width={8/zoom}
                         height={8/zoom}
                         fill="white"
                         stroke="#3b82f6"
                         strokeWidth={1.5}
                         vectorEffect="non-scaling-stroke"
                       />
                   ))}
                 </g>
             );
          })()}

          {/* Current Drawing Path */}
          {currentPath.length > 0 && mode !== 'shape' && (
            <g>
              {/* Actual accepted segments */}
              <path 
                d={pointsToPath(currentPath, isDrawingCurve === 'closing')} 
                fill="none" 
                stroke={livePathStroke.strokeEnabled ? livePathStroke.strokeColor : 'none'} 
                strokeWidth={livePathStroke.strokeEnabled ? livePathStrokeRenderWidth : 0}
                strokeLinejoin="round"
                strokeLinecap="round"
              />
              
              {/* Ghost segment to mouse cursor (only for pen tool) */}
              {ghostPoint && !isDrawingCurve && mode === 'draw' && (
                <path 
                  d={`M ${currentPath[currentPath.length - 1].x} ${currentPath[currentPath.length - 1].y} C ${currentPath[currentPath.length - 1].hOut ? currentPath[currentPath.length - 1].hOut.x : currentPath[currentPath.length - 1].x} ${currentPath[currentPath.length - 1].hOut ? currentPath[currentPath.length - 1].hOut.y : currentPath[currentPath.length - 1].y}, ${ghostPoint.x} ${ghostPoint.y}, ${ghostPoint.x} ${ghostPoint.y}`}
                  fill="none"
                  stroke="#98a2b3" 
                  strokeWidth={strokeWidth}
                  strokeDasharray={`${4/zoom},${4/zoom}`}
                />
              )}

              {/* Handles of the active drawing point (only for pen tool) */}
              {isDrawingCurve && showNodes && mode === 'draw' && (
                <g>
                  {(() => {
                    const activeP = isDrawingCurve === 'closing' ? currentPath[0] : currentPath[currentPath.length - 1];
                    return (
                      <>
                        {activeP.hIn && <line x1={activeP.x} y1={activeP.y} x2={activeP.hIn.x} y2={activeP.hIn.y} stroke={THEME.main} strokeWidth={0.8/zoom} />}
                        {activeP.hOut && <line x1={activeP.x} y1={activeP.y} x2={activeP.hOut.x} y2={activeP.hOut.y} stroke={THEME.main} strokeWidth={0.8/zoom} />}
                        {activeP.hIn && <circle cx={activeP.hIn.x} cy={activeP.hIn.y} r={2.5/zoom} fill={THEME.nodeFill} stroke={THEME.main} strokeWidth={1/zoom} className="cursor-pointer transition-colors duration-150 hover:fill-white hover:stroke-[#2563eb]" />}
                        {activeP.hOut && <circle cx={activeP.hOut.x} cy={activeP.hOut.y} r={2.5/zoom} fill={THEME.nodeFill} stroke={THEME.main} strokeWidth={1/zoom} className="cursor-pointer transition-colors duration-150 hover:fill-white hover:stroke-[#2563eb]" />}
                      </>
                    );
                  })()}
                </g>
              )}

              {/* Nodes for current path (only for pen tool to reduce visual noise while freehand drawing) */}
              {showNodes && mode === 'draw' && currentPath.map((p, i) => {
                const corner = isCorner(p);
                const isStart = i === 0;
                
                if (corner) {
                   return (
                     <rect 
                       key={i} 
                       x={p.x - (isStart && hoveredStartPoint ? 4.5/zoom : 3.5/zoom)} 
                       y={p.y - (isStart && hoveredStartPoint ? 4.5/zoom : 3.5/zoom)} 
                       width={isStart && hoveredStartPoint ? 9/zoom : 7/zoom} 
                       height={isStart && hoveredStartPoint ? 9/zoom : 7/zoom} 
                       fill={isStart && hoveredStartPoint ? "#10b981" : THEME.nodeFill} 
                       stroke={isStart && hoveredStartPoint ? "#059669" : THEME.main} 
                       strokeWidth={1.5/zoom}
                     />
                   );
                } else {
                   return (
                     <circle 
                       key={i} 
                       cx={p.x} 
                       cy={p.y} 
                       r={isStart && hoveredStartPoint ? 5/zoom : 3.5/zoom} 
                       fill={isStart && hoveredStartPoint ? "#10b981" : THEME.nodeFill} 
                       stroke={isStart && hoveredStartPoint ? "#059669" : THEME.main} 
                       strokeWidth={1.5/zoom}
                     />
                   );
                }
              })}
              
              {/* Ghost Node */}
              {ghostPoint && !hoveredStartPoint && !isDrawingCurve && showNodes && mode === 'draw' && (
                <rect x={ghostPoint.x - 3/zoom} y={ghostPoint.y - 3/zoom} width={6/zoom} height={6/zoom} fill="#98a2b3" />
              )}
            </g>
          )}
          
          {/* Draw Hover Indicator */}
          {drawHover && mode === 'draw' && showNodes && !isDrawingCurve && (
            <circle 
              cx={drawHover.x} 
              cy={drawHover.y} 
              r={drawHover.type === 'endpoint' ? 5/zoom : 4/zoom} 
              fill={drawHover.type === 'endpoint' ? "#10b981" : THEME.nodeFill} 
              stroke={drawHover.type === 'endpoint' ? "#059669" : THEME.main} 
              strokeWidth={1.5/zoom}
              className="pointer-events-none"
            />
          )}
        </g>

        {/* Pixel Grid Overlay (Visible from 800%+) */}
        {showPixelGridOverlay && (
          <rect
            width="100%"
            height="100%"
            fill="url(#pixel-grid)"
            pointerEvents="none"
          />
        )}
      </svg>

      {/* --- UI OVERLAYS --- */}

      {/* Hidden File Input for Sketch Upload */}
      <input 
        type="file" 
        accept="image/*" 
        ref={fileInputRef} 
        onChange={handleImageUpload} 
        className="hidden" 
      />

      {selectedLayersInStackOrder.length > 1 && !openPanels.layers && (!isMobile || !anyMobileOverlayOpen) && (
        <div
          className={`absolute z-[24] pointer-events-none ${
            isMobile ? 'left-2 right-2' : 'top-7 left-1/2 -translate-x-1/2'
          }`}
          style={isMobile ? { top: 'calc(env(safe-area-inset-top, 0px) + 56px)' } : undefined}
        >
          <div className="pointer-events-auto w-full overflow-hidden rounded-2xl border border-[#e4e7ec] bg-[#f8fafc] shadow-[0_14px_32px_rgba(52,64,84,0.16)]">
            <div className="flex items-center justify-between px-3 py-2 border-b border-[#e4e7ec] bg-[#f2f4f7]">
              <div className="flex items-center gap-2 text-[10px] font-bold uppercase tracking-widest text-[#667085]">
                <Layers size={13} />
                Quick Layer Reorder
              </div>
              <span className="text-[10px] font-semibold text-[#98a2b3]">
                {selectedLayersInStackOrder.length} selected
              </span>
            </div>
            <div className="p-2 max-h-[32vh] overflow-y-auto flex flex-col gap-1" style={{ touchAction: 'pan-y' }}>
              {selectedLayersInStackOrder.map(layer => {
                const layerIndex = layerIndexById.get(layer.id) ?? -1;
                const canMoveUp = layerIndex > 0;
                const canMoveDown = layerIndex >= 0 && layerIndex < layers.length - 1;
                const instanceCount = (pathCountByLayerId[layer.id] || 0) + (imageCountByLayerId[layer.id] || 0);
                const isActive = activeLayerId === layer.id;
                const layerPaths = pathsByLayerId[layer.id] || [];
                const layerImages = imagesByLayerId[layer.id] || [];
                const previewBounds = getLayerPreviewBounds(layerPaths, layerImages);

                return (
                  <div
                    key={`quick-layer-${layer.id}`}
                    className={`flex items-center gap-2 rounded-xl border p-1.5 transition-colors ${
                      isActive
                        ? 'bg-[#eaecf0] border-[#d0d5dd]'
                        : 'bg-[#f8fafc] border-[#e4e7ec]'
                    }`}
                  >
                    <button
                      type="button"
                      onClick={() => setActiveLayerId(layer.id)}
                      className="flex items-center gap-2 min-w-0 flex-1 text-left rounded-md px-1 py-1 hover:bg-[#f2f4f7] transition-colors"
                    >
                      <div className="w-14 h-9 shrink-0 overflow-hidden rounded-md border border-[#d0d5dd] bg-white flex items-center justify-center">
                        {previewBounds ? (
                          <svg
                            className="w-full h-full"
                            viewBox={`${previewBounds.minX} ${previewBounds.minY} ${previewBounds.width} ${previewBounds.height}`}
                            preserveAspectRatio="xMidYMid meet"
                          >
                            {layerImages.map(img => (
                              <image
                                key={`quick-layer-img-${img.id}`}
                                href={img.url}
                                x={-img.width / 2}
                                y={-img.height / 2}
                                width={img.width}
                                height={img.height}
                                opacity={Number.isFinite(img.opacity) ? Math.max(0, Math.min(1, img.opacity)) : 1}
                                transform={`translate(${img.x}, ${img.y}) scale(${img.scale}) rotate(${img.rotation})`}
                              />
                            ))}
                            {layerPaths.map((path, index) => {
                              const pathD = pointsToPath(path.points, path.isClosed);
                              const pathStroke = getPathStrokeStyle(path, pathStyleDefaults);
                              const isSinglePointPath = path.points.length === 1;

                              if (isSinglePointPath) {
                                if (!pathStroke.strokeEnabled) return null;
                                return (
                                  <circle
                                    key={`quick-layer-path-dot-${path.id}-${index}`}
                                    cx={path.points[0].x}
                                    cy={path.points[0].y}
                                    r={Math.max(2, pathStroke.strokeWidth * 1.2)}
                                    fill={pathStroke.strokeColor}
                                    stroke={pathStroke.strokeColor}
                                    strokeWidth={0.5}
                                  />
                                );
                              }

                              return (
                                <path
                                  key={`quick-layer-path-${path.id}-${index}`}
                                  d={pathD}
                                  fill={path.fillEnabled ? THEME.main : 'none'}
                                  stroke={pathStroke.strokeEnabled ? pathStroke.strokeColor : 'none'}
                                  strokeWidth={pathStroke.strokeEnabled ? Math.max(0.8, pathStroke.strokeWidth) : 0}
                                  strokeLinecap="round"
                                  strokeLinejoin="round"
                                />
                              );
                            })}
                          </svg>
                        ) : (
                          <LayerIcon type={layer.itemType} />
                        )}
                      </div>
                      <span className="text-xs font-semibold text-[#344054] truncate">{layer.name}</span>
                      <span className="text-[10px] text-[#98a2b3] shrink-0">{instanceCount} obj</span>
                    </button>
                    <div className="flex items-center gap-1 shrink-0">
                      <button
                        type="button"
                        onClick={() => moveSelectedLayerQuick(layer.id, 'up')}
                        disabled={!canMoveUp}
                        className={`h-7 w-7 rounded-md border flex items-center justify-center transition-colors ${
                          canMoveUp
                            ? 'border-[#d0d5dd] text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
                            : 'border-[#e4e7ec] text-[#d0d5dd] cursor-not-allowed'
                        }`}
                        title="Move layer up"
                      >
                        <ChevronUp size={13} />
                      </button>
                      <button
                        type="button"
                        onClick={() => moveSelectedLayerQuick(layer.id, 'down')}
                        disabled={!canMoveDown}
                        className={`h-7 w-7 rounded-md border flex items-center justify-center transition-colors ${
                          canMoveDown
                            ? 'border-[#d0d5dd] text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
                            : 'border-[#e4e7ec] text-[#d0d5dd] cursor-not-allowed'
                        }`}
                        title="Move layer down"
                      >
                        <ChevronUp size={13} className="rotate-180" />
                      </button>
                    </div>
                  </div>
                );
              })}
            </div>
          </div>
        </div>
      )}

      {isMobile && (
        <>
          {anyMobileOverlayOpen && (
            <button
              type="button"
              onClick={closeAllPanels}
              className="absolute inset-0 z-[9] bg-[#344054]/8"
              aria-label="Close panels overlay"
            />
          )}

          {mobileContextMenu && (
            <>
              <button
                type="button"
                className="absolute inset-0 z-[22] bg-transparent"
                onClick={closeMobileContextMenu}
                aria-label="Close actions menu"
              />
              <div
                className="absolute z-[23] pointer-events-none"
                style={{ left: `${mobileContextMenu.x}px`, top: `${mobileContextMenu.y}px` }}
              >
                <div className="pointer-events-auto -translate-x-1/2 -translate-y-full mb-2 bg-[#f8fafc] border border-[#e4e7ec] rounded-[12px] shadow-[0_12px_24px_rgba(52,64,84,0.14)] p-1.5">
                  <div className="flex flex-col gap-1">
                    {mobileContextMenu.type === 'actions' && (
                      <>
                        <button
                          type="button"
                          onClick={() => {
                            copyCurrentSelection();
                            closeMobileContextMenu();
                          }}
                          className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#344054] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                        >
                          <Copy size={14} />
                          Copy
                        </button>
                        <button
                          type="button"
                          onClick={() => {
                            cutCurrentSelection();
                            closeMobileContextMenu();
                          }}
                          className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#b42318] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                        >
                          <Scissors size={14} />
                          Cut
                        </button>
                        <button
                          type="button"
                          onClick={() => {
                            duplicateCurrentSelection();
                            closeMobileContextMenu();
                          }}
                          className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#344054] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                        >
                          <Plus size={14} />
                          Duplicate
                        </button>
                      </>
                    )}
                    {mobileContextMenu.type === 'paste' && (
                      <button
                        type="button"
                        onClick={handleMobileContextPaste}
                        className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#344054] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                      >
                        <ClipboardPaste size={14} />
                        Paste
                      </button>
                    )}
                  </div>
                </div>
              </div>
            </>
          )}

          <div
            className="absolute left-2 right-2 z-20 pointer-events-none flex flex-wrap items-center justify-between gap-2"
            style={{ top: mobileTopInset }}
          >
            <div className="pointer-events-auto h-11 bg-[#f8fafc] rounded-[16px] shadow-lg border border-[#e4e7ec] px-2 flex items-center gap-1 max-w-full">
              <button
                type="button"
                onClick={handleMobileUndo}
                onPointerUp={clearTapFocus}
                onPointerCancel={clearTapFocus}
                onTouchEnd={clearTapFocus}
                onMouseUp={clearTapFocus}
                className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                title="Undo"
              >
                <RefreshCw size={13} className="-scale-x-100" />
              </button>
              <button
                type="button"
                onClick={handleMobileRedo}
                onPointerUp={clearTapFocus}
                onPointerCancel={clearTapFocus}
                onTouchEnd={clearTapFocus}
                onMouseUp={clearTapFocus}
                className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                title="Redo"
              >
                <RefreshCw size={13} />
              </button>
            </div>
            <div className="pointer-events-auto h-11 bg-[#f8fafc] rounded-[16px] shadow-lg border border-[#e4e7ec] px-1.5 flex items-center gap-1.5 max-w-full">
              <button
                type="button"
                onClick={resetZoomToHundred}
                onPointerUp={clearTapFocus}
                onPointerCancel={clearTapFocus}
                onTouchEnd={clearTapFocus}
                onMouseUp={clearTapFocus}
                className="h-8 min-w-[52px] px-2.5 rounded-[8px] border border-transparent flex items-center justify-center text-[12px] leading-none font-semibold font-mono text-[#667085] bg-transparent active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                title="Reset zoom to 100%"
              >
                {Math.round(zoom * 100)}%
              </button>
              <div className="flex items-center gap-0.5">
                <button
                  type="button"
                  onClick={handleMobileZoomOut}
                  onPointerUp={clearTapFocus}
                  onPointerCancel={clearTapFocus}
                  onTouchEnd={clearTapFocus}
                  onMouseUp={clearTapFocus}
                  className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                  title="Zoom Out"
                >
                  <Minus size={13} />
                </button>
                <button
                  type="button"
                  onClick={handleMobileZoomIn}
                  onPointerUp={clearTapFocus}
                  onPointerCancel={clearTapFocus}
                  onTouchEnd={clearTapFocus}
                  onMouseUp={clearTapFocus}
                  className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                  title="Zoom In"
                >
                  <Plus size={13} />
                </button>
              </div>
            </div>
          </div>

          <div
            className="absolute left-1/2 -translate-x-1/2 z-20 pointer-events-none"
            style={{ ...mobileToolbarSharedWidthStyle, bottom: mobileMenuDrawerBottom }}
          >
            <div
              className={`pointer-events-auto w-full rounded-[16px] shadow-[0_12px_28px_rgba(52,64,84,0.14)] mobile-drawer ${
                mobileToolsOpen ? 'mobile-drawer-open' : 'mobile-drawer-closed'
              }`}
            >
              <div className="bg-[#f8fafc] rounded-[16px] border border-[#e4e7ec] p-1.5 max-h-[44vh] overflow-y-auto overflow-x-hidden">
                <div className="grid grid-cols-4 gap-1">
                  <MobileToolButton active={showNodes} onClick={() => setShowNodes(prev => !prev)} icon={<CircleDot size={14} />} label="Nodes" />
                  <MobileToolButton
                    active={showBackgroundAids}
                    onClick={() => setShowBackgroundAids(prev => !prev)}
                    icon={showBackgroundAids ? <Eye size={14} /> : <EyeOff size={14} />}
                    label={showBackgroundAids ? "Hide Background Aids" : "Show Background Aids"}
                  />
                  <MobileToolButton
                    active={fillToggleActive}
                    onClick={() => applyPathStyle({ fillEnabled: !fillToggleActive })}
                    icon={<Droplet size={14} />}
                    label="Fill"
                  />
                  <MobileToolButton
                    active={openPanels.stroke}
                    onClick={() => {
                      openMobilePanel('stroke');
                    }}
                    icon={<Minus size={14} />}
                    label="Stroke"
                  />
                  <MobileToolButton onClick={correctPathDirections} icon={<RefreshCw size={14} />} label="Reverse" />
                  <MobileToolButton
                    onClick={() => {
                      fileInputRef.current?.click();
                      openMobilePanel('image');
                    }}
                    icon={<ImageIcon size={14} />}
                    label="Image"
                  />
                  <MobileToolButton
                    onClick={() => {
                      closeAllPanels();
                      insertTextFromPrompt();
                    }}
                    icon={<Type size={14} />}
                    label="Text"
                  />
                  <MobileToolButton
                    active={openPanels.grid}
                    onClick={() => {
                      openMobilePanel('grid');
                    }}
                    icon={<Grid size={14} />}
                    label="Grid"
                  />
                  <MobileToolButton
                    active={openPanels.layers}
                    onClick={() => {
                      openMobilePanel('layers');
                    }}
                    icon={<Layers size={14} />}
                    label="Layers"
                  />
                  <MobileToolButton
                    active={openPanels.export}
                    onClick={() => {
                      openMobilePanel('export');
                    }}
                    icon={<Download size={14} />}
                    label="Export"
                  />
                  <MobileToolButton onClick={clearCanvas} icon={<Trash2 size={14} />} label="Clear" />
                </div>
              </div>
            </div>
          </div>

          {mobileShapePanelOpen && (
            <div
              className="absolute left-1/2 -translate-x-1/2 z-[21] pointer-events-none w-max max-w-[calc(100vw-16px)]"
              style={{ bottom: mobileShapePanelBottom }}
            >
              <div className="pointer-events-auto rounded-[16px] shadow-[0_12px_28px_rgba(52,64,84,0.14)] w-max max-w-[calc(100vw-16px)]">
                <div className="bg-[#f8fafc] rounded-[16px] border border-[#e4e7ec] p-1 overflow-hidden">
                  <div className="flex items-center gap-0.5 overflow-x-auto">
                    <MobileToolButton active={shapeType === 'rectangle'} onClick={() => selectMobileShape('rectangle')} icon={<Square size={14} />} label="Rect" />
                    <MobileToolButton active={shapeType === 'ellipse'} onClick={() => selectMobileShape('ellipse')} icon={<Circle size={14} />} label="Ellipse" />
                    <MobileToolButton active={shapeType === 'polygon'} onClick={() => selectMobileShape('polygon')} icon={<Triangle size={14} />} label="Poly" />
                    <MobileToolButton active={shapeType === 'star'} onClick={() => selectMobileShape('star')} icon={<Star size={14} />} label="Star" />
                    <MobileToolButton active={shapeType === 'line'} onClick={() => selectMobileShape('line')} icon={<Minus size={14} />} label="Line" />
                  </div>
                </div>
              </div>
            </div>
          )}

          <div
            className="absolute left-1/2 -translate-x-1/2 z-20 pointer-events-none w-max max-w-[calc(100vw-16px)]"
            style={{ bottom: mobileToolbarBottom }}
          >
            <div ref={mobileToolbarShellRef} className="pointer-events-auto bg-[#f8fafc] rounded-[16px] shadow-lg border border-[#e4e7ec] p-[6px] w-max max-w-[calc(100vw-16px)]">
              <div className="flex items-center gap-1 overflow-x-auto">
                <MobileToolButton
                  variant="toolbar"
                  radiusClass="rounded-[8px]"
                  active={false}
                  onClick={toggleMobileToolsMenu}
                  icon={<Menu size={16} />}
                  label="Menu"
                />
                <div className="mx-2 h-7 w-px bg-[#d0d5dd] shrink-0" />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'edit'} onClick={() => changeMode('edit')} icon={<MousePointer2 size={16} />} label="Edit" />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'draw'} onClick={() => changeMode('draw')} icon={<PenTool size={16} />} label="Path" />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'pencil'} onClick={() => changeMode('pencil')} icon={<Pencil size={16} />} label="Pencil" />
                <MobileToolButton
                  variant="toolbar"
                  radiusClass="rounded-[8px]"
                  active={mode === 'shape'}
                  onClick={toggleMobileShapePanel}
                  icon={getShapeToolIcon(16)}
                  label="Shape"
                />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'pan'} onClick={() => changeMode('pan')} icon={<Hand size={16} />} label="Pan" />
                <MobileToolButton
                  variant="toolbar"
                  radiusClass="rounded-[8px]"
                  active={hasActiveSelection}
                  onClick={deleteSelectedItems}
                  icon={<Trash2 size={16} />}
                  label="Delete"
                />
              </div>
            </div>
          </div>
        </>
      )}

      {/* Right-Side Panels Container */}
      <div
        className={`absolute flex flex-col gap-2 z-[30] pointer-events-none ${
          isMobile
            ? `top-14 left-2 right-2 max-h-[56vh] overflow-y-visible overflow-x-visible pb-1 items-stretch mobile-panels-wrap ${
                mobilePanelsOpen || anyPanelOpen ? 'mobile-panels-open' : 'mobile-panels-closed'
              }`
            : 'top-8 right-8 items-end'
        }`}
      >
        {PANELS_CONFIG.map(panel => {
          if (!openPanels[panel.id]) return null;
          const isExpanded = expandedPanel === panel.id;
          return (
            <div
              key={panel.id}
              className={`bg-[#f8fafc] rounded-2xl shadow-[0_14px_28px_rgba(52,64,84,0.14)] border border-[#e4e7ec] overflow-hidden flex flex-col pointer-events-auto shrink-0 transition-all duration-300 ${
                isMobile ? 'w-full' : 'w-60'
              }`}
            >
              <div 
                className={`flex items-center justify-between px-3 py-2.5 cursor-pointer hover:bg-[#f2f4f7] transition-colors rounded-t-2xl ${!isExpanded ? 'rounded-b-2xl' : 'border-b border-[#e4e7ec] bg-[#f2f4f7]'}`}
                onClick={() => {
                  setExpandedPanel(isExpanded ? null : panel.id);
                }}
              >
                <h3 className="text-[10px] font-bold text-[#667085] uppercase tracking-widest select-none">{panel.title}</h3>
                <button 
                  onClick={(e) => { e.stopPropagation(); setOpenPanels(p => ({...p, [panel.id]: false})); if(expandedPanel===panel.id) setExpandedPanel(null); }}
                  className="p-1 -mr-1 hover:bg-[#eaecf0] rounded text-[#667085] hover:text-[#344054] transition-colors"
                  title="Close Panel"
                >
                  <X size={14} />
                </button>
              </div>
              
              {isExpanded && (
                <div className="flex flex-col">
                  {panel.id === 'grid' && (
                    <div className="p-3.5 flex flex-col gap-3">
                      <div className="flex flex-col gap-3">
                        <div className="grid grid-cols-3 gap-2 bg-[#f2f4f7] p-1.5 rounded-lg">
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'none' ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'none'})}
                           >None</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'dots' ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'dots'})}
                           >Dots</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'lines' ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'lines'})}
                           >Grid</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'circular' ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'circular'})}
                           >Circular</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'circles' ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'circles'})}
                           >Circles</button>
                        </div>

                        {gridConfig.type === 'lines' && (
                          <div className="flex flex-col gap-2 mt-1">
                            <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest px-1">Grid Shape (Edges)</label>
                            <div className="flex gap-2 bg-[#f2f4f7] p-1.5 rounded-lg">
                               <button
                                  className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 3 ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                                  onClick={() => setGridConfig({...gridConfig, edges: 3})}
                               >3 (Tri)</button>
                               <button
                                  className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 4 ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                                  onClick={() => setGridConfig({...gridConfig, edges: 4})}
                               >4 (Sqr)</button>
                               <button
                                  className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 6 ? 'bg-white shadow-sm text-[#344054]' : 'text-[#667085] hover:text-[#344054]'}`}
                                  onClick={() => setGridConfig({...gridConfig, edges: 6})}
                               >6 (Hex)</button>
                            </div>
                          </div>
                        )}

                        {gridConfig.type !== 'none' && (
                          <div className="flex flex-col gap-2 mt-1">
                            <div className="grid grid-cols-[1fr_88px] items-center gap-2">
                              <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest px-1">Grid Density</label>
                              <ScrubbableNumberInput
                                value={effectiveGridSize}
                                min={MIN_GRID_SIZE}
                                max={MAX_GRID_SIZE}
                                step={1}
                                suffix="px"
                                onChange={(next) => {
                                  const clamped = Math.max(MIN_GRID_SIZE, Math.min(MAX_GRID_SIZE, Number(next) || GRID_SIZE));
                                  setGridConfig(prev => ({ ...prev, size: clamped }));
                                }}
                              />
                            </div>
                            {gridConfig.type === 'circular' && (
                              <div className="grid grid-cols-[1fr_88px] items-center gap-2">
                                <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest px-1">Angle Step</label>
                                <ScrubbableNumberInput
                                  value={effectiveCircularStep}
                                  min={MIN_CIRCULAR_STEP}
                                  max={MAX_CIRCULAR_STEP}
                                  step={1}
                                  suffix="deg"
                                  onChange={(next) => {
                                    const clamped = Math.max(
                                      MIN_CIRCULAR_STEP,
                                      Math.min(MAX_CIRCULAR_STEP, Number(next) || DEFAULT_CIRCULAR_STEP)
                                    );
                                    setGridConfig(prev => ({ ...prev, circularStep: clamped }));
                                  }}
                                />
                              </div>
                            )}
                          </div>
                        )}
                        
                        <div className="flex items-center justify-between mt-2 pt-3 border-t border-[#e4e7ec]">
                           <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest px-1">Snap to Grid</label>
                           <button
                               onClick={() => setGridConfig({...gridConfig, snapToGrid: !gridConfig.snapToGrid})}
                               className={`relative inline-flex h-4 w-7 items-center rounded-full transition-colors focus:outline-none ${gridConfig.snapToGrid ? 'bg-[#344054]' : 'bg-[#d0d5dd]'}`}
                           >
                               <span className={`inline-block h-3 w-3 transform rounded-full bg-white transition-transform ${gridConfig.snapToGrid ? 'translate-x-3.5' : 'translate-x-0.5'}`} />
                           </button>
                        </div>
                      </div>
                    </div>
                  )}

                  {panel.id === 'image' && (
                    <div className="p-3.5 flex flex-col gap-2">
                      <button
                        onClick={() => fileInputRef.current?.click()}
                        className="flex items-center justify-center gap-2 py-2 bg-[#f2f4f7] hover:bg-[#eaecf0] text-[#344054] rounded-lg text-xs font-semibold transition-colors border border-[#d0d5dd]"
                      >
                        <ImageIcon size={14} />
                        Upload Image
                      </button>

                      {activeImage && (
                        <div className="flex flex-col gap-2 mt-2 pt-2 border-t border-[#e4e7ec]">
                          <div className="flex items-center justify-between px-1 mb-1">
                            <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest">Image Transform</label>
                            <div className="flex items-center gap-1">
                               <button
                                 onClick={() => updateActiveImage({ locked: !activeImage.locked })}
                                 className={`p-1 rounded transition-colors ${activeImage.locked ? 'bg-[#eaecf0] text-[#344054]' : 'text-[#667085] hover:text-[#344054] hover:bg-[#eaecf0]'}`}
                                 title={activeImage.locked ? "Unlock Image" : "Lock Image"}
                               >
                                 {activeImage.locked ? <Lock size={12} /> : <Unlock size={12} />}
                               </button>
                            </div>
                          </div>

                          <div className="grid grid-cols-2 gap-2 mt-1">
                            <ConfigInput
                              label="X"
                              value={activeImage.x}
                              onChange={v => updateActiveImage({ x: v })}
                            />
                            <ConfigInput
                              label="Y"
                              value={activeImage.y}
                              onChange={v => updateActiveImage({ y: v })}
                            />
                            <ConfigInput
                              icon={<Ruler size={14} />}
                              value={activeImage.scale}
                              scaleFactor={100}
                              suffix="%"
                              onChange={v => updateActiveImage({ scale: Math.max(0.01, v) })}
                            />
                            <ConfigInput
                              icon={<RefreshCw size={14} />}
                              value={activeImage.rotation}
                              suffix="°"
                              onChange={v => updateActiveImage({ rotation: v })}
                            />
                            <div className="col-span-1">
                              <ConfigInput
                                icon={<Droplet size={14} />}
                                value={activeImage.opacity}
                                scaleFactor={100}
                                suffix="%"
                                onChange={v => updateActiveImage({ opacity: Math.max(0, Math.min(1, v)) })}
                              />
                            </div>
                          </div>
                        </div>
                      )}
                    </div>
                  )}

                  {panel.id === 'stroke' && (
                    <div className="p-3.5 flex flex-col gap-3">
                      <div className="flex items-center justify-between px-1 pb-2 border-b border-[#e4e7ec]">
                        <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest">Enable Stroke</label>
                        <button
                          onClick={() => applyPathStyle({ strokeEnabled: !strokeToggleActive })}
                          className={`relative inline-flex h-4 w-7 items-center rounded-full transition-colors focus:outline-none ${strokeToggleActive ? 'bg-[#344054]' : 'bg-[#d0d5dd]'}`}
                          title={strokeToggleActive ? 'Disable Stroke' : 'Enable Stroke'}
                        >
                          <span className={`inline-block h-3 w-3 transform rounded-full bg-white transition-transform ${strokeToggleActive ? 'translate-x-3.5' : 'translate-x-0.5'}`} />
                        </button>
                      </div>

                      <div className="grid grid-cols-[1fr_88px] gap-2">
                        <div className="h-8 flex items-center gap-2 bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all">
                          <input
                            type="color"
                            value={strokePanelStyle.strokeColor}
                            onChange={(e) => {
                              const next = normalizeStrokeColor(e.target.value, strokePanelStyle.strokeColor);
                              setStrokeColorInput(next.replace('#', ''));
                              applyPathStyle({ strokeColor: next, strokeEnabled: true });
                            }}
                            className="h-5 w-5 p-0 border border-[#d0d5dd] rounded cursor-pointer bg-transparent"
                            title="Stroke Color"
                          />
                          <input
                            type="text"
                            value={strokeColorInput}
                            onChange={(e) => handleStrokeColorInputChange(e.target.value)}
                            onBlur={commitStrokeColorInput}
                            onKeyDown={(e) => {
                              if (e.key === 'Enter') {
                                e.preventDefault();
                                commitStrokeColorInput();
                                e.currentTarget.blur();
                              }
                            }}
                            className="flex-1 min-w-0 text-xs text-left bg-transparent border-none outline-none py-1 text-[#344054] font-mono uppercase"
                            placeholder="4A2622"
                            maxLength={6}
                          />
                        </div>
                        <div className="h-8 flex items-center gap-1 bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all">
                          <input
                            type="text"
                            value={strokeWidthInput}
                            onChange={(e) => handleStrokeWidthInputChange(e.target.value)}
                            onBlur={commitStrokeWidthInput}
                            onKeyDown={(e) => {
                              if (e.key === 'Enter') {
                                e.preventDefault();
                                commitStrokeWidthInput();
                                e.currentTarget.blur();
                              }
                            }}
                            className="flex-1 min-w-0 text-xs text-right bg-transparent border-none outline-none py-1 text-[#344054] font-mono"
                            placeholder="1.5"
                          />
                          <span className="text-xs text-[#667085] font-mono select-none">px</span>
                        </div>
                      </div>

                      <div className="grid grid-cols-[1fr] gap-2">
                        <select
                          value={strokePanelStyle.strokeAlign}
                          onChange={(e) => applyPathStyle({ strokeAlign: e.target.value })}
                          className="h-8 bg-[#f2f4f7] rounded-md border border-transparent px-2 text-xs text-[#344054] focus:outline-none focus:ring-1 focus:ring-[#d0d5dd]"
                        >
                          <option value="center">Center</option>
                          <option value="inside">Inside</option>
                          <option value="outside">Outside</option>
                        </select>
                      </div>
                    </div>
                  )}

                  {panel.id === 'layers' && (
                    <div className={`p-3 flex flex-col gap-2 min-h-0 flex-1 ${isMobile ? 'max-h-[36vh]' : 'max-h-[60vh]'}`}>
                      <div className="flex-1 overflow-y-auto flex flex-col gap-1 pr-1" style={{ touchAction: 'pan-y' }}>
                        {layers.map(layer => {
                          const isSelected = selectedLayerIds.has(layer.id);
                          return (
                            <div className="relative" key={layer.id}>
                                {dragDropTarget?.id === layer.id && dragDropTarget.position === 'top' && (
                                   <div className="absolute top-[-2px] left-0 right-0 h-[2px] bg-[#344054] z-10 rounded-full" />
                                )}
                                <div 
                                    draggable={!isMobile && editingLayerId !== layer.id}
                                    onDragStart={(e) => handleLayerDragStart(e, layer.id)}
                                    onDragOver={(e) => handleLayerDragOver(e, layer.id)}
                                    onDrop={(e) => handleLayerDrop(e, layer.id)}
                                    onDragEnd={handleLayerDragEnd}
                                    className={`flex items-center justify-between p-2 rounded-xl border transition-all cursor-pointer ${
                                      isSelected 
                                        ? 'bg-[#eaecf0] border-[#d0d5dd] shadow-sm text-[#344054]' 
                                        : 'bg-[#f8fafc] border-transparent hover:bg-[#f5f8fc] hover:border-[#e4e7ec] text-[#667085]'
                                    } ${draggedLayerId === layer.id ? 'opacity-50' : ''}`}
                                    onClick={(e) => handleLayerSelect(e, layer)}
                                >
                                    <div className="flex items-center gap-1.5 flex-1 min-w-0">
                                      <div className="cursor-grab active:cursor-grabbing opacity-50 hover:opacity-100 p-1 -ml-1">
                                        <GripVertical size={14} />
                                      </div>
                                      <LayerIcon type={layer.itemType} />
                                      {editingLayerId === layer.id ? (
                                        <input
                                          type="text"
                                          value={editingLayerName}
                                          onChange={(e) => setEditingLayerName(e.target.value)}
                                          onBlur={saveLayerName}
                                          onKeyDown={handleLayerNameKeyDown}
                                          autoFocus
                                          onFocus={(e) => e.target.select()}
                                          onClick={(e) => e.stopPropagation()}
                                          onPointerDown={(e) => e.stopPropagation()}
                                          onMouseDown={(e) => e.stopPropagation()}
                                          className="text-xs font-semibold text-[#344054] bg-white border border-[#344054] rounded px-1 outline-none w-24 py-0.5 select-text cursor-text ml-1"
                                        />
                                      ) : (
                                        <span 
                                          onDoubleClick={(e) => { e.stopPropagation(); startEditingLayer(layer); }}
                                          title="Double-click to rename"
                                          className={`text-xs font-semibold select-none ml-1 truncate ${layer.visible ? (layer.locked ? 'opacity-60' : 'opacity-100') : 'opacity-50'} hover:opacity-100 transition-opacity`}
                                        >
                                          {layer.name}
                                        </span>
                                      )}
                                    </div>
                                    
                                    <div className="flex items-center gap-0.5 shrink-0 ml-2">
                                      <button 
                                        onClick={(e) => { e.stopPropagation(); toggleLayerVisibility(layer.id); }}
                                        className={`p-1.5 rounded-md hover:bg-[#e4e7ec]/50 transition-colors ${layer.visible ? 'opacity-100' : 'opacity-40'}`}
                                        title={layer.visible ? "Hide Layer" : "Show Layer"}
                                      >
                                        {layer.visible ? <Eye size={14} /> : <EyeOff size={14} />}
                                      </button>
                                      <button 
                                        onClick={(e) => { e.stopPropagation(); toggleLayerLock(layer.id); }}
                                        className={`p-1.5 rounded-md hover:bg-[#e4e7ec]/50 transition-colors ${layer.locked ? 'opacity-100' : 'opacity-40'}`}
                                        title={layer.locked ? "Unlock Layer" : "Lock Layer"}
                                      >
                                        {layer.locked ? <Lock size={14} /> : <Unlock size={14} />}
                                      </button>
                                      <button
                                        onClick={(e) => { e.stopPropagation(); deleteLayer(layer.id); }}
                                        className="p-1.5 rounded-md hover:bg-[#fee4e2] text-[#b42318] transition-colors"
                                        title="Delete Layer"
                                      >
                                        <Trash2 size={14} />
                                      </button>
                                    </div>
                                </div>
                                {dragDropTarget?.id === layer.id && dragDropTarget.position === 'bottom' && (
                                   <div className="absolute bottom-[-2px] left-0 right-0 h-[2px] bg-[#344054] z-10 rounded-full" />
                                )}
                            </div>
                          )
                        })}
                      </div>
                    </div>
                  )}

                  {panel.id === 'export' && (
                    <div className="p-3.5 flex flex-col gap-3">
                      <div className="grid grid-cols-2 gap-2 bg-[#f2f4f7] p-1.5 rounded-lg">
                        <button
                          onClick={() => setMobileExportScope('selection')}
                          className={`py-1.5 text-xs font-semibold rounded-md transition-all ${
                            mobileExportScope === 'selection'
                              ? 'bg-white shadow-sm text-[#344054]'
                              : 'text-[#667085] hover:text-[#344054]'
                          }`}
                        >
                          Selection
                        </button>
                        <button
                          onClick={() => setMobileExportScope('canvas')}
                          className={`py-1.5 text-xs font-semibold rounded-md transition-all ${
                            mobileExportScope === 'canvas'
                              ? 'bg-white shadow-sm text-[#344054]'
                              : 'text-[#667085] hover:text-[#344054]'
                          }`}
                        >
                          Canvas
                        </button>
                      </div>

                      <div className="grid grid-cols-3 gap-2 bg-[#f2f4f7] p-1.5 rounded-lg">
                        {['png', 'jpg', 'svg'].map(format => (
                          <button
                            key={format}
                            onClick={() => setMobileExportFormat(format)}
                            className={`py-1.5 text-xs font-semibold uppercase rounded-md transition-all ${
                              mobileExportFormat === format
                                ? 'bg-white shadow-sm text-[#344054]'
                                : 'text-[#667085] hover:text-[#344054]'
                            }`}
                          >
                            {format}
                          </button>
                        ))}
                      </div>

                      {mobileExportScope === 'selection' && !canExportSelection && (
                        <p className="text-[10px] text-[#98a2b3] px-1">
                          Select one or more objects to export selection.
                        </p>
                      )}

                      <button
                        type="button"
                        onClick={handleExport}
                        disabled={isExporting || (mobileExportScope === 'selection' && !canExportSelection)}
                        className={`h-9 rounded-lg border text-xs font-semibold transition-colors flex items-center justify-center gap-2 ${
                          isExporting || (mobileExportScope === 'selection' && !canExportSelection)
                            ? 'bg-[#ecf1f7] border-[#d7dee8] text-[#98a2b3] cursor-not-allowed'
                            : 'bg-[#f2f4f7] border-[#d0d5dd] text-[#344054] hover:bg-[#eaecf0]'
                        }`}
                      >
                        <Download size={14} />
                        {isExporting ? 'Exporting…' : `Export ${mobileExportFormat.toUpperCase()}`}
                      </button>
                    </div>
                  )}
                </div>
              )}
            </div>
          );
        })}
      </div>

      {/* Bottom Toolbar (Desktop Tools) */}
      {!isMobile && <DesktopToolbar />}

    </div>
    </EditorProvider>
  );
}
