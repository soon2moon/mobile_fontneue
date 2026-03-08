import React, { useState, useRef, useEffect, useCallback } from 'react';
import { 
  PenTool, 
  Pencil,
  MousePointer2, 
  Hand, 
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
  ChevronUp
} from 'lucide-react';

// --- THEME ---
const THEME = {
  main: "#4a2622",
  nodeFill: "#e4cfcc",
  bg: "#f4f1ed",
  handle: "#7c4a45",
  guide: "#d4c8c5"
};

// --- UTILS ---
const SNAP_RADIUS = 10;
const GRID_SIZE = 50;
const MIN_GRID_SIZE = 5;
const MAX_GRID_SIZE = 200;
const MIN_CIRCULAR_STEP = 1;
const MAX_CIRCULAR_STEP = 180;
const DEFAULT_CIRCULAR_STEP = 30;
const MIN_ZOOM = 0.1;
const MAX_ZOOM = 256; // 25600%
const PIXEL_GRID_MIN_ZOOM = 8; // 800%

const distToSegmentSquared = (p, v, w) => {
  const l2 = (w.x - v.x)**2 + (w.y - v.y)**2;
  if (l2 === 0) return (p.x - v.x)**2 + (p.y - v.y)**2;
  let t = ((p.x - v.x) * (w.x - v.x) + (p.y - v.y) * (w.y - v.y)) / l2;
  t = Math.max(0, Math.min(1, t));
  return (p.x - (v.x + t * (w.x - v.x)))**2 + (p.y - (v.y + t * (w.y - v.y)))**2;
};
const distToSegment = (p, v, w) => Math.sqrt(distToSegmentSquared(p, v, w));

const getBezierPoint = (p0, p1, p2, p3, t) => {
  const u = 1 - t;
  const tt = t * t;
  const uu = u * u;
  const uuu = uu * u;
  const ttt = tt * t;
  return {
    x: uuu * p0.x + 3 * uu * t * p1.x + 3 * u * tt * p2.x + ttt * p3.x,
    y: uuu * p0.y + 3 * uu * t * p1.y + 3 * u * tt * p2.y + ttt * p3.y
  };
};

const distToBezier = (point, p0, p1, p2, p3) => {
  let minDist = Infinity;
  let bestT = 0;
  let prevPoint = p0;
  const steps = 20; 
  for (let i = 1; i <= steps; i++) {
    const tCurr = i / steps;
    const currPoint = getBezierPoint(p0, p1, p2, p3, tCurr);
    
    const l2 = (currPoint.x - prevPoint.x)**2 + (currPoint.y - prevPoint.y)**2;
    let tSeg = 0;
    if (l2 !== 0) {
      tSeg = ((point.x - prevPoint.x) * (currPoint.x - prevPoint.x) + (point.y - prevPoint.y) * (currPoint.y - prevPoint.y)) / l2;
      tSeg = Math.max(0, Math.min(1, tSeg));
    }
    const projX = prevPoint.x + tSeg * (currPoint.x - prevPoint.x);
    const projY = prevPoint.y + tSeg * (currPoint.y - prevPoint.y);
    const d = Math.sqrt((point.x - projX)**2 + (point.y - projY)**2);

    if (d < minDist) {
      minDist = d;
      bestT = (i - 1) / steps + tSeg * (1 / steps);
    }
    prevPoint = currPoint;
  }
  return { dist: minDist, t: bestT };
};

const splitBezier = (p0, p1, p2, p3, t) => {
  const lerp = (a, b, t) => ({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t });
  const isStraight = Math.hypot(p1.x - p0.x, p1.y - p0.y) < 0.1 && Math.hypot(p3.x - p2.x, p3.y - p2.y) < 0.1;
  
  if (isStraight) {
    const b = lerp(p0, p3, t);
    return {
      left: { hOut: p0 },
      right: { hIn: p3 },
      newPoint: { x: b.x, y: b.y, hIn: { ...b }, hOut: { ...b } }
    };
  }

  const q0 = lerp(p0, p1, t);
  const q1 = lerp(p1, p2, t);
  const q2 = lerp(p2, p3, t);
  const r0 = lerp(q0, q1, t);
  const r1 = lerp(q1, q2, t);
  const b = lerp(r0, r1, t);
  
  return {
    left: { hOut: q0 },
    right: { hIn: q2 },
    newPoint: { x: b.x, y: b.y, hIn: r0, hOut: r1 }
  };
};

const reflectPointAcrossPerpBisector = (p, p1, p2) => {
  const m = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
  const dx = p2.x - p1.x;
  const dy = p2.y - p1.y;
  const dotDD = dx * dx + dy * dy;
  if (dotDD === 0) return { ...p };
  const vx = p.x - m.x;
  const vy = p.y - m.y;
  const dotVD = vx * dx + vy * dy;
  return {
    x: p.x - 2 * (dotVD / dotDD) * dx,
    y: p.y - 2 * (dotVD / dotDD) * dy
  };
};

const pointsToPath = (points, isClosed) => {
  if (!points || points.length === 0) return '';
  let d = `M ${points[0].x} ${points[0].y}`;
  
  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cp1 = prev.hOut || { x: prev.x, y: prev.y };
    const cp2 = curr.hIn || { x: curr.x, y: curr.y };
    d += ` C ${cp1.x} ${cp1.y}, ${cp2.x} ${cp2.y}, ${curr.x} ${curr.y}`;
  }
  
  if (isClosed && points.length > 2) {
    const prev = points[points.length - 1];
    const curr = points[0];
    const cp1 = prev.hOut || { x: prev.x, y: prev.y };
    const cp2 = curr.hIn || { x: curr.x, y: curr.y };
    d += ` C ${cp1.x} ${cp1.y}, ${cp2.x} ${cp2.y}, ${curr.x} ${curr.y} Z`;
  }
  return d;
};

const isCorner = (p) => {
  const dIn = p.hIn ? Math.hypot(p.hIn.x - p.x, p.hIn.y - p.y) : 0;
  const dOut = p.hOut ? Math.hypot(p.hOut.x - p.x, p.hOut.y - p.y) : 0;
  return dIn < 0.1 && dOut < 0.1;
};

const applyShiftSnap = (currentCoords, refPoint, shiftKey) => {
  if (!shiftKey || !refPoint) return currentCoords;
  const dx = currentCoords.x - refPoint.x;
  const dy = currentCoords.y - refPoint.y;
  const angle = Math.atan2(dy, dx);
  const snappedAngle = Math.round(angle / (Math.PI / 12)) * (Math.PI / 12);
  const dist = Math.hypot(dx, dy);
  return {
    x: refPoint.x + Math.cos(snappedAngle) * dist,
    y: refPoint.y + Math.sin(snappedAngle) * dist
  };
};

const applyGridSnap = (point, config) => {
  if (!config.snapToGrid) return point;
  if (config.type === 'none') return point;
  const s = Math.max(MIN_GRID_SIZE, Number(config.size) || GRID_SIZE);
  
  if (config.type === 'dots' || (config.type === 'lines' && config.edges === 4)) {
    return {
      x: Math.round(point.x / s) * s,
      y: Math.round(point.y / s) * s
    };
  } else if (config.type === 'lines' && config.edges === 3) {
    const w = s;
    const h = s * Math.sqrt(3);
    const j = Math.round(point.y / (h / 2));
    const offsetX = (Math.abs(j) % 2 === 1) ? w / 2 : 0;
    const i = Math.round((point.x - offsetX) / w);
    return {
      x: i * w + offsetX,
      y: j * (h / 2)
    };
  } else if (config.type === 'lines' && config.edges === 6) {
     const w = s * Math.sqrt(3);
     return {
       x: Math.round(point.x / (w/2)) * (w/2),
       y: Math.round(point.y / (s/2)) * (s/2)
     };
  } else if (config.type === 'circular') {
    const r = Math.hypot(point.x, point.y);
    const angle = Math.atan2(point.y, point.x);
    const snapR = Math.round(r / s) * s;
    const circularStepDeg = Math.max(
      MIN_CIRCULAR_STEP,
      Math.min(MAX_CIRCULAR_STEP, Number(config.circularStep) || DEFAULT_CIRCULAR_STEP)
    );
    const circularStepRad = circularStepDeg * (Math.PI / 180);
    const snapAngle = Math.round(angle / circularStepRad) * circularStepRad;
    return {
      x: snapR * Math.cos(snapAngle),
      y: snapR * Math.sin(snapAngle)
    };
  } else if (config.type === 'circles') {
    const cx = Math.floor(point.x / s) * s + s / 2;
    const cy = Math.floor(point.y / s) * s + s / 2;
    return { x: cx, y: cy };
  }
  return point;
};

const clonePaths = (pathsArray) => {
  return pathsArray.map(p => ({
    ...p,
    points: p.points.map(pt => ({
      ...pt,
      hIn: pt.hIn ? { ...pt.hIn } : undefined,
      hOut: pt.hOut ? { ...pt.hOut } : undefined
    }))
  }));
};

const cloneState = (pathsArray, currentPathArray, imagesArray, layersArray) => ({
  paths: clonePaths(pathsArray),
  currentPath: currentPathArray.map(pt => ({
    ...pt,
    hIn: pt.hIn ? { ...pt.hIn } : undefined,
    hOut: pt.hOut ? { ...pt.hOut } : undefined
  })),
  images: imagesArray ? imagesArray.map(img => ({ ...img })) : [],
  layers: layersArray ? layersArray.map(l => ({ ...l })) : []
});

const copyToClipboard = (text) => {
  const textArea = document.createElement("textarea");
  textArea.value = text;
  textArea.style.top = "0";
  textArea.style.left = "0";
  textArea.style.position = "fixed";
  document.body.appendChild(textArea);
  textArea.focus();
  textArea.select();
  try {
    document.execCommand('copy');
  } catch (err) {
    console.error('Fallback: Oops, unable to copy', err);
  }
  document.body.removeChild(textArea);
};

// --- SHAPE GENERATION HELPER ---
const generateShapePath = (startX, startY, endX, endY, type, shiftKey) => {
  let minX = Math.min(startX, endX);
  let minY = Math.min(startY, endY);
  let maxX = Math.max(startX, endX);
  let maxY = Math.max(startY, endY);
  
  if (shiftKey && type !== 'line') {
      const size = Math.max(maxX - minX, maxY - minY);
      maxX = startX < endX ? startX + size : startX;
      minX = startX < endX ? startX : startX - size;
      maxY = startY < endY ? startY + size : startY;
      minY = startY < endY ? startY : startY - size;
  }

  const w = maxX - minX;
  const h = maxY - minY;
  const cx = minX + w / 2;
  const cy = minY + h / 2;

  if (type === 'rectangle') {
      return {
          isClosed: true,
          points: [
              { x: minX, y: minY, hIn: {x: minX, y: minY}, hOut: {x: minX, y: minY} },
              { x: maxX, y: minY, hIn: {x: maxX, y: minY}, hOut: {x: maxX, y: minY} },
              { x: maxX, y: maxY, hIn: {x: maxX, y: maxY}, hOut: {x: maxX, y: maxY} },
              { x: minX, y: maxY, hIn: {x: minX, y: maxY}, hOut: {x: minX, y: maxY} }
          ]
      };
  }
  if (type === 'ellipse') {
      const rx = w / 2;
      const ry = h / 2;
      const kappa = 0.5522847498;
      const kx = rx * kappa;
      const ky = ry * kappa;
      return {
          isClosed: true,
          points: [
              { x: cx, y: minY, hIn: {x: cx - kx, y: minY}, hOut: {x: cx + kx, y: minY} },
              { x: maxX, y: cy, hIn: {x: maxX, y: cy - ky}, hOut: {x: maxX, y: cy + ky} },
              { x: cx, y: maxY, hIn: {x: cx + kx, y: maxY}, hOut: {x: cx - kx, y: maxY} },
              { x: minX, y: cy, hIn: {x: minX, y: cy + ky}, hOut: {x: minX, y: cy - ky} }
          ]
      };
  }
  if (type === 'line') {
      let p2x = endX;
      let p2y = endY;
      if (shiftKey) {
          const angle = Math.atan2(endY - startY, endX - startX);
          const snappedAngle = Math.round(angle / (Math.PI / 12)) * (Math.PI / 12);
          const dist = Math.hypot(endX - startX, endY - startY);
          p2x = startX + Math.cos(snappedAngle) * dist;
          p2y = startY + Math.sin(snappedAngle) * dist;
      }
      return {
          isClosed: false,
          points: [
              { x: startX, y: startY, hIn: {x: startX, y: startY}, hOut: {x: startX, y: startY} },
              { x: p2x, y: p2y, hIn: {x: p2x, y: p2y}, hOut: {x: p2x, y: p2y} }
          ]
      };
  }
  if (type === 'polygon') {
      return {
          isClosed: true,
          points: [
              { x: cx, y: minY, hIn: {x: cx, y: minY}, hOut: {x: cx, y: minY} },
              { x: maxX, y: maxY, hIn: {x: maxX, y: maxY}, hOut: {x: maxX, y: maxY} },
              { x: minX, y: maxY, hIn: {x: minX, y: maxY}, hOut: {x: minX, y: maxY} }
          ]
      };
  }
  if (type === 'star') {
      const points = [];
      const outerRadius = Math.min(w, h) / 2;
      const innerRadius = outerRadius * 0.382;
      for (let i = 0; i < 10; i++) {
          const radius = i % 2 === 0 ? outerRadius : innerRadius;
          const angle = (i * Math.PI) / 5 - Math.PI / 2;
          const px = cx + Math.cos(angle) * radius;
          const py = cy + Math.sin(angle) * radius;
          points.push({ x: px, y: py, hIn: {x: px, y: py}, hOut: {x: px, y: py} });
      }
      return { isClosed: true, points };
  }
  return { isClosed: false, points: [] };
};

// --- LAYER HELPER ---
const generateLayerId = () => `layer-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

const createLayer = (type, existingCount) => {
   let name = "Vector";
   if (type === 'image') name = "Image";
   else if (type === 'rectangle') name = "Rectangle";
   else if (type === 'ellipse') name = "Ellipse";
   else if (type === 'polygon') name = "Polygon";
   else if (type === 'star') name = "Star";
   else if (type === 'line') name = "Line";

   return {
       id: generateLayerId(),
       name: `${name} ${existingCount + 1}`,
       visible: true,
       locked: false,
       itemType: type || 'vector'
   };
};

const LayerIcon = ({ type }) => {
    switch(type) {
        case 'rectangle': return <Square size={14} className="text-[#8c746f]" />;
        case 'ellipse': return <Circle size={14} className="text-[#8c746f]" />;
        case 'polygon': return <Triangle size={14} className="text-[#8c746f]" />;
        case 'star': return <Star size={14} className="text-[#8c746f]" />;
        case 'line': return <Minus size={14} className="text-[#8c746f]" />;
        case 'image': return <ImageIcon size={14} className="text-[#8c746f]" />;
        case 'vector':
        default: 
            return <PenTool size={14} className="text-[#8c746f]" />;
    }
};

// --- UI COMPONENTS ---
const ConfigInput = ({ icon, label, value, onChange, suffix = "", scaleFactor = 1, ...props }) => {
  const displayValue = Number((value * scaleFactor).toFixed(2));
  const [focused, setFocused] = useState(false);
  const [tempVal, setTempVal] = useState(displayValue.toString());

  useEffect(() => {
    if (!focused) setTempVal(displayValue.toString());
  }, [displayValue, focused]);

  return (
    <div className="flex items-center bg-[#f4f1ed] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d4c8c5] transition-all overflow-hidden h-8 gap-2">
      {icon ? (
        <span className="flex items-center justify-center text-[#a89b99] w-3.5 shrink-0">
          {icon}
        </span>
      ) : label ? (
        <span className="text-xs font-medium text-[#a89b99] w-3.5 shrink-0 select-none flex items-center justify-center">
          {label}
        </span>
      ) : null}
      <input
        type="text"
        value={focused ? tempVal : `${tempVal}${suffix}`}
        onFocus={() => {
           setFocused(true);
           setTempVal(displayValue.toString());
        }}
        onBlur={() => {
           setFocused(false);
           let parsed = parseFloat(tempVal.replace(/[^0-9.-]/g, ''));
           if (isNaN(parsed)) parsed = 0;
           onChange(parsed / scaleFactor);
           setTempVal(parsed.toString());
        }}
        onChange={e => {
           setTempVal(e.target.value);
           let parsed = parseFloat(e.target.value.replace(/[^0-9.-]/g, ''));
           if (!isNaN(parsed)) {
             onChange(parsed / scaleFactor);
           }
        }}
        className="w-full text-xs text-left bg-transparent border-none outline-none py-1 text-[#4a2622] font-mono"
        {...props}
      />
    </div>
  );
};

const ScrubbableNumberInput = ({
  value,
  onChange,
  min = -Infinity,
  max = Infinity,
  step = 1,
  suffix = ""
}) => {
  const sanitizedValue = Number.isFinite(value) ? value : 0;
  const [focused, setFocused] = useState(false);
  const [tempVal, setTempVal] = useState(String(Math.round(sanitizedValue)));
  const scrubRef = useRef({
    active: false,
    pointerId: null,
    startX: 0,
    startValue: 0,
    moved: false
  });

  const clamp = useCallback((v) => Math.min(max, Math.max(min, v)), [min, max]);

  useEffect(() => {
    if (!focused && !scrubRef.current.active) {
      setTempVal(String(Math.round(sanitizedValue)));
    }
  }, [sanitizedValue, focused]);

  useEffect(() => {
    return () => {
      if (scrubRef.current.active) {
        document.body.style.userSelect = '';
        document.body.style.cursor = '';
      }
    };
  }, []);

  const commitValue = useCallback((rawValue) => {
    let parsed = Number(rawValue);
    if (!Number.isFinite(parsed)) parsed = sanitizedValue;
    parsed = clamp(parsed);
    onChange(parsed);
    setTempVal(String(Math.round(parsed)));
  }, [clamp, onChange, sanitizedValue]);

  const startScrub = (e) => {
    if (e.button !== 0) return;
    scrubRef.current = {
      active: true,
      pointerId: e.pointerId,
      startX: e.clientX,
      startValue: sanitizedValue,
      moved: false
    };
    if (e.currentTarget.setPointerCapture) {
      e.currentTarget.setPointerCapture(e.pointerId);
    }
    document.body.style.userSelect = 'none';
    document.body.style.cursor = 'ew-resize';
  };

  const moveScrub = (e) => {
    if (!scrubRef.current.active) return;
    const deltaX = e.clientX - scrubRef.current.startX;
    if (Math.abs(deltaX) >= 2) scrubRef.current.moved = true;
    const multiplier = e.shiftKey ? 0.2 : 1;
    const steppedDelta = (deltaX * multiplier) / step;
    const next = clamp(Math.round((scrubRef.current.startValue + steppedDelta * step) / step) * step);
    onChange(next);
    setTempVal(String(Math.round(next)));
    e.preventDefault();
  };

  const endScrub = (e) => {
    if (!scrubRef.current.active) return;
    const moved = scrubRef.current.moved;
    scrubRef.current.active = false;
    scrubRef.current.pointerId = null;
    document.body.style.userSelect = '';
    document.body.style.cursor = '';

    if (e.currentTarget.hasPointerCapture && e.currentTarget.hasPointerCapture(e.pointerId)) {
      e.currentTarget.releasePointerCapture(e.pointerId);
    }

    if (moved) {
      setFocused(false);
      if (document.activeElement === e.currentTarget) {
        e.currentTarget.blur();
      }
      e.preventDefault();
    }
  };

  return (
    <div className="flex items-center gap-1 bg-[#f4f1ed] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d4c8c5] transition-all overflow-hidden h-8">
      <input
        type="text"
        value={focused ? tempVal : String(Math.round(sanitizedValue))}
        onFocus={() => {
          setFocused(true);
          setTempVal(String(Math.round(sanitizedValue)));
        }}
        onBlur={() => {
          setFocused(false);
          commitValue(tempVal.replace(/[^0-9.-]/g, ''));
        }}
        onChange={(e) => {
          setTempVal(e.target.value);
          const parsed = parseFloat(e.target.value.replace(/[^0-9.-]/g, ''));
          if (!Number.isNaN(parsed)) {
            onChange(clamp(parsed));
          }
        }}
        onPointerDown={startScrub}
        onPointerMove={moveScrub}
        onPointerUp={endScrub}
        onPointerCancel={endScrub}
        className={`flex-1 min-w-0 text-xs text-left bg-transparent border-none outline-none py-1 text-[#4a2622] font-mono ${focused ? 'cursor-text' : 'cursor-ew-resize'}`}
      />
      {suffix && (
        <span className="shrink-0 text-xs text-[#8c746f] font-mono pointer-events-none select-none">
          {suffix}
        </span>
      )}
    </div>
  );
};

const PANELS_CONFIG = [
  { id: 'layers', title: 'Layers' },
  { id: 'image', title: 'Image Settings' },
  { id: 'grid', title: 'Background Config' },
  { id: 'guides', title: 'Guides Config' }
];

// --- MAIN APP COMPONENT ---
export default function App() {
  // Canvas State
  const [pan, setPan] = useState({ x: window.innerWidth / 2, y: window.innerHeight / 2 });
  const [zoom, setZoom] = useState(1);
  const [isPanning, setIsPanning] = useState(false);
  const panRef = useRef({ x: window.innerWidth / 2, y: window.innerHeight / 2 });
  const zoomRef = useRef(1);
  const [viewportSize, setViewportSize] = useState({
    width: window.innerWidth,
    height: window.innerHeight
  });
  const isMobile = viewportSize.width <= 900;
  const [mobileToolsOpen, setMobileToolsOpen] = useState(false);
  const [mobilePanelsOpen, setMobilePanelsOpen] = useState(false);
  
  // Tool State
  const [mode, setMode] = useState('edit'); 
  const [showNodes, setShowNodes] = useState(true);
  const [pathStyleDefaults, setPathStyleDefaults] = useState({ fillEnabled: false, strokeEnabled: true });
  
  // Shape Tool State
  const [shapeType, setShapeType] = useState('rectangle');
  const [showShapeMenu, setShowShapeMenu] = useState(false);
  const [drawingShape, setDrawingShape] = useState(null);
  const shapeMenuContainerRef = useRef(null);
  
  // Panels State (Accordion)
  const [openPanels, setOpenPanels] = useState({ grid: false, image: false, guides: false, layers: false });
  const [expandedPanel, setExpandedPanel] = useState(null);

  // Grid State
  const [gridConfig, setGridConfig] = useState({
    type: 'none',
    edges: 4,
    snapToGrid: false,
    size: GRID_SIZE,
    circularStep: DEFAULT_CIRCULAR_STEP
  });

  // Guides State
  const [guides, setGuides] = useState({
    capHeight: 300,
    xHeight: 200,
    descender: 100
  });
  const [showGuides, setShowGuides] = useState(true);

  // Layers & Objects State
  const [layers, setLayers] = useState([]);
  const [activeLayerId, setActiveLayerId] = useState(null);
  const [editingLayerId, setEditingLayerId] = useState(null);
  const [editingLayerName, setEditingLayerName] = useState("");
  const [lastSelectedLayerId, setLastSelectedLayerId] = useState(null);
  const [dragDropTarget, setDragDropTarget] = useState(null); // { id: 'layer-2', position: 'top' | 'bottom' }
  const [draggedLayerId, setDraggedLayerId] = useState(null);
  
  // Drawing & Editing State
  const [paths, setPaths] = useState([]); 
  const [images, setImages] = useState([]); 
  const [currentPath, setCurrentPath] = useState([]);
  const [currentPathInfo, setCurrentPathInfo] = useState(null);
  const [ghostPoint, setGhostPoint] = useState(null);
  const [isDrawingCurve, setIsDrawingCurve] = useState(false); 
  const [snapState, setSnapState] = useState({ endpoint: null, segment: null }); 
  
  const [selectedPoints, setSelectedPoints] = useState([]); 
  const [activePathEditId, setActivePathEditId] = useState(null);
  const [activeHandle, setActiveHandle] = useState(null); 
  const [selectionBox, setSelectionBox] = useState(null); 
  const [isDraggingPoints, setIsDraggingPoints] = useState(false);
  const [hoveredStartPoint, setHoveredStartPoint] = useState(false);
  const [drawHover, setDrawHover] = useState(null); 
  const [hoveredHandle, setHoveredHandle] = useState(null); // { pathIndex, pointIndex, type: 'hIn' | 'hOut' }
  
  // Transform States
  const [pointAction, setPointAction] = useState(null); 
  const [selectedImageIds, setSelectedImageIds] = useState([]);
  const [bgAction, setBgAction] = useState(null);
  const [bgInitialState, setBgInitialState] = useState(null);
  const [bgHoverAction, setBgHoverAction] = useState(null);

  // History State (Undo/Redo)
  const [pastPaths, setPastPaths] = useState([]);
  const [futurePaths, setFuturePaths] = useState([]);
  const dragStartPathsRef = useRef([]);
  const dragStartImagesRef = useRef([]);
  const hasDraggedRef = useRef(false);
  const spacePanRef = useRef({ active: false, prevMode: null });
  const pointRotateRef = useRef({ lastAngle: 0, accumulated: 0 });
  const bgRotateRef = useRef({ lastAngle: 0, accumulated: 0 });
  const pointerGestureRef = useRef({
    pointerId: null,
    pointerType: 'mouse',
    startClientX: 0,
    startClientY: 0,
    dragActivated: false
  });

  const svgRef = useRef(null);
  const fileInputRef = useRef(null);
  const lastPointerDownRef = useRef({ time: 0, x: 0, y: 0, canvasX: 0, canvasY: 0, refPoint: null }); 
  const lastClickedPathIdRef = useRef(null);
  const lastFocusedPathEditIdRef = useRef(null);

  const visibleLayerIds = new Set(layers.filter(l => l.visible).map(l => l.id));
  const lockedLayerIds = new Set(layers.filter(l => l.locked).map(l => l.id));
  const isPathVisible = (path) => visibleLayerIds.has(path.layerId);
  const isPathLocked = (path) => lockedLayerIds.has(path.layerId);

  const getCanvasCoords = useCallback((clientX, clientY) => {
    return {
      x: (clientX - pan.x) / zoom,
      y: (clientY - pan.y) / zoom
    };
  }, [pan, zoom]);

  useEffect(() => {
    panRef.current = pan;
  }, [pan]);

  useEffect(() => {
    zoomRef.current = zoom;
  }, [zoom]);

  useEffect(() => {
    const handleResize = () => {
      setViewportSize({
        width: window.innerWidth,
        height: window.innerHeight
      });
    };
    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  useEffect(() => {
    if (!isMobile) {
      setMobileToolsOpen(false);
      setMobilePanelsOpen(false);
    }
  }, [isMobile]);

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

  const touchHitScale = isMobile ? 1.65 : 1;
  const scaleHandleHitRadius = (8 * touchHitScale) / zoom;
  const rotateHandleHitRadius = (24 * touchHitScale) / zoom;
  const handleHitRadius = (8 * touchHitScale) / zoom;
  const pointHitRadius = (10 * touchHitScale) / zoom;
  const segmentHitRadius = (10 * touchHitScale) / zoom;
  const snapHitRadius = (SNAP_RADIUS * touchHitScale) / zoom;
  const pencilSamplingDistance = (isMobile ? 12 : 8) / zoom;
  const touchDragThresholdPx = isMobile ? 10 : 0;

  const hasPassedDragThreshold = (e) => {
    const gesture = pointerGestureRef.current;
    if (!gesture || gesture.pointerId == null || e.pointerId !== gesture.pointerId) return true;
    const isTouchLike = gesture.pointerType === 'touch' || gesture.pointerType === 'pen';
    if (!isTouchLike || touchDragThresholdPx <= 0) return true;
    if (gesture.dragActivated) return true;
    const dist = Math.hypot(e.clientX - gesture.startClientX, e.clientY - gesture.startClientY);
    if (dist >= touchDragThresholdPx) {
      gesture.dragActivated = true;
      return true;
    }
    return false;
  };

  const togglePanel = (panelId) => {
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

  // --- HISTORY HELPERS ---
  const commitHistory = useCallback((stateToSave) => {
    setPastPaths(prev => [...prev, cloneState(stateToSave.paths, stateToSave.currentPath, stateToSave.images, stateToSave.layers)]);
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
    
    setFuturePaths(prev => [cloneState(paths, currentPath, images, layers), ...prev]);
    setPaths(previous.paths);
    setCurrentPath(previous.currentPath);
    setImages(previous.images || []);
    setLayers(previous.layers || []);
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
  }, [pastPaths, futurePaths, paths, currentPath, images, layers, mode]);

  const handleRedo = useCallback(() => {
    if ((mode === 'draw' || mode === 'pencil') && currentPath.length > 0) return; 
    if (futurePaths.length === 0) return;
    
    const next = futurePaths[0];
    const newFuture = futurePaths.slice(1);
    
    setPastPaths(prev => [...prev, cloneState(paths, currentPath, images, layers)]);
    setPaths(next.paths);
    setCurrentPath(next.currentPath);
    setImages(next.images || []);
    setLayers(next.layers || []);
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
  }, [pastPaths, futurePaths, paths, currentPath, images, layers, mode]);

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

  // --- EVENT HANDLERS ---
  const capturePointer = (e) => {
    if (e.button === 2) return;
    if (!svgRef.current || e.pointerId == null) return;
    try {
      svgRef.current.setPointerCapture(e.pointerId);
    } catch (err) {
      // Ignore capture errors (e.g. unsupported pointer type)
    }
  };

  const releasePointer = (e) => {
    if (!svgRef.current || e?.pointerId == null) return;
    try {
      if (svgRef.current.hasPointerCapture(e.pointerId)) {
        svgRef.current.releasePointerCapture(e.pointerId);
      }
    } catch (err) {
      // Ignore release errors if capture state changed asynchronously
    }
  };

  const handlePointerDown = (e) => {
    capturePointer(e);
    pointerGestureRef.current = {
      pointerId: e.pointerId ?? null,
      pointerType: e.pointerType || 'mouse',
      startClientX: e.clientX,
      startClientY: e.clientY,
      dragActivated: (e.pointerType || 'mouse') === 'mouse'
    };
    if (showShapeMenu) setShowShapeMenu(false);
    setHoveredHandle(null);

    if (e.button === 1 || mode === 'pan') { 
      setIsPanning(true);
      return;
    }

    if (['shape', 'pencil', 'draw'].includes(mode)) {
        if (activeLayerId && lockedLayerIds.has(activeLayerId)) return;
    }

    let coords = getCanvasCoords(e.clientX, e.clientY);
    let snappedCoords = applyGridSnap(coords, gridConfig);

    const now = Date.now();
    const distToLast = Math.hypot(e.clientX - lastPointerDownRef.current.x, e.clientY - lastPointerDownRef.current.y);
    const isDoubleClick = (now - lastPointerDownRef.current.time < 350) && (distToLast < 20);
    
    // Will update refPoint down below depending on context
    lastPointerDownRef.current = { time: now, x: e.clientX, y: e.clientY, canvasX: coords.x, canvasY: coords.y, refPoint: null };

    if (mode === 'shape') {
      setDrawingShape({ startX: snappedCoords.x, startY: snappedCoords.y, currentX: snappedCoords.x, currentY: snappedCoords.y, shiftKey: e.shiftKey });
      return;
    }

    if (mode === 'edit') {
      dragStartPathsRef.current = clonePaths(paths);
      dragStartImagesRef.current = images.map(img => ({...img}));
      hasDraggedRef.current = false;
    }

    if (mode === 'pencil') {
      commitHistory({ paths, currentPath, images, layers });
      const newPoint = { 
        x: coords.x, y: coords.y, 
        hIn: { x: coords.x, y: coords.y }, 
        hOut: { x: coords.x, y: coords.y } 
      };
      setCurrentPathInfo({
        layerId: null,
        itemType: 'vector',
        fillEnabled: pathStyleDefaults.fillEnabled,
        strokeEnabled: pathStyleDefaults.strokeEnabled
      });
      setCurrentPath([newPoint]);
      return;
    }

    if (mode === 'draw') {

      if (currentPath.length === 0) {
        let hitSegment = null;
        let hitT = 0;
        let bestDist = Infinity;
        for (let i = paths.length - 1; i >= 0; i--) {
          const path = paths[i];
          if (!isPathVisible(path) || isPathLocked(path)) continue;
          for (let j = 0; j < path.points.length; j++) {
            if (j === 0 && !path.isClosed) continue;
            const prevIdx = j === 0 ? path.points.length - 1 : j - 1;
            const prevP = path.points[prevIdx];
            const currP = path.points[j];
            const hit = distToBezier(coords, prevP, prevP.hOut || prevP, currP.hIn || currP, currP);
            if (hit.dist < snapHitRadius && hit.dist < bestDist) {
              bestDist = hit.dist;
              hitSegment = { pathIndex: i, prevIndex: prevIdx, currIndex: j };
              hitT = hit.t;
            }
          }
        }

        if (hitSegment) {
          commitHistory({ paths, currentPath, images, layers });
          const newPaths = clonePaths(paths);
          const path = newPaths[hitSegment.pathIndex];
          const prevP = path.points[hitSegment.prevIndex];
          const currP = path.points[hitSegment.currIndex];
          const split = splitBezier(prevP, prevP.hOut || prevP, currP.hIn || currP, currP, hitT);

          prevP.hOut = split.left.hOut;
          currP.hIn = split.right.hIn;
          const insertIdx = hitSegment.currIndex === 0 ? path.points.length : hitSegment.currIndex;
          path.points.splice(insertIdx, 0, split.newPoint);

          setPaths(newPaths);
          setGhostPoint(null);
          setDrawHover(null);
          return;
        }

        commitHistory({ paths, currentPath, images, layers });
        const newPoint = { 
          x: snappedCoords.x, y: snappedCoords.y, 
          hIn: { x: snappedCoords.x, y: snappedCoords.y }, 
          hOut: { x: snappedCoords.x, y: snappedCoords.y } 
        };
        setCurrentPathInfo({
          layerId: null,
          itemType: 'vector',
          fillEnabled: pathStyleDefaults.fillEnabled,
          strokeEnabled: pathStyleDefaults.strokeEnabled
        });
        setCurrentPath([newPoint]);
        setIsDrawingCurve('drawing');
      } else {
        if (hoveredStartPoint) {
          setIsDrawingCurve('closing');
        } else {
          commitHistory({ paths, currentPath, images, layers });
          if (e.shiftKey) {
             snappedCoords = applyShiftSnap(snappedCoords, currentPath[currentPath.length - 1], true);
          }
          const newPoint = { 
            x: snappedCoords.x, y: snappedCoords.y, 
            hIn: { x: snappedCoords.x, y: snappedCoords.y }, 
            hOut: { x: snappedCoords.x, y: snappedCoords.y } 
          };
          setCurrentPath([...currentPath, newPoint]);
          setIsDrawingCurve('drawing');
        }
      }
    } else if (mode === 'edit') {

      const startDragging = (selArray) => {
        if (!selArray || selArray.length === 0) {
            setIsDraggingPoints(true);
            return;
        }
        let bestRefPoint = null;
        let minDist = Infinity;
        selArray.forEach(sp => {
            const path = dragStartPathsRef.current[sp.pathIndex];
            if(path) {
                const ptObj = path.points[sp.pointIndex];
                if (ptObj) {
                    const d = Math.hypot(ptObj.x - coords.x, ptObj.y - coords.y);
                    if (d < minDist) {
                        minDist = d;
                        bestRefPoint = { x: ptObj.x, y: ptObj.y };
                    }
                }
            }
        });
        lastPointerDownRef.current.refPoint = bestRefPoint || coords;
        setIsDraggingPoints(true);
      };
      const isDirectPathEdit = !!activePathEditId;
      const buildPathSelection = (pathIndex) => {
        const path = paths[pathIndex];
        if (!path) return [];
        return path.points.map((_, idx) => ({ pathIndex, pointIndex: idx }));
      };
      const buildEdgeSelection = (segment) => {
        if (!segment) return [];
        const edge = [
          { pathIndex: segment.pathIndex, pointIndex: segment.prevIndex },
          { pathIndex: segment.pathIndex, pointIndex: segment.currIndex }
        ];
        return edge.filter((pt, idx, arr) =>
          arr.findIndex(other => other.pathIndex === pt.pathIndex && other.pointIndex === pt.pointIndex) === idx
        );
      };
      const isWholePathSelection = (selection) => {
        if (!selection || selection.length === 0) return false;
        const pointsByPath = new Map();
        selection.forEach(sp => {
          if (!pointsByPath.has(sp.pathIndex)) pointsByPath.set(sp.pathIndex, new Set());
          pointsByPath.get(sp.pathIndex).add(sp.pointIndex);
        });
        for (const [pathIndex, pointSet] of pointsByPath.entries()) {
          const path = paths[pathIndex];
          if (!path || pointSet.size !== path.points.length) return false;
        }
        return true;
      };

      // 0. Check Selection Bounding Box Handles (Scale / Rotate)
      if (selBBox && !e.shiftKey && !e.altKey) {
        const corners = [
            { id: 'nw', x: selBBox.minX, y: selBBox.minY, angle: 225 },
            { id: 'ne', x: selBBox.maxX, y: selBBox.minY, angle: 315 },
            { id: 'se', x: selBBox.maxX, y: selBBox.maxY, angle: 45 },
            { id: 'sw', x: selBBox.minX, y: selBBox.maxY, angle: 135 }
        ];

        let hitAction = null;
        let cursorAngle = 0;

        for (const c of corners) {
            const dist = Math.hypot(coords.x - c.x, coords.y - c.y);
            if (dist <= scaleHandleHitRadius) {
                hitAction = `scale-${c.id}`;
                cursorAngle = c.angle;
                break;
            }
            if (dist <= rotateHandleHitRadius) {
                hitAction = `rotate-${c.id}`;
                cursorAngle = null;
                break;
            }
        }

        if (hitAction) {
            const startAngle = Math.atan2(
              coords.y - (selBBox.minY + selBBox.maxY) / 2,
              coords.x - (selBBox.minX + selBBox.maxX) / 2
            ) * 180 / Math.PI;
            if (hitAction.startsWith('rotate-')) {
              pointRotateRef.current = { lastAngle: startAngle, accumulated: 0 };
            }
            setPointAction({
                action: hitAction,
                cursorAngle,
                bbox: { ...selBBox },
                startCoords: coords,
                startAngle
            });
            return;
        }
      }

      let clickedHandle = null;
      let clickedPoint = null;

      if (isDirectPathEdit) {
        for (let i = paths.length - 1; i >= 0; i--) {
          if (!isPathVisible(paths[i]) || isPathLocked(paths[i])) continue;
          if (paths[i].id !== activePathEditId) continue;
          for (let j = 0; j < paths[i].points.length; j++) {
            const p = paths[i].points[j];
            const hasIn = p.hIn && Math.hypot(p.hIn.x - p.x, p.hIn.y - p.y) > 0.1;
            const hasOut = p.hOut && Math.hypot(p.hOut.x - p.x, p.hOut.y - p.y) > 0.1;
            
            if (hasIn && Math.hypot(p.hIn.x - coords.x, p.hIn.y - coords.y) < handleHitRadius) {
              clickedHandle = { pathIndex: i, pointIndex: j, type: 'hIn' }; break;
            }
            if (hasOut && Math.hypot(p.hOut.x - coords.x, p.hOut.y - coords.y) < handleHitRadius) {
              clickedHandle = { pathIndex: i, pointIndex: j, type: 'hOut' }; break;
            }
          }
          if (clickedHandle) break;
        }
      }

      if (clickedHandle) {
        setActiveHandle(clickedHandle);
        const alreadySelected = selectedPoints.some(sp => sp.pathIndex === clickedHandle.pathIndex && sp.pointIndex === clickedHandle.pointIndex);
        if (!alreadySelected) {
          if (e.shiftKey) {
            setSelectedPoints(prev => [...prev, { pathIndex: clickedHandle.pathIndex, pointIndex: clickedHandle.pointIndex }]);
          } else {
            setSelectedPoints([{ pathIndex: clickedHandle.pathIndex, pointIndex: clickedHandle.pointIndex }]);
          }
        }
        return;
      }

      if (isDirectPathEdit) {
        for (let i = paths.length - 1; i >= 0; i--) {
          if (!isPathVisible(paths[i]) || isPathLocked(paths[i])) continue;
          if (paths[i].id !== activePathEditId) continue;
          for (let j = 0; j < paths[i].points.length; j++) {
            const p = paths[i].points[j];
            const dist = Math.hypot(p.x - coords.x, p.y - coords.y);
            if (dist < pointHitRadius) {
              clickedPoint = { pathIndex: i, pointIndex: j };
              break;
            }
          }
          if (clickedPoint) break;
        }
      }

      if (clickedPoint) {
        if (isDoubleClick) {
          commitHistory({ paths, currentPath, images, layers });
          const newPaths = clonePaths(paths);
          const path = newPaths[clickedPoint.pathIndex];
          const ptIndex = clickedPoint.pointIndex;
          const pt = path.points[ptIndex];
          
          const dIn = pt.hIn ? Math.hypot(pt.hIn.x - pt.x, pt.hIn.y - pt.y) : 0;
          const dOut = pt.hOut ? Math.hypot(pt.hOut.x - pt.x, pt.hOut.y - pt.y) : 0;
          const isCornerNode = dIn < 0.1 && dOut < 0.1;

          if (!isCornerNode) {
            pt.hIn = { x: pt.x, y: pt.y };
            pt.hOut = { x: pt.x, y: pt.y };
          } else {
            const prevIdx = ptIndex === 0 ? path.points.length - 1 : ptIndex - 1;
            const nextIdx = (ptIndex + 1) % path.points.length;
            
            if (path.points.length > 1 && (path.isClosed || (ptIndex > 0 && ptIndex < path.points.length - 1))) {
                const prevP = path.points[prevIdx];
                const nextP = path.points[nextIdx];
                
                const dx = nextP.x - prevP.x;
                const dy = nextP.y - prevP.y;
                const len = Math.hypot(dx, dy);
                
                if (len > 0) {
                    const nx = dx / len;
                    const ny = dy / len;
                    const distPrev = Math.hypot(pt.x - prevP.x, pt.y - prevP.y);
                    const distNext = Math.hypot(nextP.x - pt.x, nextP.y - pt.y);
                    
                    pt.hIn = { x: pt.x - nx * (distPrev / 3), y: pt.y - ny * (distPrev / 3) };
                    pt.hOut = { x: pt.x + nx * (distNext / 3), y: pt.y + ny * (distNext / 3) };
                }
            } else if (path.points.length > 1) {
                 const neighborIdx = ptIndex === 0 ? 1 : ptIndex - 1;
                 const neighborP = path.points[neighborIdx];
                 const dx = neighborP.x - pt.x;
                 const dy = neighborP.y - pt.y;
                 
                 if (ptIndex === 0) {
                     pt.hOut = { x: pt.x + dx / 3, y: pt.y + dy / 3 }; 
                 } else {
                     pt.hIn = { x: pt.x + dx / 3, y: pt.y + dy / 3 };
                 }
            }
          }
          
          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          
          const newSel = [{ pathIndex: clickedPoint.pathIndex, pointIndex: clickedPoint.pointIndex }];
          setSelectedPoints(newSel);
          startDragging(newSel);
          return;
        }

        const alreadySelected = selectedPoints.some(sp => sp.pathIndex === clickedPoint.pathIndex && sp.pointIndex === clickedPoint.pointIndex);
        
        if (e.shiftKey) {
          if (alreadySelected) {
            setSelectedPoints(prev => prev.filter(sp => !(sp.pathIndex === clickedPoint.pathIndex && sp.pointIndex === clickedPoint.pointIndex)));
            return; 
          } else {
            const newSel = [...selectedPoints, clickedPoint];
            setSelectedPoints(newSel);
            startDragging(newSel);
            return;
          }
        } else {
          if (!alreadySelected) {
            const newSel = [clickedPoint];
            setSelectedPoints(newSel);
            startDragging(newSel);
            return;
          } else {
            startDragging(selectedPoints);
            return;
          }
        }
      }

      // 3. Check Background Image Handles (Scale / Rotate)
      const hitBg = isDirectPathEdit ? null : getBgHit(coords);

      if (hitBg && (hitBg.action.startsWith('scale') || hitBg.action.startsWith('rotate'))) {
        lastClickedPathIdRef.current = null;
        setBgAction(hitBg.action);
        setSelectedImageIds([hitBg.imageId]);
        const img = images.find(i => i.id === hitBg.imageId);
        if (hitBg.action.startsWith('scale')) {
           setBgInitialState({ coords, img: { ...img }, cursorAngle: hitBg.cursorAngle });
        } else {
           const initAngle = Math.atan2(coords.y - img.y, coords.x - img.x) * 180 / Math.PI;
           bgRotateRef.current = { lastAngle: initAngle, accumulated: 0 };
           setBgInitialState({ angle: initAngle, img: { ...img } });
        }
        return;
      }

      // 4. Check path segments
      let clickedSegment = null;
      for (let i = paths.length - 1; i >= 0; i--) {
        const path = paths[i];
        if (!isPathVisible(path) || isPathLocked(path)) continue;
        for (let j = 0; j < path.points.length; j++) {
          if (j === 0 && !path.isClosed) continue;
          
          const prevIdx = j === 0 ? path.points.length - 1 : j - 1;
          const prevP = path.points[prevIdx];
          const currP = path.points[j];
          
          const p0 = prevP;
          const p1 = prevP.hOut || prevP;
          const p2 = currP.hIn || currP;
          const p3 = currP;
          
          const hit = distToBezier(coords, p0, p1, p2, p3);
          if (hit.dist < segmentHitRadius) {
            clickedSegment = { pathIndex: i, prevIndex: prevIdx, currIndex: j };
            break;
          }
        }
        if (clickedSegment) break;
      }

      if (clickedSegment) {
        const clickedPath = paths[clickedSegment.pathIndex];
        const clickedPathSelection = buildPathSelection(clickedSegment.pathIndex);
        const clickedEdgeSelection = buildEdgeSelection(clickedSegment);
        const isDirectClickOnActivePath = !!activePathEditId && clickedPath?.id === activePathEditId;

        if (!isDirectClickOnActivePath) {
          const isPathSelected = clickedPathSelection.every(nsp => (
            selectedPoints.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)
          ));
          const shouldEnterDirect = isDoubleClick && clickedPath && lastClickedPathIdRef.current === clickedPath.id;
          lastClickedPathIdRef.current = clickedPath?.id || null;

          if (shouldEnterDirect && clickedPath) {
            setActivePathEditId(clickedPath.id);
            setSelectedPoints([]);
            setSelectedImageIds([]);
            setActiveLayerId(clickedPath.layerId);
            return;
          }

          setActivePathEditId(null);
          setSelectedImageIds([]);
          if (e.shiftKey) {
            if (isPathSelected) {
              setSelectedPoints(prev => prev.filter(sp => sp.pathIndex !== clickedSegment.pathIndex));
              return;
            }
            const merged = [...selectedPoints];
            clickedPathSelection.forEach(nsp => {
              if (!merged.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)) {
                merged.push(nsp);
              }
            });
            setSelectedPoints(merged);
            startDragging(merged);
            return;
          }

          if (!isPathSelected) {
            setSelectedPoints(clickedPathSelection);
            startDragging(clickedPathSelection);
          } else {
            startDragging(selectedPoints);
          }
          return;
        }

        if (e.shiftKey && e.altKey && (e.ctrlKey || e.metaKey)) {
          commitHistory({ paths, currentPath, images, layers });
          const newPaths = clonePaths(paths);
          const path = newPaths[clickedSegment.pathIndex];
          
          for (let j = 0; j < path.points.length; j++) {
            if (j === 0 && !path.isClosed) continue;
            const prevIdx = j === 0 ? path.points.length - 1 : j - 1;
            const p1 = path.points[prevIdx];
            const p2 = path.points[j];
            p1.hOut = { x: p1.x, y: p1.y };
            p2.hIn = { x: p2.x, y: p2.y };
          }
          
          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          
          const newSel = paths[clickedSegment.pathIndex].points.map((_, idx) => ({ 
            pathIndex: clickedSegment.pathIndex, 
            pointIndex: idx 
          }));
          setSelectedPoints(newSel);
          startDragging(newSel);
          return;
        } else if (e.shiftKey && (e.ctrlKey || e.metaKey)) {
          commitHistory({ paths, currentPath, images, layers });
          const newPaths = clonePaths(paths);
          const path = newPaths[clickedSegment.pathIndex];
          const p1 = path.points[clickedSegment.prevIndex];
          const p2 = path.points[clickedSegment.currIndex];
          
          p1.hOut = { x: p1.x, y: p1.y };
          p2.hIn = { x: p2.x, y: p2.y };
          
          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          
          const newSel = [
            { pathIndex: clickedSegment.pathIndex, pointIndex: clickedSegment.prevIndex },
            { pathIndex: clickedSegment.pathIndex, pointIndex: clickedSegment.currIndex }
          ];
          setSelectedPoints(newSel);
          startDragging(newSel);
          return;
        } else if (e.altKey && (e.ctrlKey || e.metaKey)) {
          commitHistory({ paths, currentPath, images, layers });
          const newPaths = clonePaths(paths);
          const path = newPaths[clickedSegment.pathIndex];
          
          for (let j = 0; j < path.points.length; j++) {
            if (j === 0 && !path.isClosed) continue;
            const prevIdx = j === 0 ? path.points.length - 1 : j - 1;
            const p1 = path.points[prevIdx];
            const p2 = path.points[j];
            
            p1.hOut = { x: p1.x + (p2.x - p1.x)/3, y: p1.y + (p2.y - p1.y)/3 };
            p2.hIn = { x: p1.x + 2*(p2.x - p1.x)/3, y: p1.y + 2*(p2.y - p1.y)/3 };
          }
          
          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          return;
        } else if (e.altKey) {
          commitHistory({ paths, currentPath, images, layers });
          const newPaths = clonePaths(paths);
          const path = newPaths[clickedSegment.pathIndex];
          const p1 = path.points[clickedSegment.prevIndex];
          const p2 = path.points[clickedSegment.currIndex];
          
          p1.hOut = { x: p1.x + (p2.x - p1.x)/3, y: p1.y + (p2.y - p1.y)/3 };
          p2.hIn = { x: p1.x + 2*(p2.x - p1.x)/3, y: p1.y + 2*(p2.y - p1.y)/3 };
          
          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          return;
        } else {
          const newSel = clickedEdgeSelection;
          
          const alreadySelected = newSel.every(nsp => selectedPoints.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex));
          
          if (e.shiftKey) {
            if (alreadySelected) {
              setSelectedPoints(prev => prev.filter(sp => (
                !newSel.some(sel => sel.pathIndex === sp.pathIndex && sel.pointIndex === sp.pointIndex)
              )));
              return; 
            } else {
              const newSelMerged = [...selectedPoints];
              newSel.forEach(nsp => {
                if (!newSelMerged.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)) {
                  newSelMerged.push(nsp);
                }
              });
              setSelectedPoints(newSelMerged);
              startDragging(newSelMerged);
              return;
            }
          } else {
            if (!alreadySelected) {
              setSelectedPoints(newSel);
              startDragging(newSel);
              return;
            } else {
              startDragging(selectedPoints);
              return;
            }
          }
        }
      }

      // 4.25 Check filled closed path bodies (click-to-select/move)
      let clickedFilledPathIndex = -1;
      for (let i = paths.length - 1; i >= 0; i--) {
        const path = paths[i];
        if (!isPathVisible(path) || isPathLocked(path)) continue;
        if (!path.isClosed || !path.fillEnabled) continue;

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
          const xk = poly[k].x, yk = poly[k].y;
          const xl = poly[l].x, yl = poly[l].y;
          const intersects = ((yk > coords.y) !== (yl > coords.y))
            && (coords.x < (xl - xk) * (coords.y - yk) / (yl - yk) + xk);
          if (intersects) inside = !inside;
        }

        if (inside) {
          clickedFilledPathIndex = i;
          break;
        }
      }

      if (clickedFilledPathIndex !== -1) {
        const path = paths[clickedFilledPathIndex];
        const newSel = buildPathSelection(clickedFilledPathIndex);
        const isDirectClickOnActivePath = !!activePathEditId && path?.id === activePathEditId;
        const alreadySelected = newSel.every(nsp =>
          selectedPoints.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)
        );

        if (!isDirectClickOnActivePath) {
          const shouldEnterDirect = isDoubleClick && path && lastClickedPathIdRef.current === path.id;
          lastClickedPathIdRef.current = path?.id || null;

          if (shouldEnterDirect && path) {
            setActivePathEditId(path.id);
            setSelectedPoints([]);
            setSelectedImageIds([]);
            setActiveLayerId(path.layerId);
            return;
          }

          setActivePathEditId(null);
          if (e.shiftKey) {
            if (alreadySelected) {
              setSelectedPoints(prev => prev.filter(sp => sp.pathIndex !== clickedFilledPathIndex));
              return;
            }
            const merged = [...selectedPoints];
            newSel.forEach(nsp => {
              if (!merged.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)) {
                merged.push(nsp);
              }
            });
            setSelectedPoints(merged);
            startDragging(merged);
            return;
          }

          if (!alreadySelected) {
            setSelectedPoints(newSel);
            setSelectedImageIds([]);
            startDragging(newSel);
          } else {
            startDragging(selectedPoints);
          }
          return;
        }

        if (e.shiftKey) {
          if (alreadySelected) {
            setSelectedPoints(prev => prev.filter(sp => sp.pathIndex !== clickedFilledPathIndex));
            return;
          }
          const newSelMerged = [...selectedPoints];
          newSel.forEach(nsp => {
            if (!newSelMerged.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)) {
              newSelMerged.push(nsp);
            }
          });
          setSelectedPoints(newSelMerged);
          startDragging(newSelMerged);
          return;
        }

        if (!alreadySelected) {
          setSelectedPoints(newSel);
          startDragging(newSel);
        } else {
          startDragging(selectedPoints);
        }
        return;
      }

      // 4.5 Check Selection Bounding Box (Move selected object)
      // Bypass this if holding Shift or Alt to allow drawing a selection area instead
      const canMoveSelectionByBBox = selectedImageIds.length > 0 || isWholePathSelection(selectedPoints);
      if (!e.shiftKey && !e.altKey && canMoveSelectionByBBox && selBBox && coords.x >= selBBox.minX && coords.x <= selBBox.maxX && coords.y >= selBBox.minY && coords.y <= selBBox.maxY) {
        startDragging(selectedPoints);
        return;
      }

      // 5. Check Background Image Body (Move)
      if (hitBg && hitBg.action === 'move') {
        lastClickedPathIdRef.current = null;
        setBgAction('move');
        setSelectedImageIds([hitBg.imageId]);
        const img = images.find(i => i.id === hitBg.imageId);
        setSelectedPoints([]); 
        setBgInitialState({ coords, img: { ...img } });
        return;
      }

      if (isDoubleClick && activePathEditId && !e.shiftKey && !e.altKey && !e.ctrlKey && !e.metaKey) {
        lastClickedPathIdRef.current = null;
        setActivePathEditId(null);
        lastFocusedPathEditIdRef.current = null;
        setSelectedPoints([]);
        setActiveHandle(null);
        setSelectionBox(null);
        return;
      }

      // 6. Start Box selection
      lastClickedPathIdRef.current = null;
      setSelectedImageIds([]);
      setSelectionBox({ 
        startX: coords.x, 
        startY: coords.y, 
        currentX: coords.x, 
        currentY: coords.y, 
        initialSelection: [...selectedPoints],
        initialSelectedImageIds: [...selectedImageIds]
      });
      if (!e.shiftKey && !e.altKey) {
        setSelectedPoints([]);
      }
    }
  };

  const handlePointerMove = (e) => {
    const dragThresholdPassed = hasPassedDragThreshold(e);

    if (isPanning) {
      if (!dragThresholdPassed) return;
      setPan(prev => {
        const next = {
          x: prev.x + e.movementX,
          y: prev.y + e.movementY
        };
        panRef.current = next;
        return next;
      });
      return;
    }

    let coords = getCanvasCoords(e.clientX, e.clientY);
    let snappedCoords = applyGridSnap(coords, gridConfig);

    if (mode === 'shape' && drawingShape) {
      if (!dragThresholdPassed) return;
      setDrawingShape(prev => ({ ...prev, currentX: snappedCoords.x, currentY: snappedCoords.y, shiftKey: e.shiftKey }));
      return;
    }

    if (pointAction) {
      if (!dragThresholdPassed) return;
      hasDraggedRef.current = true;
      if (pointAction.action.startsWith('scale-')) {
          const cornerId = pointAction.action.split('-')[1];
          const bbox = pointAction.bbox;
          let localCorner, opposite;
          
          if (cornerId === 'nw') { localCorner = {x: bbox.minX, y: bbox.minY}; opposite = {x: bbox.maxX, y: bbox.maxY}; }
          if (cornerId === 'ne') { localCorner = {x: bbox.maxX, y: bbox.minY}; opposite = {x: bbox.minX, y: bbox.maxY}; }
          if (cornerId === 'se') { localCorner = {x: bbox.maxX, y: bbox.maxY}; opposite = {x: bbox.minX, y: bbox.minY}; }
          if (cornerId === 'sw') { localCorner = {x: bbox.minX, y: bbox.maxY}; opposite = {x: bbox.maxX, y: bbox.minY}; }

          const diagVec = { x: localCorner.x - opposite.x, y: localCorner.y - opposite.y };
          const diagLen = Math.hypot(diagVec.x, diagVec.y);
          let s_new = 1;
          
          if (diagLen > 0.1) {
              const u = { x: diagVec.x / diagLen, y: diagVec.y / diagLen };
              const v = { x: coords.x - opposite.x, y: coords.y - opposite.y };
              s_new = Math.max(0.01, (v.x * u.x + v.y * u.y) / diagLen);
          }

          setPointAction(prev => ({ ...prev, scale: s_new, origin: opposite }));

          setPaths(prev => {
              const newPaths = dragStartPathsRef.current.map(p => ({ ...p, points: [...p.points] }));
              selectedPoints.forEach(sp => {
                  const srcPt = dragStartPathsRef.current[sp.pathIndex].points[sp.pointIndex];
                  const pt = {
                      ...srcPt,
                      hIn: srcPt.hIn ? { ...srcPt.hIn } : undefined,
                      hOut: srcPt.hOut ? { ...srcPt.hOut } : undefined
                  };
                  pt.x = opposite.x + (pt.x - opposite.x) * s_new;
                  pt.y = opposite.y + (pt.y - opposite.y) * s_new;
                  if (pt.hIn) pt.hIn = { x: opposite.x + (pt.hIn.x - opposite.x) * s_new, y: opposite.y + (pt.hIn.y - opposite.y) * s_new };
                  if (pt.hOut) pt.hOut = { x: opposite.x + (pt.hOut.x - opposite.x) * s_new, y: opposite.y + (pt.hOut.y - opposite.y) * s_new };
                  newPaths[sp.pathIndex].points[sp.pointIndex] = pt;
              });
              return newPaths;
          });

          if (selectedImageIds.length > 0) {
            setImages(() => dragStartImagesRef.current.map(img => {
              if (!selectedImageIds.includes(img.id)) return img;
              return {
                ...img,
                x: opposite.x + (img.x - opposite.x) * s_new,
                y: opposite.y + (img.y - opposite.y) * s_new,
                scale: Math.max(0.01, img.scale * s_new)
              };
            }));
          }
      } else if (pointAction.action.startsWith('rotate-')) {
          const bbox = pointAction.bbox;
          const cx = (bbox.minX + bbox.maxX) / 2;
          const cy = (bbox.minY + bbox.maxY) / 2;
          const currentAngle = Math.atan2(coords.y - cy, coords.x - cx) * 180 / Math.PI;
          const stepDelta = shortestDeltaDeg(currentAngle, pointRotateRef.current.lastAngle);
          pointRotateRef.current.lastAngle = currentAngle;
          pointRotateRef.current.accumulated += stepDelta;
          const deltaAngle = e.shiftKey
            ? Math.round(pointRotateRef.current.accumulated / 15) * 15
            : pointRotateRef.current.accumulated;
          
          const rad = deltaAngle * Math.PI / 180;
          const cos = Math.cos(rad);
          const sin = Math.sin(rad);
          const rotatePt = (p) => ({
              x: cx + (p.x - cx) * cos - (p.y - cy) * sin,
              y: cy + (p.x - cx) * sin + (p.y - cy) * cos
          });

          setPointAction(prev => ({ ...prev, angle: deltaAngle, origin: {x: cx, y: cy} }));

          setPaths(prev => {
              const newPaths = dragStartPathsRef.current.map(p => ({ ...p, points: [...p.points] }));
              selectedPoints.forEach(sp => {
                  const srcPt = dragStartPathsRef.current[sp.pathIndex].points[sp.pointIndex];
                  const pt = {
                      ...srcPt,
                      hIn: srcPt.hIn ? { ...srcPt.hIn } : undefined,
                      hOut: srcPt.hOut ? { ...srcPt.hOut } : undefined
                  };
                  const rp = rotatePt(pt);
                  pt.x = rp.x; pt.y = rp.y;
                  if (pt.hIn) pt.hIn = rotatePt(pt.hIn);
                  if (pt.hOut) pt.hOut = rotatePt(pt.hOut);
                  newPaths[sp.pathIndex].points[sp.pointIndex] = pt;
              });
              return newPaths;
          });

          if (selectedImageIds.length > 0) {
            setImages(() => dragStartImagesRef.current.map(img => {
              if (!selectedImageIds.includes(img.id)) return img;
              const rp = rotatePt({ x: img.x, y: img.y });
              return {
                ...img,
                x: rp.x,
                y: rp.y,
                rotation: normalizeAngleDeg(img.rotation + deltaAngle)
              };
            }));
          }
      }
      return;
    }

    if (bgAction && selectedImageIds.length > 0) {
      if (!dragThresholdPassed) return;
      hasDraggedRef.current = true;
      setImages(prev => prev.map(img => {
        if (!selectedImageIds.includes(img.id)) return img;
        
        if (bgAction === 'move') {
          return {
            ...img,
            x: bgInitialState.img.x + (coords.x - bgInitialState.coords.x),
            y: bgInitialState.img.y + (coords.y - bgInitialState.coords.y)
          };
        } else if (bgAction.startsWith('scale-')) {
          const cornerId = bgAction.split('-')[1];
          const init = bgInitialState.img;
          const lw = init.width / 2;
          const lh = init.height / 2;

          let localCorner, localOpposite;
          if (cornerId === 'nw') { localCorner = {x: -lw, y: -lh}; localOpposite = {x: lw, y: lh}; }
          if (cornerId === 'ne') { localCorner = {x: lw, y: -lh}; localOpposite = {x: -lw, y: lh}; }
          if (cornerId === 'se') { localCorner = {x: lw, y: lh}; localOpposite = {x: -lw, y: -lh}; }
          if (cornerId === 'sw') { localCorner = {x: -lw, y: lh}; localOpposite = {x: lw, y: -lh}; }

          const theta = init.rotation * Math.PI / 180;
          const rotateVec = (v, a) => ({
              x: v.x * Math.cos(a) - v.y * Math.sin(a),
              y: v.x * Math.sin(a) + v.y * Math.cos(a)
          });

          const fixedPtOffset = rotateVec({ x: init.scale * localOpposite.x, y: init.scale * localOpposite.y }, theta);
          const fixedPt = { x: init.x + fixedPtOffset.x, y: init.y + fixedPtOffset.y };

          const diagVec = { x: localCorner.x - localOpposite.x, y: localCorner.y - localOpposite.y };
          const diagLen = Math.hypot(diagVec.x, diagVec.y);
          const u = rotateVec({ x: diagVec.x / diagLen, y: diagVec.y / diagLen }, theta);

          const v = { x: coords.x - fixedPt.x, y: coords.y - fixedPt.y };
          const s_new = Math.max(0.01, (v.x * u.x + v.y * u.y) / diagLen);

          const newOppositeOffset = rotateVec({ x: s_new * localOpposite.x, y: s_new * localOpposite.y }, theta);
          const newCenter = { x: fixedPt.x - newOppositeOffset.x, y: fixedPt.y - newOppositeOffset.y };

          return { ...img, scale: s_new, x: newCenter.x, y: newCenter.y };
        } else if (bgAction.startsWith('rotate-')) {
          const init = bgInitialState.img;
          const currentAngle = Math.atan2(coords.y - init.y, coords.x - init.x) * 180 / Math.PI;
          const stepDelta = shortestDeltaDeg(currentAngle, bgRotateRef.current.lastAngle);
          bgRotateRef.current.lastAngle = currentAngle;
          bgRotateRef.current.accumulated += stepDelta;
          const deltaAngle = e.shiftKey
            ? Math.round(bgRotateRef.current.accumulated / 15) * 15
            : bgRotateRef.current.accumulated;
          const newRotation = normalizeAngleDeg(init.rotation + deltaAngle);
          return { ...img, rotation: newRotation };
        }
        return img;
      }));
      return;
    }

    if (mode === 'pencil') {
      if (currentPath.length > 0) {
        const lastPoint = currentPath[currentPath.length - 1];
        if (Math.hypot(coords.x - lastPoint.x, coords.y - lastPoint.y) > pencilSamplingDistance) {
          const newPoint = { 
            x: coords.x, y: coords.y, 
            hIn: { x: coords.x, y: coords.y }, 
            hOut: { x: coords.x, y: coords.y } 
          };
          setCurrentPath(prev => [...prev, newPoint]);
        }
      }
      return;
    }

    if (mode === 'draw') {

      let snapPoint = null;
      let segmentSnap = null;

      if (currentPath.length === 0) {
        let bestDist = Infinity;
        for (let i = paths.length - 1; i >= 0; i--) {
          const path = paths[i];
          if (!isPathVisible(path) || isPathLocked(path)) continue;
          for (let j = 0; j < path.points.length; j++) {
            if (j === 0 && !path.isClosed) continue;
            const prevIdx = j === 0 ? path.points.length - 1 : j - 1;
            const prevP = path.points[prevIdx];
            const currP = path.points[j];
            const hit = distToBezier(coords, prevP, prevP.hOut || prevP, currP.hIn || currP, currP);
            if (hit.dist < snapHitRadius && hit.dist < bestDist) {
              bestDist = hit.dist;
              segmentSnap = { pathIndex: i, prevIndex: prevIdx, currIndex: j, t: hit.t };
              snapPoint = getBezierPoint(prevP, prevP.hOut || prevP, currP.hIn || currP, currP, hit.t);
            }
          }
        }
      }

      if (currentPath.length > 0) {
        const startP = currentPath[0];
        if (currentPath.length > 2 && Math.hypot(startP.x - coords.x, startP.y - coords.y) < snapHitRadius) {
          setHoveredStartPoint(true);
          snapPoint = startP;
        } else {
          setHoveredStartPoint(false);
        }
      }

      if (!snapPoint && currentPath.length > 0 && e.shiftKey && !isDrawingCurve) {
          snappedCoords = applyShiftSnap(snappedCoords, currentPath[currentPath.length - 1], true);
      }

      setSnapState({ endpoint: null, segment: segmentSnap });
      setGhostPoint(snapPoint || snappedCoords);

      if (isDrawingCurve) {
        const isClosing = isDrawingCurve === 'closing';
        setCurrentPath(prev => {
          const newPath = [...prev];
          const targetIdx = isClosing ? 0 : newPath.length - 1;
          const p = { ...newPath[targetIdx] };
          
          let handleCoords = { ...snappedCoords };
          if (e.shiftKey) {
             handleCoords = applyShiftSnap(coords, p, true);
          }
          
          p.hOut = { x: handleCoords.x, y: handleCoords.y };
          p.hIn = { 
            x: p.x - (handleCoords.x - p.x), 
            y: p.y - (handleCoords.y - p.y) 
          };
          newPath[targetIdx] = p;
          return newPath;
        });
      } else if (currentPath.length > 0) {
        setGhostPoint(snapPoint || snappedCoords);
        
        const startP = currentPath[0];
        const distToStart = Math.hypot(startP.x - coords.x, startP.y - coords.y);
        if (currentPath.length > 2 && distToStart < snapHitRadius) {
          setHoveredStartPoint(true);
          setGhostPoint(startP); 
        } else {
          setHoveredStartPoint(false);
        }
        setDrawHover(null);
      } else {
        setHoveredStartPoint(false);
        if (segmentSnap && snapPoint) {
          setDrawHover({ x: snapPoint.x, y: snapPoint.y, type: 'segment' });
        } else {
          setDrawHover(null);
        }
      }
    } else if (mode === 'edit') {
      if (activeHandle) {
        if (!dragThresholdPassed) return;
        hasDraggedRef.current = true;
        let type = activeHandle.type;

        setPaths(prev => {
          const newPaths = prev.map(p => ({ ...p, points: [...p.points] }));
          const path = newPaths[activeHandle.pathIndex];
          const pointIndex = activeHandle.pointIndex;
          
          const srcPt = path.points[pointIndex];
          const point = {
              ...srcPt,
              hIn: srcPt.hIn ? { ...srcPt.hIn } : undefined,
              hOut: srcPt.hOut ? { ...srcPt.hOut } : undefined
          };
          
          let handleCoords = { ...snappedCoords };
          if (e.shiftKey) {
              handleCoords = applyShiftSnap(coords, point, true);
          }
          
          point[type] = { x: handleCoords.x, y: handleCoords.y };
          
          if (e.altKey && (e.ctrlKey || e.metaKey)) {
            let prevIdx, currIdx;
            if (type === 'hOut') {
              prevIdx = pointIndex;
              currIdx = (pointIndex + 1) % path.points.length;
            } else {
              currIdx = pointIndex;
              prevIdx = pointIndex === 0 ? path.points.length - 1 : pointIndex - 1;
            }

            if (path.isClosed || (type === 'hOut' && currIdx !== 0) || (type === 'hIn' && prevIdx !== path.points.length - 1)) {
              const p1Ref = path.points[prevIdx];
              const p2Ref = path.points[currIdx];

              const dx = p2Ref.x - p1Ref.x;
              const dy = p2Ref.y - p1Ref.y;
              const L = Math.hypot(dx, dy);

              let u = 0.33, v = 0;
              if (L > 0) {
                const U = { x: dx / L, y: dy / L };
                const V = { x: -U.y, y: U.x };
                
                if (type === 'hOut') {
                  const H = { x: handleCoords.x - p1Ref.x, y: handleCoords.y - p1Ref.y };
                  u = (H.x * U.x + H.y * U.y) / L;
                  v = (H.x * V.x + H.y * V.y) / L;
                } else {
                  const H = { x: handleCoords.x - p2Ref.x, y: handleCoords.y - p2Ref.y };
                  u = -(H.x * U.x + H.y * U.y) / L;
                  v = (H.x * V.x + H.y * V.y) / L;
                }
              }

              for (let i = 0; i < path.points.length; i++) {
                if (i === 0 && !path.isClosed) continue;
                const pIdx1 = i === 0 ? path.points.length - 1 : i - 1;
                const pIdx2 = i;
                
                const P1 = { ...path.points[pIdx1] };
                const P2 = { ...path.points[pIdx2] };
                
                const sdx = P2.x - P1.x;
                const sdy = P2.y - P1.y;
                const sL = Math.hypot(sdx, sdy);
                
                if (sL > 0) {
                  const sU = { x: sdx / sL, y: sdy / sL };
                  const sV = { x: -sU.y, y: sU.x };
                  
                  P1.hOut = {
                    x: P1.x + u * sL * sU.x + v * sL * sV.x,
                    y: P1.y + u * sL * sU.y + v * sL * sV.y
                  };
                  P2.hIn = {
                    x: P2.x - u * sL * sU.x + v * sL * sV.x,
                    y: P2.y - u * sL * sU.y + v * sL * sV.y
                  };
                }
                path.points[pIdx1] = P1;
                path.points[pIdx2] = P2;
              }
            } else {
              path.points[pointIndex] = point;
            }
          } else if (e.altKey) {
            path.points[pointIndex] = point;
            
            if (type === 'hOut') {
              const nextIndex = (pointIndex + 1) % path.points.length;
              if (nextIndex !== 0 || path.isClosed) {
                const nextPoint = { ...path.points[nextIndex] };
                if (nextPoint.hIn) {
                  nextPoint.hIn = reflectPointAcrossPerpBisector(handleCoords, path.points[pointIndex], nextPoint);
                  path.points[nextIndex] = nextPoint;
                }
              }
            } else if (type === 'hIn') {
              const prevIndex = pointIndex === 0 ? path.points.length - 1 : pointIndex - 1;
              if (pointIndex !== 0 || path.isClosed) {
                const prevPoint = { ...path.points[prevIndex] };
                if (prevPoint.hOut) {
                  prevPoint.hOut = reflectPointAcrossPerpBisector(handleCoords, prevPoint, path.points[pointIndex]);
                  path.points[prevIndex] = prevPoint;
                }
              }
            }
          } else if (e.ctrlKey || e.metaKey) {
            const otherType = type === 'hIn' ? 'hOut' : 'hIn';
            if (point[otherType]) {
              point[otherType] = {
                 x: point.x - (handleCoords.x - point.x),
                 y: point.y - (handleCoords.y - point.y)
              };
            }
            path.points[pointIndex] = point;
          } else {
            path.points[pointIndex] = point;
          }
          
          return newPaths;
        });
      } else if (isDraggingPoints) {
        if (!dragThresholdPassed) return;
        hasDraggedRef.current = true;
        let dragDx = coords.x - lastPointerDownRef.current.canvasX;
        let dragDy = coords.y - lastPointerDownRef.current.canvasY;
        if (e.shiftKey) {
          if (Math.abs(dragDx) >= Math.abs(dragDy)) {
            dragDy = 0;
          } else {
            dragDx = 0;
          }
        }
        if (gridConfig.snapToGrid && selectedPoints.length > 0) {
            // Absolute snapping logic tracking the actual node grabbed or BBox corner
            const refPoint = lastPointerDownRef.current.refPoint || { x: lastPointerDownRef.current.canvasX, y: lastPointerDownRef.current.canvasY };
            const currentRefPoint = {
                x: refPoint.x + dragDx,
                y: refPoint.y + dragDy
            };
            const snappedRefPoint = applyGridSnap(currentRefPoint, gridConfig);
            const dx = snappedRefPoint.x - refPoint.x;
            const dy = snappedRefPoint.y - refPoint.y;

            setPaths(prev => {
                const newPaths = dragStartPathsRef.current.map(p => ({ ...p, points: [...p.points] }));
                selectedPoints.forEach(sp => {
                    const srcPt = dragStartPathsRef.current[sp.pathIndex].points[sp.pointIndex];
                    const pt = {
                        ...srcPt,
                        hIn: srcPt.hIn ? { ...srcPt.hIn } : undefined,
                        hOut: srcPt.hOut ? { ...srcPt.hOut } : undefined
                    };
                    pt.x += dx; pt.y += dy;
                    if (pt.hIn) { pt.hIn.x += dx; pt.hIn.y += dy; }
                    if (pt.hOut) { pt.hOut.x += dx; pt.hOut.y += dy; }
                    newPaths[sp.pathIndex].points[sp.pointIndex] = pt;
                });
                return newPaths;
            });

            if (selectedImageIds.length > 0) {
              setImages(() => dragStartImagesRef.current.map(img => {
                if (!selectedImageIds.includes(img.id)) return img;
                return { ...img, x: img.x + dx, y: img.y + dy };
              }));
            }
        } else {
            // Standard absolute dragging from drag start
            setPaths(() => {
                const newPaths = dragStartPathsRef.current.map(p => ({ ...p, points: [...p.points] }));
                selectedPoints.forEach(sp => {
                    const srcPt = dragStartPathsRef.current[sp.pathIndex].points[sp.pointIndex];
                    const pt = {
                        ...srcPt,
                        hIn: srcPt.hIn ? { ...srcPt.hIn } : undefined,
                        hOut: srcPt.hOut ? { ...srcPt.hOut } : undefined
                    };
                    pt.x += dragDx; pt.y += dragDy;
                    if (pt.hIn) { pt.hIn.x += dragDx; pt.hIn.y += dragDy; }
                    if (pt.hOut) { pt.hOut.x += dragDx; pt.hOut.y += dragDy; }
                    newPaths[sp.pathIndex].points[sp.pointIndex] = pt;
                });
                return newPaths;
            });

            if (selectedImageIds.length > 0) {
              setImages(() => dragStartImagesRef.current.map(img => (
                selectedImageIds.includes(img.id)
                  ? { ...img, x: img.x + dragDx, y: img.y + dragDy }
                  : img
              )));
            }
        }
      } else if (selectionBox) {
        if (!dragThresholdPassed) return;
        setSelectionBox(prev => ({ 
          ...prev, 
          currentX: coords.x, 
          currentY: coords.y
        }));
        
        const minX = Math.min(selectionBox.startX, coords.x);
        const maxX = Math.max(selectionBox.startX, coords.x);
        const minY = Math.min(selectionBox.startY, coords.y);
        const maxY = Math.max(selectionBox.startY, coords.y);
        const pointInRect = (p) => p.x >= minX && p.x <= maxX && p.y >= minY && p.y <= maxY;
        const pathIntersectsMarquee = (path) => {
          if (!path || path.points.length === 0) return false;

          for (let j = 0; j < path.points.length; j++) {
            if (pointInRect(path.points[j])) return true;
          }

          const segCount = path.isClosed ? path.points.length : Math.max(0, path.points.length - 1);
          const steps = 24;
          for (let seg = 0; seg < segCount; seg++) {
            const p0 = path.points[seg];
            const p3 = path.points[(seg + 1) % path.points.length];
            const p1 = p0.hOut || p0;
            const p2 = p3.hIn || p3;
            for (let step = 0; step <= steps; step++) {
              const sample = getBezierPoint(p0, p1, p2, p3, step / steps);
              if (pointInRect(sample)) return true;
            }
          }

          if (path.isClosed) {
            const testPoint = { x: (minX + maxX) / 2, y: (minY + maxY) / 2 };
            const poly = [];
            for (let seg = 0; seg < path.points.length; seg++) {
              const p0 = path.points[seg];
              const p3 = path.points[(seg + 1) % path.points.length];
              const p1 = p0.hOut || p0;
              const p2 = p3.hIn || p3;
              for (let step = 0; step < 12; step++) {
                poly.push(getBezierPoint(p0, p1, p2, p3, step / 12));
              }
            }
            let inside = false;
            for (let k = 0, l = poly.length - 1; k < poly.length; l = k++) {
              const xk = poly[k].x, yk = poly[k].y;
              const xl = poly[l].x, yl = poly[l].y;
              const intersects = ((yk > testPoint.y) !== (yl > testPoint.y))
                && (testPoint.x < (xl - xk) * (testPoint.y - yk) / (yl - yk) + xk);
              if (intersects) inside = !inside;
            }
            if (inside) return true;
          }

          return false;
        };
        
        let newSelected = [];
        let newSelectedImageIds = [];
        if (e.shiftKey || e.altKey) {
          newSelected = [...selectionBox.initialSelection];
          newSelectedImageIds = [...selectionBox.initialSelectedImageIds];
        }
        
        paths.forEach((path, i) => {
          if (!isPathVisible(path) || isPathLocked(path)) return;
          if (activePathEditId && path.id !== activePathEditId) return;

          if (activePathEditId) {
            path.points.forEach((pt, j) => {
              if (!pointInRect(pt)) return;
              if (e.altKey) {
                newSelected = newSelected.filter(sp => !(sp.pathIndex === i && sp.pointIndex === j));
              } else if (e.shiftKey) {
                const initiallySelected = selectionBox.initialSelection.some(sp => sp.pathIndex === i && sp.pointIndex === j);
                if (initiallySelected) {
                  newSelected = newSelected.filter(sp => !(sp.pathIndex === i && sp.pointIndex === j));
                } else if (!newSelected.some(sp => sp.pathIndex === i && sp.pointIndex === j)) {
                  newSelected.push({ pathIndex: i, pointIndex: j });
                }
              } else if (!newSelected.some(sp => sp.pathIndex === i && sp.pointIndex === j)) {
                newSelected.push({ pathIndex: i, pointIndex: j });
              }
            });
            return;
          }

          if (!pathIntersectsMarquee(path)) return;
          const pathSelection = path.points.map((_, pointIndex) => ({ pathIndex: i, pointIndex }));

          if (e.altKey) {
            newSelected = newSelected.filter(sp => sp.pathIndex !== i);
            return;
          }

          if (e.shiftKey) {
            const wasInitiallySelected = pathSelection.every(sp => (
              selectionBox.initialSelection.some(init => init.pathIndex === sp.pathIndex && init.pointIndex === sp.pointIndex)
            ));
            if (wasInitiallySelected) {
              newSelected = newSelected.filter(sp => sp.pathIndex !== i);
              return;
            }
          }

          pathSelection.forEach(sp => {
            if (!newSelected.some(sel => sel.pathIndex === sp.pathIndex && sel.pointIndex === sp.pointIndex)) {
              newSelected.push(sp);
            }
          });
        });

        // Marquee intersection check for images
        images.forEach(img => {
          if (activePathEditId) return;
          const layer = layers.find(l => l.id === img.layerId);
          if (!layer || !layer.visible || layer.locked || img.locked) return;

          const imgMinX = img.x - (img.width * img.scale) / 2;
          const imgMaxX = img.x + (img.width * img.scale) / 2;
          const imgMinY = img.y - (img.height * img.scale) / 2;
          const imgMaxY = img.y + (img.height * img.scale) / 2;

          const intersects = !(imgMaxX < minX || imgMinX > maxX || imgMaxY < minY || imgMinY > maxY);

          if (intersects) {
            if (e.altKey) {
              newSelectedImageIds = newSelectedImageIds.filter(id => id !== img.id);
            } else {
              if (!newSelectedImageIds.includes(img.id)) newSelectedImageIds.push(img.id);
            }
          }
        });

        setSelectedImageIds(newSelectedImageIds);
        setSelectedPoints(newSelected);
      }
    }

    if (mode === 'edit' && !isDraggingPoints && !activeHandle && !selectionBox && !bgAction && !pointAction) {
      let hitAction = null;
      const hitBg = activePathEditId ? null : getBgHit(coords);
      
      let ptHit = null;
      if (selBBox && !e.shiftKey && !e.altKey) {
        const corners = [
          { id: 'nw', x: selBBox.minX, y: selBBox.minY, angle: 225 },
          { id: 'ne', x: selBBox.maxX, y: selBBox.minY, angle: 315 },
          { id: 'se', x: selBBox.maxX, y: selBBox.maxY, angle: 45 },
          { id: 'sw', x: selBBox.minX, y: selBBox.maxY, angle: 135 }
        ];
        for (const c of corners) {
          const dist = Math.hypot(coords.x - c.x, coords.y - c.y);
          if (dist <= scaleHandleHitRadius) {
            ptHit = { action: `scale-${c.id}`, cursorAngle: c.angle, type: 'point' };
            break;
          }
          if (dist <= rotateHandleHitRadius) {
            ptHit = { action: `rotate-${c.id}`, cursorAngle: null, type: 'point' };
            break;
          }
        }
      }

      if (ptHit) {
        hitAction = ptHit;
      } else if (hitBg && hitBg.action.startsWith('scale')) {
        hitAction = hitBg;
      } else if (hitBg && hitBg.action.startsWith('rotate')) {
        hitAction = hitBg;
      } else if (!e.shiftKey && !e.altKey && selBBox && coords.x >= selBBox.minX && coords.x <= selBBox.maxX && coords.y >= selBBox.minY && coords.y <= selBBox.maxY) {
        hitAction = { action: 'move-points' };
      } else if (hitBg && hitBg.action === 'move') {
        hitAction = hitBg;
      }
      
      setBgHoverAction(hitAction);
    } else {
      setBgHoverAction(null);
    }
  };

  const handlePointerUp = (e) => {
    releasePointer(e);
    pointerGestureRef.current = {
      pointerId: null,
      pointerType: 'mouse',
      startClientX: 0,
      startClientY: 0,
      dragActivated: false
    };
    setIsPanning(false);
    if (mode === 'shape') {
      if (drawingShape) {
        if (Math.hypot(drawingShape.currentX - drawingShape.startX, drawingShape.currentY - drawingShape.startY) > 2 / zoom) {
          const generated = generateShapePath(drawingShape.startX, drawingShape.startY, drawingShape.currentX, drawingShape.currentY, shapeType, drawingShape.shiftKey);
          commitHistory({ paths, currentPath, images, layers });
          
          const count = layers.filter(l => l.itemType === shapeType).length;
          const newLayer = createLayer(shapeType, count);
          const newPath = {
            id: Date.now(),
            points: generated.points,
            isClosed: generated.isClosed,
            layerId: newLayer.id,
            itemType: shapeType,
            fillEnabled: pathStyleDefaults.fillEnabled,
            strokeEnabled: pathStyleDefaults.strokeEnabled
          };
          const nextPaths = [...paths, newPath];

          setLayers(prev => [newLayer, ...prev]);
          setPaths(nextPaths);
          activatePathEditSession(nextPaths, newPath.id);
        }
        setDrawingShape(null);
      }
      return;
    }
    if (pointAction) {
      if (hasDraggedRef.current) {
          commitHistory({ paths: dragStartPathsRef.current, currentPath, images: dragStartImagesRef.current, layers });
          hasDraggedRef.current = false;
      }
      pointRotateRef.current = { lastAngle: 0, accumulated: 0 };
      setPointAction(null);
      return;
    }
    if (bgAction) {
      if (hasDraggedRef.current) {
         commitHistory({ paths: dragStartPathsRef.current, currentPath, images: dragStartImagesRef.current, layers });
         hasDraggedRef.current = false;
      }
      bgRotateRef.current = { lastAngle: 0, accumulated: 0 };
      setBgAction(null);
      setBgInitialState(null);
      return;
    }
    if (mode === 'pencil') {
      if (currentPath.length > 1) {
        let finalPath = [...currentPath];
        let isClosed = false;
        if (finalPath.length > 2) {
          const startP = finalPath[0];
          const lastP = finalPath[finalPath.length - 1];
          if (Math.hypot(startP.x - lastP.x, startP.y - lastP.y) < snapHitRadius) {
            isClosed = true;
            finalPath.pop(); // Remove redundant end point and close loop
          }
        }
        
        const count = layers.filter(l => l.itemType === 'vector').length;
        const newLayer = createLayer('vector', count);
        const newPath = {
          id: Date.now(),
          points: finalPath,
          isClosed,
          layerId: newLayer.id,
          itemType: 'vector',
          fillEnabled: pathStyleDefaults.fillEnabled,
          strokeEnabled: pathStyleDefaults.strokeEnabled
        };
        const nextPaths = [...paths, newPath];
        setLayers(prev => [newLayer, ...prev]);
        setPaths(nextPaths);
        activatePathEditSession(nextPaths, newPath.id);
      }
      setCurrentPath([]);
      setCurrentPathInfo(null);
      return;
    }
    if (mode === 'draw') {
      if (isDrawingCurve === 'closing') {
        finishPath(true);
      }
      setIsDrawingCurve(false);
    } else if (mode === 'edit') {
      if (hasDraggedRef.current) {
        commitHistory({ paths: dragStartPathsRef.current, currentPath, images: dragStartImagesRef.current, layers });
        hasDraggedRef.current = false;
      }
      setIsDraggingPoints(false);
      setActiveHandle(null);
      setSelectionBox(null);
    }
  };

  const zoomAtScreenPoint = useCallback((scaleMultiplier, screenX, screenY) => {
    const currentZoom = zoomRef.current;
    const currentPan = panRef.current;
    const newZoom = Math.min(Math.max(MIN_ZOOM, currentZoom * scaleMultiplier), MAX_ZOOM);
    if (newZoom === currentZoom) return;

    const worldX = (screenX - currentPan.x) / currentZoom;
    const worldY = (screenY - currentPan.y) / currentZoom;
    const nextPan = {
      x: screenX - worldX * newZoom,
      y: screenY - worldY * newZoom
    };

    panRef.current = nextPan;
    zoomRef.current = newZoom;
    setPan(nextPan);
    setZoom(newZoom);
  }, []);

  const stepZoom = useCallback((direction) => {
    const scaleMultiplier = direction > 0 ? 1.2 : 1 / 1.2;
    zoomAtScreenPoint(
      scaleMultiplier,
      window.innerWidth / 2,
      window.innerHeight / 2
    );
  }, [zoomAtScreenPoint]);

  const handleWheel = useCallback((e) => {
    e.preventDefault();
    const zoomSensitivity = 0.001;
    const delta = -e.deltaY * zoomSensitivity;
    const currentZoom = zoomRef.current;
    const currentPan = panRef.current;
    const newZoom = Math.min(Math.max(MIN_ZOOM, currentZoom * (1 + delta)), MAX_ZOOM);
    if (newZoom === currentZoom) return;
    if (!svgRef.current) return;
    
    const rect = svgRef.current.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    const worldX = (mouseX - currentPan.x) / currentZoom;
    const worldY = (mouseY - currentPan.y) / currentZoom;
    const nextPan = {
      x: mouseX - worldX * newZoom,
      y: mouseY - worldY * newZoom
    };

    panRef.current = nextPan;
    zoomRef.current = newZoom;
    setPan(nextPan);
    setZoom(newZoom);
  }, []);

  // --- ACTIONS --- 
  const activatePathEditSession = (nextPaths, pathId) => {
    const pathIndex = nextPaths.findIndex(p => p.id === pathId);
    if (pathIndex === -1) return;
    const path = nextPaths[pathIndex];
    setMode('edit');
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

  const finishPath = (isClosed = false, enterDirectEdit = true) => {
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
      const newPath = {
        id: Date.now(),
        points: currentPath,
        isClosed,
        layerId: targetLayerId,
        itemType: layerType,
        fillEnabled: currentPathInfo?.fillEnabled ?? pathStyleDefaults.fillEnabled,
        strokeEnabled: currentPathInfo?.strokeEnabled ?? pathStyleDefaults.strokeEnabled
      };
      const nextPaths = [...paths, newPath];
      setPaths(nextPaths);
      if (enterDirectEdit) {
        activatePathEditSession(nextPaths, newPath.id);
      }
    }
    setCurrentPath([]);
    setCurrentPathInfo(null);
    setGhostPoint(null);
    setHoveredStartPoint(false);
    setIsDrawingCurve(false);
    setSnapState({ endpoint: null, segment: null });
  };

  const changeMode = (newMode) => {
    const targetMode = newMode;

    if ((mode === 'draw' || mode === 'pencil') && targetMode !== mode && currentPath.length > 0) {
      finishPath(false, false);
    }
    setMode(targetMode);
    setDrawHover(null);
    setHoveredHandle(null);
    
    // Always close the shape menu when transitioning modes
    setShowShapeMenu(false);
    if (isMobile) {
      setMobileToolsOpen(false);
    }

    if (targetMode !== 'shape') {
      setDrawingShape(null);
    }

    if (targetMode === 'edit' && !activePathEditId && lastFocusedPathEditIdRef.current) {
      const candidatePath = paths.find(p => p.id === lastFocusedPathEditIdRef.current);
      const candidateLayer = candidatePath ? layers.find(l => l.id === candidatePath.layerId) : null;
      if (candidatePath && candidateLayer?.visible && !candidateLayer.locked) {
        setActivePathEditId(candidatePath.id);
        setActiveLayerId(candidatePath.layerId);
      } else {
        lastFocusedPathEditIdRef.current = null;
      }
    }

    if (targetMode !== 'edit') {
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
  };

  // --- SKETCH UPLOAD ---
  const handleImageUpload = (e) => {
    if (activeLayerId && lockedLayerIds.has(activeLayerId)) return;

    const file = e.target.files?.[0];
    if (file) {
      const url = URL.createObjectURL(file);
      const img = new window.Image();
      img.onload = () => {
        commitHistory({ paths, currentPath, images, layers });
        const count = layers.filter(l => l.itemType === 'image').length;
        const newLayer = createLayer('image', count);
        setLayers(prev => [newLayer, ...prev]);
        setActiveLayerId(newLayer.id);

        const newImg = {
          id: Date.now(),
          url,
          width: img.width,
          height: img.height,
          x: 0,
          y: 0,
          scale: 1,
          rotation: 0,
          opacity: 0.35,
          locked: false,
          layerId: newLayer.id
        };
        setImages(prev => [...prev, newImg]);
        setSelectedImageIds([newImg.id]);
        setSelectedPoints([]);
        setOpenPanels(prev => ({ ...prev, image: true }));
        setExpandedPanel('image');
      };
      img.src = url;
    }
    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }
  };

  // --- PASTE HANDLER ---
  useEffect(() => {
    const handlePaste = (e) => {
      if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;
      if (activeLayerId && lockedLayerIds.has(activeLayerId)) return;

      // 1. Try to paste JSON paths first
      try {
        const textData = e.clipboardData?.getData('text/plain');
        if (textData) {
          const parsed = JSON.parse(textData);
          if (parsed && parsed.type === 'typolab-paths') {
            e.preventDefault();
            commitHistory({ paths, currentPath, images, layers });
            
            const newLayers = [];
            const newPaths = [];
            const newImages = [];
            const newSelPoints = [];
            const newSelImages = [];

            if (Array.isArray(parsed.paths)) {
              parsed.paths.forEach(p => {
                const layerType = p.itemType || 'vector';
                const count = layers.filter(l => l.itemType === layerType).length + newLayers.filter(l => l.itemType === layerType).length;
                const l = createLayer(layerType, count);
                newLayers.push(l);
                const newPath = {
                  ...p,
                  id: Date.now() + Math.random(),
                  layerId: l.id,
                  itemType: layerType,
                  fillEnabled: !!p.fillEnabled,
                  strokeEnabled: p.strokeEnabled !== false
                };
                newPaths.push(newPath);
              });
            }

            if (Array.isArray(parsed.images)) {
              parsed.images.forEach(img => {
                const count = layers.filter(l => l.itemType === 'image').length + newLayers.filter(l => l.itemType === 'image').length;
                const l = createLayer('image', count);
                newLayers.push(l);
                const newImg = { ...img, id: Date.now() + Math.random(), layerId: l.id };
                newImages.push(newImg);
              });
            }
            
            if (newLayers.length > 0) {
               setLayers(prev => [...newLayers, ...prev]);
            }
            if (newPaths.length > 0) {
               setPaths(prev => {
                  const updated = [...prev, ...newPaths];
                  if (mode === 'edit') {
                     const startIndex = prev.length;
                     newPaths.forEach((np, i) => {
                       np.points.forEach((_, j) => {
                         newSelPoints.push({ pathIndex: startIndex + i, pointIndex: j });
                       });
                     });
                     setSelectedPoints(newSelPoints);
                  }
                  return updated;
               });
            }
            if (newImages.length > 0) {
               setImages(prev => {
                  const updated = [...prev, ...newImages];
                  if (mode === 'edit') {
                     newImages.forEach(img => newSelImages.push(img.id));
                     setSelectedImageIds(newSelImages);
                  }
                  return updated;
               });
            }
            return;
          }
        }
      } catch (err) {
        // Not our JSON, ignore and continue to image paste check
      }

      // 2. Fallback to image paste
      const items = e.clipboardData?.items;
      if (!items) return;

      for (let i = 0; i < items.length; i++) {
        if (items[i].type.indexOf('image') !== -1) {
          const file = items[i].getAsFile();
          if (file) {
            const url = URL.createObjectURL(file);
            const img = new window.Image();
            img.onload = () => {
              commitHistory({ paths, currentPath, images, layers });
              const count = layers.filter(l => l.itemType === 'image').length;
              const newLayer = createLayer('image', count);
              setLayers(prev => [newLayer, ...prev]);

              const newImg = {
                id: Date.now(),
                url, width: img.width, height: img.height,
                x: 0, y: 0, scale: 1, rotation: 0, opacity: 0.35, locked: false,
                layerId: newLayer.id
              };
              setImages(prev => [...prev, newImg]);
              setSelectedImageIds([newImg.id]);
              setOpenPanels(prev => ({ ...prev, image: true }));
              setExpandedPanel('image');
            };
            img.src = url;
          }
          break; 
        }
      }
    };

    window.addEventListener('paste', handlePaste);
    return () => window.removeEventListener('paste', handlePaste);
  }, [layers, paths, currentPath, images, commitHistory, mode, activeLayerId, lockedLayerIds]);

  // --- LAYER MANAGEMENT ---
  const toggleLayerVisibility = (id) => {
    const selectedIds = new Set();
    selectedImageIds.forEach(imgId => {
      const img = images.find(i => i.id === imgId);
      if (img) selectedIds.add(img.layerId);
    });
    selectedPoints.forEach(sp => {
      const p = paths[sp.pathIndex];
      if (p) selectedIds.add(p.layerId);
    });

    const targetIds = selectedIds.size > 1 && selectedIds.has(id) ? [...selectedIds] : [id];
    const targetIdSet = new Set(targetIds);
    const targetLayers = layers.filter(l => targetIdSet.has(l.id));
    if (targetLayers.length === 0) return;

    const makeVisible = targetLayers.some(l => !l.visible);
    setLayers(prev => prev.map(l => targetIdSet.has(l.id) ? { ...l, visible: makeVisible } : l));

    if (!makeVisible) {
      setSelectedPoints(prev => prev.filter(sp => {
        const p = paths[sp.pathIndex];
        return p && !targetIdSet.has(p.layerId);
      }));
      setSelectedImageIds(prev => prev.filter(imgId => {
        const img = images.find(i => i.id === imgId);
        return img && !targetIdSet.has(img.layerId);
      }));
    }
  };

  const toggleLayerLock = (id) => {
    const selectedIds = new Set();
    selectedImageIds.forEach(imgId => {
      const img = images.find(i => i.id === imgId);
      if (img) selectedIds.add(img.layerId);
    });
    selectedPoints.forEach(sp => {
      const p = paths[sp.pathIndex];
      if (p) selectedIds.add(p.layerId);
    });

    const targetIds = selectedIds.size > 1 && selectedIds.has(id) ? [...selectedIds] : [id];
    const targetIdSet = new Set(targetIds);
    const targetLayers = layers.filter(l => targetIdSet.has(l.id));
    if (targetLayers.length === 0) return;

    const makeLocked = targetLayers.some(l => !l.locked);
    setLayers(prevLayers => prevLayers.map(l => targetIdSet.has(l.id) ? { ...l, locked: makeLocked } : l));
    
    if (makeLocked) {
      // Locking deselects anything on the affected layers.
      setSelectedPoints(prev => prev.filter(sp => {
        const p = paths[sp.pathIndex];
        return p && !targetIdSet.has(p.layerId);
      }));
      setSelectedImageIds(prev => prev.filter(imgId => {
          const img = images.find(i => i.id === imgId);
          return img && !targetIdSet.has(img.layerId);
      }));
    }
  };

  const startEditingLayer = (layer) => {
    setEditingLayerId(layer.id);
    setEditingLayerName(layer.name);
  };

  const saveLayerName = () => {
    if (editingLayerId && editingLayerName.trim()) {
      setLayers(layers.map(l => l.id === editingLayerId ? { ...l, name: editingLayerName.trim() } : l));
    }
    setEditingLayerId(null);
    setEditingLayerName("");
  };

  const handleLayerNameKeyDown = (e) => {
    if (e.key === 'Enter') {
      saveLayerName();
    } else if (e.key === 'Escape') {
      setEditingLayerId(null);
      setEditingLayerName("");
    }
  };

  const handleLayerDragStart = (e, id) => {
    setDraggedLayerId(id);
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('text/plain', id); 
  };

  const handleLayerDragOver = (e, id) => {
    e.preventDefault(); 
    e.dataTransfer.dropEffect = 'move';
    const rect = e.currentTarget.getBoundingClientRect();
    const y = e.clientY - rect.top;
    const position = y < rect.height / 2 ? 'top' : 'bottom';
    
    if (!dragDropTarget || dragDropTarget.id !== id || dragDropTarget.position !== position) {
      setDragDropTarget({ id, position });
    }
  };

  const handleLayerDrop = (e, targetId) => {
    e.preventDefault();
    if (draggedLayerId && draggedLayerId !== targetId && dragDropTarget) {
      setLayers(prev => {
        const oldIndex = prev.findIndex(l => l.id === draggedLayerId);
        if (oldIndex === -1) return prev;
        const newLayers = [...prev];
        const [movedLayer] = newLayers.splice(oldIndex, 1);
        
        let newIndex = newLayers.findIndex(l => l.id === targetId);
        if (dragDropTarget.position === 'bottom') {
           newIndex += 1;
        }
        
        newLayers.splice(newIndex, 0, movedLayer);
        return newLayers;
      });
    }
    setDraggedLayerId(null);
    setDragDropTarget(null);
  };

  const handleLayerDragEnd = () => {
    setDraggedLayerId(null);
    setDragDropTarget(null);
  };

  const handleLayerSelect = (e, layer) => {
      e.stopPropagation();
      let newSelectedLayerIds = new Set(selectedLayerIds);
      
      if (e.shiftKey && lastSelectedLayerId) {
          const currentIndex = layers.findIndex(l => l.id === layer.id);
          const lastIndex = layers.findIndex(l => l.id === lastSelectedLayerId);
          const start = Math.min(currentIndex, lastIndex);
          const end = Math.max(currentIndex, lastIndex);
          
          if (!e.ctrlKey && !e.metaKey) {
              newSelectedLayerIds.clear();
          }
          for(let i = start; i <= end; i++) {
              newSelectedLayerIds.add(layers[i].id);
          }
      } else if (e.ctrlKey || e.metaKey) {
          if (newSelectedLayerIds.has(layer.id)) newSelectedLayerIds.delete(layer.id);
          else newSelectedLayerIds.add(layer.id);
          setLastSelectedLayerId(layer.id);
      } else {
          newSelectedLayerIds = new Set([layer.id]);
          setLastSelectedLayerId(layer.id);
          setActiveLayerId(layer.id);
      }
      
      const newSelPoints = [];
      const newSelImages = [];
      newSelectedLayerIds.forEach(lId => {
          const layerObj = layers.find(l => l.id === lId);
          if (!layerObj || layerObj.locked || !layerObj.visible) return;
          
          if (layerObj.itemType === 'image') {
              const img = images.find(i => i.layerId === lId);
              if (img) newSelImages.push(img.id);
          } else {
              paths.forEach((p, pIdx) => {
                  if (p.layerId === lId) {
                      p.points.forEach((_, ptIdx) => {
                          newSelPoints.push({ pathIndex: pIdx, pointIndex: ptIdx });
                      });
                  }
              });
          }
      });
      
      if (mode !== 'edit') {
          changeMode('edit');
      }
      
      setActivePathEditId(null);
      setSelectedPoints(newSelPoints);
      setSelectedImageIds(newSelImages);
  };

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
            const copiedPaths = [...new Set(selectedPoints.map(sp => sp.pathIndex))].map(idx => paths[idx]);
            const copiedImages = images.filter(img => selectedImageIds.includes(img.id));
            
            const dataStr = JSON.stringify({
              type: 'typolab-paths',
              paths: copiedPaths,
              images: copiedImages
            });
            
            copyToClipboard(dataStr);
        }
        return;
      }

      // Cut
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'x' && mode === 'edit') {
        if (selectedPoints.length > 0 || selectedImageIds.length > 0) {
            e.preventDefault();
            const copiedPaths = [...new Set(selectedPoints.map(sp => sp.pathIndex))].map(idx => paths[idx]);
            const copiedImages = images.filter(img => selectedImageIds.includes(img.id));
            
            const dataStr = JSON.stringify({
              type: 'typolab-paths',
              paths: copiedPaths,
              images: copiedImages
            });
            
            copyToClipboard(dataStr);
            deleteSelectedItems();
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
      if (e.key.toLowerCase() === 'g') {
        togglePanel('guides');
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
  }, [mode, selectedPoints, selectedImageIds, currentPath, pastPaths, futurePaths, paths, images, layers, handleUndo, handleRedo, commitHistory, deleteSelectedItems, editingLayerId, activePathEditId]);

  // --- RENDER HELPERS ---
  const strokeWidth = 1.5 / zoom;

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

  if (gridConfig.type === 'dots') {
    patternW = s;
    patternH = s;
    patternContent = <circle cx={1/zoom} cy={1/zoom} r={1.5/zoom} fill="#d1ccc7" />;
  } else if (gridConfig.type === 'circles') {
    patternW = s;
    patternH = s;
    patternContent = <circle cx={s/2} cy={s/2} r={s / 2} fill="none" stroke="#d1ccc7" strokeWidth={1/zoom} />;
  } else if (gridConfig.type === 'lines') {
    if (gridConfig.edges === 4) {
      patternW = s;
      patternH = s;
      patternContent = <path d={`M ${s} 0 L 0 0 L 0 ${s}`} fill="none" stroke="#d1ccc7" strokeWidth={1/zoom} />;
    } else if (gridConfig.edges === 3) {
      patternW = s;
      patternH = s * Math.sqrt(3);
      patternContent = <path d={`M 0 0 L ${patternW} 0 M 0 ${patternH/2} L ${patternW} ${patternH/2} M 0 ${patternH/2} L ${patternW/2} 0 M ${patternW/2} ${patternH} L ${patternW} ${patternH/2} M ${patternW/2} 0 L ${patternW} ${patternH/2} M 0 ${patternH/2} L ${patternW/2} ${patternH}`} fill="none" stroke="#d1ccc7" strokeWidth={1/zoom} />;
    } else if (gridConfig.edges === 6) {
      patternW = s * Math.sqrt(3);
      patternH = s * 3;
      patternContent = <path d={`M 0 ${0.5*s} L ${patternW/2} 0 L ${patternW} ${0.5*s} L ${patternW} ${1.5*s} L ${patternW/2} ${2*s} L 0 ${1.5*s} Z M ${patternW/2} ${2*s} L ${patternW/2} ${3*s}`} fill="none" stroke="#d1ccc7" strokeWidth={1/zoom} />;
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
  const hasSelectedPaths = selectedPathObjects.length > 0;
  const fillToggleActive = hasSelectedPaths
    ? selectedPathObjects.every(path => !!path.fillEnabled)
    : pathStyleDefaults.fillEnabled;
  const strokeToggleActive = true;

  const applyPathStyle = (updates) => {
    if (hasSelectedPaths) {
      commitHistory({ paths, currentPath, images, layers });
      const selectedSet = new Set(selectedPathIndices);
      setPaths(prev => prev.map((path, idx) => (
        selectedSet.has(idx) ? { ...path, ...updates } : path
      )));
      return;
    }
    setPathStyleDefaults(prev => ({ ...prev, ...updates }));
  };

  const selectedLayerIds = new Set();
  if (selectedImageIds.length > 0) {
      selectedImageIds.forEach(id => {
          const img = images.find(i => i.id === id);
          if (img) selectedLayerIds.add(img.layerId);
      });
  }
  selectedPoints.forEach(sp => {
      const path = paths[sp.pathIndex];
      if (path) selectedLayerIds.add(path.layerId);
  });
  const compositeFillPathD = paths
    .filter(path => path.isClosed && path.fillEnabled && visibleLayerIds.has(path.layerId))
    .map(path => pointsToPath(path.points, path.isClosed))
    .join(' ');
  const anyPanelOpen = Object.values(openPanels).some(Boolean);
  const closeAllPanels = () => {
    setOpenPanels({ grid: false, image: false, guides: false, layers: false });
    setExpandedPanel(null);
  };
  const toggleMobilePanelTray = () => {
    if (mobilePanelsOpen || anyPanelOpen) {
      setMobilePanelsOpen(false);
      closeAllPanels();
      return;
    }
    setMobilePanelsOpen(true);
    setOpenPanels(prev => ({ ...prev, layers: true }));
    setExpandedPanel('layers');
  };

  return (
    <div className="w-screen h-screen bg-[#f4f1ed] overflow-hidden select-none font-sans text-slate-800 flex flex-col fixed inset-0 touch-none">
      
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
        .cursor-pen {
          cursor: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='white' stroke='%234a2622' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M12 19l7-7 3 3-7 7-3-3z'/%3E%3Cpath d='M18 13l-1.5-7.5L2 2l3.5 14.5L13 18l5-5z'/%3E%3Cpath d='M2 2l7.586 7.586'/%3E%3Ccircle cx='11' cy='11' r='2'/%3E%3C/svg%3E") 2 2, crosshair !important;
        }
        .cursor-pencil {
          cursor: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='24' height='24' viewBox='0 0 24 24' fill='white' stroke='%234a2622' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M17 3a2.828 2.828 0 1 1 4 4L7.5 20.5 2 22l1.5-5.5L17 3z'/%3E%3C/svg%3E") 2 22, crosshair !important;
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
          transform: translateY(-8px);
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
      >
        <defs>
          {gridConfig.type !== 'none' && gridConfig.type !== 'circular' && (
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
          {showPixelGrid && (
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
                  stroke="#8c746f"
                  strokeOpacity="0.22"
                  strokeWidth={1 / zoom}
                />
              </g>
            </pattern>
          )}
        </defs>

        {/* Background Grid */}
        {gridConfig.type !== 'none' && gridConfig.type !== 'circular' && <rect width="100%" height="100%" fill="url(#bg-grid)" />}

        {/* Transform Group for Pan & Zoom */}
        <g transform={`translate(${pan.x}, ${pan.y}) scale(${zoom})`}>
          
          {/* Circular Grid (Drawn inside world coordinates) */}
          {gridConfig.type === 'circular' && (
            <g className="opacity-60 pointer-events-none">
              {Array.from({length: 100}).map((_, i) => (
                <circle key={`circ-${i}`} cx={0} cy={0} r={(i + 1) * s} stroke="#d1ccc7" strokeWidth={1/zoom} fill="none" />
              ))}
              {Array.from({length: circularRayCount}).map((_, i) => {
                 const angle = (i * effectiveCircularStep * Math.PI) / 180;
                 return <line key={`rad-${i}`} x1={-5000 * Math.cos(angle)} y1={-5000 * Math.sin(angle)} x2={5000 * Math.cos(angle)} y2={5000 * Math.sin(angle)} stroke="#d1ccc7" strokeWidth={1/zoom} />
              })}
            </g>
          )}

          {/* Typographic Guides */}
          {showGuides && (
            <g className="opacity-60 pointer-events-none">
              <line x1="-10000" y1={-guides.capHeight} x2="10000" y2={-guides.capHeight} stroke="#7dd3fc" strokeWidth={1/zoom} strokeDasharray={`${4/zoom},${4/zoom}`} />
              <text x="10" y={-guides.capHeight - 5/zoom} fontSize={12/zoom} fill="#7dd3fc" className="uppercase tracking-widest font-mono">Cap Height</text>
              
              <line x1="-10000" y1={-guides.xHeight} x2="10000" y2={-guides.xHeight} stroke="#818cf8" strokeWidth={1/zoom} strokeDasharray={`${4/zoom},${4/zoom}`} />
              <text x="10" y={-guides.xHeight - 5/zoom} fontSize={12/zoom} fill="#818cf8" className="uppercase tracking-widest font-mono">X-Height</text>
              
              <line x1="-10000" y1={0} x2="10000" y2={0} stroke="#f43f5e" strokeWidth={1/zoom} />
              <text x="10" y={0 - 5/zoom} fontSize={12/zoom} fill="#f43f5e" className="uppercase tracking-widest font-mono">Baseline</text>

              <line x1="-10000" y1={guides.descender} x2="10000" y2={guides.descender} stroke="#c084fc" strokeWidth={1/zoom} strokeDasharray={`${4/zoom},${4/zoom}`} />
              <text x="10" y={guides.descender - 5/zoom} fontSize={12/zoom} fill="#c084fc" className="uppercase tracking-widest font-mono">Descender</text>
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
                      imageRendering={showPixelGrid ? 'pixelated' : 'auto'}
                      style={showPixelGrid ? { imageRendering: 'pixelated' } : undefined}
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
                const pathD = pointsToPath(path.points, path.isClosed);

                return (
                  <g key={path.id}>
                    <path 
                      d={pathD} 
                      fill="none" 
                      stroke={THEME.main} 
                      strokeWidth={strokeWidth}
                      strokeLinejoin="round"
                      strokeLinecap="round"
                    />
                    
                    {/* Nodes and Handles (controlled by Show Nodes, hidden only in pencil mode, and when unlocked) */}
                    {showNodes && (mode === 'edit' || mode === 'draw') && !layer.locked && activePathEditId === path.id && (
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
              stroke={THEME.main}
              strokeWidth={strokeWidth}
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
                       strokeWidth={1/zoom}
                       strokeDasharray={`${4/zoom},${4/zoom}`}
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
                         strokeWidth={1.5/zoom}
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
                stroke={THEME.main} 
                strokeWidth={strokeWidth}
                strokeLinejoin="round"
                strokeLinecap="round"
              />
              
              {/* Ghost segment to mouse cursor (only for pen tool) */}
              {ghostPoint && !isDrawingCurve && mode === 'draw' && (
                <path 
                  d={`M ${currentPath[currentPath.length - 1].x} ${currentPath[currentPath.length - 1].y} C ${currentPath[currentPath.length - 1].hOut ? currentPath[currentPath.length - 1].hOut.x : currentPath[currentPath.length - 1].x} ${currentPath[currentPath.length - 1].hOut ? currentPath[currentPath.length - 1].hOut.y : currentPath[currentPath.length - 1].y}, ${ghostPoint.x} ${ghostPoint.y}, ${ghostPoint.x} ${ghostPoint.y}`}
                  fill="none"
                  stroke="#a89b99" 
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
                <rect x={ghostPoint.x - 3/zoom} y={ghostPoint.y - 3/zoom} width={6/zoom} height={6/zoom} fill="#a89b99" />
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
        {showPixelGrid && (
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

      {isMobile && (
        <>
          {(mobilePanelsOpen || anyPanelOpen) && (
            <button
              type="button"
              onClick={() => {
                setMobilePanelsOpen(false);
                closeAllPanels();
              }}
              className="absolute inset-0 z-[9] bg-[#4a2622]/8 backdrop-blur-[1px]"
              aria-label="Close panels overlay"
            />
          )}

          <div className="absolute top-3 left-3 right-3 z-20 flex items-center justify-between pointer-events-none">
            <button
              onClick={() => setMobileToolsOpen(prev => !prev)}
              className={`pointer-events-auto h-11 w-11 rounded-xl border border-[#e8dfdb] shadow-sm flex items-center justify-center transition-colors ${
                mobileToolsOpen ? 'bg-[#ede3e1] text-[#4a2622]' : 'bg-[#f1f0f5] text-[#6d6a76]'
              }`}
              title="Tools"
            >
              <GripVertical size={18} />
            </button>
            <button
              onClick={toggleMobilePanelTray}
              className={`pointer-events-auto h-11 w-11 rounded-xl border border-[#e8dfdb] shadow-sm flex items-center justify-center transition-colors ${
                mobilePanelsOpen || anyPanelOpen ? 'bg-[#ede3e1] text-[#4a2622]' : 'bg-[#f1f0f5] text-[#6d6a76]'
              }`}
              title="Panels"
            >
              <Layers size={18} />
            </button>
          </div>

          <div
            className={`absolute top-16 left-3 right-3 z-20 bg-[#fdfcfa] rounded-2xl shadow-lg border border-[#e8dfdb] p-2 mobile-drawer ${
              mobileToolsOpen ? 'mobile-drawer-open' : 'mobile-drawer-closed'
            }`}
          >
              <div className="grid grid-cols-5 gap-1">
                <MobileToolButton active={mode === 'edit'} onClick={() => changeMode('edit')} icon={<MousePointer2 size={17} />} label="Edit" />
                <MobileToolButton active={mode === 'draw'} onClick={() => changeMode('draw')} icon={<PenTool size={17} />} label="Path" />
                <MobileToolButton active={mode === 'pencil'} onClick={() => changeMode('pencil')} icon={<Pencil size={17} />} label="Pencil" />
                <MobileToolButton active={mode === 'shape'} onClick={() => changeMode('shape')} icon={<Square size={17} />} label="Shape" />
                <MobileToolButton active={mode === 'pan'} onClick={() => changeMode('pan')} icon={<Hand size={17} />} label="Pan" />
              </div>
              <div className="mt-2 grid grid-cols-4 gap-1">
                <MobileToolButton active={showNodes} onClick={() => setShowNodes(prev => !prev)} icon={<CircleDot size={16} />} label="Nodes" />
                <MobileToolButton
                  active={fillToggleActive}
                  onClick={() => applyPathStyle({ fillEnabled: !fillToggleActive })}
                  icon={<Droplet size={16} />}
                  label="Fill"
                />
                <MobileToolButton onClick={correctPathDirections} icon={<RefreshCw size={16} />} label="Reverse" />
                <MobileToolButton
                  onClick={() => {
                    fileInputRef.current?.click();
                    setMobilePanelsOpen(true);
                    setOpenPanels(prev => ({ ...prev, image: true }));
                    setExpandedPanel('image');
                  }}
                  icon={<ImageIcon size={16} />}
                  label="Image"
                />
              </div>
            </div>

          <div className="absolute bottom-[84px] left-3 right-3 z-20 flex items-center justify-between pointer-events-none">
            <div className="pointer-events-auto bg-[#fdfcfa] rounded-xl shadow-md border border-[#e8dfdb] p-1 flex items-center gap-1">
              <MobileToolButton onClick={handleUndo} icon={<RefreshCw size={15} className="-scale-x-100" />} label="Undo" />
              <MobileToolButton onClick={handleRedo} icon={<RefreshCw size={15} />} label="Redo" />
            </div>
            <div className="pointer-events-auto bg-[#fdfcfa] rounded-xl shadow-md border border-[#e8dfdb] p-1 flex items-center gap-1">
              <MobileToolButton onClick={() => stepZoom(-1)} icon={<Minus size={15} />} label="Zoom Out" />
              <div className="px-2 text-[11px] font-mono text-[#8c746f] min-w-[52px] text-center">
                {Math.round(zoom * 100)}%
              </div>
              <MobileToolButton onClick={() => stepZoom(1)} icon={<Plus size={15} />} label="Zoom In" />
            </div>
          </div>

          <div className="absolute bottom-3 left-3 right-3 z-20 pointer-events-none">
            <div className="pointer-events-auto bg-[#fdfcfa] rounded-2xl shadow-lg border border-[#e8dfdb] p-1.5">
              <div className="flex items-center gap-1 overflow-x-auto">
                <MobileToolButton active={mode === 'edit'} onClick={() => changeMode('edit')} icon={<MousePointer2 size={18} />} label="Edit" />
                <MobileToolButton active={mode === 'draw'} onClick={() => changeMode('draw')} icon={<PenTool size={18} />} label="Path" />
                <MobileToolButton active={mode === 'pencil'} onClick={() => changeMode('pencil')} icon={<Pencil size={18} />} label="Pencil" />
                <MobileToolButton
                  active={mode === 'shape'}
                  onClick={() => {
                    changeMode('shape');
                    setShapeType('rectangle');
                  }}
                  icon={<Square size={18} />}
                  label="Shape"
                />
                <MobileToolButton active={mode === 'pan'} onClick={() => changeMode('pan')} icon={<Hand size={18} />} label="Pan" />
                <MobileToolButton active={openPanels.grid} onClick={() => { setMobilePanelsOpen(true); togglePanel('grid'); }} icon={<Grid size={18} />} label="Grid" />
                <MobileToolButton active={openPanels.layers} onClick={() => { setMobilePanelsOpen(true); togglePanel('layers'); }} icon={<Layers size={18} />} label="Layers" />
                <MobileToolButton onClick={clearCanvas} icon={<Trash2 size={18} />} label="Clear" />
              </div>
              {mode === 'shape' && (
                <div className="mt-1.5 flex items-center gap-1 overflow-x-auto pt-1 border-t border-[#ece5e2]">
                  <MobileToolButton active={shapeType === 'rectangle'} onClick={() => setShapeType('rectangle')} icon={<Square size={16} />} label="Rect" />
                  <MobileToolButton active={shapeType === 'ellipse'} onClick={() => setShapeType('ellipse')} icon={<Circle size={16} />} label="Ellipse" />
                  <MobileToolButton active={shapeType === 'polygon'} onClick={() => setShapeType('polygon')} icon={<Triangle size={16} />} label="Poly" />
                  <MobileToolButton active={shapeType === 'star'} onClick={() => setShapeType('star')} icon={<Star size={16} />} label="Star" />
                  <MobileToolButton active={shapeType === 'line'} onClick={() => setShapeType('line')} icon={<Minus size={16} />} label="Line" />
                </div>
              )}
            </div>
          </div>
        </>
      )}

      {/* Right-Side Panels Container */}
      <div
        className={`absolute flex flex-col gap-2 z-10 pointer-events-none ${
          isMobile
            ? `top-16 left-3 right-3 max-h-[56vh] overflow-y-auto items-stretch mobile-panels-wrap ${
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
              className={`bg-[#fdfcfa] rounded-2xl shadow-lg border border-[#e8dfdb] flex flex-col pointer-events-auto shrink-0 transition-all duration-300 ${
                isMobile ? 'w-full' : 'w-60'
              }`}
            >
              <div 
                className={`flex items-center justify-between px-3 py-2.5 cursor-pointer hover:bg-[#f4f1ed] transition-colors rounded-t-2xl ${!isExpanded ? 'rounded-b-2xl' : 'border-b border-[#e8dfdb] bg-[#f4f1ed]'}`}
                onClick={() => {
                  setExpandedPanel(isExpanded ? null : panel.id);
                }}
              >
                <h3 className="text-[10px] font-bold text-[#8c746f] uppercase tracking-widest select-none">{panel.title}</h3>
                <button 
                  onClick={(e) => { e.stopPropagation(); setOpenPanels(p => ({...p, [panel.id]: false})); if(expandedPanel===panel.id) setExpandedPanel(null); }}
                  className="p-1 -mr-1 hover:bg-[#ede3e1] rounded text-[#8c746f] hover:text-[#4a2622] transition-colors"
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
                        <div className="grid grid-cols-3 gap-2 bg-[#f4f1ed] p-1.5 rounded-lg">
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'none' ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'none'})}
                           >None</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'dots' ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'dots'})}
                           >Dots</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'lines' ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'lines'})}
                           >Grid</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'circular' ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'circular'})}
                           >Circular</button>
                           <button
                              className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'circles' ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                              onClick={() => setGridConfig({...gridConfig, type: 'circles'})}
                           >Circles</button>
                        </div>

                        {gridConfig.type === 'lines' && (
                          <div className="flex flex-col gap-2 mt-1">
                            <label className="text-[10px] font-bold text-[#8c746f] uppercase tracking-widest px-1">Grid Shape (Edges)</label>
                            <div className="flex gap-2 bg-[#f4f1ed] p-1.5 rounded-lg">
                               <button
                                  className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 3 ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                                  onClick={() => setGridConfig({...gridConfig, edges: 3})}
                               >3 (Tri)</button>
                               <button
                                  className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 4 ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                                  onClick={() => setGridConfig({...gridConfig, edges: 4})}
                               >4 (Sqr)</button>
                               <button
                                  className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 6 ? 'bg-white shadow-sm text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622]'}`}
                                  onClick={() => setGridConfig({...gridConfig, edges: 6})}
                               >6 (Hex)</button>
                            </div>
                          </div>
                        )}

                        {gridConfig.type !== 'none' && (
                          <div className="flex flex-col gap-2 mt-1">
                            <div className="grid grid-cols-[1fr_88px] items-center gap-2">
                              <label className="text-[10px] font-bold text-[#8c746f] uppercase tracking-widest px-1">Grid Density</label>
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
                                <label className="text-[10px] font-bold text-[#8c746f] uppercase tracking-widest px-1">Angle Step</label>
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
                        
                        <div className="flex items-center justify-between mt-2 pt-3 border-t border-[#e8dfdb]">
                           <label className="text-[10px] font-bold text-[#8c746f] uppercase tracking-widest px-1">Snap to Grid</label>
                           <button
                               onClick={() => setGridConfig({...gridConfig, snapToGrid: !gridConfig.snapToGrid})}
                               className={`relative inline-flex h-4 w-7 items-center rounded-full transition-colors focus:outline-none ${gridConfig.snapToGrid ? 'bg-[#4a2622]' : 'bg-[#d4c8c5]'}`}
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
                        className="flex items-center justify-center gap-2 py-2 bg-[#f4f1ed] hover:bg-[#ede3e1] text-[#4a2622] rounded-lg text-xs font-semibold transition-colors border border-[#d4c8c5]"
                      >
                        <ImageIcon size={14} />
                        Upload Image
                      </button>

                      {activeImage && (
                        <div className="flex flex-col gap-2 mt-2 pt-2 border-t border-[#e8dfdb]">
                          <div className="flex items-center justify-between px-1 mb-1">
                            <label className="text-[10px] font-bold text-[#8c746f] uppercase tracking-widest">Image Transform</label>
                            <div className="flex items-center gap-1">
                               <button
                                 onClick={() => updateActiveImage({ locked: !activeImage.locked })}
                                 className={`p-1 rounded transition-colors ${activeImage.locked ? 'bg-[#ede3e1] text-[#4a2622]' : 'text-[#8c746f] hover:text-[#4a2622] hover:bg-[#ede3e1]'}`}
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

                  {panel.id === 'guides' && (
                    <div className="p-3.5 flex flex-col gap-2.5">
                      <div className="flex flex-col gap-2.5">
                        <div className="flex items-center justify-between px-1">
                          <label className="text-xs font-semibold text-[#7dd3fc]">Cap Height</label>
                          <div className="flex items-center bg-[#f4f1ed] rounded-md focus-within:ring-1 focus-within:ring-[#d4c8c5] w-16 transition-all">
                            <input 
                              type="number" 
                              value={guides.capHeight} 
                              onChange={(e) => setGuides({...guides, capHeight: e.target.value === '' ? '' : Number(e.target.value)})} 
                              onBlur={(e) => e.target.value === '' && setGuides({...guides, capHeight: 0})}
                              className="w-full text-xs text-left bg-transparent border-none outline-none py-1.5 px-2 text-[#4a2622] font-mono" 
                            />
                          </div>
                        </div>
                        <div className="flex items-center justify-between px-1">
                          <label className="text-xs font-semibold text-[#818cf8]">X-Height</label>
                          <div className="flex items-center bg-[#f4f1ed] rounded-md focus-within:ring-1 focus-within:ring-[#d4c8c5] w-16 transition-all">
                            <input 
                              type="number" 
                              value={guides.xHeight} 
                              onChange={(e) => setGuides({...guides, xHeight: e.target.value === '' ? '' : Number(e.target.value)})} 
                              onBlur={(e) => e.target.value === '' && setGuides({...guides, xHeight: 0})}
                              className="w-full text-xs text-left bg-transparent border-none outline-none py-1.5 px-2 text-[#4a2622] font-mono" 
                            />
                          </div>
                        </div>
                        <div className="flex items-center justify-between px-1">
                          <label className="text-xs font-semibold text-[#c084fc]">Descender</label>
                          <div className="flex items-center bg-[#f4f1ed] rounded-md focus-within:ring-1 focus-within:ring-[#d4c8c5] w-16 transition-all">
                            <input 
                              type="number" 
                              value={guides.descender} 
                              onChange={(e) => setGuides({...guides, descender: e.target.value === '' ? '' : Number(e.target.value)})} 
                              onBlur={(e) => e.target.value === '' && setGuides({...guides, descender: 0})}
                              className="w-full text-xs text-left bg-transparent border-none outline-none py-1.5 px-2 text-[#4a2622] font-mono" 
                            />
                          </div>
                        </div>
                      </div>
                    </div>
                  )}

                  {panel.id === 'layers' && (
                    <div className={`p-3 flex flex-col gap-2 min-h-0 flex-1 ${isMobile ? 'max-h-[36vh]' : 'max-h-[60vh]'}`}>
                      <div className="flex-1 overflow-y-auto flex flex-col gap-1 pr-1">
                        {layers.map(layer => {
                          const isSelected = selectedLayerIds.has(layer.id);
                          return (
                            <div className="relative" key={layer.id}>
                                {dragDropTarget?.id === layer.id && dragDropTarget.position === 'top' && (
                                   <div className="absolute top-[-2px] left-0 right-0 h-[2px] bg-[#4a2622] z-10 rounded-full" />
                                )}
                                <div 
                                    draggable={editingLayerId !== layer.id}
                                    onDragStart={(e) => handleLayerDragStart(e, layer.id)}
                                    onDragOver={(e) => handleLayerDragOver(e, layer.id)}
                                    onDrop={(e) => handleLayerDrop(e, layer.id)}
                                    onDragEnd={handleLayerDragEnd}
                                    className={`flex items-center justify-between p-2 rounded-xl border transition-all cursor-pointer ${
                                      isSelected 
                                        ? 'bg-[#ede3e1] border-[#d4c8c5] shadow-sm text-[#4a2622]' 
                                        : 'bg-[#fdfcfa] border-transparent hover:bg-[#fcfaf8] hover:border-[#e8dfdb] text-[#8c746f]'
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
                                          className="text-xs font-semibold text-[#4a2622] bg-white border border-[#4a2622] rounded px-1 outline-none w-24 py-0.5 select-text cursor-text ml-1"
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
                                        className={`p-1.5 rounded-md hover:bg-[#e8dfdb]/50 transition-colors ${layer.visible ? 'opacity-100' : 'opacity-40'}`}
                                        title={layer.visible ? "Hide Layer" : "Show Layer"}
                                      >
                                        {layer.visible ? <Eye size={14} /> : <EyeOff size={14} />}
                                      </button>
                                      <button 
                                        onClick={(e) => { e.stopPropagation(); toggleLayerLock(layer.id); }}
                                        className={`p-1.5 rounded-md hover:bg-[#e8dfdb]/50 transition-colors ${layer.locked ? 'opacity-100' : 'opacity-40'}`}
                                        title={layer.locked ? "Unlock Layer" : "Lock Layer"}
                                      >
                                        {layer.locked ? <Lock size={14} /> : <Unlock size={14} />}
                                      </button>
                                    </div>
                                </div>
                                {dragDropTarget?.id === layer.id && dragDropTarget.position === 'bottom' && (
                                   <div className="absolute bottom-[-2px] left-0 right-0 h-[2px] bg-[#4a2622] z-10 rounded-full" />
                                )}
                            </div>
                          )
                        })}
                      </div>
                    </div>
                  )}
                </div>
              )}
            </div>
          );
        })}
      </div>

      {/* Bottom Toolbar (Desktop Tools) */}
      {!isMobile && (
      <div className="absolute bottom-8 left-1/2 -translate-x-1/2 flex items-center gap-2 bg-[#fdfcfa] p-2 rounded-2xl shadow-lg border border-[#e8dfdb]">
        
        {/* Drawing Tools Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={mode === 'draw'} 
            onClick={() => changeMode('draw')} 
            icon={<PenTool size={20} />} 
            label="Path Tool" 
            hotkey="P"
          />
          <ToolButton 
            active={mode === 'pencil'} 
            onClick={() => changeMode('pencil')} 
            icon={<Pencil size={20} />} 
            label="Pencil Tool" 
            hotkey="F"
          />

          {/* Contextual Shape Menu */}
          <div className="relative flex items-center gap-0.5 group" ref={shapeMenuContainerRef}>
            <button
              onClick={() => { changeMode('shape'); setShowShapeMenu(false); }}
              className={`p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
                mode === 'shape' 
                  ? 'bg-[#ede3e1] text-[#4a2622]' 
                  : 'text-[#8c746f] hover:bg-[#f4f1ed] hover:text-[#4a2622]'
              }`}
              title="Shape Tool (R/O)"
            >
              {shapeType === 'rectangle' && <Square size={20} />}
              {shapeType === 'ellipse' && <Circle size={20} />}
              {shapeType === 'polygon' && <Triangle size={20} />}
              {shapeType === 'star' && <Star size={20} />}
              {shapeType === 'line' && <Minus size={20} />}
            </button>
            <button
              onClick={() => setShowShapeMenu(!showShapeMenu)}
              className={`w-6 h-11 rounded-xl transition-all duration-200 flex items-center justify-center ${
                 showShapeMenu
                  ? 'bg-[#ede3e1] text-[#4a2622]' 
                  : 'text-[#8c746f] hover:bg-[#f4f1ed] hover:text-[#4a2622]'
              }`}
              title="Shape Options"
            >
              <ChevronUp size={14} />
            </button>
            
            {/* Shape Dropdown Menu */}
            {showShapeMenu && (
               <div className="absolute bottom-[calc(100%+8px)] left-0 w-36 bg-[#fdfcfa] p-1.5 rounded-2xl shadow-xl border border-[#e8dfdb] flex flex-col gap-0.5 z-20">
                   <ShapeMenuItem type="rectangle" icon={<Square size={16}/>} label="Rectangle" hotkey="R" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="ellipse" icon={<Circle size={16}/>} label="Ellipse" hotkey="O" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="polygon" icon={<Triangle size={16}/>} label="Polygon" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="star" icon={<Star size={16}/>} label="Star" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="line" icon={<Minus size={16}/>} label="Line" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
               </div>
            )}
          </div>
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e8dfdb] mx-1"></div>

        {/* Manipulation Tools Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={mode === 'edit'} 
            onClick={() => changeMode('edit')} 
            icon={<MousePointer2 size={20} />} 
            label="Node Editor" 
            hotkey="V"
          />
          <ToolButton 
            active={mode === 'pan'} 
            onClick={() => changeMode('pan')} 
            icon={<Hand size={20} />} 
            label="Pan Canvas" 
            hotkey="Space"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e8dfdb] mx-1"></div>

        {/* Configuration Panels Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={openPanels.image} 
            onClick={() => togglePanel('image')} 
            icon={<ImageIcon size={20} />} 
            label="Image Settings" 
            hotkey="U"
          />
          <ToolButton 
            active={openPanels.grid} 
            onClick={() => togglePanel('grid')} 
            icon={<Grid size={20} />} 
            label="Background Config" 
            hotkey="B"
          />
          <ToolButton 
            active={openPanels.guides} 
            onClick={() => togglePanel('guides')} 
            icon={<Ruler size={20} />} 
            label="Guides Config" 
            hotkey="G"
          />
          <ToolButton 
            active={openPanels.layers} 
            onClick={() => togglePanel('layers')} 
            icon={<Layers size={20} />} 
            label="Layers Panel" 
            hotkey="L"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e8dfdb] mx-1"></div>

        {/* View Toggles Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={showNodes && mode !== 'pencil'} 
            onClick={() => { 
                if (mode === 'pencil') {
                  changeMode('edit');
                  setShowNodes(true);
                } else {
                  setShowNodes(!showNodes);
                }
            }} 
            icon={<CircleDot size={20} />} 
            label="Show Nodes" 
            hotkey="N"
          />
          <ToolButton 
            active={fillToggleActive}
            onClick={() => applyPathStyle({ fillEnabled: !fillToggleActive })}
            icon={<Droplet size={20} />}
            label={hasSelectedPaths ? "Toggle Fill (Selection)" : "Toggle Fill (Default)"}
          />
          <ToolButton
            active={strokeToggleActive}
            onClick={() => {}}
            icon={<Minus size={20} />}
            label={hasSelectedPaths ? "Toggle Stroke (Selection)" : "Toggle Stroke (Default)"}
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e8dfdb] mx-1"></div>

        {/* Global Actions Section */}
        <div className="flex gap-1">
          <button 
            onClick={correctPathDirections}
            className="p-3 text-[#8c746f] hover:text-[#4a2622] hover:bg-[#f4f1ed] rounded-xl transition-all"
            title={selectedPoints.length > 0 ? "Reverse Path Direction (Manual)" : "Auto-Correct Path Directions"}
          >
            <RefreshCw size={20} />
          </button>
          
          <button 
            onClick={clearCanvas}
            className="p-3 text-[#8c746f] hover:text-red-600 hover:bg-red-50 rounded-xl transition-all"
            title="Clear Canvas"
          >
            <Trash2 size={20} />
          </button>
        </div>
      </div>
      )}

    </div>
  );
}

// Sub-component for Toolbar Buttons
function ToolButton({ active, onClick, icon, label, hotkey }) {
  return (
    <button
      onClick={onClick}
      className={`relative group p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
        active 
          ? 'bg-[#ede3e1] text-[#4a2622]' 
          : 'text-[#8c746f] hover:text-[#4a2622] hover:bg-[#f4f1ed]'
      }`}
      title={hotkey ? `${label} (${hotkey})` : label}
    >
      {icon}
      
      {/* Tooltip */}
      <div className="absolute -top-10 scale-0 group-hover:scale-100 opacity-0 group-hover:opacity-100 transition-all origin-bottom bg-[#4a2622] text-[#f4f1ed] text-xs font-medium px-2 py-1 rounded shadow-lg flex items-center gap-2 pointer-events-none whitespace-nowrap z-50">
        <span>{label}</span>
        {hotkey && <span className="text-[#a89b99] font-mono text-[10px] bg-[#3d1d1a] px-1 rounded">{hotkey}</span>}
        <div className="absolute -bottom-1 left-1/2 -translate-x-1/2 w-2 h-2 bg-[#4a2622] rotate-45"></div>
      </div>
    </button>
  );
}

function MobileToolButton({ active = false, onClick, icon, label }) {
  return (
    <button
      onClick={onClick}
      title={label}
      className={`h-11 min-w-11 px-2 rounded-lg border transition-all duration-150 flex items-center justify-center shrink-0 ${
        active
          ? 'bg-[#ded9f4] border-[#d0c8f0] text-[#4f4a77]'
          : 'bg-[#f8f6f3] border-transparent text-[#6f6968] active:bg-[#ede6e2]'
      }`}
    >
      {icon}
    </button>
  );
}

// Sub-component for Shape Menu Option
function ShapeMenuItem({ type, icon, label, hotkey, current, onClick }) {
  const active = current === type;
  return (
      <button 
        onClick={() => onClick(type)}
        className={`flex items-center justify-between w-full p-2 text-xs font-medium rounded-lg transition-colors ${
            active ? 'bg-[#ede3e1] text-[#4a2622]' : 'text-[#8c746f] hover:bg-[#f4f1ed] hover:text-[#4a2622]'
        }`}
      >
          <div className="flex items-center gap-2">
            {icon}
            <span>{label}</span>
          </div>
          {hotkey && <span className="text-[10px] font-mono text-[#a89b99]">{hotkey}</span>}
      </button>
  )
}
