import { useRef } from 'react';
import {
  SNAP_RADIUS,
  MIN_ZOOM,
  MAX_ZOOM,
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN,
  DEFAULT_FILL_COLOR
} from '../constants';
import {
  getBezierPoint,
  distToBezier,
  splitBezier,
  reflectPointAcrossPerpBisector,
  applyShiftSnap,
  shortestDeltaDeg,
  normalizeAngleDeg,
  computeCornerScale
} from '../lib/geometry';
import { applyGridSnap } from '../lib/snap';
import {
  normalizeStrokeWidth,
  normalizeStrokeColor,
  normalizeStrokeAlign
} from '../lib/stroke';
import {
  pointsToPath,
  isCorner,
  clonePoint,
  reversePathPoints,
  simplifyPolylinePoints,
  clonePaths,
  getPathStrokeStyle,
  getPathFillStyle,
  resolvePathEditGroupId
} from '../lib/paths';
import { generateEditGroupId } from '../lib/svg';
import { generateShapePath } from '../lib/shapes';
import { createLayer } from '../lib/layers';
import { MIN_FONT_SIZE } from '../lib/objectModel';
import { getTextLocalLayout } from '../lib/textMeasure';

// The pointer/gesture engine: pen, pencil, shape, select, edit, pan tools;
// touch pinch/two-finger pan; long-press; drag thresholds; rotation.
// The three handlers and their refs are one inseparable unit -- they share
// closure state via the refs above and must stay together.
export function usePointerInteraction(deps) {
  const {
activeEditGroupId,
    activeHandle,
    activeLayerId,
    activePathEditId,
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
  } = deps;

  const dragStartPathsRef = useRef([]);
  const dragStartImagesRef = useRef([]);
  const dragStartTextsRef = useRef([]);
  const hasDraggedRef = useRef(false);
  const pointRotateRef = useRef({ lastAngle: 0, accumulated: 0 });
  const bgRotateRef = useRef({ lastAngle: 0, accumulated: 0 });
  const pointerGestureRef = useRef({
    pointerId: null,
    pointerType: 'mouse',
    startClientX: 0,
    startClientY: 0,
    dragActivated: false
  });
  const touchPointsRef = useRef(new Map());
  const pinchGestureRef = useRef({ active: false, lastDistance: 0, lastMidpoint: null });
  const pinchWasActiveRef = useRef(false);
  const lastPointerDownRef = useRef({ time: 0, x: 0, y: 0, canvasX: 0, canvasY: 0, refPoint: null });
  const lastClickedPathIdRef = useRef(null);
  const lastClickedTextIdRef = useRef(null);

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
    const isTouchLikePointer = e.pointerType === 'touch' || e.pointerType === 'pen';

    if (isTouchLikePointer) {
      touchPointsRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (touchPointsRef.current.size >= 2) {
        const [p1, p2] = Array.from(touchPointsRef.current.values());
        pinchGestureRef.current = {
          active: true,
          lastDistance: Math.hypot(p2.x - p1.x, p2.y - p1.y),
          lastMidpoint: { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 }
        };
        pinchWasActiveRef.current = true;
        rollbackPendingTouchDrawAction();
        clearMobileLongPress();
        setIsPanning(false);
        return;
      }
    }

    pointerGestureRef.current = {
      pointerId: e.pointerId ?? null,
      pointerType: e.pointerType || 'mouse',
      startClientX: e.clientX,
      startClientY: e.clientY,
      dragActivated: (e.pointerType || 'mouse') === 'mouse'
    };
    setHoveredHandle(null);
    if (!(mode === 'draw' && isTouchLikePointer)) {
      clearPendingTouchDrawAction();
    }

    if (e.button === 1 || mode === 'pan') {
      setIsPanning(true);
      return;
    }

    // Quiet UI: panels fade while actively working on the canvas (any
    // non-pan press; pointer capture guarantees the matching up/cancel).
    setIsCanvasWorking(true);

    if (['shape', 'pencil', 'draw', 'text'].includes(mode)) {
        if (activeLayerId && lockedLayerIds.has(activeLayerId)) return;
    }

    let coords = getCanvasCoords(e.clientX, e.clientY);
    let snappedCoords = applyGridSnap(coords, gridConfig);

    const now = Date.now();
    const distToLast = Math.hypot(e.clientX - lastPointerDownRef.current.x, e.clientY - lastPointerDownRef.current.y);
    const isDoubleClick = (now - lastPointerDownRef.current.time < 350) && (distToLast < 20);
    
    // Will update refPoint down below depending on context
    lastPointerDownRef.current = { time: now, x: e.clientX, y: e.clientY, canvasX: coords.x, canvasY: coords.y, refPoint: null };
    if (canvasContextMenu) {
      setCanvasContextMenu(null);
    }

    if (
      isMobile
      && (e.pointerType === 'touch' || e.pointerType === 'pen')
      && !['draw', 'pencil', 'shape', 'text'].includes(mode)
    ) {
      clearMobileLongPress();
      const hitText = findTopTextAtCoords(coords);
      const hitImage = hitText ? null : findTopImageAtCoords(coords);
      const hitPath = hitText || hitImage ? null : findTopPathAtCoords(coords);
      const longPressTargetType = hitText ? 'text' : (hitImage ? 'image' : (hitPath ? 'path' : 'canvas'));
      const longPressTargetId = hitText ? hitText.id : (hitImage ? hitImage.id : (hitPath ? hitPath.path.id : null));
      const pointerId = e.pointerId ?? null;
      const timerId = setTimeout(() => {
        mobileLongPressRef.current.triggered = true;
        setActiveHandle(null);
        setSelectionBox(null);
        setBgAction(null);
        setPointAction(null);
        setIsDraggingPoints(false);

        const longPressWorld = getCanvasCoords(e.clientX, e.clientY);
        setCanvasContextMenu({
          type: 'paste',
          x: e.clientX,
          y: e.clientY,
          worldX: longPressWorld.x,
          worldY: longPressWorld.y,
          targetLayerId: null
        });
      }, 520);

      mobileLongPressRef.current = {
        timerId,
        pointerId,
        startX: e.clientX,
        startY: e.clientY,
        targetType: longPressTargetType,
        targetId: longPressTargetId,
        triggered: false
      };
    } else {
      clearMobileLongPress();
    }

    if (mode === 'shape') {
      setDrawingShape({ startX: snappedCoords.x, startY: snappedCoords.y, currentX: snappedCoords.x, currentY: snappedCoords.y, shiftKey: e.shiftKey });
      return;
    }

    if (mode === 'text') {
      if (e.button === 2) return;
      // Cancel the pointerdown's default action (focus moving to body after
      // this handler) so it cannot blur the textarea the overlay focuses.
      e.preventDefault();
      beginNewTextAt(coords);
      return;
    }

    if (mode === 'edit') {
      dragStartPathsRef.current = clonePaths(paths);
      dragStartImagesRef.current = images.map(img => ({...img}));
      dragStartTextsRef.current = texts.map(text => ({...text}));
      hasDraggedRef.current = false;
    }

    if (mode === 'pencil') {
      commitHistory({ paths, currentPath, images, layers, texts });
      const newPoint = { 
        x: coords.x, y: coords.y, 
        hIn: { x: coords.x, y: coords.y }, 
        hOut: { x: coords.x, y: coords.y } 
      };
      setCurrentPathInfo({
        layerId: resolveEditContextLayerId(),
        itemType: 'vector',
        fillEnabled: pathStyleDefaults.fillEnabled,
        fillColor: normalizeStrokeColor(pathStyleDefaults.fillColor, DEFAULT_FILL_COLOR),
        strokeEnabled: pathStyleDefaults.strokeEnabled,
        strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
        strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
        strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN),
        editGroupId: activeEditGroupId || generateEditGroupId()
      });
      setCurrentPath([newPoint]);
      return;
    }

    if (mode === 'draw') {
      if (isTouchLikePointer) {
        beginPendingTouchDrawAction(e.pointerId ?? null, {
          path: currentPath,
          info: currentPathInfo,
          paths,
          layers,
          activeLayerId,
          ghostPoint,
          drawHover,
          hoveredStartPoint,
          isDrawingCurve,
          snapState
        });
      } else {
        clearPendingTouchDrawAction();
      }

      if (currentPath.length === 0) {
        let endpointSnapInfo = snapState.endpoint;
        if (!endpointSnapInfo) {
          let bestEndpointDist = Infinity;
          for (let i = paths.length - 1; i >= 0; i--) {
            const path = paths[i];
            if (!isPathVisible(path) || isPathLocked(path) || path.isClosed || path.points.length === 0) continue;
            const endpointIndices = path.points.length === 1 ? [0] : [0, path.points.length - 1];
            for (const pointIndex of endpointIndices) {
              const endpoint = path.points[pointIndex];
              const dist = Math.hypot(endpoint.x - coords.x, endpoint.y - coords.y);
              if (dist < pointHitRadius && dist < bestEndpointDist) {
                bestEndpointDist = dist;
                endpointSnapInfo = { pathIndex: i, pointIndex };
              }
            }
          }
        }

        const resumePath = endpointSnapInfo ? paths[endpointSnapInfo.pathIndex] : null;
        commitHistory({ paths, currentPath, images, layers, texts });

        if (resumePath && !resumePath.isClosed && resumePath.points.length > 0) {
          const shouldReverseForResume = resumePath.points.length > 1 && endpointSnapInfo.pointIndex === 0;
          const basePathPoints = resumePath.points.map(clonePoint);
          const resumedPoints = shouldReverseForResume
            ? reversePathPoints(basePathPoints)
            : basePathPoints;
          const existingStroke = getPathStrokeStyle(resumePath);
          setCurrentPathInfo({
            layerId: resumePath.layerId,
            itemType: resumePath.itemType || 'vector',
            fillEnabled: resumePath.fillEnabled ?? pathStyleDefaults.fillEnabled,
            fillColor: getPathFillStyle(resumePath).fillColor,
            strokeEnabled: existingStroke.strokeEnabled,
            strokeWidth: existingStroke.strokeWidth,
            strokeColor: existingStroke.strokeColor,
            strokeAlign: existingStroke.strokeAlign,
            editGroupId: resolvePathEditGroupId(resumePath),
            resumePathId: resumePath.id,
            resumePathIndex: endpointSnapInfo.pathIndex,
            resumeReverseOnSave: shouldReverseForResume
          });
          setCurrentPath(resumedPoints);
        } else {
          const drawStart = ghostPoint || snappedCoords;
          const newPoint = {
            x: drawStart.x, y: drawStart.y,
            hIn: { x: drawStart.x, y: drawStart.y },
            hOut: { x: drawStart.x, y: drawStart.y }
          };
          setCurrentPathInfo({
            layerId: resolveEditContextLayerId(),
            itemType: 'vector',
            fillEnabled: pathStyleDefaults.fillEnabled,
            fillColor: normalizeStrokeColor(pathStyleDefaults.fillColor, DEFAULT_FILL_COLOR),
            strokeEnabled: pathStyleDefaults.strokeEnabled,
            strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
            strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
            strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN),
            editGroupId: activeEditGroupId || generateEditGroupId()
          });
          setCurrentPath([newPoint]);
        }
        setIsDrawingCurve('drawing');
      } else {
        const startP = currentPath[0];
        const isClosingHit = currentPath.length > 2
          && Math.hypot(startP.x - coords.x, startP.y - coords.y) < closePathHitRadius;
        if (hoveredStartPoint || isClosingHit) {
          setHoveredStartPoint(true);
          setGhostPoint(startP);
          setIsDrawingCurve('closing');
        } else {
          let endpointSnap = snapState.endpoint;
          let endpointPath = endpointSnap ? paths[endpointSnap.pathIndex] : null;
          if (!endpointPath) {
            let bestEndpointDist = Infinity;
            for (let i = paths.length - 1; i >= 0; i--) {
              const path = paths[i];
              if (!isPathVisible(path) || isPathLocked(path) || path.isClosed || path.points.length === 0) continue;
              if (activePathEditId && !isPathInActiveEditContext(path)) continue;
              if (currentPathInfo?.resumePathId != null && path.id === currentPathInfo.resumePathId) continue;
              const endpointIndices = path.points.length === 1 ? [0] : [0, path.points.length - 1];
              for (const pointIndex of endpointIndices) {
                const endpoint = path.points[pointIndex];
                const dist = Math.hypot(endpoint.x - coords.x, endpoint.y - coords.y);
                if (dist < pointHitRadius && dist < bestEndpointDist) {
                  bestEndpointDist = dist;
                  endpointSnap = { pathIndex: i, pointIndex };
                  endpointPath = path;
                }
              }
            }
          }
          const canMergeIntoEndpointPath = !!endpointPath
            && !endpointPath.isClosed
            && endpointPath.points.length > 0
            && endpointPath.id !== currentPathInfo?.resumePathId;

          commitHistory({ paths, currentPath, images, layers, texts });

          if (canMergeIntoEndpointPath) {
            const endpointPathPoints = endpointPath.points.map(clonePoint);
            const orderedEndpointPathPoints = endpointSnap.pointIndex === 0
              ? endpointPathPoints
              : reversePathPoints(endpointPathPoints);
            const endpointAnchor = orderedEndpointPathPoints[0];
            const mergedPath = currentPath.map(clonePoint);
            const lastPoint = mergedPath[mergedPath.length - 1];
            if (!lastPoint || Math.hypot(lastPoint.x - endpointAnchor.x, lastPoint.y - endpointAnchor.y) > 0.001) {
              mergedPath.push(clonePoint(endpointAnchor));
            }
            mergedPath.push(...orderedEndpointPathPoints.slice(1).map(clonePoint));

            setCurrentPath(mergedPath);
            setCurrentPathInfo(prev => {
              const mergedPathIds = new Set([...(prev?.mergedPathIds || []), endpointPath.id]);
              return {
                ...(prev || {}),
                editGroupId: prev?.editGroupId || resolvePathEditGroupId(endpointPath),
                mergedPathIds: [...mergedPathIds]
              };
            });
            const nextPaths = paths.filter(path => path.id !== endpointPath.id);
            setPaths(nextPaths);
            setLayers(prevLayers => {
              const usedLayerIds = new Set([
                ...nextPaths.map(path => path.layerId),
                ...images.map(img => img.layerId),
                ...texts.map(text => text.layerId)
              ]);
              const filteredLayers = prevLayers.filter(layer => usedLayerIds.has(layer.id));
              if (activeLayerId && !usedLayerIds.has(activeLayerId)) {
                const preferredLayerId = currentPathInfo?.layerId && usedLayerIds.has(currentPathInfo.layerId)
                  ? currentPathInfo.layerId
                  : (filteredLayers[0]?.id ?? null);
                setActiveLayerId(preferredLayerId);
              }
              return filteredLayers;
            });
            setSnapState({ endpoint: null, segment: null });
            setGhostPoint(null);
            setDrawHover(null);
            setIsDrawingCurve('drawing');
            return;
          }

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
      const isDirectPathEdit = !!activeEditGroupId && showNodes;
      const buildPathSelection = (pathIndex) => {
        const path = paths[pathIndex];
        if (!path) return [];
        return path.points.map((_, idx) => ({ pathIndex, pointIndex: idx }));
      };
      const buildGroupPathIndices = (pathIndex) => {
        const path = paths[pathIndex];
        if (!path) return [];
        const groupId = resolvePathEditGroupId(path);
        if (groupId == null) return [pathIndex];
        const members = [];
        paths.forEach((candidate, idx) => {
          if (!isPathVisible(candidate) || isPathLocked(candidate)) return;
          if (resolvePathEditGroupId(candidate) === groupId) {
            members.push(idx);
          }
        });
        return members.length > 0 ? members : [pathIndex];
      };
      const buildGroupSelection = (pathIndex) => {
        const members = buildGroupPathIndices(pathIndex);
        const selection = [];
        members.forEach((memberIndex) => {
          const memberPath = paths[memberIndex];
          if (!memberPath) return;
          memberPath.points.forEach((_, pointIndex) => {
            selection.push({ pathIndex: memberIndex, pointIndex });
          });
        });
        return selection;
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
          if (!isPathInActiveEditContext(paths[i])) continue;
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
        const anchor = paths[clickedHandle.pathIndex]?.points?.[clickedHandle.pointIndex];
        const anchorDist = anchor ? Math.hypot(anchor.x - coords.x, anchor.y - coords.y) : Infinity;
        const preferAnchorToggle = isDoubleClick && anchorDist < pointHitRadius;

        if (!preferAnchorToggle) {
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
      }

      if (isDirectPathEdit) {
        for (let i = paths.length - 1; i >= 0; i--) {
          if (!isPathVisible(paths[i]) || isPathLocked(paths[i])) continue;
          if (!isPathInActiveEditContext(paths[i])) continue;
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
          commitHistory({ paths, currentPath, images, layers, texts });
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
                 const handle = { x: pt.x + dx / 3, y: pt.y + dy / 3 };

                 if (ptIndex === 0) {
                     pt.hOut = handle;
                     pt.hIn = { x: pt.x - (handle.x - pt.x), y: pt.y - (handle.y - pt.y) };
                 } else {
                     pt.hIn = handle;
                     pt.hOut = { x: pt.x - (handle.x - pt.x), y: pt.y - (handle.y - pt.y) };
                 }
            }
          }
          
          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          
          const newSel = [{ pathIndex: clickedPoint.pathIndex, pointIndex: clickedPoint.pointIndex }];
          setSelectedPoints(newSel);
          setActiveHandle(null);
          setIsDraggingPoints(false);
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

      // 3. Check Background Object Handles (Scale / Rotate)
      const hitBg = isDirectPathEdit ? null : getBgHit(coords);

      if (hitBg && (hitBg.action.startsWith('scale') || hitBg.action.startsWith('rotate'))) {
        lastClickedPathIdRef.current = null;
        lastClickedTextIdRef.current = null;
        setBgAction(hitBg.action);
        const obj = hitBg.kind === 'text'
          ? texts.find(t => t.id === hitBg.id)
          : images.find(i => i.id === hitBg.id);
        if (hitBg.kind === 'text') {
          setSelectedTextIds([hitBg.id]);
          setSelectedImageIds([]);
        } else {
          setSelectedImageIds([hitBg.id]);
          setSelectedTextIds([]);
        }
        if (hitBg.action.startsWith('scale')) {
           setBgInitialState({ coords, obj: { ...obj }, kind: hitBg.kind, cursorAngle: hitBg.cursorAngle });
        } else {
           const initAngle = Math.atan2(coords.y - obj.y, coords.x - obj.x) * 180 / Math.PI;
           bgRotateRef.current = { lastAngle: initAngle, accumulated: 0 };
           setBgInitialState({ angle: initAngle, obj: { ...obj }, kind: hitBg.kind });
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
            clickedSegment = { pathIndex: i, prevIndex: prevIdx, currIndex: j, t: hit.t };
            break;
          }
        }
        if (clickedSegment) break;
      }

      if (clickedSegment) {
        const clickedPath = paths[clickedSegment.pathIndex];
        const clickedPathSelection = buildGroupSelection(clickedSegment.pathIndex);
        const clickedGroupPathIndices = new Set(buildGroupPathIndices(clickedSegment.pathIndex));
        const clickedEdgeSelection = buildEdgeSelection(clickedSegment);
        const isDirectClickOnActivePath = isDirectPathEdit && isPathInActiveEditContext(clickedPath);

        if (!isDirectClickOnActivePath) {
          const isPathSelected = clickedPathSelection.every(nsp => (
            selectedPoints.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)
          ));
          const shouldEnterDirect = isDoubleClick && clickedPath && lastClickedPathIdRef.current === clickedPath.id;
          lastClickedPathIdRef.current = clickedPath?.id || null;

          if (shouldEnterDirect && clickedPath) {
            setShowNodes(true);
            setActivePathEditId(clickedPath.id);
            setSelectedPoints([]);
            setSelectedImageIds([]);
            setSelectedTextIds([]);
            setActiveLayerId(clickedPath.layerId);
            return;
          }

          setActivePathEditId(null);
          setSelectedImageIds([]);
          setSelectedTextIds([]);
          if (e.shiftKey) {
            if (isPathSelected) {
              setSelectedPoints(prev => prev.filter(sp => !clickedGroupPathIndices.has(sp.pathIndex)));
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

        const hasModifierKeys = e.shiftKey || e.altKey || e.ctrlKey || e.metaKey;
        if (!hasModifierKeys) {
          commitHistory({ paths, currentPath, images, layers, texts });
          const newPaths = clonePaths(paths);
          const path = newPaths[clickedSegment.pathIndex];
          const prevP = path.points[clickedSegment.prevIndex];
          const currP = path.points[clickedSegment.currIndex];
          const split = splitBezier(
            prevP,
            prevP.hOut || prevP,
            currP.hIn || currP,
            currP,
            clickedSegment.t
          );

          prevP.hOut = split.left.hOut;
          currP.hIn = split.right.hIn;
          const insertIdx = clickedSegment.currIndex === 0 ? path.points.length : clickedSegment.currIndex;
          path.points.splice(insertIdx, 0, split.newPoint);

          setPaths(newPaths);
          dragStartPathsRef.current = clonePaths(newPaths);
          const insertedPointSelection = [{ pathIndex: clickedSegment.pathIndex, pointIndex: insertIdx }];
          setSelectedPoints(insertedPointSelection);
          setSelectedImageIds([]);
          setSelectedTextIds([]);
          setActiveHandle(null);
          startDragging(insertedPointSelection);
          return;
        }

        if (e.shiftKey && e.altKey && (e.ctrlKey || e.metaKey)) {
          commitHistory({ paths, currentPath, images, layers, texts });
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
          commitHistory({ paths, currentPath, images, layers, texts });
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
          commitHistory({ paths, currentPath, images, layers, texts });
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
          commitHistory({ paths, currentPath, images, layers, texts });
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

      // 4.2 Check single-point paths (supports entering direct edit mode)
      let clickedSinglePointPathIndex = -1;
      for (let i = paths.length - 1; i >= 0; i--) {
        const path = paths[i];
        if (!isPathVisible(path) || isPathLocked(path)) continue;
        if (path.points.length !== 1) continue;
        const p = path.points[0];
        const dist = Math.hypot(p.x - coords.x, p.y - coords.y);
        if (dist < pointHitRadius) {
          clickedSinglePointPathIndex = i;
          break;
        }
      }

      if (clickedSinglePointPathIndex !== -1) {
        const path = paths[clickedSinglePointPathIndex];
        const newSel = buildGroupSelection(clickedSinglePointPathIndex);
        const clickedGroupPathIndices = new Set(buildGroupPathIndices(clickedSinglePointPathIndex));
        const isDirectClickOnActivePath = isDirectPathEdit && isPathInActiveEditContext(path);
        const alreadySelected = newSel.every(nsp => (
          selectedPoints.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)
        ));

        if (!isDirectClickOnActivePath) {
          const shouldEnterDirect = isDoubleClick && path && lastClickedPathIdRef.current === path.id;
          lastClickedPathIdRef.current = path?.id || null;

          if (shouldEnterDirect && path) {
            setShowNodes(true);
            setActivePathEditId(path.id);
            setSelectedPoints([]);
            setSelectedImageIds([]);
            setSelectedTextIds([]);
            setActiveLayerId(path.layerId);
            return;
          }

          setActivePathEditId(null);
          if (e.shiftKey) {
            if (alreadySelected) {
              setSelectedPoints(prev => prev.filter(sp => !clickedGroupPathIndices.has(sp.pathIndex)));
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

          setSelectedPoints(newSel);
          setSelectedImageIds([]);
          startDragging(newSel);
          return;
        }

        if (e.shiftKey) {
          if (alreadySelected) {
            setSelectedPoints(prev => prev.filter(sp => !clickedGroupPathIndices.has(sp.pathIndex)));
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

        setSelectedPoints(newSel);
        startDragging(newSel);
        return;
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
        const newSel = buildGroupSelection(clickedFilledPathIndex);
        const clickedGroupPathIndices = new Set(buildGroupPathIndices(clickedFilledPathIndex));
        const isDirectClickOnActivePath = isDirectPathEdit && isPathInActiveEditContext(path);
        const alreadySelected = newSel.every(nsp =>
          selectedPoints.some(sp => sp.pathIndex === nsp.pathIndex && sp.pointIndex === nsp.pointIndex)
        );

        if (!isDirectClickOnActivePath) {
          const shouldEnterDirect = isDoubleClick && path && lastClickedPathIdRef.current === path.id;
          lastClickedPathIdRef.current = path?.id || null;

          if (shouldEnterDirect && path) {
            setShowNodes(true);
            setActivePathEditId(path.id);
            setSelectedPoints([]);
            setSelectedImageIds([]);
            setSelectedTextIds([]);
            setActiveLayerId(path.layerId);
            return;
          }

          setActivePathEditId(null);
          if (e.shiftKey) {
            if (alreadySelected) {
              setSelectedPoints(prev => prev.filter(sp => !clickedGroupPathIndices.has(sp.pathIndex)));
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
            setSelectedTextIds([]);
            startDragging(newSel);
          } else {
            startDragging(selectedPoints);
          }
          return;
        }

        if (e.shiftKey) {
          if (alreadySelected) {
            setSelectedPoints(prev => prev.filter(sp => !clickedGroupPathIndices.has(sp.pathIndex)));
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
      const canMoveSelectionByBBox = selectedImageIds.length > 0 || selectedTextIds.length > 0 || isWholePathSelection(selectedPoints);
      if (!e.shiftKey && !e.altKey && canMoveSelectionByBBox && selBBox && coords.x >= selBBox.minX && coords.x <= selBBox.maxX && coords.y >= selBBox.minY && coords.y <= selBBox.maxY) {
        startDragging(selectedPoints);
        return;
      }

      // 5. Check Background Object Body (Move); double-click on a text
      // re-opens its editor instead.
      if (hitBg && hitBg.action === 'move') {
        if (hitBg.kind === 'text') {
          const text = texts.find(t => t.id === hitBg.id);
          if (!text) return;
          if (isDoubleClick && lastClickedTextIdRef.current === hitBg.id) {
            // Same focus-stealing default as the text tool: cancel it so the
            // editor textarea keeps focus.
            e.preventDefault();
            lastClickedTextIdRef.current = null;
            setSelectedTextIds([hitBg.id]);
            setSelectedImageIds([]);
            setSelectedPoints([]);
            beginEditingText(text);
            return;
          }
          lastClickedTextIdRef.current = hitBg.id;
          lastClickedPathIdRef.current = null;
          setBgAction('move');
          setSelectedTextIds([hitBg.id]);
          setSelectedImageIds([]);
          setSelectedPoints([]);
          setBgInitialState({ coords, obj: { ...text }, kind: 'text' });
          return;
        }
        lastClickedPathIdRef.current = null;
        lastClickedTextIdRef.current = null;
        setBgAction('move');
        setSelectedImageIds([hitBg.id]);
        setSelectedTextIds([]);
        const img = images.find(i => i.id === hitBg.id);
        setSelectedPoints([]);
        setBgInitialState({ coords, obj: { ...img }, kind: 'image' });
        return;
      }

      if (isDoubleClick && activePathEditId && !e.shiftKey && !e.altKey && !e.ctrlKey && !e.metaKey) {
        lastClickedPathIdRef.current = null;
        lastClickedTextIdRef.current = null;
        setActivePathEditId(null);
        lastFocusedPathEditIdRef.current = null;
        setSelectedPoints([]);
        setActiveHandle(null);
        setSelectionBox(null);
        return;
      }

      // 6. Start Box selection
      lastClickedPathIdRef.current = null;
      lastClickedTextIdRef.current = null;
      setSelectedImageIds([]);
      setSelectedTextIds([]);
      setSelectionBox({
        startX: coords.x,
        startY: coords.y,
        currentX: coords.x,
        currentY: coords.y,
        initialSelection: [...selectedPoints],
        initialSelectedImageIds: [...selectedImageIds],
        initialSelectedTextIds: [...selectedTextIds]
      });
      if (!e.shiftKey && !e.altKey) {
        setSelectedPoints([]);
      }
    }
  };

  const handlePointerMove = (e) => {
    if ((e.pointerType === 'touch' || e.pointerType === 'pen') && touchPointsRef.current.has(e.pointerId)) {
      touchPointsRef.current.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (pinchGestureRef.current.active && touchPointsRef.current.size >= 2) {
        const [p1, p2] = Array.from(touchPointsRef.current.values());
        const midpoint = { x: (p1.x + p2.x) / 2, y: (p1.y + p2.y) / 2 };
        const distance = Math.hypot(p2.x - p1.x, p2.y - p1.y);
        const prevMidpoint = pinchGestureRef.current.lastMidpoint;
        const prevDistance = pinchGestureRef.current.lastDistance;

        const midDeltaX = prevMidpoint ? midpoint.x - prevMidpoint.x : 0;
        const midDeltaY = prevMidpoint ? midpoint.y - prevMidpoint.y : 0;

        const currentZoom = zoomRef.current;
        const currentPan = panRef.current;
        const scaleMultiplier = prevDistance > 0 ? distance / prevDistance : 1;
        const nextZoom = Math.min(Math.max(MIN_ZOOM, currentZoom * scaleMultiplier), MAX_ZOOM);

        const worldX = (midpoint.x - currentPan.x) / currentZoom;
        const worldY = (midpoint.y - currentPan.y) / currentZoom;

        const nextPan = {
          x: midpoint.x - worldX * nextZoom + midDeltaX,
          y: midpoint.y - worldY * nextZoom + midDeltaY
        };

        panRef.current = nextPan;
        zoomRef.current = nextZoom;
        setPan(nextPan);
        setZoom(nextZoom);

        pinchGestureRef.current.lastDistance = distance;
        pinchGestureRef.current.lastMidpoint = midpoint;
        return;
      }
    }

    const longPressState = mobileLongPressRef.current;
    if (longPressState.pointerId != null && longPressState.pointerId === (e.pointerId ?? null)) {
      const delta = Math.hypot(e.clientX - longPressState.startX, e.clientY - longPressState.startY);
      if (!longPressState.triggered && delta > 12) {
        clearMobileLongPress();
      } else if (longPressState.triggered) {
        return;
      }
    }

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

          if (selectedTextIds.length > 0) {
            setTexts(() => dragStartTextsRef.current.map(text => {
              if (!selectedTextIds.includes(text.id)) return text;
              return {
                ...text,
                x: opposite.x + (text.x - opposite.x) * s_new,
                y: opposite.y + (text.y - opposite.y) * s_new,
                fontSize: Math.max(MIN_FONT_SIZE, text.fontSize * s_new)
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
          const shouldSnapRotation = e.shiftKey || e.pointerType === 'touch' || e.pointerType === 'pen';
          const deltaAngle = shouldSnapRotation
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

          if (selectedTextIds.length > 0) {
            setTexts(() => dragStartTextsRef.current.map(text => {
              if (!selectedTextIds.includes(text.id)) return text;
              const rp = rotatePt({ x: text.x, y: text.y });
              return {
                ...text,
                x: rp.x,
                y: rp.y,
                rotation: normalizeAngleDeg(text.rotation + deltaAngle)
              };
            }));
          }
      }
      return;
    }

    if (bgAction && bgInitialState && bgInitialState.kind === 'text' && selectedTextIds.length > 0) {
      if (!dragThresholdPassed) return;
      hasDraggedRef.current = true;
      setTexts(prev => prev.map(text => {
        if (!selectedTextIds.includes(text.id)) return text;

        if (bgAction === 'move') {
          return {
            ...text,
            x: bgInitialState.obj.x + (coords.x - bgInitialState.coords.x),
            y: bgInitialState.obj.y + (coords.y - bgInitialState.coords.y)
          };
        } else if (bgAction.startsWith('scale-')) {
          const init = bgInitialState.obj;
          const { halfW, halfH } = getTextLocalLayout(init);
          const { s, newCenter } = computeCornerScale({
            coords,
            cornerId: bgAction.split('-')[1],
            center: { x: init.x, y: init.y },
            rotation: init.rotation,
            halfW,
            halfH,
            minScale: MIN_FONT_SIZE / init.fontSize
          });
          return { ...text, fontSize: init.fontSize * s, x: newCenter.x, y: newCenter.y };
        } else if (bgAction.startsWith('rotate-')) {
          const init = bgInitialState.obj;
          const currentAngle = Math.atan2(coords.y - init.y, coords.x - init.x) * 180 / Math.PI;
          const stepDelta = shortestDeltaDeg(currentAngle, bgRotateRef.current.lastAngle);
          bgRotateRef.current.lastAngle = currentAngle;
          bgRotateRef.current.accumulated += stepDelta;
          const shouldSnapRotation = e.shiftKey || e.pointerType === 'touch' || e.pointerType === 'pen';
          const deltaAngle = shouldSnapRotation
            ? Math.round(bgRotateRef.current.accumulated / 15) * 15
            : bgRotateRef.current.accumulated;
          return { ...text, rotation: normalizeAngleDeg(init.rotation + deltaAngle) };
        }
        return text;
      }));
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
            x: bgInitialState.obj.x + (coords.x - bgInitialState.coords.x),
            y: bgInitialState.obj.y + (coords.y - bgInitialState.coords.y)
          };
        } else if (bgAction.startsWith('scale-')) {
          const init = bgInitialState.obj;
          const { s, newCenter } = computeCornerScale({
            coords,
            cornerId: bgAction.split('-')[1],
            center: { x: init.x, y: init.y },
            rotation: init.rotation,
            halfW: (init.width * init.scale) / 2,
            halfH: (init.height * init.scale) / 2,
            minScale: 0.01 / init.scale
          });
          return { ...img, scale: init.scale * s, x: newCenter.x, y: newCenter.y };
        } else if (bgAction.startsWith('rotate-')) {
          const init = bgInitialState.obj;
          const currentAngle = Math.atan2(coords.y - init.y, coords.x - init.x) * 180 / Math.PI;
          const stepDelta = shortestDeltaDeg(currentAngle, bgRotateRef.current.lastAngle);
          bgRotateRef.current.lastAngle = currentAngle;
          bgRotateRef.current.accumulated += stepDelta;
          const shouldSnapRotation = e.shiftKey || e.pointerType === 'touch' || e.pointerType === 'pen';
          const deltaAngle = shouldSnapRotation
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
      let endpointSnap = null;
      let segmentSnap = null;

      {
        let bestEndpointDist = Infinity;
        for (let i = paths.length - 1; i >= 0; i--) {
          const path = paths[i];
          if (!isPathVisible(path) || isPathLocked(path) || path.isClosed || path.points.length === 0) continue;
          if (activePathEditId && !isPathInActiveEditContext(path)) continue;
          if (currentPath.length > 0 && currentPathInfo?.resumePathId != null && path.id === currentPathInfo.resumePathId) continue;
          const endpointIndices = path.points.length === 1 ? [0] : [0, path.points.length - 1];
          for (const pointIndex of endpointIndices) {
            const endpoint = path.points[pointIndex];
            const dist = Math.hypot(endpoint.x - coords.x, endpoint.y - coords.y);
            if (dist < pointHitRadius && dist < bestEndpointDist) {
              bestEndpointDist = dist;
              endpointSnap = { pathIndex: i, pointIndex, point: endpoint };
            }
          }
        }
      }

      if (currentPath.length === 0 && !endpointSnap) {
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

      if (endpointSnap) {
        snapPoint = { x: endpointSnap.point.x, y: endpointSnap.point.y };
      }

      if (currentPath.length > 0) {
        const startP = currentPath[0];
        if (currentPath.length > 2 && Math.hypot(startP.x - coords.x, startP.y - coords.y) < closePathHitRadius) {
          setHoveredStartPoint(true);
          snapPoint = startP;
        } else {
          setHoveredStartPoint(false);
        }
      }

      if (!snapPoint && currentPath.length > 0 && e.shiftKey && !isDrawingCurve) {
          snappedCoords = applyShiftSnap(snappedCoords, currentPath[currentPath.length - 1], true);
      }

      setSnapState({
        endpoint: endpointSnap ? { pathIndex: endpointSnap.pathIndex, pointIndex: endpointSnap.pointIndex } : null,
        segment: endpointSnap ? null : segmentSnap
      });
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
        if (currentPath.length > 2 && distToStart < closePathHitRadius) {
          setHoveredStartPoint(true);
          setGhostPoint(startP); 
        } else {
          setHoveredStartPoint(false);
        }
        setDrawHover(null);
      } else {
        setHoveredStartPoint(false);
        if (endpointSnap && snapPoint) {
          setDrawHover({ x: snapPoint.x, y: snapPoint.y, type: 'endpoint' });
        } else if (segmentSnap && snapPoint) {
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

            if (selectedTextIds.length > 0) {
              setTexts(() => dragStartTextsRef.current.map(text => {
                if (!selectedTextIds.includes(text.id)) return text;
                return { ...text, x: text.x + dx, y: text.y + dy };
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

            if (selectedTextIds.length > 0) {
              setTexts(() => dragStartTextsRef.current.map(text => (
                selectedTextIds.includes(text.id)
                  ? { ...text, x: text.x + dragDx, y: text.y + dragDy }
                  : text
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
        let newSelectedTextIds = [];
        if (e.shiftKey || e.altKey) {
          newSelected = [...selectionBox.initialSelection];
          newSelectedImageIds = [...selectionBox.initialSelectedImageIds];
          newSelectedTextIds = [...(selectionBox.initialSelectedTextIds || [])];
        }
        
        paths.forEach((path, i) => {
          if (!isPathVisible(path) || isPathLocked(path)) return;
          if (activePathEditId && !isPathInActiveEditContext(path)) return;

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
          if (activePathEditId && showNodes) return;
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

        // Marquee intersection check for texts (unrotated AABB, like images)
        texts.forEach(text => {
          if (activePathEditId && showNodes) return;
          const layer = layers.find(l => l.id === text.layerId);
          if (!layer || !layer.visible || layer.locked || text.locked) return;

          const { halfW, halfH } = getTextLocalLayout(text);
          const intersects = !(text.x + halfW < minX || text.x - halfW > maxX || text.y + halfH < minY || text.y - halfH > maxY);

          if (intersects) {
            if (e.altKey) {
              newSelectedTextIds = newSelectedTextIds.filter(id => id !== text.id);
            } else {
              if (!newSelectedTextIds.includes(text.id)) newSelectedTextIds.push(text.id);
            }
          }
        });

        setSelectedImageIds(newSelectedImageIds);
        setSelectedTextIds(newSelectedTextIds);
        setSelectedPoints(newSelected);
      }
    }

    if (mode === 'edit' && !isDraggingPoints && !activeHandle && !selectionBox && !bgAction && !pointAction) {
      let hitAction = null;
      const hitBg = (activePathEditId && showNodes) ? null : getBgHit(coords);
      
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
    setIsCanvasWorking(false);
    releasePointer(e);
    const isTouchLikePointer = e.pointerType === 'touch' || e.pointerType === 'pen';
    touchPointsRef.current.delete(e.pointerId);
    if (touchPointsRef.current.size < 2) {
      pinchGestureRef.current = { active: false, lastDistance: 0, lastMidpoint: null };
      if (isTouchLikePointer) {
        setIsPanning(false);
      }
    }
    if (pinchGestureRef.current.active) return;
    if (pinchWasActiveRef.current && isTouchLikePointer) {
      clearPendingTouchDrawAction();
      if (touchPointsRef.current.size === 0) {
        pinchWasActiveRef.current = false;
        if (mode === 'shape') {
          setDrawingShape(null);
        } else if (mode === 'draw') {
          setIsDrawingCurve(false);
          setGhostPoint(null);
          setDrawHover(null);
        } else if (mode === 'pencil') {
          setCurrentPath([]);
          setCurrentPathInfo(null);
        }
      }
      return;
    }
    const pendingTouchDrawAction = pendingTouchDrawActionRef.current;
    if (pendingTouchDrawAction.active && pendingTouchDrawAction.pointerId === (e.pointerId ?? null)) {
      clearPendingTouchDrawAction();
    }

    const longPressState = mobileLongPressRef.current;
    const wasLongPressAction = longPressState.pointerId != null
      && longPressState.pointerId === (e.pointerId ?? null)
      && longPressState.triggered;
    const shortPressTargetType = longPressState.targetType;
    const shortPressTargetId = longPressState.targetId;
    const isShortPressAction = isMobile
      && isTouchLikePointer
      && longPressState.pointerId != null
      && longPressState.pointerId === (e.pointerId ?? null)
      && !longPressState.triggered
      && !['draw', 'pencil', 'shape', 'text'].includes(mode);
    clearMobileLongPress();
    if (wasLongPressAction) {
      setIsPanning(false);
      return;
    }
    if (isShortPressAction && (shortPressTargetType === 'path' || shortPressTargetType === 'image' || shortPressTargetType === 'text')) {
      const selectedPathIndicesSet = new Set(selectedPoints.map(point => point.pathIndex));
      const totalSelectedObjects = selectedPathIndicesSet.size + selectedImageIds.length + selectedTextIds.length;
      pointerGestureRef.current = {
        pointerId: null,
        pointerType: 'mouse',
        startClientX: 0,
        startClientY: 0,
        dragActivated: false
      };
      setIsPanning(false);

      if (shortPressTargetType === 'text') {
        const keepCurrentSelection = totalSelectedObjects > 1 && selectedTextIds.includes(shortPressTargetId);
        if (!keepCurrentSelection) {
          setSelectedTextIds([shortPressTargetId]);
          setSelectedImageIds([]);
          setSelectedPoints([]);
        }
        setActivePathEditId(null);
        const textMenuWorld = getCanvasCoords(e.clientX, e.clientY);
        setCanvasContextMenu({
          type: 'actions',
          x: e.clientX,
          y: e.clientY,
          worldX: textMenuWorld.x,
          worldY: textMenuWorld.y,
          targetLayerId: texts.find(text => text.id === shortPressTargetId)?.layerId ?? null
        });
        return;
      }

      if (shortPressTargetType === 'path') {
        const targetPathIndex = paths.findIndex(path => path.id === shortPressTargetId);
        if (targetPathIndex !== -1) {
          const keepCurrentSelection = totalSelectedObjects > 1 && selectedPathIndicesSet.has(targetPathIndex);
          if (!keepCurrentSelection) {
            setSelectedPoints(getPathSelection(targetPathIndex));
            setSelectedImageIds([]);
            setSelectedTextIds([]);
          }
          setActivePathEditId(null);
          const pathMenuWorld = getCanvasCoords(e.clientX, e.clientY);
          setCanvasContextMenu({
            type: 'actions',
            x: e.clientX,
            y: e.clientY,
            worldX: pathMenuWorld.x,
            worldY: pathMenuWorld.y,
            targetLayerId: paths[targetPathIndex]?.layerId ?? null
          });
          return;
        }
      }

      if (shortPressTargetType === 'image') {
        const keepCurrentSelection = totalSelectedObjects > 1 && selectedImageIds.includes(shortPressTargetId);
        if (!keepCurrentSelection) {
          setSelectedImageIds([shortPressTargetId]);
          setSelectedPoints([]);
          setSelectedTextIds([]);
        }
        setActivePathEditId(null);
        const imageMenuWorld = getCanvasCoords(e.clientX, e.clientY);
        setCanvasContextMenu({
          type: 'actions',
          x: e.clientX,
          y: e.clientY,
          worldX: imageMenuWorld.x,
          worldY: imageMenuWorld.y,
          targetLayerId: images.find(img => img.id === shortPressTargetId)?.layerId ?? null
        });
        return;
      }
    }

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
          commitHistory({ paths, currentPath, images, layers, texts });
          
          const reusableLayerId = resolveEditContextLayerId();
          const count = layers.filter(l => l.itemType === shapeType).length;
          const newLayer = reusableLayerId ? null : createLayer(shapeType, count);
          const targetLayerId = reusableLayerId || newLayer.id;
          const newPathId = Date.now();
          const newPath = {
            id: newPathId,
            points: generated.points,
            isClosed: generated.isClosed,
            layerId: targetLayerId,
            itemType: shapeType,
            fillEnabled: pathStyleDefaults.fillEnabled,
            fillColor: normalizeStrokeColor(pathStyleDefaults.fillColor, DEFAULT_FILL_COLOR),
            strokeEnabled: pathStyleDefaults.strokeEnabled,
            strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
            strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
            strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN),
            editGroupId: activeEditGroupId || `path-${newPathId}`
          };
          const nextPaths = [...paths, newPath];

          if (newLayer) {
            setLayers(prev => [newLayer, ...prev]);
          }
          setPaths(nextPaths);
          setActiveLayerId(targetLayerId);
          setActivePathEditId(null);
          setSelectedPoints([]);
          setSelectedImageIds([]);
          setActiveHandle(null);
          setSelectionBox(null);
          setPointAction(null);
          setBgAction(null);
          setBgInitialState(null);
        }
        setDrawingShape(null);
      }
      return;
    }
    if (pointAction) {
      if (hasDraggedRef.current) {
          commitHistory({ paths: dragStartPathsRef.current, currentPath, images: dragStartImagesRef.current, layers, texts: dragStartTextsRef.current });
          hasDraggedRef.current = false;
      }
      pointRotateRef.current = { lastAngle: 0, accumulated: 0 };
      setPointAction(null);
      return;
    }
    if (bgAction) {
      if (hasDraggedRef.current) {
         commitHistory({ paths: dragStartPathsRef.current, currentPath, images: dragStartImagesRef.current, layers, texts: dragStartTextsRef.current });
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

        const simplificationTolerance = (isMobile ? 2.8 : 2) / zoom;
        finalPath = simplifyPolylinePoints(finalPath, simplificationTolerance);
        if (isClosed && finalPath.length < 3) {
          isClosed = false;
        }
        
        const count = layers.filter(l => l.itemType === 'vector').length;
        const reusableLayerId = resolveEditContextLayerId();
        const newLayer = reusableLayerId ? null : createLayer('vector', count);
        const targetLayerId = reusableLayerId || newLayer.id;
        const newPathId = Date.now();
        const newPath = {
          id: newPathId,
          points: finalPath,
          isClosed,
          layerId: targetLayerId,
          itemType: 'vector',
          fillEnabled: pathStyleDefaults.fillEnabled,
          strokeEnabled: pathStyleDefaults.strokeEnabled,
          strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
          strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
          strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN),
          editGroupId: activeEditGroupId || `path-${newPathId}`
        };
        const nextPaths = [...paths, newPath];
        if (newLayer) {
          setLayers(prev => [newLayer, ...prev]);
        }
        setPaths(nextPaths);
        setActiveLayerId(targetLayerId);
        setActivePathEditId(null);
        setSelectedPoints([]);
        setSelectedImageIds([]);
        setActiveHandle(null);
        setSelectionBox(null);
        setPointAction(null);
        setBgAction(null);
        setBgInitialState(null);
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
      clearPendingTouchDrawAction();
    } else if (mode === 'edit') {
      if (hasDraggedRef.current) {
        commitHistory({ paths: dragStartPathsRef.current, currentPath, images: dragStartImagesRef.current, layers, texts: dragStartTextsRef.current });
        hasDraggedRef.current = false;
      }
      setIsDraggingPoints(false);
      setActiveHandle(null);
      setSelectionBox(null);
    }
  };

  return { handlePointerDown, handlePointerMove, handlePointerUp };
}
