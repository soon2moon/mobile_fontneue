import { useRef, useCallback } from 'react';
import { clonePoint } from '../lib/paths';

// Rollback snapshot for touch drawing: a one-finger pen/pencil action is
// provisional until we know a second finger isn't joining for a pinch/pan —
// begin() captures the pre-gesture state, rollback() restores it.
export function usePendingTouchDraw({
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
}) {
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

  return {
    pendingTouchDrawActionRef,
    clearPendingTouchDrawAction,
    beginPendingTouchDrawAction,
    rollbackPendingTouchDrawAction
  };
}
