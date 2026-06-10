import { useState, useRef, useEffect, useCallback } from 'react';
import { MIN_ZOOM, MAX_ZOOM } from '../constants';

// Owns pan/zoom state plus the refs that mirror them. The refs are load-bearing:
// async callbacks (e.g. image onload placement) read panRef/zoomRef for current
// values without re-subscribing to state.
export function useViewport(svgRef) {
  const [pan, setPan] = useState({ x: window.innerWidth / 2, y: window.innerHeight / 2 });
  const [zoom, setZoom] = useState(1);
  const [isPanning, setIsPanning] = useState(false);
  const panRef = useRef({ x: window.innerWidth / 2, y: window.innerHeight / 2 });
  const zoomRef = useRef(1);

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
  }, [svgRef]);

  return {
    pan, setPan,
    zoom, setZoom,
    isPanning, setIsPanning,
    panRef, zoomRef,
    getCanvasCoords,
    zoomAtScreenPoint,
    stepZoom,
    handleWheel
  };
}
