import { useState, useEffect } from 'react';
import { SESSION_STORAGE_KEY, LEGACY_SESSION_STORAGE_KEY } from '../constants';
import { clonePoint } from '../lib/paths';

// Loads the saved session once on mount, then persists on every change.
// The sessionLoaded gate is load-bearing: without it the save effect would
// run before the load effect finishes and wipe the stored session.
export function useSessionPersistence({
  layers, setLayers,
  paths, setPaths,
  images, setImages,
  currentPath, setCurrentPath,
  currentPathInfo, setCurrentPathInfo,
  pathStyleDefaults, setPathStyleDefaults,
  gridConfig, setGridConfig,
  showBackgroundAids, setShowBackgroundAids,
  activeLayerId, setActiveLayerId
}) {
  const [sessionLoaded, setSessionLoaded] = useState(false);

  useEffect(() => {
    try {
      let rawSession = localStorage.getItem(SESSION_STORAGE_KEY);
      if (!rawSession) {
        // One-time migration from the legacy (font-tool era) session key.
        rawSession = localStorage.getItem(LEGACY_SESSION_STORAGE_KEY);
        if (rawSession) {
          localStorage.removeItem(LEGACY_SESSION_STORAGE_KEY);
        }
      }
      if (!rawSession) {
        setSessionLoaded(true);
        return;
      }
      const parsedSession = JSON.parse(rawSession);
      if (Array.isArray(parsedSession.layers)) {
        setLayers(parsedSession.layers.map(layer => ({ ...layer })));
      }
      if (Array.isArray(parsedSession.paths)) {
        setPaths(parsedSession.paths.map(path => ({
          ...path,
          points: Array.isArray(path.points) ? path.points.map(clonePoint) : []
        })));
      }
      if (Array.isArray(parsedSession.images)) {
        setImages(parsedSession.images.map(image => ({ ...image })));
      }
      if (Array.isArray(parsedSession.currentPath)) {
        setCurrentPath(parsedSession.currentPath.map(clonePoint));
      }
      if (parsedSession.currentPathInfo && typeof parsedSession.currentPathInfo === 'object') {
        setCurrentPathInfo({ ...parsedSession.currentPathInfo });
      }
      if (parsedSession.pathStyleDefaults && typeof parsedSession.pathStyleDefaults === 'object') {
        setPathStyleDefaults(prev => ({ ...prev, ...parsedSession.pathStyleDefaults }));
      }
      if (parsedSession.gridConfig && typeof parsedSession.gridConfig === 'object') {
        setGridConfig(prev => ({ ...prev, ...parsedSession.gridConfig }));
      }
      if (typeof parsedSession.showBackgroundAids === 'boolean') {
        setShowBackgroundAids(parsedSession.showBackgroundAids);
      }
      if (typeof parsedSession.activeLayerId === 'string' || parsedSession.activeLayerId === null) {
        setActiveLayerId(parsedSession.activeLayerId);
      }
    } catch (err) {
      // Ignore invalid session data and continue with defaults.
    } finally {
      setSessionLoaded(true);
    }
  }, []);

  useEffect(() => {
    if (!sessionLoaded) return;
    const sessionPayload = {
      layers: layers.map(layer => ({ ...layer })),
      paths: paths.map(path => ({
        ...path,
        points: (path.points || []).map(clonePoint)
      })),
      images: images.map(image => ({ ...image })),
      currentPath: currentPath.map(clonePoint),
      currentPathInfo: currentPathInfo ? { ...currentPathInfo } : null,
      pathStyleDefaults: { ...pathStyleDefaults },
      gridConfig: { ...gridConfig },
      showBackgroundAids,
      activeLayerId
    };
    try {
      localStorage.setItem(SESSION_STORAGE_KEY, JSON.stringify(sessionPayload));
    } catch (err) {
      // Ignore storage quota or permission failures.
    }
  }, [
    sessionLoaded,
    layers,
    paths,
    images,
    currentPath,
    currentPathInfo,
    pathStyleDefaults,
    gridConfig,
    showBackgroundAids,
    activeLayerId
  ]);

  return { sessionLoaded };
}
