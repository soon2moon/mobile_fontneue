import { useState } from 'react';

// Layer management: visibility/lock toggles (multi-target when the clicked
// layer is part of the selection), delete-with-contents, inline rename,
// drag-drop reorder, click/shift/ctrl selection, and quick move up/down.
export function useLayers({
  layers, setLayers,
  paths, setPaths,
  images, setImages,
  texts, setTexts,
  currentPath,
  commitHistory,
  selectedPoints, setSelectedPoints,
  selectedImageIds, setSelectedImageIds,
  selectedTextIds, setSelectedTextIds,
  activeLayerId, setActiveLayerId,
  setActivePathEditId,
  mode, changeMode,
  isMobile
}) {
  const [editingLayerId, setEditingLayerId] = useState(null);
  const [editingLayerName, setEditingLayerName] = useState("");
  const [lastSelectedLayerId, setLastSelectedLayerId] = useState(null);
  const [dragDropTarget, setDragDropTarget] = useState(null); // { id: 'layer-2', position: 'top' | 'bottom' }
  const [draggedLayerId, setDraggedLayerId] = useState(null);

  const selectedLayerIds = new Set();
  if (selectedImageIds.length > 0) {
      selectedImageIds.forEach(id => {
          const img = images.find(i => i.id === id);
          if (img) selectedLayerIds.add(img.layerId);
      });
  }
  if (selectedTextIds.length > 0) {
      selectedTextIds.forEach(id => {
          const text = texts.find(t => t.id === id);
          if (text) selectedLayerIds.add(text.layerId);
      });
  }
  selectedPoints.forEach(sp => {
      const path = paths[sp.pathIndex];
      if (path) selectedLayerIds.add(path.layerId);
  });

  const toggleLayerVisibility = (id) => {
    const selectedIds = new Set();
    selectedImageIds.forEach(imgId => {
      const img = images.find(i => i.id === imgId);
      if (img) selectedIds.add(img.layerId);
    });
    selectedTextIds.forEach(textId => {
      const text = texts.find(t => t.id === textId);
      if (text) selectedIds.add(text.layerId);
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
      setSelectedTextIds(prev => prev.filter(textId => {
        const text = texts.find(t => t.id === textId);
        return text && !targetIdSet.has(text.layerId);
      }));
    }
  };

  const toggleLayerLock = (id) => {
    const selectedIds = new Set();
    selectedImageIds.forEach(imgId => {
      const img = images.find(i => i.id === imgId);
      if (img) selectedIds.add(img.layerId);
    });
    selectedTextIds.forEach(textId => {
      const text = texts.find(t => t.id === textId);
      if (text) selectedIds.add(text.layerId);
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
      setSelectedTextIds(prev => prev.filter(textId => {
          const text = texts.find(t => t.id === textId);
          return text && !targetIdSet.has(text.layerId);
      }));
    }
  };

  const deleteLayer = (layerId) => {
    const pathIdsInLayer = new Set(paths.filter(path => path.layerId === layerId).map(path => path.id));
    const imageIdsInLayer = new Set(images.filter(image => image.layerId === layerId).map(image => image.id));
    const textIdsInLayer = new Set(texts.filter(text => text.layerId === layerId).map(text => text.id));

    if (pathIdsInLayer.size === 0 && imageIdsInLayer.size === 0 && textIdsInLayer.size === 0) {
      setLayers(prevLayers => prevLayers.filter(layer => layer.id !== layerId));
      return;
    }

    commitHistory({ paths, currentPath, images, layers, texts });
    setPaths(prevPaths => prevPaths.filter(path => path.layerId !== layerId));
    setImages(prevImages => prevImages.filter(image => image.layerId !== layerId));
    setTexts(prevTexts => prevTexts.filter(text => text.layerId !== layerId));
    setLayers(prevLayers => prevLayers.filter(layer => layer.id !== layerId));

    setSelectedPoints(prev => prev.filter(sp => {
      const path = paths[sp.pathIndex];
      return path && path.layerId !== layerId && !pathIdsInLayer.has(path.id);
    }));
    setSelectedImageIds(prev => prev.filter(id => !imageIdsInLayer.has(id)));
    setSelectedTextIds(prev => prev.filter(id => !textIdsInLayer.has(id)));

    if (activeLayerId === layerId) {
      const fallbackLayer = layers.find(layer => layer.id !== layerId);
      setActiveLayerId(fallbackLayer ? fallbackLayer.id : null);
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
    if (isMobile) return;
    setDraggedLayerId(id);
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('text/plain', id);
  };

  const handleLayerDragOver = (e, id) => {
    if (!draggedLayerId) return;
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
    if (!draggedLayerId || !dragDropTarget) return;
    e.preventDefault();
    if (draggedLayerId !== targetId) {
      setLayers(prev => {
        const oldIndex = prev.findIndex(l => l.id === draggedLayerId);
        if (oldIndex === -1) return prev;
        const newLayers = [...prev];
        const [movedLayer] = newLayers.splice(oldIndex, 1);

        let newIndex = newLayers.findIndex(l => l.id === targetId);
        if (newIndex === -1) return prev;
        if (oldIndex < newIndex) {
          newIndex -= 1;
        }
        if (dragDropTarget.position === 'bottom') {
           newIndex += 1;
        }
        newIndex = Math.max(0, Math.min(newIndex, newLayers.length));
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

      // Content-based selection: pick up whatever the layer actually holds
      // (also keeps legacy rasterized-text layers — images on itemType
      // 'text' layers — selectable).
      const newSelPoints = [];
      const newSelImages = [];
      const newSelTexts = [];
      newSelectedLayerIds.forEach(lId => {
          const layerObj = layers.find(l => l.id === lId);
          if (!layerObj || layerObj.locked || !layerObj.visible) return;

          images.forEach(img => {
              if (img.layerId === lId) newSelImages.push(img.id);
          });
          texts.forEach(text => {
              if (text.layerId === lId) newSelTexts.push(text.id);
          });
          paths.forEach((p, pIdx) => {
              if (p.layerId === lId) {
                  p.points.forEach((_, ptIdx) => {
                      newSelPoints.push({ pathIndex: pIdx, pointIndex: ptIdx });
                  });
              }
          });
      });

      if (mode !== 'edit') {
          changeMode('edit');
      }

      setActivePathEditId(null);
      setSelectedPoints(newSelPoints);
      setSelectedImageIds(newSelImages);
      setSelectedTextIds(newSelTexts);
  };

  const moveSelectedLayerQuick = (layerId, direction) => {
    const currentIndex = layers.findIndex(layer => layer.id === layerId);
    if (currentIndex === -1) return;

    const nextIndex = direction === 'up' ? currentIndex - 1 : currentIndex + 1;
    if (nextIndex < 0 || nextIndex >= layers.length) return;

    commitHistory({ paths, currentPath, images, layers, texts });
    setLayers(prevLayers => {
      const fromIndex = prevLayers.findIndex(layer => layer.id === layerId);
      if (fromIndex === -1) return prevLayers;

      const toIndex = direction === 'up' ? fromIndex - 1 : fromIndex + 1;
      if (toIndex < 0 || toIndex >= prevLayers.length) return prevLayers;

      const reordered = [...prevLayers];
      const [movedLayer] = reordered.splice(fromIndex, 1);
      reordered.splice(toIndex, 0, movedLayer);
      return reordered;
    });
    setActiveLayerId(layerId);
  };

  return {
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
  };
}
