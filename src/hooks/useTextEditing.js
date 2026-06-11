import { useState, useRef, useCallback } from 'react';
import { createTextObject, DEFAULT_TEXT_STYLE } from '../lib/objectModel';
import { measureTextBlock, getTextLocalLayout } from '../lib/textMeasure';
import { createLayer } from '../lib/layers';

// The text-editing session: one overlay textarea at a time, opened by the
// text tool (new) or double-click (existing). The session anchors at the
// block's top-LEFT corner so typing grows right/down; the object's center
// x/y is recomputed from the measured block on commit.
//
// Key invariant: a 'new' text is NOT in texts[] while its editor is open.
// Commit produces exactly ONE history entry (or none when nothing changed /
// an empty draft is discarded), so empty objects are never persisted.
export function useTextEditing({
  paths, currentPath,
  images,
  texts, setTexts,
  layers, setLayers,
  commitHistory,
  activeLayerId, setActiveLayerId,
  setMode,
  setSelectedTextIds,
  setSelectedPoints,
  setSelectedImageIds,
  setActivePathEditId
}) {
  const [editingText, setEditingText] = useState(null);
  // Synchronous mirror so commit stays idempotent when blur and the backdrop
  // pointerdown both fire for the same gesture.
  const editingTextRef = useRef(null);

  const setEditing = (next) => {
    editingTextRef.current = next;
    setEditingText(next);
  };

  const beginNewTextAt = useCallback((worldPoint) => {
    setEditing({
      mode: 'new',
      textId: null,
      anchorLeft: worldPoint.x,
      anchorTop: worldPoint.y,
      draft: '',
      style: { ...DEFAULT_TEXT_STYLE },
      rotation: 0,
      layerId: null
    });
  }, []);

  const beginEditingText = useCallback((text) => {
    const { halfW, halfH } = getTextLocalLayout(text);
    setEditing({
      mode: 'existing',
      textId: text.id,
      anchorLeft: text.x - halfW,
      anchorTop: text.y - halfH,
      draft: text.content,
      style: {
        fontSize: text.fontSize,
        fontFamily: text.fontFamily,
        fontWeight: text.fontWeight,
        textAlign: text.textAlign,
        lineHeight: text.lineHeight,
        fill: text.fill,
        opacity: text.opacity
      },
      rotation: text.rotation || 0,
      layerId: text.layerId
    });
  }, []);

  const updateDraft = useCallback((draft) => {
    const editing = editingTextRef.current;
    if (!editing) return;
    setEditing({ ...editing, draft });
  }, []);

  const selectCommittedText = (textId) => {
    setMode('edit');
    setSelectedTextIds([textId]);
    setSelectedPoints([]);
    setSelectedImageIds([]);
    setActivePathEditId(null);
  };

  const pruneLayerIfEmpty = (layerId, nextTexts) => {
    const hasPaths = paths.some(path => path.layerId === layerId);
    const hasImages = images.some(img => img.layerId === layerId);
    const hasTexts = nextTexts.some(text => text.layerId === layerId);
    if (hasPaths || hasImages || hasTexts) return;
    setLayers(prevLayers => {
      const remainingLayers = prevLayers.filter(l => l.id !== layerId);
      if (activeLayerId === layerId) {
        setActiveLayerId(remainingLayers.length > 0 ? remainingLayers[0].id : null);
      }
      return remainingLayers;
    });
  };

  const commitTextEditing = () => {
    const editing = editingTextRef.current;
    if (!editing) return;
    setEditing(null);

    const content = editing.draft;
    const isEmpty = content.trim().length === 0;

    if (editing.mode === 'new') {
      if (isEmpty) return;
      commitHistory({ paths, currentPath, images, texts, layers });
      const block = measureTextBlock(content, editing.style);
      const count = layers.filter(l => l.itemType === 'text').length;
      const newLayer = createLayer('text', count);
      const newText = createTextObject({
        x: editing.anchorLeft + block.width / 2,
        y: editing.anchorTop + block.height / 2,
        content,
        layerId: newLayer.id,
        style: editing.style
      });
      setLayers(prev => [newLayer, ...prev]);
      setActiveLayerId(newLayer.id);
      setTexts(prev => [...prev, newText]);
      selectCommittedText(newText.id);
      return;
    }

    const target = texts.find(text => text.id === editing.textId);
    if (!target) return;

    if (isEmpty) {
      commitHistory({ paths, currentPath, images, texts, layers });
      const nextTexts = texts.filter(text => text.id !== editing.textId);
      setTexts(nextTexts);
      pruneLayerIfEmpty(target.layerId, nextTexts);
      setSelectedTextIds(prev => prev.filter(id => id !== editing.textId));
      return;
    }

    if (content === target.content) {
      selectCommittedText(target.id);
      return;
    }

    commitHistory({ paths, currentPath, images, texts, layers });
    const block = measureTextBlock(content, target);
    setTexts(prev => prev.map(text => text.id === editing.textId
      ? {
          ...text,
          content,
          x: editing.anchorLeft + block.width / 2,
          y: editing.anchorTop + block.height / 2
        }
      : text));
    selectCommittedText(target.id);
  };

  // Latest-closure ref so the pointer hook and changeMode can commit without
  // re-capturing the per-render callback.
  const commitTextEditingRef = useRef(commitTextEditing);
  commitTextEditingRef.current = commitTextEditing;

  return {
    editingText,
    editingTextId: editingText ? editingText.textId : null,
    beginNewTextAt,
    beginEditingText,
    updateDraft,
    commitTextEditing,
    commitTextEditingRef
  };
}
