import { useEffect, useRef } from 'react';
import { useEditor } from '../../state/EditorContext';
import { measureTextBlock } from '../../lib/textMeasure';

// Screen-space editor for the active text session: a full-screen transparent
// backdrop that commits on pointerdown (settles the blur-vs-pointerdown race)
// plus a borderless textarea sized to the measured block. A textarea — not
// contentEditable — so the global hotkey guard's TEXTAREA check covers it.
export default function TextEditorOverlay() {
  const {
    editingText,
    updateDraft,
    commitTextEditing,
    pan,
    setPan,
    zoom,
    isMobile,
    viewportSize,
    mobileBottomInset
  } = useEditor();

  const textareaRef = useRef(null);
  const editingTextLatestRef = useRef(editingText);
  editingTextLatestRef.current = editingText;

  // Focus once per session; an existing text starts fully selected.
  useEffect(() => {
    if (!editingText) return;
    const node = textareaRef.current;
    if (!node) return;
    node.focus({ preventScroll: true });
    if (editingText.mode === 'existing') {
      node.select();
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [editingText?.mode, editingText?.textId]);

  // Mobile: when the on-screen keyboard insets the viewport, lift the canvas
  // once so the block being edited stays visible above it.
  useEffect(() => {
    if (!isMobile || mobileBottomInset <= 0) return;
    const editing = editingTextLatestRef.current;
    if (!editing) return;
    const block = measureTextBlock(editing.draft.length > 0 ? editing.draft : ' ', editing.style);
    const bottomOnScreen = pan.y + (editing.anchorTop + block.height) * zoom;
    const limit = viewportSize.height - mobileBottomInset - 16;
    if (bottomOnScreen > limit) {
      setPan(prev => ({ ...prev, y: prev.y - (bottomOnScreen - limit) }));
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [isMobile, mobileBottomInset]);

  if (!editingText) return null;

  const block = measureTextBlock(
    editingText.draft.length > 0 ? editingText.draft : ' ',
    editingText.style
  );
  const widthPx = block.width * zoom;
  const heightPx = block.height * zoom;
  const caretPad = Math.max(8, editingText.style.fontSize * zoom * 0.5);
  const rotation = editingText.rotation || 0;

  return (
    <div
      className="absolute inset-0 z-[40]"
      onPointerDown={(e) => {
        e.stopPropagation();
        commitTextEditing();
      }}
    >
      <textarea
        ref={textareaRef}
        value={editingText.draft}
        onChange={(e) => updateDraft(e.target.value)}
        onBlur={commitTextEditing}
        onPointerDown={(e) => e.stopPropagation()}
        onKeyDown={(e) => {
          if (e.key === 'Escape') {
            e.preventDefault();
            e.stopPropagation();
            commitTextEditing();
          }
        }}
        spellCheck={false}
        autoCapitalize="off"
        autoCorrect="off"
        wrap="off"
        className="absolute resize-none border-none outline-none bg-transparent p-0 m-0 overflow-hidden"
        style={{
          left: pan.x + editingText.anchorLeft * zoom,
          top: pan.y + editingText.anchorTop * zoom,
          width: widthPx + caretPad,
          height: heightPx,
          fontSize: editingText.style.fontSize * zoom,
          lineHeight: editingText.style.lineHeight,
          fontFamily: editingText.style.fontFamily,
          fontWeight: editingText.style.fontWeight,
          textAlign: editingText.style.textAlign,
          color: editingText.style.fill,
          opacity: editingText.style.opacity,
          caretColor: editingText.style.fill,
          whiteSpace: 'pre',
          transform: rotation ? `rotate(${rotation}deg)` : undefined,
          transformOrigin: `${widthPx / 2}px ${heightPx / 2}px`
        }}
      />
    </div>
  );
}
