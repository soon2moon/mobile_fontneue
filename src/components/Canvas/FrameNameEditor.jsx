import { useEffect, useRef, useState } from 'react';
import { useEditor } from '../../state/EditorContext';

// Inline editor for a frame's name, opened by double-clicking the frame's
// title label on the canvas (usePointerInteraction sets renamingFrameId).
// Positioned over the label in screen space (pan + world * zoom, matching the
// canvas transform). Commits on Enter / blur / backdrop press, cancels on
// Escape. Mirrors TextEditorOverlay's commit-vs-blur race handling.
export default function FrameNameEditor() {
  const { renamingFrameId, setRenamingFrameId, frames, pan, zoom, renameFrame } = useEditor();
  const frame = renamingFrameId != null ? frames.find(f => f.id === renamingFrameId) : null;

  const inputRef = useRef(null);
  const committedRef = useRef(false);
  const [draft, setDraft] = useState('');

  useEffect(() => {
    if (renamingFrameId == null) return;
    const target = frames.find(f => f.id === renamingFrameId);
    if (!target) return;
    committedRef.current = false;
    setDraft(target.name);
    const node = inputRef.current;
    if (node) {
      node.focus({ preventScroll: true });
      node.select();
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [renamingFrameId]);

  if (!frame) return null;

  const commit = () => {
    if (committedRef.current) return;
    committedRef.current = true;
    renameFrame(frame.id, draft);
    setRenamingFrameId(null);
  };
  const cancel = () => {
    if (committedRef.current) return;
    committedRef.current = true;
    setRenamingFrameId(null);
  };

  const left = pan.x + (frame.x - frame.width / 2) * zoom;
  const top = pan.y + (frame.y - frame.height / 2) * zoom - 18;

  return (
    <div
      className="absolute inset-0 z-[40]"
      onPointerDown={(e) => {
        e.stopPropagation();
        commit();
      }}
    >
      <input
        ref={inputRef}
        value={draft}
        onChange={(e) => setDraft(e.target.value)}
        onBlur={commit}
        onPointerDown={(e) => e.stopPropagation()}
        onKeyDown={(e) => {
          if (e.key === 'Enter') {
            e.preventDefault();
            e.stopPropagation();
            commit();
          } else if (e.key === 'Escape') {
            e.preventDefault();
            e.stopPropagation();
            cancel();
          }
        }}
        spellCheck={false}
        autoCapitalize="off"
        autoCorrect="off"
        className="absolute bg-raised text-ink text-[11px] leading-none font-sans px-1 rounded-sm outline-none ring-1 ring-accent"
        style={{ left, top, height: 18, minWidth: 40 }}
      />
    </div>
  );
}
