import { useState, useEffect } from 'react';
import ColorControl from '../../ui/ColorControl';
import { useEditor } from '../../state/EditorContext';
import { normalizeStrokeColor } from '../../lib/stroke';

// Frame (board) name + background fill for the selected frame.
export default function FrameSection() {
  const { inspector } = useEditor();
  const { frame, apply, applyTransient } = inspector;
  const [nameDraft, setNameDraft] = useState(frame.name);

  useEffect(() => {
    setNameDraft(frame.name);
  }, [frame.name]);

  const commitName = () => {
    const next = nameDraft.trim() || 'Frame';
    setNameDraft(next);
    apply({ name: next });
  };

  return (
    <div className="flex flex-col gap-2">
      <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Frame</label>
      <input
        type="text"
        value={nameDraft}
        onChange={(e) => setNameDraft(e.target.value)}
        onBlur={commitName}
        onKeyDown={(e) => {
          if (e.key === 'Enter') {
            e.preventDefault();
            commitName();
            e.currentTarget.blur();
          }
        }}
        className="h-8 bg-sunken rounded-md px-2 text-xs text-ink outline-none focus:ring-1 focus:ring-edge-strong"
        title="Frame Name"
      />
      <div className="h-8 flex items-center gap-2 bg-sunken rounded-md px-2 focus-within:ring-1 focus-within:ring-edge-strong transition-all">
        <ColorControl
          value={frame.fill}
          label="Frame Fill"
          onChange={(color) => apply({ fill: normalizeStrokeColor(color, frame.fill) })}
          onChangeTransient={(color) => applyTransient({ fill: normalizeStrokeColor(color, frame.fill) })}
        />
        <span className="text-xs text-secondary select-none">Background</span>
      </div>
    </div>
  );
}
