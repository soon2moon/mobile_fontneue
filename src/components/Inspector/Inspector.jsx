import { useEditor } from '../../state/EditorContext';
import FillSection from './FillSection';
import StrokeSection from './StrokeSection';
import TransformSection from './TransformSection';
import TextSection from './TextSection';
import FrameSection from './FrameSection';

const FRAME_PRESETS = [
  { label: 'Phone', width: 390, height: 844 },
  { label: 'Tablet', width: 768, height: 1024 },
  { label: 'Desktop', width: 1440, height: 1024 },
  { label: 'Presentation', width: 1920, height: 1080 },
  { label: 'Square', width: 1080, height: 1080 },
  { label: 'A4', width: 595, height: 842 }
];

// Unified selection-aware panel body: path fill/stroke for path (or empty)
// selections, transform for images, font + transform for texts, name + fill
// + size for frames. When the Frame tool is active with nothing selected, a
// preset-size list drops a board at the viewport center.
export default function Inspector() {
  const { inspector, mode, createFramePreset } = useEditor();
  const { kind, fill, stroke, transform, text, frame } = inspector;

  return (
    <div className="p-3.5 flex flex-col gap-3">
      {mode === 'frame' && kind === 'none' && (
        <div className="flex flex-col gap-2">
          <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Frame Presets</label>
          <div className="grid grid-cols-2 gap-2">
            {FRAME_PRESETS.map(preset => (
              <button
                key={preset.label}
                type="button"
                onClick={() => createFramePreset(preset.width, preset.height)}
                className="flex flex-col items-start px-2 py-1.5 rounded-md bg-sunken hover:bg-pressed text-left transition-colors"
              >
                <span className="text-xs font-semibold text-ink">{preset.label}</span>
                <span className="text-[10px] text-muted font-mono">{preset.width}×{preset.height}</span>
              </button>
            ))}
          </div>
        </div>
      )}

      {frame && <FrameSection />}
      {fill && <FillSection />}
      {stroke && <StrokeSection />}
      {text && <TextSection />}
      {transform && <TransformSection />}

      {kind === 'none' && mode !== 'frame' && (
        <p className="text-[10px] text-muted px-1">
          Nothing selected — edits set the style for the next drawn path.
        </p>
      )}
      {kind === 'mixed' && fill && (
        <p className="text-[10px] text-muted px-1">
          Fill &amp; stroke apply to the selected paths.
        </p>
      )}
      {kind === 'mixed' && !fill && (
        <p className="text-[10px] text-muted px-1">
          Mixed selection — no shared properties to edit.
        </p>
      )}
    </div>
  );
}
