import { useState, useEffect } from 'react';
import ColorControl from '../../ui/ColorControl';
import Toggle from '../../ui/inputs/Toggle';
import { useEditor } from '../../state/EditorContext';
import { normalizeStrokeColor } from '../../lib/stroke';

// Fill on/off + color (swatch & hex) for the selected paths (or the
// next-path defaults). Mixed-value fields show a placeholder until focused;
// committing a value unifies the whole selection.
export default function FillSection() {
  const { inspector } = useEditor();
  const { fill, apply, applyTransient } = inspector;
  const [hexInput, setHexInput] = useState(fill.color.replace('#', ''));
  const [hexFocused, setHexFocused] = useState(false);

  useEffect(() => {
    setHexInput(fill.color.replace('#', ''));
  }, [fill.color]);

  const showMixedColor = fill.indeterminate.color && !hexFocused;

  const commitHexInput = () => {
    const normalized = normalizeStrokeColor(`#${hexInput}`, fill.color);
    setHexInput(normalized.replace('#', ''));
    apply({ fillColor: normalized, fillEnabled: true });
  };

  return (
    <div className="flex flex-col gap-3">
      <div className="flex items-center justify-between px-1 pb-2 border-b border-[#e4e7ec]">
        <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest">
          Fill{fill.indeterminate.enabled ? ' · Mixed' : ''}
        </label>
        <Toggle
          checked={fill.enabled}
          onChange={(next) => apply({ fillEnabled: next })}
          title={fill.enabled ? 'Disable Fill' : 'Enable Fill'}
        />
      </div>

      <div className="h-8 flex items-center gap-2 bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all">
        <ColorControl
          value={fill.color}
          showIndeterminate={fill.indeterminate.color}
          label="Fill Color"
          onChange={(color) => {
            setHexInput(color.replace('#', ''));
            apply({ fillColor: color, fillEnabled: true });
          }}
          onChangeTransient={(color) => {
            setHexInput(color.replace('#', ''));
            applyTransient({ fillColor: color });
          }}
        />
        <input
          type="text"
          value={showMixedColor ? '' : hexInput}
          onChange={(e) => setHexInput(e.target.value.replace(/[^0-9a-fA-F]/g, '').slice(0, 6).toLowerCase())}
          onFocus={() => setHexFocused(true)}
          onBlur={() => {
            setHexFocused(false);
            commitHexInput();
          }}
          onKeyDown={(e) => {
            if (e.key === 'Enter') {
              e.preventDefault();
              commitHexInput();
              e.currentTarget.blur();
            }
          }}
          className="flex-1 min-w-0 text-xs text-left bg-transparent border-none outline-none py-1 text-[#344054] font-mono uppercase"
          placeholder={showMixedColor ? 'Mixed' : '344054'}
          maxLength={6}
          title="Fill Color (Hex)"
        />
      </div>
    </div>
  );
}
