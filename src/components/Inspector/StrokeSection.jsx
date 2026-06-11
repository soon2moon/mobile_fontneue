import { useState } from 'react';
import { normalizeStrokeColor } from '../../lib/stroke';
import { useEditor } from '../../state/EditorContext';

// Stroke toggle + color (swatch & hex) + width + align for the selected
// paths (or the next-path defaults). Fields whose value differs across the
// selection show a "Mixed" placeholder until focused; committing a value
// unifies the whole selection.
export default function StrokeSection() {
  const {
    inspector,
    strokeColorInput,
    setStrokeColorInput,
    handleStrokeColorInputChange,
    commitStrokeColorInput,
    strokeWidthInput,
    handleStrokeWidthInputChange,
    commitStrokeWidthInput
  } = useEditor();
  const { stroke, apply } = inspector;
  const [widthFocused, setWidthFocused] = useState(false);
  const [colorFocused, setColorFocused] = useState(false);

  const showMixedWidth = stroke.indeterminate.width && !widthFocused;
  const showMixedColor = stroke.indeterminate.color && !colorFocused;

  return (
    <div className="flex flex-col gap-3">
      <div className="flex items-center justify-between px-1 pb-2 border-b border-[#e4e7ec]">
        <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest">
          Stroke{stroke.indeterminate.enabled ? ' · Mixed' : ''}
        </label>
        <button
          onClick={() => apply({ strokeEnabled: !stroke.enabled })}
          className={`relative inline-flex h-4 w-7 items-center rounded-full transition-colors focus:outline-none ${stroke.enabled ? 'bg-[#344054]' : 'bg-[#d0d5dd]'}`}
          title={stroke.enabled ? 'Disable Stroke' : 'Enable Stroke'}
        >
          <span className={`inline-block h-3 w-3 transform rounded-full bg-white transition-transform ${stroke.enabled ? 'translate-x-3.5' : 'translate-x-0.5'}`} />
        </button>
      </div>

      <div className="grid grid-cols-[1fr_88px] gap-2">
        <div className="h-8 flex items-center gap-2 bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all">
          <input
            type="color"
            value={stroke.color}
            onChange={(e) => {
              const next = normalizeStrokeColor(e.target.value, stroke.color);
              setStrokeColorInput(next.replace('#', ''));
              apply({ strokeColor: next, strokeEnabled: true });
            }}
            className="h-5 w-5 p-0 border border-[#d0d5dd] rounded cursor-pointer bg-transparent"
            title="Stroke Color"
          />
          <input
            type="text"
            value={showMixedColor ? '' : strokeColorInput}
            onChange={(e) => handleStrokeColorInputChange(e.target.value)}
            onFocus={() => setColorFocused(true)}
            onBlur={() => {
              setColorFocused(false);
              commitStrokeColorInput();
            }}
            onKeyDown={(e) => {
              if (e.key === 'Enter') {
                e.preventDefault();
                commitStrokeColorInput();
                e.currentTarget.blur();
              }
            }}
            className="flex-1 min-w-0 text-xs text-left bg-transparent border-none outline-none py-1 text-[#344054] font-mono uppercase"
            placeholder={showMixedColor ? 'Mixed' : '4A2622'}
            maxLength={6}
            title="Stroke Color (Hex)"
          />
        </div>
        <div className="h-8 flex items-center gap-1 bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all">
          <input
            type="text"
            value={showMixedWidth ? '' : strokeWidthInput}
            onChange={(e) => handleStrokeWidthInputChange(e.target.value)}
            onFocus={() => setWidthFocused(true)}
            onBlur={() => {
              setWidthFocused(false);
              commitStrokeWidthInput();
            }}
            onKeyDown={(e) => {
              if (e.key === 'Enter') {
                e.preventDefault();
                commitStrokeWidthInput();
                e.currentTarget.blur();
              }
            }}
            className="flex-1 min-w-0 text-xs text-right bg-transparent border-none outline-none py-1 text-[#344054] font-mono"
            placeholder={showMixedWidth ? 'Mixed' : '1.5'}
            title="Stroke Width"
          />
          <span className="text-xs text-[#667085] font-mono select-none">px</span>
        </div>
      </div>

      <div className="grid grid-cols-[1fr] gap-2">
        <select
          value={stroke.indeterminate.align ? '' : stroke.align}
          onChange={(e) => {
            if (e.target.value) apply({ strokeAlign: e.target.value });
          }}
          className="h-8 bg-[#f2f4f7] rounded-md border border-transparent px-2 text-xs text-[#344054] focus:outline-none focus:ring-1 focus:ring-[#d0d5dd]"
          title="Stroke Align"
        >
          {stroke.indeterminate.align && <option value="" disabled>Mixed</option>}
          <option value="center">Center</option>
          <option value="inside">Inside</option>
          <option value="outside">Outside</option>
        </select>
      </div>
    </div>
  );
}
