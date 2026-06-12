import { useState } from 'react';
import ColorControl from '../../ui/ColorControl';
import Toggle from '../../ui/inputs/Toggle';
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
  const { stroke, apply, applyTransient } = inspector;
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
        <Toggle
          checked={stroke.enabled}
          onChange={(next) => apply({ strokeEnabled: next })}
          title={stroke.enabled ? 'Disable Stroke' : 'Enable Stroke'}
        />
      </div>

      <div className="grid grid-cols-[minmax(0,1fr)_88px] gap-2">
        <div className="h-8 flex items-center gap-2 bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all">
          <ColorControl
            value={stroke.color}
            showIndeterminate={stroke.indeterminate.color}
            label="Stroke Color"
            onChange={(color) => {
              setStrokeColorInput(color.replace('#', ''));
              apply({ strokeColor: color, strokeEnabled: true });
            }}
            onChangeTransient={(color) => {
              setStrokeColorInput(color.replace('#', ''));
              applyTransient({ strokeColor: color });
            }}
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
