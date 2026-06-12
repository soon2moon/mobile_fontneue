import { Type } from 'lucide-react';
import ConfigInput from '../../ui/inputs/ConfigInput';
import ColorControl from '../../ui/ColorControl';
import { MIN_FONT_SIZE } from '../../lib/objectModel';
import { useEditor } from '../../state/EditorContext';

// Text-specific properties for the active text object.
export default function TextSection() {
  const { inspector } = useEditor();
  const { text, apply, applyTransient } = inspector;

  return (
    <div className="flex flex-col gap-2">
      <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Text</label>
      <div className="grid grid-cols-2 gap-2">
        <ConfigInput
          icon={<Type size={14} />}
          value={text.fontSize}
          suffix="px"
          onChange={v => apply({ fontSize: Math.max(MIN_FONT_SIZE, v) })}
          title="Font Size"
        />
        <div className="h-8 flex items-center gap-2 bg-sunken rounded-md px-2">
          <ColorControl
            value={text.fill}
            label="Text Color"
            onChange={(color) => apply({ fill: color })}
            onChangeTransient={(color) => applyTransient({ fill: color })}
          />
          <span className="text-xs text-secondary select-none">Color</span>
        </div>
      </div>
    </div>
  );
}
