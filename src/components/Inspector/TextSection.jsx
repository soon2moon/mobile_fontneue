import { Type } from 'lucide-react';
import ConfigInput from '../../ui/inputs/ConfigInput';
import { MIN_FONT_SIZE } from '../../lib/objectModel';
import { useEditor } from '../../state/EditorContext';

// Text-specific properties for the active text object. The fill color
// control lands here in 7C.
export default function TextSection() {
  const { inspector } = useEditor();
  const { text, apply } = inspector;

  return (
    <div className="flex flex-col gap-2">
      <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest px-1">Text</label>
      <div className="grid grid-cols-2 gap-2">
        <ConfigInput
          icon={<Type size={14} />}
          value={text.fontSize}
          suffix="px"
          onChange={v => apply({ fontSize: Math.max(MIN_FONT_SIZE, v) })}
          title="Font Size"
        />
      </div>
    </div>
  );
}
