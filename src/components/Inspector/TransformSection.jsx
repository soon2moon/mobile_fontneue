import { RefreshCw, Ruler, Droplet, Lock, Unlock } from 'lucide-react';
import ConfigInput from '../../ui/inputs/ConfigInput';
import { useEditor } from '../../state/EditorContext';

// Position / scale / rotation / opacity + lock for the active image or text.
// Texts have no free scale (their size is fontSize, edited in TextSection).
export default function TransformSection() {
  const { inspector } = useEditor();
  const { transform, apply } = inspector;

  return (
    <div className="flex flex-col gap-2">
      <div className="flex items-center justify-between px-1 mb-1">
        <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest">Transform</label>
        <button
          onClick={() => apply({ locked: !transform.locked })}
          className={`p-1 rounded transition-colors ${transform.locked ? 'bg-[#eaecf0] text-[#344054]' : 'text-[#667085] hover:text-[#344054] hover:bg-[#eaecf0]'}`}
          title={transform.locked ? 'Unlock Object' : 'Lock Object'}
        >
          {transform.locked ? <Lock size={12} /> : <Unlock size={12} />}
        </button>
      </div>

      <div className="grid grid-cols-2 gap-2 mt-1">
        <ConfigInput
          label="X"
          value={transform.x}
          onChange={v => apply({ x: v })}
          title="X"
        />
        <ConfigInput
          label="Y"
          value={transform.y}
          onChange={v => apply({ y: v })}
          title="Y"
        />
        {transform.scale != null && (
          <ConfigInput
            icon={<Ruler size={14} />}
            value={transform.scale}
            scaleFactor={100}
            suffix="%"
            onChange={v => apply({ scale: Math.max(0.01, v) })}
            title="Scale"
          />
        )}
        <ConfigInput
          icon={<RefreshCw size={14} />}
          value={transform.rotation}
          suffix="°"
          onChange={v => apply({ rotation: v })}
          title="Rotation"
        />
        <div className="col-span-1">
          <ConfigInput
            icon={<Droplet size={14} />}
            value={transform.opacity}
            scaleFactor={100}
            suffix="%"
            onChange={v => apply({ opacity: Math.max(0, Math.min(1, v)) })}
            title="Opacity"
          />
        </div>
      </div>
    </div>
  );
}
