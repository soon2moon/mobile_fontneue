import { useEditor } from '../../state/EditorContext';

// Fill on/off for the selected paths (or the next-path defaults). The color
// itself becomes editable in 7C.
export default function FillSection() {
  const { inspector } = useEditor();
  const { fill, apply } = inspector;

  return (
    <div className="flex items-center justify-between px-1 pb-2 border-b border-[#e4e7ec]">
      <label className="text-[10px] font-bold text-[#667085] uppercase tracking-widest">
        Fill{fill.indeterminate ? ' · Mixed' : ''}
      </label>
      <button
        onClick={() => apply({ fillEnabled: !fill.enabled })}
        className={`relative inline-flex h-4 w-7 items-center rounded-full transition-colors focus:outline-none ${fill.enabled ? 'bg-[#344054]' : 'bg-[#d0d5dd]'}`}
        title={fill.enabled ? 'Disable Fill' : 'Enable Fill'}
      >
        <span className={`inline-block h-3 w-3 transform rounded-full bg-white transition-transform ${fill.enabled ? 'translate-x-3.5' : 'translate-x-0.5'}`} />
      </button>
    </div>
  );
}
