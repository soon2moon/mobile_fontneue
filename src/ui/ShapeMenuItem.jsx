// Sub-component for Shape Menu Option
function ShapeMenuItem({ type, icon, label, hotkey, current, onClick }) {
  const active = current === type;
  return (
      <button
        onClick={() => onClick(type)}
        className={`flex items-center justify-between w-full p-2 text-xs font-medium rounded-lg transition-colors ${
            active ? 'bg-[#eaecf0] text-[#344054]' : 'text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
        }`}
      >
          <div className="flex items-center gap-2">
            {icon}
            <span>{label}</span>
          </div>
          {hotkey && <span className="text-[10px] font-mono text-[#98a2b3]">{hotkey}</span>}
      </button>
  )
}

export default ShapeMenuItem;
