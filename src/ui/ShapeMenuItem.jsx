// Sub-component for Shape Menu Option
function ShapeMenuItem({ type, icon, label, hotkey, current, onClick }) {
  const active = current === type;
  return (
      <button
        onClick={() => onClick(type)}
        className={`flex items-center justify-between w-full p-2 text-xs font-medium rounded-lg transition-colors ${
            active ? 'bg-pressed text-ink' : 'text-secondary hover:bg-sunken hover:text-ink'
        }`}
      >
          <div className="flex items-center gap-2">
            {icon}
            <span>{label}</span>
          </div>
          {hotkey && <span className="text-[10px] font-mono text-muted">{hotkey}</span>}
      </button>
  )
}

export default ShapeMenuItem;
