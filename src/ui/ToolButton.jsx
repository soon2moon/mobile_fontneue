// Sub-component for Toolbar Buttons
function ToolButton({ active, onClick, icon, label, hotkey }) {
  return (
    <button
      onClick={onClick}
      className={`relative group p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
        active
          ? 'bg-[#eaecf0] text-[#344054]'
          : 'text-[#667085] hover:text-[#344054] hover:bg-[#f2f4f7]'
      }`}
      title={hotkey ? `${label} (${hotkey})` : label}
    >
      {icon}

      {/* Tooltip */}
      <div className="absolute -top-10 scale-0 group-hover:scale-100 opacity-0 group-hover:opacity-100 transition-all origin-bottom bg-[#344054] text-[#f2f4f7] text-xs font-medium px-2 py-1 rounded shadow-lg flex items-center gap-2 pointer-events-none whitespace-nowrap z-50">
        <span>{label}</span>
        {hotkey && <span className="text-[#98a2b3] font-mono text-[10px] bg-[#1f2937] px-1 rounded">{hotkey}</span>}
        <div className="absolute -bottom-1 left-1/2 -translate-x-1/2 w-2 h-2 bg-[#344054] rotate-45"></div>
      </div>
    </button>
  );
}

export default ToolButton;
