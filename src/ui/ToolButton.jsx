import Tooltip from './Tooltip';

// Sub-component for Toolbar Buttons
function ToolButton({ active, onClick, icon, label, hotkey }) {
  return (
    <Tooltip label={label} hotkey={hotkey}>
      <button
        onClick={onClick}
        aria-label={hotkey ? `${label} (${hotkey})` : label}
        className={`p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
          active
            ? 'bg-[#eaecf0] text-[#344054]'
            : 'text-[#667085] hover:text-[#344054] hover:bg-[#f2f4f7]'
        }`}
      >
        {icon}
      </button>
    </Tooltip>
  );
}

export default ToolButton;
