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
            ? 'bg-accent text-white'
            : 'text-secondary hover:text-ink hover:bg-sunken'
        }`}
      >
        {icon}
      </button>
    </Tooltip>
  );
}

export default ToolButton;
