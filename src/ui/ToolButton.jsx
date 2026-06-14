import Tooltip from './Tooltip';

// Shared toolbar button. The active tool uses the solid accent; panel toggles
// pass tone="panel" for a quieter grey active state, so multiple open panels
// don't flood the toolbar with blue.
function ToolButton({ active, onClick, icon, label, hotkey, tone = 'tool' }) {
  const activeClass = tone === 'panel' ? 'bg-pressed text-ink' : 'bg-accent text-white';
  return (
    <Tooltip label={label} hotkey={hotkey}>
      <button
        onClick={onClick}
        aria-label={hotkey ? `${label} (${hotkey})` : label}
        className={`p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
          active ? activeClass : 'text-secondary hover:text-ink hover:bg-sunken'
        }`}
      >
        {icon}
      </button>
    </Tooltip>
  );
}

export default ToolButton;
