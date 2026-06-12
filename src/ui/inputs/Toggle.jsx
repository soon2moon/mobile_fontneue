// Shared pill switch for boolean settings (snap-to-grid, fill/stroke
// enable). Markup matches the previously inlined pattern so styling is
// unchanged at every call site.
export default function Toggle({ checked, onChange, title, disabled = false }) {
  return (
    <button
      onClick={() => onChange(!checked)}
      disabled={disabled}
      className={`relative inline-flex h-4 w-7 items-center rounded-full transition-colors focus:outline-none ${checked ? 'bg-[#344054]' : 'bg-[#d0d5dd]'} ${disabled ? 'opacity-40 cursor-default' : ''}`}
      title={title}
    >
      <span className={`inline-block h-3 w-3 transform rounded-full bg-white transition-transform ${checked ? 'translate-x-3.5' : 'translate-x-0.5'}`} />
    </button>
  );
}
