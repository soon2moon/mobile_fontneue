function MobileToolButton({ active = false, onClick, icon, label, radiusClass = 'rounded-lg', variant = 'solid' }) {
  const activeStyle = 'bg-accent border-accent text-white';
  const solidIdleStyle = 'bg-sunken border-edge text-secondary active:bg-pressed';
  const toolbarIdleStyle = 'bg-transparent border-transparent text-secondary active:bg-pressed active:text-ink active:border-edge-strong';
  const idleStyle = variant === 'toolbar' ? toolbarIdleStyle : solidIdleStyle;
  const handlePointerRelease = (event) => {
    if (event?.currentTarget && typeof event.currentTarget.blur === 'function') {
      event.currentTarget.blur();
    }
  };

  return (
    <button
      onClick={onClick}
      onPointerUp={handlePointerRelease}
      onPointerCancel={handlePointerRelease}
      onTouchEnd={handlePointerRelease}
      onMouseUp={handlePointerRelease}
      title={label}
      className={`h-9 min-w-9 px-1.5 ${radiusClass} border flex items-center justify-center shrink-0 ${
        active ? activeStyle : idleStyle
      }`}
    >
      {icon}
    </button>
  );
}

export default MobileToolButton;
