function MobileToolButton({ active = false, onClick, icon, label, radiusClass = 'rounded-lg', variant = 'solid' }) {
  const activeStyle = 'bg-[#eaecf0] border-[#d0d5dd] text-[#344054]';
  const solidIdleStyle = 'bg-[#f5f7fb] border-[#e6eaf0] text-[#667085] active:bg-[#eaecf0]';
  const toolbarIdleStyle = 'bg-transparent border-transparent text-[#667085] active:bg-[#eaecf0] active:text-[#344054] active:border-[#d0d5dd]';
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
