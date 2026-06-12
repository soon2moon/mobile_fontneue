import { useState, useRef, useEffect, useCallback } from 'react';

const ScrubbableNumberInput = ({
  value,
  onChange,
  min = -Infinity,
  max = Infinity,
  step = 1,
  suffix = ""
}) => {
  const sanitizedValue = Number.isFinite(value) ? value : 0;
  const [focused, setFocused] = useState(false);
  const [tempVal, setTempVal] = useState(String(Math.round(sanitizedValue)));
  const scrubRef = useRef({
    active: false,
    pointerId: null,
    startX: 0,
    startValue: 0,
    moved: false
  });

  const clamp = useCallback((v) => Math.min(max, Math.max(min, v)), [min, max]);

  useEffect(() => {
    if (!focused && !scrubRef.current.active) {
      setTempVal(String(Math.round(sanitizedValue)));
    }
  }, [sanitizedValue, focused]);

  useEffect(() => {
    return () => {
      if (scrubRef.current.active) {
        document.body.style.userSelect = '';
        document.body.style.cursor = '';
      }
    };
  }, []);

  const commitValue = useCallback((rawValue) => {
    let parsed = Number(rawValue);
    if (!Number.isFinite(parsed)) parsed = sanitizedValue;
    parsed = clamp(parsed);
    onChange(parsed);
    setTempVal(String(Math.round(parsed)));
  }, [clamp, onChange, sanitizedValue]);

  const startScrub = (e) => {
    if (e.button !== 0) return;
    scrubRef.current = {
      active: true,
      pointerId: e.pointerId,
      startX: e.clientX,
      startValue: sanitizedValue,
      moved: false
    };
    if (e.currentTarget.setPointerCapture) {
      e.currentTarget.setPointerCapture(e.pointerId);
    }
    document.body.style.userSelect = 'none';
    document.body.style.cursor = 'ew-resize';
  };

  const moveScrub = (e) => {
    if (!scrubRef.current.active) return;
    const deltaX = e.clientX - scrubRef.current.startX;
    if (Math.abs(deltaX) >= 2) scrubRef.current.moved = true;
    const multiplier = e.shiftKey ? 0.2 : 1;
    const steppedDelta = (deltaX * multiplier) / step;
    const next = clamp(Math.round((scrubRef.current.startValue + steppedDelta * step) / step) * step);
    onChange(next);
    setTempVal(String(Math.round(next)));
    e.preventDefault();
  };

  const endScrub = (e) => {
    if (!scrubRef.current.active) return;
    const moved = scrubRef.current.moved;
    scrubRef.current.active = false;
    scrubRef.current.pointerId = null;
    document.body.style.userSelect = '';
    document.body.style.cursor = '';

    if (e.currentTarget.hasPointerCapture && e.currentTarget.hasPointerCapture(e.pointerId)) {
      e.currentTarget.releasePointerCapture(e.pointerId);
    }

    if (moved) {
      setFocused(false);
      if (document.activeElement === e.currentTarget) {
        e.currentTarget.blur();
      }
      e.preventDefault();
    }
  };

  return (
    <div className="flex items-center gap-1 bg-sunken rounded-md px-2 focus-within:ring-1 focus-within:ring-edge-strong transition-all overflow-hidden h-8">
      <input
        type="text"
        value={focused ? tempVal : String(Math.round(sanitizedValue))}
        onFocus={() => {
          setFocused(true);
          setTempVal(String(Math.round(sanitizedValue)));
        }}
        onBlur={() => {
          setFocused(false);
          commitValue(tempVal.replace(/[^0-9.-]/g, ''));
        }}
        onChange={(e) => {
          setTempVal(e.target.value);
          const parsed = parseFloat(e.target.value.replace(/[^0-9.-]/g, ''));
          if (!Number.isNaN(parsed)) {
            onChange(clamp(parsed));
          }
        }}
        onPointerDown={startScrub}
        onPointerMove={moveScrub}
        onPointerUp={endScrub}
        onPointerCancel={endScrub}
        className={`flex-1 min-w-0 text-xs text-left bg-transparent border-none outline-none py-1 text-ink font-mono ${focused ? 'cursor-text' : 'cursor-ew-resize'}`}
      />
      {suffix && (
        <span className="shrink-0 text-xs text-secondary font-mono pointer-events-none select-none">
          {suffix}
        </span>
      )}
    </div>
  );
};

export default ScrubbableNumberInput;
