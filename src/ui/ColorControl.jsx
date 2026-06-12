import { useState, useRef, useEffect } from 'react';
import { HexColorPicker } from 'react-colorful';
import Popover from './Popover';
import { normalizeStrokeColor } from '../lib/stroke';

const RECENT_COLORS_KEY = 'vector-editor-recent-colors';
const RECENT_COLORS_CAP = 8;
const PRESET_COLORS = ['#ffffff', '#d9d9d9', '#757575', '#1e1e1e', '#f24822', '#ffcd29', '#14ae5c', '#0d99ff'];

const readRecentColors = () => {
  try {
    const raw = localStorage.getItem(RECENT_COLORS_KEY);
    const parsed = raw ? JSON.parse(raw) : [];
    return Array.isArray(parsed) ? parsed.filter(c => typeof c === 'string') : [];
  } catch {
    return [];
  }
};

// Swatch chip that opens a color popover (picker + hex field + recent and
// preset swatches). History granularity: the FIRST picker change of each
// pointer gesture goes through onChange (one undo entry); the rest of the
// drag streams through onChangeTransient. Discrete actions (hex commit,
// swatch taps) are single onChange commits.
export default function ColorControl({
  value,
  onChange,
  onChangeTransient,
  label = 'Color',
  disabled = false,
  showIndeterminate = false
}) {
  const [open, setOpen] = useState(false);
  const [hexDraft, setHexDraft] = useState(value.replace('#', ''));
  const [recentColors, setRecentColors] = useState(readRecentColors);
  const chipRef = useRef(null);
  const gestureCommittedRef = useRef(false);
  const openedValueRef = useRef(value);

  useEffect(() => {
    setHexDraft(value.replace('#', ''));
  }, [value]);

  // Reset the once-per-gesture commit flag when a NEW pointer gesture begins
  // (capture phase, so it precedes the picker's own handlers). Resetting on
  // pointerup instead would race react-colorful's document-level pointerup
  // listener, which emits one final onChange after the pointer lifts.
  useEffect(() => {
    if (!open) return;
    const beginGesture = () => { gestureCommittedRef.current = false; };
    window.addEventListener('pointerdown', beginGesture, true);
    return () => window.removeEventListener('pointerdown', beginGesture, true);
  }, [open]);

  const pushRecentColor = (color) => {
    setRecentColors(prev => {
      const next = [color, ...prev.filter(c => c !== color)].slice(0, RECENT_COLORS_CAP);
      try {
        localStorage.setItem(RECENT_COLORS_KEY, JSON.stringify(next));
      } catch {
        // Persisting recents is best-effort.
      }
      return next;
    });
  };

  const handleOpenChange = (next) => {
    setOpen(next);
    if (next) {
      openedValueRef.current = value;
      gestureCommittedRef.current = false;
    } else if (value !== openedValueRef.current) {
      pushRecentColor(value);
    }
  };

  const handlePickerChange = (color) => {
    const normalized = normalizeStrokeColor(color, value);
    if (!gestureCommittedRef.current) {
      gestureCommittedRef.current = true;
      onChange(normalized);
    } else if (onChangeTransient) {
      onChangeTransient(normalized);
    } else {
      onChange(normalized);
    }
  };

  const commitHexDraft = () => {
    const normalized = normalizeStrokeColor(`#${hexDraft}`, value);
    setHexDraft(normalized.replace('#', ''));
    if (normalized !== value) {
      onChange(normalized);
    }
  };

  const swatchRow = (colors, prefix) => (
    <div className="grid grid-cols-8 gap-1">
      {colors.map((color, index) => (
        <button
          key={`${prefix}-${index}`}
          onClick={() => onChange(color)}
          className="h-4 w-4 rounded border border-edge-strong"
          style={{ background: color }}
          title={color}
        />
      ))}
    </div>
  );

  return (
    <>
      <button
        ref={chipRef}
        disabled={disabled}
        onClick={() => handleOpenChange(!open)}
        className={`h-5 w-5 p-0 border border-edge-strong rounded shrink-0 ${disabled ? 'opacity-40 cursor-default' : 'cursor-pointer'}`}
        style={{
          background: showIndeterminate
            ? 'linear-gradient(135deg, #ffffff 0 45%, #d0d5dd 45% 55%, #ffffff 55% 100%)'
            : value
        }}
        title={label}
      />
      <Popover open={open} onOpenChange={handleOpenChange} anchorRef={chipRef} placement="bottom-start" offsetPx={8}>
        <div className="bg-raised border border-edge rounded-xl shadow-popover p-2.5 flex flex-col gap-2 w-[216px]">
          <HexColorPicker color={value} onChange={handlePickerChange} style={{ width: '100%', height: 140 }} />
          <div className="h-8 flex items-center gap-2 bg-sunken rounded-md px-2 focus-within:ring-1 focus-within:ring-edge-strong transition-all">
            <span className="text-xs text-secondary font-mono select-none">#</span>
            <input
              type="text"
              value={hexDraft}
              onChange={(e) => setHexDraft(e.target.value.replace(/[^0-9a-fA-F]/g, '').slice(0, 6).toLowerCase())}
              onBlur={commitHexDraft}
              onKeyDown={(e) => {
                if (e.key === 'Enter') {
                  e.preventDefault();
                  commitHexDraft();
                  e.currentTarget.blur();
                }
              }}
              className="flex-1 min-w-0 text-xs text-left bg-transparent border-none outline-none py-1 text-ink font-mono uppercase"
              maxLength={6}
              title={`${label} (Hex)`}
            />
          </div>
          {recentColors.length > 0 && (
            <div className="flex flex-col gap-1">
              <span className="text-[10px] font-bold text-secondary uppercase tracking-widest px-0.5">Recent</span>
              {swatchRow(recentColors, 'recent')}
            </div>
          )}
          <div className="flex flex-col gap-1">
            <span className="text-[10px] font-bold text-secondary uppercase tracking-widest px-0.5">Presets</span>
            {swatchRow(PRESET_COLORS, 'preset')}
          </div>
        </div>
      </Popover>
    </>
  );
}
