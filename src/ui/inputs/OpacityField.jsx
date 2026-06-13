import { useState, useEffect } from 'react';

// Inline opacity (0–100%) cluster designed to sit INSIDE an existing input
// pill, after the hex field: a thin divider + a right-aligned % field. `value`
// is a 0–1 fraction; onCommit receives a 0–1 fraction. Shows blank for a mixed
// (indeterminate) selection until focused.
export default function OpacityField({ value, indeterminate = false, onCommit, title = 'Opacity' }) {
  const toPct = (v) => String(Math.round(Math.max(0, Math.min(1, Number(v) || 0)) * 100));
  const [draft, setDraft] = useState(toPct(value));
  const [focused, setFocused] = useState(false);

  useEffect(() => {
    if (!focused) setDraft(toPct(value));
  }, [value, focused]);

  const commit = () => {
    const parsed = parseInt(draft, 10);
    const pct = Number.isFinite(parsed)
      ? Math.max(0, Math.min(100, parsed))
      : Math.round((Number(value) || 0) * 100);
    setDraft(String(pct));
    onCommit(pct / 100);
  };

  return (
    <>
      <span className="w-px self-stretch my-1.5 bg-edge shrink-0" />
      <input
        type="text"
        value={focused ? draft : (indeterminate ? '' : draft)}
        onChange={(e) => setDraft(e.target.value.replace(/[^0-9]/g, '').slice(0, 3))}
        onFocus={() => setFocused(true)}
        onBlur={() => { setFocused(false); commit(); }}
        onKeyDown={(e) => {
          if (e.key === 'Enter') {
            e.preventDefault();
            commit();
            e.currentTarget.blur();
          }
        }}
        className="w-7 text-xs text-right bg-transparent border-none outline-none py-1 text-ink font-mono shrink-0"
        placeholder={indeterminate ? '–' : '100'}
        title={title}
      />
      <span className="text-xs text-secondary font-mono select-none shrink-0">%</span>
    </>
  );
}
