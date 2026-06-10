import { useState, useEffect } from 'react';

const ConfigInput = ({ icon, label, value, onChange, suffix = "", scaleFactor = 1, ...props }) => {
  const displayValue = Number((value * scaleFactor).toFixed(2));
  const [focused, setFocused] = useState(false);
  const [tempVal, setTempVal] = useState(displayValue.toString());

  useEffect(() => {
    if (!focused) setTempVal(displayValue.toString());
  }, [displayValue, focused]);

  return (
    <div className="flex items-center bg-[#f2f4f7] rounded-md px-2 focus-within:ring-1 focus-within:ring-[#d0d5dd] transition-all overflow-hidden h-8 gap-2">
      {icon ? (
        <span className="flex items-center justify-center text-[#98a2b3] w-3.5 shrink-0">
          {icon}
        </span>
      ) : label ? (
        <span className="text-xs font-medium text-[#98a2b3] w-3.5 shrink-0 select-none flex items-center justify-center">
          {label}
        </span>
      ) : null}
      <input
        type="text"
        value={focused ? tempVal : `${tempVal}${suffix}`}
        onFocus={() => {
           setFocused(true);
           setTempVal(displayValue.toString());
        }}
        onBlur={() => {
           setFocused(false);
           let parsed = parseFloat(tempVal.replace(/[^0-9.-]/g, ''));
           if (isNaN(parsed)) parsed = 0;
           onChange(parsed / scaleFactor);
           setTempVal(parsed.toString());
        }}
        onChange={e => {
           setTempVal(e.target.value);
           let parsed = parseFloat(e.target.value.replace(/[^0-9.-]/g, ''));
           if (!isNaN(parsed)) {
             onChange(parsed / scaleFactor);
           }
        }}
        className="w-full text-xs text-left bg-transparent border-none outline-none py-1 text-[#344054] font-mono"
        {...props}
      />
    </div>
  );
};

export default ConfigInput;
