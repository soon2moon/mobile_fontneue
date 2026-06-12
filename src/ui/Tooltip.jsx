import { cloneElement, useState } from 'react';
import {
  useFloating,
  autoUpdate,
  offset,
  flip,
  shift,
  useHover,
  useFocus,
  useDismiss,
  useRole,
  useInteractions,
  FloatingPortal
} from '@floating-ui/react';

// Hover/focus tooltip (300 ms open delay) portaled to <body> so it escapes
// overflow-clipped toolbars and stays on-screen via flip/shift. The single
// child element becomes the anchor.
export default function Tooltip({ label, hotkey, children }) {
  const [open, setOpen] = useState(false);
  const { refs, floatingStyles, context } = useFloating({
    open,
    onOpenChange: setOpen,
    placement: 'top',
    whileElementsMounted: autoUpdate,
    middleware: [offset(8), flip({ padding: 8 }), shift({ padding: 8 })]
  });
  const hover = useHover(context, { delay: { open: 300, close: 0 }, move: false });
  const focus = useFocus(context);
  const dismiss = useDismiss(context);
  const role = useRole(context, { role: 'tooltip' });
  const { getReferenceProps, getFloatingProps } = useInteractions([hover, focus, dismiss, role]);

  return (
    <>
      {cloneElement(children, getReferenceProps({ ref: refs.setReference, ...children.props }))}
      {open && (
        <FloatingPortal>
          <div
            ref={refs.setFloating}
            style={{ ...floatingStyles, zIndex: 60 }}
            {...getFloatingProps()}
            className="bg-tooltip text-tooltip-ink text-xs font-medium px-2 py-1 rounded shadow-lg flex items-center gap-2 pointer-events-none whitespace-nowrap"
          >
            <span>{label}</span>
            {hotkey && <span className="text-muted font-mono text-[10px] bg-tooltip-chip px-1 rounded">{hotkey}</span>}
          </div>
        </FloatingPortal>
      )}
    </>
  );
}
