import { useLayoutEffect, useEffect, useRef } from 'react';
import {
  useFloating,
  autoUpdate,
  offset,
  flip,
  shift,
  useDismiss,
  useInteractions,
  FloatingPortal
} from '@floating-ui/react';

// Positioned floating container: anchored to a DOM ref or a virtual
// client-coordinate point, kept on-screen by flip/shift, dismissed on
// outside press or Escape, and portaled to <body> so it escapes any
// overflow-hidden ancestors. Escape is consumed during window capture so
// closing a popover never also reaches the app's global Escape handling;
// guardOutsidePressMs ignores presses right after opening — the touch
// long-press "compatibility click" fired on finger lift would otherwise
// dismiss a menu the moment it opened.
export default function Popover({
  open,
  onOpenChange,
  anchorRef,
  virtualAnchor,
  placement = 'bottom-start',
  offsetPx = 6,
  guardOutsidePressMs = 0,
  children
}) {
  const openedAtRef = useRef(0);

  useEffect(() => {
    if (open) openedAtRef.current = Date.now();
  }, [open]);

  const { refs, floatingStyles, context } = useFloating({
    open,
    onOpenChange,
    placement,
    whileElementsMounted: autoUpdate,
    middleware: [offset(offsetPx), flip({ padding: 8 }), shift({ padding: 8 })]
  });

  const dismiss = useDismiss(context, {
    escapeKey: false,
    outsidePress: () => Date.now() - openedAtRef.current >= guardOutsidePressMs
  });
  const { getFloatingProps } = useInteractions([dismiss]);

  useEffect(() => {
    if (!open) return;
    const consumeEscape = (e) => {
      if (e.key !== 'Escape') return;
      e.stopPropagation();
      onOpenChange(false);
    };
    window.addEventListener('keydown', consumeEscape, true);
    return () => window.removeEventListener('keydown', consumeEscape, true);
  }, [open, onOpenChange]);

  useLayoutEffect(() => {
    if (virtualAnchor) {
      refs.setPositionReference({
        getBoundingClientRect: () => ({
          x: virtualAnchor.x,
          y: virtualAnchor.y,
          width: 0,
          height: 0,
          top: virtualAnchor.y,
          bottom: virtualAnchor.y,
          left: virtualAnchor.x,
          right: virtualAnchor.x
        })
      });
    } else if (anchorRef?.current) {
      // Full DOM reference (not just a position reference) so useDismiss
      // counts presses on the anchor as inside — otherwise the anchor's own
      // toggle would dismiss-on-pointerdown and reopen on the click.
      refs.setReference(anchorRef.current);
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [refs, anchorRef, virtualAnchor?.x, virtualAnchor?.y, open]);

  if (!open) return null;

  return (
    <FloatingPortal>
      <div
        ref={refs.setFloating}
        style={{ ...floatingStyles, zIndex: 60 }}
        {...getFloatingProps()}
      >
        {children}
      </div>
    </FloatingPortal>
  );
}
