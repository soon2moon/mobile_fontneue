import { useLayoutEffect } from 'react';
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
// overflow-hidden ancestors.
export default function Popover({
  open,
  onOpenChange,
  anchorRef,
  virtualAnchor,
  placement = 'bottom-start',
  offsetPx = 6,
  children
}) {
  const { refs, floatingStyles, context } = useFloating({
    open,
    onOpenChange,
    placement,
    whileElementsMounted: autoUpdate,
    middleware: [offset(offsetPx), flip({ padding: 8 }), shift({ padding: 8 })]
  });

  const dismiss = useDismiss(context);
  const { getFloatingProps } = useInteractions([dismiss]);

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
      refs.setPositionReference(anchorRef.current);
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
