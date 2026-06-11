// CSS cursor class for the canvas, derived from the active tool and any
// in-progress or hovered transform. Scale cursors pick the diagonal that
// matches the handle's visual angle after the object's own rotation; both
// background-object kinds (image, text) carry their rotation on the hit.
export const computeDynamicCursor = ({
  mode,
  isPanning,
  pointAction,
  bgAction,
  bgInitialState,
  bgHoverAction
}) => {
  if (mode === 'pan' || isPanning) return 'cursor-grab active:cursor-grabbing';
  if (mode === 'draw') return 'cursor-pen';
  if (mode === 'pencil') return 'cursor-pencil';
  if (mode === 'shape') return 'cursor-crosshair';
  if (mode === 'text') return 'cursor-text';
  if (mode !== 'edit') return 'cursor-default';

  let act = null;
  let ang = 0;
  let baseRot = 0;

  if (pointAction) {
    act = pointAction.action;
    ang = pointAction.cursorAngle;
  } else if (bgAction) {
    act = bgAction;
    ang = bgInitialState?.cursorAngle;
    baseRot = bgInitialState?.obj?.rotation || 0;
  } else if (bgHoverAction) {
    act = bgHoverAction.action;
    ang = bgHoverAction.cursorAngle;
    if (bgHoverAction.type !== 'point') {
      baseRot = bgHoverAction.rotation || 0;
    }
  }

  if (act) {
    if (act === 'move' || act === 'move-points') return 'cursor-default';
    if (act.startsWith('rotate')) return 'cursor-rotate';
    if (act.startsWith('scale')) {
      let visualAngle = (ang + baseRot) % 180;
      if (visualAngle < 0) visualAngle += 180;
      if (visualAngle > 22.5 && visualAngle <= 112.5) return 'cursor-nwse';
      return 'cursor-nesw';
    }
  }
  return 'cursor-default';
};
