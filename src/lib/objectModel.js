import { NEW_TEXT_FILL_COLOR } from '../constants';
import { normalizeStrokeColor } from './stroke';

export const MIN_FONT_SIZE = 1;

export const DEFAULT_TEXT_STYLE = {
  fontSize: 96,
  fontFamily: 'Arial, sans-serif',
  fontWeight: 400,
  textAlign: 'left',
  lineHeight: 1.14,
  fill: NEW_TEXT_FILL_COLOR,
  opacity: 1
};

const TEXT_ALIGNS = ['left', 'center', 'right'];

// Live text object factory. x/y is the world-space CENTER of the text block
// (same anchor convention as images) so both share the transform pipeline.
export const createTextObject = ({ x, y, content, layerId, style = {} }) => ({
  id: crypto.randomUUID(),
  layerId: layerId ?? null,
  x,
  y,
  content: typeof content === 'string' ? content : '',
  fontSize: Math.max(MIN_FONT_SIZE, Number(style.fontSize) || DEFAULT_TEXT_STYLE.fontSize),
  fontFamily: typeof style.fontFamily === 'string' && style.fontFamily ? style.fontFamily : DEFAULT_TEXT_STYLE.fontFamily,
  fontWeight: Number.isFinite(Number(style.fontWeight)) ? Number(style.fontWeight) : DEFAULT_TEXT_STYLE.fontWeight,
  textAlign: TEXT_ALIGNS.includes(style.textAlign) ? style.textAlign : DEFAULT_TEXT_STYLE.textAlign,
  lineHeight: Number(style.lineHeight) > 0 ? Number(style.lineHeight) : DEFAULT_TEXT_STYLE.lineHeight,
  fill: normalizeStrokeColor(style.fill, DEFAULT_TEXT_STYLE.fill),
  opacity: Number.isFinite(Number(style.opacity)) ? Math.max(0, Math.min(1, Number(style.opacity))) : DEFAULT_TEXT_STYLE.opacity,
  rotation: 0,
  locked: false
});

export const MIN_FRAME_SIZE = 1;
export const DEFAULT_FRAME_FILL = '#ffffff';

// Frame (artboard/board) factory. x/y is the world-space CENTER (image/text
// anchor convention); frames never rotate and paint below all content.
export const createFrameObject = ({ x, y, width, height, name, layerId, fill }) => ({
  id: crypto.randomUUID(),
  layerId: layerId ?? null,
  name: typeof name === 'string' && name ? name : 'Frame',
  x,
  y,
  width: Math.max(MIN_FRAME_SIZE, Number(width) || MIN_FRAME_SIZE),
  height: Math.max(MIN_FRAME_SIZE, Number(height) || MIN_FRAME_SIZE),
  fill: normalizeStrokeColor(fill, DEFAULT_FRAME_FILL),
  rotation: 0,
  locked: false
});

// Defensive re-validation for frames arriving from persisted sessions.
// Returns null when the record is unusable.
export const normalizeFrameObject = (raw) => {
  if (!raw || typeof raw !== 'object') return null;
  const x = Number(raw.x);
  const y = Number(raw.y);
  const width = Number(raw.width);
  const height = Number(raw.height);
  if (!Number.isFinite(x) || !Number.isFinite(y)) return null;
  if (!Number.isFinite(width) || !Number.isFinite(height)) return null;

  const normalized = createFrameObject({
    x,
    y,
    width,
    height,
    name: raw.name,
    layerId: typeof raw.layerId === 'string' ? raw.layerId : null,
    fill: raw.fill
  });
  return {
    ...normalized,
    id: typeof raw.id === 'string' || Number.isFinite(raw.id) ? raw.id : normalized.id,
    locked: raw.locked === true
  };
};

// Defensive re-validation for text objects arriving from persisted sessions
// or clipboard payloads. Returns null when the record is unusable.
export const normalizeTextObject = (raw) => {
  if (!raw || typeof raw !== 'object') return null;
  const x = Number(raw.x);
  const y = Number(raw.y);
  if (!Number.isFinite(x) || !Number.isFinite(y)) return null;
  if (typeof raw.content !== 'string' || raw.content.length === 0) return null;

  const normalized = createTextObject({
    x,
    y,
    content: raw.content,
    layerId: typeof raw.layerId === 'string' ? raw.layerId : null,
    style: raw
  });
  return {
    ...normalized,
    id: typeof raw.id === 'string' || Number.isFinite(raw.id) ? raw.id : normalized.id,
    rotation: Number.isFinite(Number(raw.rotation)) ? Number(raw.rotation) : 0,
    locked: raw.locked === true
  };
};
