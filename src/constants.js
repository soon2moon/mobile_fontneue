// Legacy content fallbacks — pinned to the original ink color so paths,
// texts, and sessions from before per-object colors keep rendering
// unchanged regardless of theme (phase7c-color.mjs asserts this).
export const DEFAULT_STROKE_WIDTH = 1.5;
export const DEFAULT_STROKE_COLOR = '#344054';
export const DEFAULT_STROKE_ALIGN = 'center';
export const DEFAULT_FILL_COLOR = '#344054';

// Defaults stamped onto NEWLY created content (Figma-style light content
// on the dark canvas). Old sessions keep their own persisted defaults.
export const NEW_SHAPE_FILL_COLOR = '#d9d9d9';
export const NEW_SHAPE_STROKE_COLOR = '#ffffff';
export const NEW_TEXT_FILL_COLOR = '#ffffff';

export const SNAP_RADIUS = 10;
export const GRID_SIZE = 50;
export const MIN_GRID_SIZE = 5;
export const MAX_GRID_SIZE = 200;
export const MIN_CIRCULAR_STEP = 1;
export const MAX_CIRCULAR_STEP = 180;
export const DEFAULT_CIRCULAR_STEP = 30;
export const MIN_ZOOM = 0.1;
export const MAX_ZOOM = 256; // 25600%
export const PIXEL_GRID_MIN_ZOOM = 8; // 800%
export const SESSION_STORAGE_KEY = 'vector-editor-session-v1';
export const LEGACY_SESSION_STORAGE_KEY = 'typolab-session-v1';
export const CLIPBOARD_PAYLOAD_TYPE = 'vector-editor-clipboard';
