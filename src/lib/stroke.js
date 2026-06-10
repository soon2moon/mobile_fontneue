import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN
} from '../constants';

export const normalizeStrokeWidth = (value, fallback = DEFAULT_STROKE_WIDTH) => {
  const parsed = Number.parseFloat(value);
  if (!Number.isFinite(parsed)) return fallback;
  return Math.max(0, parsed);
};

export const normalizeStrokeColor = (value, fallback = DEFAULT_STROKE_COLOR) => {
  if (typeof value !== 'string') return fallback;
  const trimmed = value.trim();
  if (!trimmed) return fallback;
  const withHash = trimmed.startsWith('#') ? trimmed : `#${trimmed}`;
  return /^#[0-9a-fA-F]{6}$/.test(withHash) ? withHash.toLowerCase() : fallback;
};

export const normalizeStrokeAlign = (value, fallback = DEFAULT_STROKE_ALIGN) => {
  if (value === 'inside' || value === 'outside' || value === 'center') return value;
  return fallback;
};
