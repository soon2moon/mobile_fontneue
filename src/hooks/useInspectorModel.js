import { getPathStrokeStyle } from '../lib/paths';
import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN
} from '../constants';
import {
  normalizeStrokeWidth,
  normalizeStrokeColor,
  normalizeStrokeAlign
} from '../lib/stroke';

// Selection-aware model behind the unified Inspector panel: resolves what
// kind of thing is selected, aggregates path styles (with per-field
// indeterminate flags across the WHOLE path selection), and routes edits to
// the right writer (paths/defaults via applyPathStyle, image/text via their
// updaters). applyTransient is the no-history variant for continuous
// gestures (color picker drags, 7C).
export function useInspectorModel({
  selectedPathObjects,
  selectedImageIds,
  selectedTextIds,
  pathStyleDefaults,
  applyPathStyle,
  activeImage,
  updateActiveImage,
  activeText,
  updateActiveText
}) {
  const hasPaths = selectedPathObjects.length > 0;
  const hasImages = selectedImageIds.length > 0;
  const hasTexts = selectedTextIds.length > 0;
  const selectedKindCount = (hasPaths ? 1 : 0) + (hasImages ? 1 : 0) + (hasTexts ? 1 : 0);

  const kind = selectedKindCount > 1
    ? 'mixed'
    : hasImages
      ? 'image'
      : hasTexts
        ? 'text'
        : hasPaths
          ? 'paths'
          : 'none';

  const distinct = (values) => new Set(values).size > 1;
  const strokeStyles = selectedPathObjects.map(path => getPathStrokeStyle(path, pathStyleDefaults));
  const representative = strokeStyles[0] || {
    strokeEnabled: pathStyleDefaults.strokeEnabled !== false,
    strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
    strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
    strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN)
  };

  // Path fill/stroke apply to the path selection (or the defaults for the
  // next drawn path); both are shown for 'paths', 'none', and 'mixed' (where
  // they affect the selected paths only).
  const showsPathStyle = kind === 'paths' || kind === 'none' || (kind === 'mixed' && hasPaths);

  const fill = showsPathStyle
    ? {
        enabled: hasPaths
          ? selectedPathObjects.every(path => !!path.fillEnabled)
          : !!pathStyleDefaults.fillEnabled,
        indeterminate: hasPaths && distinct(selectedPathObjects.map(path => !!path.fillEnabled))
      }
    : null;

  const stroke = showsPathStyle
    ? {
        enabled: hasPaths
          ? selectedPathObjects.every(path => path.strokeEnabled !== false)
          : pathStyleDefaults.strokeEnabled !== false,
        width: representative.strokeWidth,
        color: representative.strokeColor,
        align: representative.strokeAlign,
        indeterminate: {
          enabled: hasPaths && distinct(selectedPathObjects.map(path => path.strokeEnabled !== false)),
          width: hasPaths && distinct(strokeStyles.map(style => style.strokeWidth)),
          color: hasPaths && distinct(strokeStyles.map(style => style.strokeColor)),
          align: hasPaths && distinct(strokeStyles.map(style => style.strokeAlign))
        }
      }
    : null;

  const transform = kind === 'image' && activeImage
    ? {
        x: activeImage.x,
        y: activeImage.y,
        scale: activeImage.scale,
        rotation: activeImage.rotation,
        opacity: activeImage.opacity,
        locked: !!activeImage.locked
      }
    : kind === 'text' && activeText
      ? {
          x: activeText.x,
          y: activeText.y,
          scale: null,
          rotation: activeText.rotation,
          opacity: activeText.opacity,
          locked: !!activeText.locked
        }
      : null;

  const text = kind === 'text' && activeText
    ? { fontSize: activeText.fontSize, fill: activeText.fill }
    : null;

  const apply = (patch) => {
    if (kind === 'image') {
      updateActiveImage(patch);
      return;
    }
    if (kind === 'text') {
      updateActiveText(patch);
      return;
    }
    applyPathStyle(patch);
  };

  const applyTransient = (patch) => {
    if (kind === 'image') {
      updateActiveImage(patch);
      return;
    }
    if (kind === 'text') {
      updateActiveText(patch);
      return;
    }
    applyPathStyle(patch, { transient: true });
  };

  return { kind, fill, stroke, transform, text, apply, applyTransient };
}
