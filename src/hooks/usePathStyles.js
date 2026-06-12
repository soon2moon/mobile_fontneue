import { useState, useEffect } from 'react';
import {
  DEFAULT_STROKE_WIDTH,
  DEFAULT_STROKE_COLOR,
  DEFAULT_STROKE_ALIGN
} from '../constants';
import { getPathStrokeStyle } from '../lib/paths';
import {
  normalizeStrokeWidth,
  normalizeStrokeColor,
  normalizeStrokeAlign
} from '../lib/stroke';

// Stroke/fill styling surface: zoom-compensated render strokes for the
// in-progress path, the selection-aware Stroke panel model (first selected
// path is representative), applyPathStyle (selected paths, or the defaults
// for the next drawn path when nothing is selected), and the text-input
// mirrors for width/color with sanitize-on-type, normalize-on-commit.
export function usePathStyles({
  paths, setPaths,
  currentPath,
  currentPathInfo,
  images,
  texts,
  frames,
  layers,
  selectedPoints,
  commitHistory,
  pathStyleDefaults, setPathStyleDefaults,
  zoom
}) {
  const [strokeWidthInput, setStrokeWidthInput] = useState(String(DEFAULT_STROKE_WIDTH));
  const [strokeColorInput, setStrokeColorInput] = useState(DEFAULT_STROKE_COLOR.replace('#', ''));

  const strokeWidth = 1.5 / zoom;
  const defaultStrokeEnabled = pathStyleDefaults.strokeEnabled !== false;
  const defaultStrokeRenderWidth = normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH) / zoom;
  const defaultStrokeRenderColor = normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR);
  const livePathStroke = currentPathInfo
    ? {
        strokeEnabled: currentPathInfo.strokeEnabled !== false,
        strokeWidth: normalizeStrokeWidth(currentPathInfo.strokeWidth, normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH)),
        strokeColor: normalizeStrokeColor(currentPathInfo.strokeColor, normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR))
      }
    : {
        strokeEnabled: defaultStrokeEnabled,
        strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
        strokeColor: defaultStrokeRenderColor
      };
  const livePathStrokeRenderWidth = livePathStroke.strokeWidth / zoom;

  const selectedPathIndices = [...new Set(selectedPoints.map(sp => sp.pathIndex))]
    .filter(idx => idx >= 0 && idx < paths.length);
  const selectedPathObjects = selectedPathIndices.map(idx => paths[idx]).filter(Boolean);
  const hasSelectedPaths = selectedPathObjects.length > 0;
  const fillToggleActive = hasSelectedPaths
    ? selectedPathObjects.every(path => !!path.fillEnabled)
    : pathStyleDefaults.fillEnabled;
  const strokeToggleActive = hasSelectedPaths
    ? selectedPathObjects.every(path => path.strokeEnabled !== false)
    : pathStyleDefaults.strokeEnabled;
  const representativePathStroke = hasSelectedPaths
    ? getPathStrokeStyle(selectedPathObjects[0])
    : null;
  const strokePanelStyle = representativePathStroke || {
    strokeEnabled: pathStyleDefaults.strokeEnabled !== false,
    strokeWidth: normalizeStrokeWidth(pathStyleDefaults.strokeWidth, DEFAULT_STROKE_WIDTH),
    strokeColor: normalizeStrokeColor(pathStyleDefaults.strokeColor, DEFAULT_STROKE_COLOR),
    strokeAlign: normalizeStrokeAlign(pathStyleDefaults.strokeAlign, DEFAULT_STROKE_ALIGN)
  };

  const applyPathStyle = (updates, { transient = false } = {}) => {
    const normalizedUpdates = { ...updates };
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'strokeWidth')) {
      normalizedUpdates.strokeWidth = normalizeStrokeWidth(normalizedUpdates.strokeWidth, pathStyleDefaults.strokeWidth);
    }
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'strokeColor')) {
      normalizedUpdates.strokeColor = normalizeStrokeColor(normalizedUpdates.strokeColor, pathStyleDefaults.strokeColor);
    }
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'strokeAlign')) {
      normalizedUpdates.strokeAlign = normalizeStrokeAlign(normalizedUpdates.strokeAlign, pathStyleDefaults.strokeAlign);
    }
    if (Object.prototype.hasOwnProperty.call(normalizedUpdates, 'fillColor')) {
      normalizedUpdates.fillColor = normalizeStrokeColor(normalizedUpdates.fillColor, pathStyleDefaults.fillColor);
    }

    if (hasSelectedPaths) {
      if (!transient) {
        commitHistory({ paths, currentPath, images, layers, texts, frames });
      }
      const selectedSet = new Set(selectedPathIndices);
      setPaths(prev => prev.map((path, idx) => (
        selectedSet.has(idx) ? { ...path, ...normalizedUpdates } : path
      )));
      return;
    }
    setPathStyleDefaults(prev => ({ ...prev, ...normalizedUpdates }));
  };

  useEffect(() => {
    setStrokeWidthInput(String(Number(strokePanelStyle.strokeWidth.toFixed(2))));
    setStrokeColorInput(strokePanelStyle.strokeColor.replace('#', ''));
  }, [strokePanelStyle.strokeWidth, strokePanelStyle.strokeColor]);

  const commitStrokeWidthInput = () => {
    const parsedWidth = normalizeStrokeWidth(strokeWidthInput, strokePanelStyle.strokeWidth);
    setStrokeWidthInput(String(Number(parsedWidth.toFixed(2))));
    applyPathStyle({ strokeWidth: parsedWidth, strokeEnabled: true });
  };

  const handleStrokeWidthInputChange = (value) => {
    const sanitized = value.replace(/[^0-9.]/g, '');
    setStrokeWidthInput(sanitized);
  };

  const commitStrokeColorInput = () => {
    const normalized = normalizeStrokeColor(`#${strokeColorInput}`, strokePanelStyle.strokeColor);
    setStrokeColorInput(normalized.replace('#', ''));
    applyPathStyle({ strokeColor: normalized, strokeEnabled: true });
  };

  const handleStrokeColorInputChange = (value) => {
    const sanitized = value.replace(/[^0-9a-fA-F]/g, '').slice(0, 6).toLowerCase();
    setStrokeColorInput(sanitized);
  };

  return {
    strokeWidth,
    defaultStrokeEnabled,
    defaultStrokeRenderWidth,
    defaultStrokeRenderColor,
    livePathStroke,
    livePathStrokeRenderWidth,
    hasSelectedPaths,
    selectedPathObjects,
    fillToggleActive,
    strokeToggleActive,
    strokePanelStyle,
    applyPathStyle,
    strokeWidthInput,
    strokeColorInput, setStrokeColorInput,
    commitStrokeWidthInput,
    handleStrokeWidthInputChange,
    commitStrokeColorInput,
    handleStrokeColorInputChange
  };
}
