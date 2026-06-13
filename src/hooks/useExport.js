import { useState, useCallback } from 'react';
import {
  collectExportItems,
  buildExportSvgBundle,
  downloadBlob,
  rasterizeAndDownloadBundle
} from '../lib/export';
import { collectFrameChildren } from '../lib/hitTest';

// Export pipeline state: scope (selection/canvas) + format choice, and the
// download action (SVG directly, PNG/JPG via offscreen rasterization).
const slugifyName = (name) => (name || 'frame').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '') || 'frame';

export function useExport({ layers, paths, images, texts, frames = [], selectedPoints, selectedImageIds, selectedTextIds, selectedFrameIds = [] }) {
  const [exportScope, setExportScope] = useState('selection');
  const [exportFormat, setExportFormat] = useState('png');
  const [frameTransparent, setFrameTransparent] = useState(false);
  const [isExporting, setIsExporting] = useState(false);

  const handleExport = useCallback(async () => {
    if (isExporting) return;

    let bundle;
    let baseName;
    if (exportScope === 'frame') {
      const frame = frames.find(f => selectedFrameIds.includes(f.id));
      if (!frame) return;
      // A frame exports its children — the objects whose center is inside it —
      // cropped to the frame rect, with the frame fill (or transparent) behind.
      const { childImages, childTexts, childPaths } = collectFrameChildren(frame, { paths, images, texts, layers });
      bundle = buildExportSvgBundle({
        exportPaths: childPaths,
        exportImages: childImages,
        exportTexts: childTexts,
        layers,
        bounds: {
          minX: frame.x - frame.width / 2,
          minY: frame.y - frame.height / 2,
          maxX: frame.x + frame.width / 2,
          maxY: frame.y + frame.height / 2
        },
        background: frameTransparent ? null : frame.fill
      });
      baseName = slugifyName(frame.name);
    } else {
      const items = collectExportItems(exportScope, { layers, paths, images, texts, selectedPoints, selectedImageIds, selectedTextIds });
      bundle = buildExportSvgBundle({ ...items, layers });
      baseName = exportScope === 'selection' ? 'selection' : 'canvas';
    }
    if (!bundle) return;

    setIsExporting(true);
    try {
      if (exportFormat === 'svg') {
        downloadBlob(new Blob([bundle.svg], { type: 'image/svg+xml;charset=utf-8' }), `${baseName}.svg`);
        return;
      }
      await rasterizeAndDownloadBundle(bundle, exportFormat, baseName);
    } finally {
      setIsExporting(false);
    }
  }, [isExporting, exportScope, exportFormat, frameTransparent, layers, paths, images, texts, frames, selectedPoints, selectedImageIds, selectedTextIds, selectedFrameIds]);

  return {
    exportScope, setExportScope,
    exportFormat, setExportFormat,
    frameTransparent, setFrameTransparent,
    isExporting,
    handleExport
  };
}
