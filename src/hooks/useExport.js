import { useState, useCallback } from 'react';
import {
  collectExportItems,
  buildExportSvgBundle,
  downloadBlob,
  rasterizeAndDownloadBundle
} from '../lib/export';

// Export pipeline state: scope (selection/canvas) + format choice, and the
// download action (SVG directly, PNG/JPG via offscreen rasterization).
const slugifyName = (name) => (name || 'frame').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '') || 'frame';

export function useExport({ layers, paths, images, texts, frames = [], selectedPoints, selectedImageIds, selectedTextIds, selectedFrameIds = [] }) {
  const [exportScope, setExportScope] = useState('selection');
  const [exportFormat, setExportFormat] = useState('png');
  const [isExporting, setIsExporting] = useState(false);

  const handleExport = useCallback(async () => {
    if (isExporting) return;

    let bundle;
    let baseName;
    if (exportScope === 'frame') {
      const frame = frames.find(f => selectedFrameIds.includes(f.id));
      if (!frame) return;
      const items = collectExportItems('canvas', { layers, paths, images, texts, selectedPoints, selectedImageIds, selectedTextIds });
      bundle = buildExportSvgBundle({
        ...items,
        layers,
        bounds: {
          minX: frame.x - frame.width / 2,
          minY: frame.y - frame.height / 2,
          maxX: frame.x + frame.width / 2,
          maxY: frame.y + frame.height / 2
        },
        background: frame.fill
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
  }, [isExporting, exportScope, exportFormat, layers, paths, images, texts, frames, selectedPoints, selectedImageIds, selectedTextIds, selectedFrameIds]);

  return {
    exportScope, setExportScope,
    exportFormat, setExportFormat,
    isExporting,
    handleExport
  };
}
