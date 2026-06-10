import { useState, useCallback } from 'react';
import {
  collectExportItems,
  buildExportSvgBundle,
  downloadBlob,
  rasterizeAndDownloadBundle
} from '../lib/export';

// Export pipeline state: scope (selection/canvas) + format choice, and the
// download action (SVG directly, PNG/JPG via offscreen rasterization).
export function useExport({ layers, paths, images, selectedPoints, selectedImageIds }) {
  const [exportScope, setExportScope] = useState('selection');
  const [exportFormat, setExportFormat] = useState('png');
  const [isExporting, setIsExporting] = useState(false);

  const handleExport = useCallback(async () => {
    if (isExporting) return;
    const items = collectExportItems(exportScope, { layers, paths, images, selectedPoints, selectedImageIds });
    const bundle = buildExportSvgBundle(items);
    if (!bundle) return;

    setIsExporting(true);
    try {
      const baseName = exportScope === 'selection' ? 'selection' : 'canvas';
      if (exportFormat === 'svg') {
        downloadBlob(new Blob([bundle.svg], { type: 'image/svg+xml;charset=utf-8' }), `${baseName}.svg`);
        return;
      }
      await rasterizeAndDownloadBundle(bundle, exportFormat, baseName);
    } finally {
      setIsExporting(false);
    }
  }, [isExporting, exportScope, exportFormat, layers, paths, images, selectedPoints, selectedImageIds]);

  return {
    exportScope, setExportScope,
    exportFormat, setExportFormat,
    isExporting,
    handleExport
  };
}
