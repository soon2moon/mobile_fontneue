import { Layers, ChevronUp } from 'lucide-react';
import LayerIcon from '../../ui/LayerIcon';
import { useEditor } from '../../state/EditorContext';
import { getPathStrokeStyle, getPathFillStyle, pointsToPath } from '../../lib/paths';
import TextObject from '../Canvas/TextObject';

// Floating "Quick Layer Reorder" sheet shown while multiple layers are
// selected and the Layers panel is closed.
export default function QuickLayerReorder() {
  const {
activeLayerId,
    anyMobileOverlayOpen,
    getLayerPreviewBounds,
    imageCountByLayerId,
    imagesByLayerId,
    isMobile,
    layerIndexById,
    layers,
    moveSelectedLayerQuick,
    openPanels,
    pathCountByLayerId,
    pathStyleDefaults,
    pathsByLayerId,
    selectedLayersInStackOrder,
    setActiveLayerId,
    textCountByLayerId,
    textsByLayerId
  } = useEditor();

  return (
    <>
      {selectedLayersInStackOrder.length > 1 && !openPanels.layers && (!isMobile || !anyMobileOverlayOpen) && (
        <div
          className={`absolute z-[24] pointer-events-none ${
            isMobile ? 'left-2 right-2' : 'top-7 left-1/2 -translate-x-1/2'
          }`}
          style={isMobile ? { top: 'calc(env(safe-area-inset-top, 0px) + 56px)' } : undefined}
        >
          <div className="pointer-events-auto w-full overflow-hidden rounded-2xl border border-[#e4e7ec] bg-[#f8fafc] shadow-[0_14px_32px_rgba(52,64,84,0.16)]">
            <div className="flex items-center justify-between px-3 py-2 border-b border-[#e4e7ec] bg-[#f2f4f7]">
              <div className="flex items-center gap-2 text-[10px] font-bold uppercase tracking-widest text-[#667085]">
                <Layers size={13} />
                Quick Layer Reorder
              </div>
              <span className="text-[10px] font-semibold text-[#98a2b3]">
                {selectedLayersInStackOrder.length} selected
              </span>
            </div>
            <div className="p-2 max-h-[32vh] overflow-y-auto flex flex-col gap-1" style={{ touchAction: 'pan-y' }}>
              {selectedLayersInStackOrder.map(layer => {
                const layerIndex = layerIndexById.get(layer.id) ?? -1;
                const canMoveUp = layerIndex > 0;
                const canMoveDown = layerIndex >= 0 && layerIndex < layers.length - 1;
                const instanceCount = (pathCountByLayerId[layer.id] || 0) + (imageCountByLayerId[layer.id] || 0) + (textCountByLayerId[layer.id] || 0);
                const isActive = activeLayerId === layer.id;
                const layerPaths = pathsByLayerId[layer.id] || [];
                const layerImages = imagesByLayerId[layer.id] || [];
                const layerTexts = textsByLayerId[layer.id] || [];
                const previewBounds = getLayerPreviewBounds(layerPaths, layerImages, layerTexts);

                return (
                  <div
                    key={`quick-layer-${layer.id}`}
                    className={`flex items-center gap-2 rounded-xl border p-1.5 transition-colors ${
                      isActive
                        ? 'bg-[#eaecf0] border-[#d0d5dd]'
                        : 'bg-[#f8fafc] border-[#e4e7ec]'
                    }`}
                  >
                    <button
                      type="button"
                      onClick={() => setActiveLayerId(layer.id)}
                      className="flex items-center gap-2 min-w-0 flex-1 text-left rounded-md px-1 py-1 hover:bg-[#f2f4f7] transition-colors"
                    >
                      <div className="w-14 h-9 shrink-0 overflow-hidden rounded-md border border-[#d0d5dd] bg-white flex items-center justify-center">
                        {previewBounds ? (
                          <svg
                            className="w-full h-full"
                            viewBox={`${previewBounds.minX} ${previewBounds.minY} ${previewBounds.width} ${previewBounds.height}`}
                            preserveAspectRatio="xMidYMid meet"
                          >
                            {layerImages.map(img => (
                              <image
                                key={`quick-layer-img-${img.id}`}
                                href={img.url}
                                x={-img.width / 2}
                                y={-img.height / 2}
                                width={img.width}
                                height={img.height}
                                opacity={Number.isFinite(img.opacity) ? Math.max(0, Math.min(1, img.opacity)) : 1}
                                transform={`translate(${img.x}, ${img.y}) scale(${img.scale}) rotate(${img.rotation})`}
                              />
                            ))}
                            {layerTexts.map(text => (
                              <TextObject key={`quick-layer-text-${text.id}`} text={text} />
                            ))}
                            {layerPaths.map((path, index) => {
                              const pathD = pointsToPath(path.points, path.isClosed);
                              const pathStroke = getPathStrokeStyle(path, pathStyleDefaults);
                              const isSinglePointPath = path.points.length === 1;

                              if (isSinglePointPath) {
                                if (!pathStroke.strokeEnabled) return null;
                                return (
                                  <circle
                                    key={`quick-layer-path-dot-${path.id}-${index}`}
                                    cx={path.points[0].x}
                                    cy={path.points[0].y}
                                    r={Math.max(2, pathStroke.strokeWidth * 1.2)}
                                    fill={pathStroke.strokeColor}
                                    stroke={pathStroke.strokeColor}
                                    strokeWidth={0.5}
                                  />
                                );
                              }

                              return (
                                <path
                                  key={`quick-layer-path-${path.id}-${index}`}
                                  d={pathD}
                                  fill={path.fillEnabled ? getPathFillStyle(path).fillColor : 'none'}
                                  stroke={pathStroke.strokeEnabled ? pathStroke.strokeColor : 'none'}
                                  strokeWidth={pathStroke.strokeEnabled ? Math.max(0.8, pathStroke.strokeWidth) : 0}
                                  strokeLinecap="round"
                                  strokeLinejoin="round"
                                />
                              );
                            })}
                          </svg>
                        ) : (
                          <LayerIcon type={layer.itemType} />
                        )}
                      </div>
                      <span className="text-xs font-semibold text-[#344054] truncate">{layer.name}</span>
                      <span className="text-[10px] text-[#98a2b3] shrink-0">{instanceCount} obj</span>
                    </button>
                    <div className="flex items-center gap-1 shrink-0">
                      <button
                        type="button"
                        onClick={() => moveSelectedLayerQuick(layer.id, 'up')}
                        disabled={!canMoveUp}
                        className={`h-7 w-7 rounded-md border flex items-center justify-center transition-colors ${
                          canMoveUp
                            ? 'border-[#d0d5dd] text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
                            : 'border-[#e4e7ec] text-[#d0d5dd] cursor-not-allowed'
                        }`}
                        title="Move layer up"
                      >
                        <ChevronUp size={13} />
                      </button>
                      <button
                        type="button"
                        onClick={() => moveSelectedLayerQuick(layer.id, 'down')}
                        disabled={!canMoveDown}
                        className={`h-7 w-7 rounded-md border flex items-center justify-center transition-colors ${
                          canMoveDown
                            ? 'border-[#d0d5dd] text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
                            : 'border-[#e4e7ec] text-[#d0d5dd] cursor-not-allowed'
                        }`}
                        title="Move layer down"
                      >
                        <ChevronUp size={13} className="rotate-180" />
                      </button>
                    </div>
                  </div>
                );
              })}
            </div>
          </div>
        </div>
      )}
    </>
  );
}
