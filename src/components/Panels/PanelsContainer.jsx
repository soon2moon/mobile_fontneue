import {
  Eye,
  EyeOff,
  Trash2,
  GripVertical,
  X,
  Lock,
  Unlock,
  Download
} from 'lucide-react';
import LayerIcon from '../../ui/LayerIcon';
import ScrubbableNumberInput from '../../ui/inputs/ScrubbableNumberInput';
import Toggle from '../../ui/inputs/Toggle';
import Inspector from '../Inspector/Inspector';
import { PANELS_CONFIG } from '../../config/panels';
import {
  GRID_SIZE,
  MIN_GRID_SIZE,
  MAX_GRID_SIZE,
  MIN_CIRCULAR_STEP,
  MAX_CIRCULAR_STEP,
  DEFAULT_CIRCULAR_STEP
} from '../../constants';
import { useEditor } from '../../state/EditorContext';

// Unified panel stack (desktop right-side / mobile top sheet). Open panels share
// one card: a top icon-nav row switches the active view; hovering an icon reveals
// a ×-circle that removes that panel; clicking the active icon collapses to
// icons-only. With a single panel left, the header is an icon+label pill with the
// ×-circle on the right.
export default function PanelsContainer() {
  const {
    anyPanelOpen,
    canExportSelection,
    selectedFrameIds,
    isCanvasWorking,
    deleteLayer,
    dragDropTarget,
    draggedLayerId,
    editingLayerId,
    editingLayerName,
    effectiveCircularStep,
    effectiveGridSize,
    expandedPanel,
    gridConfig,
    handleExport,
    handleLayerDragEnd,
    handleLayerDragOver,
    handleLayerDragStart,
    handleLayerDrop,
    handleLayerNameKeyDown,
    handleLayerSelect,
    isExporting,
    isMobile,
    layers,
    exportFormat,
    exportScope,
    frameTransparent,
    setFrameTransparent,
    mobilePanelsOpen,
    openPanels,
    saveLayerName,
    selectedLayerIds,
    setEditingLayerName,
    setExpandedPanel,
    setGridConfig,
    setExportFormat,
    setExportScope,
    removePanel,
    startEditingLayer,
    toggleLayerLock,
    toggleLayerVisibility
  } = useEditor();

  const openList = PANELS_CONFIG.filter(panel => openPanels[panel.id]);
  if (openList.length === 0) return null;
  const single = openList.length === 1;
  const activeId = expandedPanel && openPanels[expandedPanel] ? expandedPanel : null;

  const renderContent = (panelId) => {
    if (panelId === 'inspector') return <Inspector />;

    if (panelId === 'grid') return (
      <div className="p-3.5 flex flex-col gap-3">
        <div className="grid grid-cols-3 gap-2 bg-sunken p-1.5 rounded-lg">
          <button className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'none' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, type: 'none' })}>None</button>
          <button className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'dots' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, type: 'dots' })}>Dots</button>
          <button className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'lines' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, type: 'lines' })}>Grid</button>
          <button className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'circular' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, type: 'circular' })}>Circular</button>
          <button className={`py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.type === 'circles' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, type: 'circles' })}>Circles</button>
        </div>

        {gridConfig.type === 'lines' && (
          <div className="flex flex-col gap-2 mt-1">
            <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Grid Shape (Edges)</label>
            <div className="flex gap-2 bg-sunken p-1.5 rounded-lg">
              <button className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 3 ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, edges: 3 })}>3 (Tri)</button>
              <button className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 4 ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, edges: 4 })}>4 (Sqr)</button>
              <button className={`flex-1 py-1.5 text-xs font-semibold rounded-md transition-all ${gridConfig.edges === 6 ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`} onClick={() => setGridConfig({ ...gridConfig, edges: 6 })}>6 (Hex)</button>
            </div>
          </div>
        )}

        {gridConfig.type !== 'none' && (
          <div className="flex flex-col gap-2 mt-1">
            <div className="grid grid-cols-[minmax(0,1fr)_88px] items-center gap-2">
              <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Grid Density</label>
              <ScrubbableNumberInput
                value={effectiveGridSize}
                min={MIN_GRID_SIZE}
                max={MAX_GRID_SIZE}
                step={1}
                suffix="px"
                onChange={(next) => {
                  const clamped = Math.max(MIN_GRID_SIZE, Math.min(MAX_GRID_SIZE, Number(next) || GRID_SIZE));
                  setGridConfig(prev => ({ ...prev, size: clamped }));
                }}
              />
            </div>
            {gridConfig.type === 'circular' && (
              <div className="grid grid-cols-[minmax(0,1fr)_88px] items-center gap-2">
                <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Angle Step</label>
                <ScrubbableNumberInput
                  value={effectiveCircularStep}
                  min={MIN_CIRCULAR_STEP}
                  max={MAX_CIRCULAR_STEP}
                  step={1}
                  suffix="deg"
                  onChange={(next) => {
                    const clamped = Math.max(MIN_CIRCULAR_STEP, Math.min(MAX_CIRCULAR_STEP, Number(next) || DEFAULT_CIRCULAR_STEP));
                    setGridConfig(prev => ({ ...prev, circularStep: clamped }));
                  }}
                />
              </div>
            )}
          </div>
        )}

        <div className="flex items-center justify-between mt-2 pt-3 border-t border-edge">
          <label className="text-[10px] font-bold text-secondary uppercase tracking-widest px-1">Snap to Grid</label>
          <Toggle checked={gridConfig.snapToGrid} onChange={(next) => setGridConfig({ ...gridConfig, snapToGrid: next })} />
        </div>
      </div>
    );

    if (panelId === 'layers') return (
      <div className={`flex flex-col min-h-0 flex-1 ${isMobile ? 'max-h-[36vh]' : 'max-h-[60vh]'}`}>
        <div className="panel-scroll flex-1 overflow-y-auto flex flex-col gap-0.5 px-1.5 py-1" style={{ touchAction: 'pan-y' }}>
          {layers.map(layer => {
            const isSelected = selectedLayerIds.has(layer.id);
            return (
              <div className="relative" key={layer.id}>
                {dragDropTarget?.id === layer.id && dragDropTarget.position === 'top' && (
                  <div className="absolute top-[-1px] left-0 right-0 h-[2px] bg-accent z-10 rounded-full" />
                )}
                <div
                  draggable={!isMobile && editingLayerId !== layer.id}
                  onDragStart={(e) => handleLayerDragStart(e, layer.id)}
                  onDragOver={(e) => handleLayerDragOver(e, layer.id)}
                  onDrop={(e) => handleLayerDrop(e, layer.id)}
                  onDragEnd={handleLayerDragEnd}
                  className={`flex items-center justify-between px-2 py-1.5 rounded-lg transition-colors cursor-pointer ${
                    isSelected
                      ? 'bg-accent-soft text-ink'
                      : 'hover:bg-sunken text-secondary'
                  } ${draggedLayerId === layer.id ? 'opacity-50' : ''}`}
                  onClick={(e) => handleLayerSelect(e, layer)}
                >
                  <div className="flex items-center gap-1.5 flex-1 min-w-0">
                    <div className="cursor-grab active:cursor-grabbing opacity-40 hover:opacity-100 p-1 -ml-1">
                      <GripVertical size={14} />
                    </div>
                    <LayerIcon type={layer.itemType} />
                    {editingLayerId === layer.id ? (
                      <input
                        type="text"
                        value={editingLayerName}
                        onChange={(e) => setEditingLayerName(e.target.value)}
                        onBlur={saveLayerName}
                        onKeyDown={handleLayerNameKeyDown}
                        autoFocus
                        onFocus={(e) => e.target.select()}
                        onClick={(e) => e.stopPropagation()}
                        onPointerDown={(e) => e.stopPropagation()}
                        onMouseDown={(e) => e.stopPropagation()}
                        className="text-xs font-semibold text-ink bg-chip border border-ink rounded px-1 outline-none w-24 py-0.5 select-text cursor-text ml-1"
                      />
                    ) : (
                      <span
                        onDoubleClick={(e) => { e.stopPropagation(); startEditingLayer(layer); }}
                        title="Double-click to rename"
                        className={`text-xs font-semibold select-none ml-1 truncate ${layer.visible ? (layer.locked ? 'opacity-60' : 'opacity-100') : 'opacity-50'} hover:opacity-100 transition-opacity`}
                      >
                        {layer.name}
                      </span>
                    )}
                  </div>

                  <div className="flex items-center gap-0.5 shrink-0 ml-2">
                    <button
                      onClick={(e) => { e.stopPropagation(); toggleLayerVisibility(layer.id); }}
                      className={`p-1.5 rounded-md hover:bg-edge/50 transition-colors ${layer.visible ? 'opacity-100' : 'opacity-40'}`}
                      title={layer.visible ? 'Hide Layer' : 'Show Layer'}
                    >
                      {layer.visible ? <Eye size={14} /> : <EyeOff size={14} />}
                    </button>
                    <button
                      onClick={(e) => { e.stopPropagation(); toggleLayerLock(layer.id); }}
                      className={`p-1.5 rounded-md hover:bg-edge/50 transition-colors ${layer.locked ? 'opacity-100' : 'opacity-40'}`}
                      title={layer.locked ? 'Unlock Layer' : 'Lock Layer'}
                    >
                      {layer.locked ? <Lock size={14} /> : <Unlock size={14} />}
                    </button>
                    <button
                      onClick={(e) => { e.stopPropagation(); deleteLayer(layer.id); }}
                      className="p-1.5 rounded-md hover:bg-danger-bg text-danger transition-colors"
                      title="Delete Layer"
                    >
                      <Trash2 size={14} />
                    </button>
                  </div>
                </div>
                {dragDropTarget?.id === layer.id && dragDropTarget.position === 'bottom' && (
                  <div className="absolute bottom-[-1px] left-0 right-0 h-[2px] bg-accent z-10 rounded-full" />
                )}
              </div>
            );
          })}
        </div>
      </div>
    );

    if (panelId === 'export') return (
      <div className="p-3.5 flex flex-col gap-3">
        <div className="grid grid-cols-3 gap-2 bg-sunken p-1.5 rounded-lg">
          <button
            onClick={() => setExportScope('selection')}
            className={`py-1.5 text-xs font-semibold rounded-md transition-all ${exportScope === 'selection' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`}
          >
            Selection
          </button>
          <button
            onClick={() => setExportScope('canvas')}
            className={`py-1.5 text-xs font-semibold rounded-md transition-all ${exportScope === 'canvas' ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`}
          >
            Canvas
          </button>
          <button
            onClick={() => setExportScope('frame')}
            disabled={selectedFrameIds.length !== 1}
            className={`py-1.5 text-xs font-semibold rounded-md transition-all ${exportScope === 'frame' ? 'bg-accent shadow-sm text-white' : selectedFrameIds.length !== 1 ? 'text-muted cursor-not-allowed' : 'text-secondary hover:text-ink'}`}
          >
            Frame
          </button>
        </div>

        <div className="grid grid-cols-3 gap-2 bg-sunken p-1.5 rounded-lg">
          {['png', 'jpg', 'svg'].map(format => (
            <button
              key={format}
              onClick={() => setExportFormat(format)}
              className={`py-1.5 text-xs font-semibold uppercase rounded-md transition-all ${exportFormat === format ? 'bg-accent shadow-sm text-white' : 'text-secondary hover:text-ink'}`}
            >
              {format}
            </button>
          ))}
        </div>

        {exportScope === 'frame' && (
          <div className="flex items-center justify-between px-1">
            <span className="text-xs text-secondary">
              Transparent background
              {exportFormat === 'jpg' && <span className="text-muted"> · JPG has no alpha</span>}
            </span>
            <Toggle
              checked={frameTransparent && exportFormat !== 'jpg'}
              onChange={setFrameTransparent}
              disabled={exportFormat === 'jpg'}
              title="Transparent background (PNG/SVG)"
            />
          </div>
        )}

        {exportScope === 'selection' && !canExportSelection && (
          <p className="text-[10px] text-muted px-1">
            Select one or more objects to export selection.
          </p>
        )}

        <button
          type="button"
          onClick={handleExport}
          disabled={isExporting || (exportScope === 'selection' && !canExportSelection)}
          className={`h-9 rounded-lg border text-xs font-semibold transition-colors flex items-center justify-center gap-2 ${
            isExporting || (exportScope === 'selection' && !canExportSelection)
              ? 'bg-sunken border-edge-strong text-muted cursor-not-allowed'
              : 'bg-sunken border-edge-strong text-ink hover:bg-pressed'
          }`}
        >
          <Download size={14} />
          {isExporting ? 'Exporting…' : `Export ${exportFormat.toUpperCase()}`}
        </button>
      </div>
    );

    return null;
  };

  return (
    <div
      className={`absolute flex flex-col z-[30] pointer-events-none ${
        isMobile
          ? `top-14 left-2 right-2 max-h-[56vh] overflow-y-visible overflow-x-visible pb-1 items-stretch mobile-panels-wrap ${
              mobilePanelsOpen || anyPanelOpen ? 'mobile-panels-open' : 'mobile-panels-closed'
            }`
          : 'top-8 right-8 items-end'
      }`}
    >
      <div
        className={`bg-raised rounded-2xl shadow-card border border-edge overflow-clip flex flex-col shrink-0 transition-all duration-300 ${
          isCanvasWorking ? 'opacity-25 pointer-events-none delay-100' : 'opacity-100 pointer-events-auto'
        } ${isMobile ? 'w-full' : 'w-60'}`}
      >
        {single ? (() => {
          const panel = openList[0];
          const Icon = panel.icon;
          const isActive = activeId === panel.id;
          return (
            <div className="flex items-center justify-between gap-1.5 p-1.5">
              <button
                type="button"
                onClick={() => setExpandedPanel(isActive ? null : panel.id)}
                title={panel.title}
                className="flex items-center gap-2 flex-1 min-w-0 text-left h-11 px-3 rounded-xl hover:bg-sunken transition-colors"
              >
                <Icon size={16} className="text-secondary shrink-0" />
                <span className="text-[11px] font-bold uppercase tracking-widest text-secondary truncate">{panel.title}</span>
              </button>
              <button
                type="button"
                onClick={() => removePanel(panel.id)}
                title={`Close ${panel.title}`}
                className="w-7 h-7 rounded-full bg-pressed border border-edge-strong text-secondary hover:text-ink hover:bg-edge-strong flex items-center justify-center shrink-0 transition-colors"
              >
                <X size={13} />
              </button>
            </div>
          );
        })() : (
          <div className="flex items-center gap-1.5 p-1.5">
            {openList.map(panel => {
              const Icon = panel.icon;
              const isActive = activeId === panel.id;
              return (
                <div key={panel.id} className="relative group flex-1">
                  <button
                    type="button"
                    onClick={() => setExpandedPanel(isActive ? null : panel.id)}
                    title={panel.title}
                    className={`w-full h-11 rounded-xl border flex items-center justify-center transition-all ${
                      isActive
                        ? 'bg-accent-soft border-accent/40 text-white shadow-sm'
                        : 'border-transparent text-secondary hover:bg-sunken hover:text-ink'
                    }`}
                  >
                    <Icon size={18} />
                  </button>
                  <button
                    type="button"
                    onClick={(e) => { e.stopPropagation(); removePanel(panel.id); }}
                    title={`Close ${panel.title}`}
                    className="absolute -top-1 -right-1 w-4 h-4 rounded-full bg-pressed border border-edge-strong text-secondary hover:text-ink hover:bg-edge-strong flex items-center justify-center opacity-0 group-hover:opacity-100 transition-opacity"
                  >
                    <X size={9} />
                  </button>
                </div>
              );
            })}
          </div>
        )}

        {activeId && (
          <div className="flex flex-col min-h-0 border-t border-edge">
            {renderContent(activeId)}
          </div>
        )}
      </div>
    </div>
  );
}
