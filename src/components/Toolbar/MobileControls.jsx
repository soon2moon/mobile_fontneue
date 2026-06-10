import {
  PenTool,
  Pencil,
  MousePointer2,
  Hand,
  Menu,
  Eye,
  EyeOff,
  Trash2,
  CircleDot,
  RefreshCw,
  Layers,
  Plus,
  Image as ImageIcon,
  X,
  Grid,
  Droplet,
  Square,
  Circle,
  Triangle,
  Star,
  Minus,
  ChevronUp,
  Copy,
  Scissors,
  ClipboardPaste,
  Download,
  Type
} from 'lucide-react';
import MobileToolButton from '../../ui/MobileToolButton';
import ShapeMenuItem from '../../ui/ShapeMenuItem';
import { useEditor } from '../../state/EditorContext';

// All mobile chrome: top controls, tools drawer, shape sheet, long-press
// context menu, and the bottom toolbar. Rendered only when isMobile.
export default function MobileControls() {
  const {
anyMobileOverlayOpen,
    applyPathStyle,
    changeMode,
    clearCanvas,
    clearTapFocus,
    closeAllPanels,
    closeMobileContextMenu,
    copyCurrentSelection,
    correctPathDirections,
    cutCurrentSelection,
    deleteSelectedItems,
    duplicateCurrentSelection,
    fileInputRef,
    fillToggleActive,
    getShapeToolIcon,
    handleMobileContextPaste,
    handleMobileRedo,
    handleMobileUndo,
    handleMobileZoomIn,
    handleMobileZoomOut,
    hasActiveSelection,
    insertTextFromPrompt,
    mobileContextMenu,
    mobileMenuDrawerBottom,
    mobileShapePanelBottom,
    mobileShapePanelOpen,
    mobileToolbarBottom,
    mobileToolbarSharedWidthStyle,
    mobileToolbarShellRef,
    mobileToolsOpen,
    mobileTopInset,
    mode,
    openMobilePanel,
    openPanels,
    resetZoomToHundred,
    selectMobileShape,
    setShowBackgroundAids,
    setShowNodes,
    shapeType,
    showBackgroundAids,
    showNodes,
    toggleMobileShapePanel,
    toggleMobileToolsMenu,
    zoom
  } = useEditor();

  return (
    <>
        <>
          {anyMobileOverlayOpen && (
            <button
              type="button"
              onClick={closeAllPanels}
              className="absolute inset-0 z-[9] bg-[#344054]/8"
              aria-label="Close panels overlay"
            />
          )}

          {mobileContextMenu && (
            <>
              <button
                type="button"
                className="absolute inset-0 z-[22] bg-transparent"
                onClick={closeMobileContextMenu}
                aria-label="Close actions menu"
              />
              <div
                className="absolute z-[23] pointer-events-none"
                style={{ left: `${mobileContextMenu.x}px`, top: `${mobileContextMenu.y}px` }}
              >
                <div className="pointer-events-auto -translate-x-1/2 -translate-y-full mb-2 bg-[#f8fafc] border border-[#e4e7ec] rounded-[12px] shadow-[0_12px_24px_rgba(52,64,84,0.14)] p-1.5">
                  <div className="flex flex-col gap-1">
                    {mobileContextMenu.type === 'actions' && (
                      <>
                        <button
                          type="button"
                          onClick={() => {
                            copyCurrentSelection();
                            closeMobileContextMenu();
                          }}
                          className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#344054] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                        >
                          <Copy size={14} />
                          Copy
                        </button>
                        <button
                          type="button"
                          onClick={() => {
                            cutCurrentSelection();
                            closeMobileContextMenu();
                          }}
                          className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#b42318] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                        >
                          <Scissors size={14} />
                          Cut
                        </button>
                        <button
                          type="button"
                          onClick={() => {
                            duplicateCurrentSelection();
                            closeMobileContextMenu();
                          }}
                          className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#344054] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                        >
                          <Plus size={14} />
                          Duplicate
                        </button>
                      </>
                    )}
                    {mobileContextMenu.type === 'paste' && (
                      <button
                        type="button"
                        onClick={handleMobileContextPaste}
                        className="h-9 px-3 rounded-[8px] border border-transparent bg-[#f2f4f7] text-[#344054] active:bg-[#eaecf0] flex items-center gap-2 text-xs font-semibold"
                      >
                        <ClipboardPaste size={14} />
                        Paste
                      </button>
                    )}
                  </div>
                </div>
              </div>
            </>
          )}

          <div
            className="absolute left-2 right-2 z-20 pointer-events-none flex flex-wrap items-center justify-between gap-2"
            style={{ top: mobileTopInset }}
          >
            <div className="pointer-events-auto h-11 bg-[#f8fafc] rounded-[16px] shadow-lg border border-[#e4e7ec] px-2 flex items-center gap-1 max-w-full">
              <button
                type="button"
                onClick={handleMobileUndo}
                onPointerUp={clearTapFocus}
                onPointerCancel={clearTapFocus}
                onTouchEnd={clearTapFocus}
                onMouseUp={clearTapFocus}
                className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                title="Undo"
              >
                <RefreshCw size={13} className="-scale-x-100" />
              </button>
              <button
                type="button"
                onClick={handleMobileRedo}
                onPointerUp={clearTapFocus}
                onPointerCancel={clearTapFocus}
                onTouchEnd={clearTapFocus}
                onMouseUp={clearTapFocus}
                className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                title="Redo"
              >
                <RefreshCw size={13} />
              </button>
            </div>
            <div className="pointer-events-auto h-11 bg-[#f8fafc] rounded-[16px] shadow-lg border border-[#e4e7ec] px-1.5 flex items-center gap-1.5 max-w-full">
              <button
                type="button"
                onClick={resetZoomToHundred}
                onPointerUp={clearTapFocus}
                onPointerCancel={clearTapFocus}
                onTouchEnd={clearTapFocus}
                onMouseUp={clearTapFocus}
                className="h-8 min-w-[52px] px-2.5 rounded-[8px] border border-transparent flex items-center justify-center text-[12px] leading-none font-semibold font-mono text-[#667085] bg-transparent active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                title="Reset zoom to 100%"
              >
                {Math.round(zoom * 100)}%
              </button>
              <div className="flex items-center gap-0.5">
                <button
                  type="button"
                  onClick={handleMobileZoomOut}
                  onPointerUp={clearTapFocus}
                  onPointerCancel={clearTapFocus}
                  onTouchEnd={clearTapFocus}
                  onMouseUp={clearTapFocus}
                  className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                  title="Zoom Out"
                >
                  <Minus size={13} />
                </button>
                <button
                  type="button"
                  onClick={handleMobileZoomIn}
                  onPointerUp={clearTapFocus}
                  onPointerCancel={clearTapFocus}
                  onTouchEnd={clearTapFocus}
                  onMouseUp={clearTapFocus}
                  className="h-8 w-8 rounded-[8px] border border-transparent flex items-center justify-center bg-transparent text-[#667085] active:bg-[#eaecf0] active:border-[#d0d5dd] active:text-[#344054]"
                  title="Zoom In"
                >
                  <Plus size={13} />
                </button>
              </div>
            </div>
          </div>

          <div
            className="absolute left-1/2 -translate-x-1/2 z-20 pointer-events-none"
            style={{ ...mobileToolbarSharedWidthStyle, bottom: mobileMenuDrawerBottom }}
          >
            <div
              className={`pointer-events-auto w-full rounded-[16px] shadow-[0_12px_28px_rgba(52,64,84,0.14)] mobile-drawer ${
                mobileToolsOpen ? 'mobile-drawer-open' : 'mobile-drawer-closed'
              }`}
            >
              <div className="bg-[#f8fafc] rounded-[16px] border border-[#e4e7ec] p-1.5 max-h-[44vh] overflow-y-auto overflow-x-hidden">
                <div className="grid grid-cols-4 gap-1">
                  <MobileToolButton active={showNodes} onClick={() => setShowNodes(prev => !prev)} icon={<CircleDot size={14} />} label="Nodes" />
                  <MobileToolButton
                    active={showBackgroundAids}
                    onClick={() => setShowBackgroundAids(prev => !prev)}
                    icon={showBackgroundAids ? <Eye size={14} /> : <EyeOff size={14} />}
                    label={showBackgroundAids ? "Hide Background Aids" : "Show Background Aids"}
                  />
                  <MobileToolButton
                    active={fillToggleActive}
                    onClick={() => applyPathStyle({ fillEnabled: !fillToggleActive })}
                    icon={<Droplet size={14} />}
                    label="Fill"
                  />
                  <MobileToolButton
                    active={openPanels.stroke}
                    onClick={() => {
                      openMobilePanel('stroke');
                    }}
                    icon={<Minus size={14} />}
                    label="Stroke"
                  />
                  <MobileToolButton onClick={correctPathDirections} icon={<RefreshCw size={14} />} label="Reverse" />
                  <MobileToolButton
                    onClick={() => {
                      fileInputRef.current?.click();
                      openMobilePanel('image');
                    }}
                    icon={<ImageIcon size={14} />}
                    label="Image"
                  />
                  <MobileToolButton
                    onClick={() => {
                      closeAllPanels();
                      insertTextFromPrompt();
                    }}
                    icon={<Type size={14} />}
                    label="Text"
                  />
                  <MobileToolButton
                    active={openPanels.grid}
                    onClick={() => {
                      openMobilePanel('grid');
                    }}
                    icon={<Grid size={14} />}
                    label="Grid"
                  />
                  <MobileToolButton
                    active={openPanels.layers}
                    onClick={() => {
                      openMobilePanel('layers');
                    }}
                    icon={<Layers size={14} />}
                    label="Layers"
                  />
                  <MobileToolButton
                    active={openPanels.export}
                    onClick={() => {
                      openMobilePanel('export');
                    }}
                    icon={<Download size={14} />}
                    label="Export"
                  />
                  <MobileToolButton onClick={clearCanvas} icon={<Trash2 size={14} />} label="Clear" />
                </div>
              </div>
            </div>
          </div>

          {mobileShapePanelOpen && (
            <div
              className="absolute left-1/2 -translate-x-1/2 z-[21] pointer-events-none w-max max-w-[calc(100vw-16px)]"
              style={{ bottom: mobileShapePanelBottom }}
            >
              <div className="pointer-events-auto rounded-[16px] shadow-[0_12px_28px_rgba(52,64,84,0.14)] w-max max-w-[calc(100vw-16px)]">
                <div className="bg-[#f8fafc] rounded-[16px] border border-[#e4e7ec] p-1 overflow-hidden">
                  <div className="flex items-center gap-0.5 overflow-x-auto">
                    <MobileToolButton active={shapeType === 'rectangle'} onClick={() => selectMobileShape('rectangle')} icon={<Square size={14} />} label="Rect" />
                    <MobileToolButton active={shapeType === 'ellipse'} onClick={() => selectMobileShape('ellipse')} icon={<Circle size={14} />} label="Ellipse" />
                    <MobileToolButton active={shapeType === 'polygon'} onClick={() => selectMobileShape('polygon')} icon={<Triangle size={14} />} label="Poly" />
                    <MobileToolButton active={shapeType === 'star'} onClick={() => selectMobileShape('star')} icon={<Star size={14} />} label="Star" />
                    <MobileToolButton active={shapeType === 'line'} onClick={() => selectMobileShape('line')} icon={<Minus size={14} />} label="Line" />
                  </div>
                </div>
              </div>
            </div>
          )}

          <div
            className="absolute left-1/2 -translate-x-1/2 z-20 pointer-events-none w-max max-w-[calc(100vw-16px)]"
            style={{ bottom: mobileToolbarBottom }}
          >
            <div ref={mobileToolbarShellRef} className="pointer-events-auto bg-[#f8fafc] rounded-[16px] shadow-lg border border-[#e4e7ec] p-[6px] w-max max-w-[calc(100vw-16px)]">
              <div className="flex items-center gap-1 overflow-x-auto">
                <MobileToolButton
                  variant="toolbar"
                  radiusClass="rounded-[8px]"
                  active={false}
                  onClick={toggleMobileToolsMenu}
                  icon={<Menu size={16} />}
                  label="Menu"
                />
                <div className="mx-2 h-7 w-px bg-[#d0d5dd] shrink-0" />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'edit'} onClick={() => changeMode('edit')} icon={<MousePointer2 size={16} />} label="Edit" />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'draw'} onClick={() => changeMode('draw')} icon={<PenTool size={16} />} label="Path" />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'pencil'} onClick={() => changeMode('pencil')} icon={<Pencil size={16} />} label="Pencil" />
                <MobileToolButton
                  variant="toolbar"
                  radiusClass="rounded-[8px]"
                  active={mode === 'shape'}
                  onClick={toggleMobileShapePanel}
                  icon={getShapeToolIcon(16)}
                  label="Shape"
                />
                <MobileToolButton variant="toolbar" radiusClass="rounded-[8px]" active={mode === 'pan'} onClick={() => changeMode('pan')} icon={<Hand size={16} />} label="Pan" />
                <MobileToolButton
                  variant="toolbar"
                  radiusClass="rounded-[8px]"
                  active={hasActiveSelection}
                  onClick={deleteSelectedItems}
                  icon={<Trash2 size={16} />}
                  label="Delete"
                />
              </div>
            </div>
          </div>
        </>
    </>
  );
}
