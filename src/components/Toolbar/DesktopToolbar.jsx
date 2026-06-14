import {
  PenTool,
  Pencil,
  MousePointer2,
  Hand,
  Layers,
  Image as ImageIcon,
  Grid,
  Square,
  Circle,
  Triangle,
  Star,
  Minus,
  ChevronUp,
  Frame as FrameIcon,
  Download,
  SlidersHorizontal,
  Type
} from 'lucide-react';
import { useRef } from 'react';
import ToolButton from '../../ui/ToolButton';
import ShapeMenuItem from '../../ui/ShapeMenuItem';
import Popover from '../../ui/Popover';
import Tooltip from '../../ui/Tooltip';
import { useEditor } from '../../state/EditorContext';

// Bottom-centered desktop toolbar: drawing tools + contextual shape menu,
// manipulation tools, and panel toggles (quiet grey when open).
export default function DesktopToolbar() {
  const {
    changeMode,
    fileInputRef,
    mode,
    openPanels,
    setShapeType,
    setShowShapeMenu,
    shapeType,
    showShapeMenu,
    togglePanel
  } = useEditor();
  const shapeAnchorRef = useRef(null);

  return (
      <div className="absolute bottom-8 left-1/2 -translate-x-1/2 flex items-center gap-2 bg-raised p-2 rounded-2xl shadow-lg border border-edge">

        {/* Drawing Tools Section */}
        <div className="flex gap-1">
          <ToolButton
            active={mode === 'draw'}
            onClick={() => changeMode('draw')}
            icon={<PenTool size={20} />}
            label="Pen"
            hotkey="P"
          />
          <ToolButton
            active={mode === 'pencil'}
            onClick={() => changeMode('pencil')}
            icon={<Pencil size={20} />}
            label="Pencil"
            hotkey="Shift+P"
          />

          {/* Contextual Shape Menu */}
          <div className="relative flex items-center gap-0.5 group" ref={shapeAnchorRef}>
            <Tooltip label="Shape Tool" hotkey="R/O">
              <button
                onClick={() => { changeMode('shape'); setShowShapeMenu(false); }}
                aria-label="Shape Tool (R/O)"
                className={`p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
                  mode === 'shape'
                    ? 'bg-accent text-white'
                    : 'text-secondary hover:bg-sunken hover:text-ink'
                }`}
              >
                {shapeType === 'rectangle' && <Square size={20} />}
                {shapeType === 'ellipse' && <Circle size={20} />}
                {shapeType === 'polygon' && <Triangle size={20} />}
                {shapeType === 'star' && <Star size={20} />}
                {shapeType === 'line' && <Minus size={20} />}
              </button>
            </Tooltip>
            <Tooltip label="Shape Options">
              <button
                onClick={() => setShowShapeMenu(!showShapeMenu)}
                aria-label="Shape Options"
                className={`w-6 h-11 rounded-xl transition-all duration-200 flex items-center justify-center ${
                   showShapeMenu
                    ? 'bg-pressed text-ink'
                    : 'text-secondary hover:bg-sunken hover:text-ink'
                }`}
              >
                <ChevronUp size={14} />
              </button>
            </Tooltip>

            {/* Shape Dropdown Menu */}
            <Popover open={showShapeMenu} onOpenChange={setShowShapeMenu} anchorRef={shapeAnchorRef} placement="top-start" offsetPx={8}>
               <div className="w-36 bg-raised p-1.5 rounded-2xl shadow-xl border border-edge flex flex-col gap-0.5">
                   <ShapeMenuItem type="rectangle" icon={<Square size={16}/>} label="Rectangle" hotkey="R" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="ellipse" icon={<Circle size={16}/>} label="Ellipse" hotkey="O" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="polygon" icon={<Triangle size={16}/>} label="Polygon" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="star" icon={<Star size={16}/>} label="Star" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="line" icon={<Minus size={16}/>} label="Line" hotkey="L" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
               </div>
            </Popover>
          </div>

          <ToolButton
            active={mode === 'frame'}
            onClick={() => changeMode('frame')}
            icon={<FrameIcon size={20} />}
            label="Frame"
            hotkey="F"
          />
          <ToolButton
            active={mode === 'text'}
            onClick={() => changeMode('text')}
            icon={<Type size={20} />}
            label="Text"
            hotkey="T"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-edge mx-1"></div>

        {/* Manipulation Tools Section */}
        <div className="flex gap-1">
          <ToolButton
            active={mode === 'edit'}
            onClick={() => changeMode('edit')}
            icon={<MousePointer2 size={20} />}
            label="Move"
            hotkey="V"
          />
          <ToolButton
            active={mode === 'pan'}
            onClick={() => changeMode('pan')}
            icon={<Hand size={20} />}
            label="Hand"
            hotkey="H"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-edge mx-1"></div>

        {/* Place Image + Panel toggles (quiet grey when open) */}
        <div className="flex gap-1">
          <ToolButton
            active={false}
            onClick={() => fileInputRef.current?.click()}
            icon={<ImageIcon size={20} />}
            label="Place Image"
            hotkey="U"
          />
          <ToolButton
            tone="panel"
            active={openPanels.layers}
            onClick={() => togglePanel('layers')}
            icon={<Layers size={20} />}
            label="Layers"
          />
          <ToolButton
            tone="panel"
            active={openPanels.inspector}
            onClick={() => togglePanel('inspector')}
            icon={<SlidersHorizontal size={20} />}
            label="Design"
          />
          <ToolButton
            tone="panel"
            active={openPanels.grid}
            onClick={() => togglePanel('grid')}
            icon={<Grid size={20} />}
            label="Canvas Grid"
          />
          <ToolButton
            tone="panel"
            active={openPanels.export}
            onClick={() => togglePanel('export')}
            icon={<Download size={20} />}
            label="Export"
          />
        </div>
      </div>
  );
}
