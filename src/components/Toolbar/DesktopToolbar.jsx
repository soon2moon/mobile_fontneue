import {
  PenTool,
  Pencil,
  MousePointer2,
  Hand,
  Eye,
  EyeOff,
  Trash2,
  CircleDot,
  RefreshCw,
  Layers,
  Image as ImageIcon,
  Grid,
  Droplet,
  Square,
  Circle,
  Triangle,
  Star,
  Minus,
  ChevronUp,
  Download,
  SlidersHorizontal,
  Type
} from 'lucide-react';
import { useRef } from 'react';
import ToolButton from '../../ui/ToolButton';
import ShapeMenuItem from '../../ui/ShapeMenuItem';
import Popover from '../../ui/Popover';
import { useEditor } from '../../state/EditorContext';

// Bottom-centered desktop toolbar: drawing tools + contextual shape menu,
// manipulation tools, panel toggles, view toggles, global actions.
export default function DesktopToolbar() {
  const {
applyPathStyle,
    changeMode,
    clearCanvas,
    correctPathDirections,
    fileInputRef,
    fillToggleActive,
    hasSelectedPaths,
    mode,
    openPanels,
    selectedPoints,
    setShapeType,
    setShowNodes,
    setShowShapeMenu,
    shapeType,
    showNodes,
    showShapeMenu,
    togglePanel
  } = useEditor();
  const shapeAnchorRef = useRef(null);

  return (
      <div className="absolute bottom-8 left-1/2 -translate-x-1/2 flex items-center gap-2 bg-[#f8fafc] p-2 rounded-2xl shadow-lg border border-[#e4e7ec]">
        
        {/* Drawing Tools Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={mode === 'draw'} 
            onClick={() => changeMode('draw')} 
            icon={<PenTool size={20} />} 
            label="Path Tool" 
            hotkey="P"
          />
          <ToolButton 
            active={mode === 'pencil'} 
            onClick={() => changeMode('pencil')} 
            icon={<Pencil size={20} />} 
            label="Pencil Tool" 
            hotkey="F"
          />

          {/* Contextual Shape Menu */}
          <div className="relative flex items-center gap-0.5 group" ref={shapeAnchorRef}>
            <button
              onClick={() => { changeMode('shape'); setShowShapeMenu(false); }}
              className={`p-3 rounded-xl transition-all duration-200 flex items-center justify-center ${
                mode === 'shape' 
                  ? 'bg-[#eaecf0] text-[#344054]' 
                  : 'text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
              }`}
              title="Shape Tool (R/O)"
            >
              {shapeType === 'rectangle' && <Square size={20} />}
              {shapeType === 'ellipse' && <Circle size={20} />}
              {shapeType === 'polygon' && <Triangle size={20} />}
              {shapeType === 'star' && <Star size={20} />}
              {shapeType === 'line' && <Minus size={20} />}
            </button>
            <button
              onClick={() => setShowShapeMenu(!showShapeMenu)}
              className={`w-6 h-11 rounded-xl transition-all duration-200 flex items-center justify-center ${
                 showShapeMenu
                  ? 'bg-[#eaecf0] text-[#344054]' 
                  : 'text-[#667085] hover:bg-[#f2f4f7] hover:text-[#344054]'
              }`}
              title="Shape Options"
            >
              <ChevronUp size={14} />
            </button>
            
            {/* Shape Dropdown Menu */}
            <Popover open={showShapeMenu} onOpenChange={setShowShapeMenu} anchorRef={shapeAnchorRef} placement="top-start" offsetPx={8}>
               <div className="w-36 bg-[#f8fafc] p-1.5 rounded-2xl shadow-xl border border-[#e4e7ec] flex flex-col gap-0.5">
                   <ShapeMenuItem type="rectangle" icon={<Square size={16}/>} label="Rectangle" hotkey="R" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="ellipse" icon={<Circle size={16}/>} label="Ellipse" hotkey="O" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="polygon" icon={<Triangle size={16}/>} label="Polygon" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="star" icon={<Star size={16}/>} label="Star" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
                   <ShapeMenuItem type="line" icon={<Minus size={16}/>} label="Line" current={shapeType} onClick={(t) => {setShapeType(t); changeMode('shape');}} />
               </div>
            </Popover>
          </div>

          <ToolButton
            active={mode === 'text'}
            onClick={() => changeMode('text')}
            icon={<Type size={20} />}
            label="Text Tool"
            hotkey="T"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e4e7ec] mx-1"></div>

        {/* Manipulation Tools Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={mode === 'edit'} 
            onClick={() => changeMode('edit')} 
            icon={<MousePointer2 size={20} />} 
            label="Node Editor" 
            hotkey="V"
          />
          <ToolButton 
            active={mode === 'pan'} 
            onClick={() => changeMode('pan')} 
            icon={<Hand size={20} />} 
            label="Pan Canvas" 
            hotkey="Space"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e4e7ec] mx-1"></div>

        {/* Configuration Panels Section */}
        <div className="flex gap-1">
          <ToolButton
            active={false}
            onClick={() => fileInputRef.current?.click()}
            icon={<ImageIcon size={20} />}
            label="Upload Image"
            hotkey="U"
          />
          <ToolButton
            active={openPanels.grid}
            onClick={() => togglePanel('grid')} 
            icon={<Grid size={20} />} 
            label="Background Config" 
            hotkey="B"
          />
          <ToolButton
            active={openPanels.layers}
            onClick={() => togglePanel('layers')} 
            icon={<Layers size={20} />} 
            label="Layers Panel" 
            hotkey="L"
          />
          <ToolButton 
            active={openPanels.export} 
            onClick={() => togglePanel('export')} 
            icon={<Download size={20} />} 
            label="Export"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e4e7ec] mx-1"></div>

        {/* View Toggles Section */}
        <div className="flex gap-1">
          <ToolButton 
            active={showNodes && mode !== 'pencil'} 
            onClick={() => { 
                if (mode === 'pencil') {
                  changeMode('edit');
                  setShowNodes(true);
                } else {
                  setShowNodes(!showNodes);
                }
            }} 
            icon={<CircleDot size={20} />} 
            label="Show Nodes" 
            hotkey="N"
          />
          <ToolButton
            active={fillToggleActive}
            onClick={() => applyPathStyle({ fillEnabled: !fillToggleActive })}
            icon={<Droplet size={20} />}
            label={hasSelectedPaths ? "Toggle Fill (Selection)" : "Toggle Fill (Default)"}
          />
          <ToolButton
            active={openPanels.inspector}
            onClick={() => togglePanel('inspector')}
            icon={<SlidersHorizontal size={20} />}
            label="Inspector"
          />
        </div>

        {/* Separator */}
        <div className="w-[1px] h-8 bg-[#e4e7ec] mx-1"></div>

        {/* Global Actions Section */}
        <div className="flex gap-1">
          <button 
            onClick={correctPathDirections}
            className="p-3 text-[#667085] hover:text-[#344054] hover:bg-[#f2f4f7] rounded-xl transition-all"
            title={selectedPoints.length > 0 ? "Reverse Path Direction (Manual)" : "Auto-Correct Path Directions"}
          >
            <RefreshCw size={20} />
          </button>
          
          <button 
            onClick={clearCanvas}
            className="p-3 text-[#667085] hover:text-red-600 hover:bg-red-50 rounded-xl transition-all"
            title="Clear Canvas"
          >
            <Trash2 size={20} />
          </button>
        </div>
      </div>
  );
}
