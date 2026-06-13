import { useState } from 'react';
import {
  Copy, Scissors, ClipboardPaste, CopyPlus, Trash2,
  ArrowUp, ArrowDown, ArrowUpToLine, ArrowDownToLine,
  ChevronRight, Eye
} from 'lucide-react';
import Popover from '../../ui/Popover';
import { useEditor } from '../../state/EditorContext';

// Shared canvas context menu: desktop right-click and mobile long-press /
// short-press both open it (App.handleCanvasContextMenu + the pointer hook
// store {type, x, y, worldX, worldY, targetLayerId}). Figma-style dark menu —
// an elevated card (rounded + drop shadow), #007EEA (accent) active row, and
// right-aligned shortcut hints. Object hits get clipboard actions + an Arrange
// side-flyout submenu; empty canvas gets Paste here + Show/Hide UI.
const MENU_SURFACE =
  'bg-raised border border-edge rounded-[12px] shadow-menu p-1.5 w-52 flex flex-col gap-0.5';

const itemClass = (danger = false) =>
  `group h-8 px-2 rounded-md flex items-center gap-2.5 text-xs font-medium cursor-default ${
    danger ? 'text-danger' : 'text-ink'
  } hover:bg-accent hover:text-white`;

function MenuItem({ icon, label, hint, danger = false, onClick, onMouseEnter, hasSubmenu = false }) {
  return (
    <button type="button" onClick={onClick} onMouseEnter={onMouseEnter} className={itemClass(danger)}>
      {icon}
      <span className="flex-1 text-left whitespace-nowrap">{label}</span>
      {hint && <span className="text-[11px] font-mono text-muted group-hover:text-white">{hint}</span>}
      {hasSubmenu && <ChevronRight size={13} className="text-muted group-hover:text-white -mr-1" />}
    </button>
  );
}

const Separator = () => <div className="h-px bg-edge my-1 mx-1" />;

export default function CanvasContextMenu() {
  const {
    canvasContextMenu,
    closeCanvasContextMenu,
    copyCurrentSelection,
    cutCurrentSelection,
    duplicateCurrentSelection,
    deleteSelectedItems,
    handleContextPaste,
    moveSelectedLayerQuick,
    toggleUiHidden
  } = useEditor();
  const [arrangeOpen, setArrangeOpen] = useState(false);

  const menu = canvasContextMenu;
  const runAndClose = (action) => () => {
    action();
    setArrangeOpen(false);
    closeCanvasContextMenu();
  };
  const arrange = (dir) => runAndClose(() => {
    if (menu?.targetLayerId) moveSelectedLayerQuick(menu.targetLayerId, dir);
  });

  return (
    <Popover
      open={!!menu}
      onOpenChange={(next) => { if (!next) { setArrangeOpen(false); closeCanvasContextMenu(); } }}
      virtualAnchor={menu ? { x: menu.x, y: menu.y } : null}
      placement="top"
      offsetPx={8}
      guardOutsidePressMs={400}
    >
      <div role="menu" aria-label="Canvas actions" className={MENU_SURFACE}>
        {menu?.type === 'actions' && (
          <>
            <MenuItem icon={<Copy size={14} />} label="Copy" hint="Ctrl+C" onClick={runAndClose(copyCurrentSelection)} onMouseEnter={() => setArrangeOpen(false)} />
            <MenuItem icon={<Scissors size={14} />} label="Cut" hint="Ctrl+X" onClick={runAndClose(cutCurrentSelection)} onMouseEnter={() => setArrangeOpen(false)} />
            <MenuItem icon={<CopyPlus size={14} />} label="Duplicate" onClick={runAndClose(duplicateCurrentSelection)} onMouseEnter={() => setArrangeOpen(false)} />
            <MenuItem icon={<Trash2 size={14} />} label="Delete" hint="Del" danger onClick={runAndClose(deleteSelectedItems)} onMouseEnter={() => setArrangeOpen(false)} />
            <Separator />
            <div className="relative" onMouseEnter={() => setArrangeOpen(true)} onMouseLeave={() => setArrangeOpen(false)}>
              <MenuItem icon={<ArrowUpToLine size={14} />} label="Arrange" hasSubmenu />
              {arrangeOpen && (
                <div className="absolute left-full top-0 pl-1.5 z-[1]">
                  <div className={MENU_SURFACE}>
                    <MenuItem icon={<ArrowUpToLine size={14} />} label="Bring to front" onClick={arrange('top')} />
                    <MenuItem icon={<ArrowUp size={14} />} label="Bring forward" onClick={arrange('up')} />
                    <MenuItem icon={<ArrowDown size={14} />} label="Send backward" onClick={arrange('down')} />
                    <MenuItem icon={<ArrowDownToLine size={14} />} label="Send to back" onClick={arrange('bottom')} />
                  </div>
                </div>
              )}
            </div>
          </>
        )}
        {menu?.type === 'paste' && (
          <>
            <MenuItem
              icon={<ClipboardPaste size={14} />}
              label="Paste here"
              onClick={runAndClose(() => handleContextPaste(menu.worldX != null ? { x: menu.worldX, y: menu.worldY } : undefined))}
            />
            <Separator />
            <MenuItem icon={<Eye size={14} />} label="Show/Hide UI" hint={"Ctrl+\\"} onClick={runAndClose(toggleUiHidden)} />
          </>
        )}
      </div>
    </Popover>
  );
}
