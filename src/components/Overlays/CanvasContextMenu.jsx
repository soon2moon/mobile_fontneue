import { Copy, Scissors, ClipboardPaste, Plus, Trash2, ArrowUp, ArrowDown } from 'lucide-react';
import Popover from '../../ui/Popover';
import { useEditor } from '../../state/EditorContext';

// Shared canvas context menu: desktop right-click and mobile long-press /
// short-press both open it (App.handleCanvasContextMenu + the pointer hook
// store {type, x, y, worldX, worldY, targetLayerId}). Object hits get
// clipboard + ordering actions with shortcut hints; empty canvas gets
// "Paste here" at the pressed point.
export default function CanvasContextMenu() {
  const {
    canvasContextMenu,
    closeCanvasContextMenu,
    copyCurrentSelection,
    cutCurrentSelection,
    duplicateCurrentSelection,
    deleteSelectedItems,
    handleContextPaste,
    moveSelectedLayerQuick
  } = useEditor();

  const menu = canvasContextMenu;
  const runAndClose = (action) => () => {
    action();
    closeCanvasContextMenu();
  };

  const itemClass = (danger = false) =>
    `h-9 px-3 rounded-[8px] border border-transparent bg-sunken ${danger ? 'text-danger' : 'text-ink'} hover:bg-pressed active:bg-pressed flex items-center gap-2 text-xs font-semibold`;

  const MenuItem = ({ icon, label, hint, danger = false, onClick }) => (
    <button type="button" onClick={onClick} className={itemClass(danger)}>
      {icon}
      <span className="flex-1 text-left">{label}</span>
      {hint && <span className="text-[10px] font-mono text-muted">{hint}</span>}
    </button>
  );

  return (
    <Popover
      open={!!menu}
      onOpenChange={(next) => { if (!next) closeCanvasContextMenu(); }}
      virtualAnchor={menu ? { x: menu.x, y: menu.y } : null}
      placement="top"
      offsetPx={8}
      guardOutsidePressMs={400}
    >
      <div
        role="menu"
        aria-label="Canvas actions"
        className="bg-raised border border-edge rounded-[12px] shadow-menu p-1.5 w-48"
      >
        <div className="flex flex-col gap-1">
          {menu?.type === 'actions' && (
            <>
              <MenuItem icon={<Copy size={14} />} label="Copy" hint="Ctrl+C" onClick={runAndClose(copyCurrentSelection)} />
              <MenuItem icon={<Scissors size={14} />} label="Cut" hint="Ctrl+X" onClick={runAndClose(cutCurrentSelection)} />
              <MenuItem icon={<Plus size={14} />} label="Duplicate" onClick={runAndClose(duplicateCurrentSelection)} />
              <MenuItem icon={<Trash2 size={14} />} label="Delete" hint="Del" danger onClick={runAndClose(deleteSelectedItems)} />
              <div className="h-px bg-edge mx-1 my-0.5" />
              <MenuItem
                icon={<ArrowUp size={14} />}
                label="Bring forward"
                onClick={runAndClose(() => {
                  if (menu.targetLayerId) moveSelectedLayerQuick(menu.targetLayerId, 'up');
                })}
              />
              <MenuItem
                icon={<ArrowDown size={14} />}
                label="Send backward"
                onClick={runAndClose(() => {
                  if (menu.targetLayerId) moveSelectedLayerQuick(menu.targetLayerId, 'down');
                })}
              />
            </>
          )}
          {menu?.type === 'paste' && (
            <MenuItem
              icon={<ClipboardPaste size={14} />}
              label="Paste here"
              onClick={() => handleContextPaste(menu.worldX != null ? { x: menu.worldX, y: menu.worldY } : undefined)}
            />
          )}
        </div>
      </div>
    </Popover>
  );
}
