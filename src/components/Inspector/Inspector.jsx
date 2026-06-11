import { useEditor } from '../../state/EditorContext';
import FillSection from './FillSection';
import StrokeSection from './StrokeSection';
import TransformSection from './TransformSection';
import TextSection from './TextSection';

// Unified selection-aware panel body: path fill/stroke for path (or empty)
// selections, transform for images, font + transform for texts. Section
// visibility is driven entirely by the useInspectorModel shape.
export default function Inspector() {
  const { inspector } = useEditor();
  const { kind, fill, stroke, transform, text } = inspector;

  return (
    <div className="p-3.5 flex flex-col gap-3">
      {fill && <FillSection />}
      {stroke && <StrokeSection />}
      {text && <TextSection />}
      {transform && <TransformSection />}

      {kind === 'none' && (
        <p className="text-[10px] text-[#98a2b3] px-1">
          Nothing selected — edits set the style for the next drawn path.
        </p>
      )}
      {kind === 'mixed' && fill && (
        <p className="text-[10px] text-[#98a2b3] px-1">
          Fill &amp; stroke apply to the selected paths.
        </p>
      )}
      {kind === 'mixed' && !fill && (
        <p className="text-[10px] text-[#98a2b3] px-1">
          Mixed selection — no shared properties to edit.
        </p>
      )}
    </div>
  );
}
