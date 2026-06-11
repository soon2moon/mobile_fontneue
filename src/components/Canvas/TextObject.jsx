import { getTextLocalLayout } from '../../lib/textMeasure';

// Live SVG text object: <text>/<tspan> lines laid out around the object's
// world-space center, plus optional edit-mode selection chrome mirroring the
// image pattern in Canvas.jsx. Also reused for layer thumbnail previews
// (chrome off, zoom irrelevant).
export default function TextObject({ text, zoom = 1, showSelectionChrome = false, showHandles = false }) {
  const layout = getTextLocalLayout(text);

  return (
    <g transform={`translate(${text.x}, ${text.y}) rotate(${text.rotation})`}>
      <text
        fill={text.fill}
        opacity={text.opacity}
        fontSize={text.fontSize}
        fontFamily={text.fontFamily}
        fontWeight={text.fontWeight}
        xmlSpace="preserve"
        pointerEvents="none"
      >
        {layout.lines.map((line, index) => (
          <tspan key={index} x={line.x} y={line.y}>{line.text}</tspan>
        ))}
      </text>

      {showSelectionChrome && (
        <g pointerEvents="none">
          <rect
            x={-layout.halfW}
            y={-layout.halfH}
            width={layout.halfW * 2}
            height={layout.halfH * 2}
            fill="none"
            stroke="#3b82f6"
            strokeWidth={1.5 / zoom}
          />
          {showHandles && [
            { x: -1, y: -1 }, { x: 1, y: -1 }, { x: 1, y: 1 }, { x: -1, y: 1 }
          ].map((c, index) => (
            <rect
              key={index}
              x={(c.x * layout.halfW) - 4 / zoom}
              y={(c.y * layout.halfH) - 4 / zoom}
              width={8 / zoom}
              height={8 / zoom}
              fill="white"
              stroke="#3b82f6"
              strokeWidth={1.5 / zoom}
            />
          ))}
        </g>
      )}
    </g>
  );
}
