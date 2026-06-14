import { useEditor } from '../../state/EditorContext';
import { THEME } from '../../theme';
import { PIXEL_GRID_MIN_ZOOM } from '../../constants';
import { pointsToPath, isCorner, getPathStrokeStyle, resolvePathEditGroupId } from '../../lib/paths';
import { toSafeSvgId } from '../../lib/svg';
import { generateShapePath } from '../../lib/shapes';
import TextObject from './TextObject';

// The drawing surface: background grid patterns, the pan/zoom world group
// (images, paths, nodes/handles, previews, selection chrome), and the
// pixel-grid overlay. All pointer events enter here.
export default function Canvas() {
  const {
activeEditGroupId,
    compositeFillGroups,
    currentPath,
    currentPathInfo,
    defaultStrokeEnabled,
    defaultStrokeRenderColor,
    defaultStrokeRenderWidth,
    drawHover,
    drawingFrame,
    drawingShape,
    dynamicCursor,
    editingTextId,
    effectiveCircularStep,
    effectiveGridSize,
    frames,
    ghostPoint,
    gridConfig,
    handleCanvasContextMenu,
    handlePointerDown,
    handlePointerMove,
    handlePointerUp,
    hoveredHandle,
    hoveredStartPoint,
    images,
    isDrawingCurve,
    isMobile,
    isPathInActiveEditContext,
    layers,
    livePathStroke,
    livePathStrokeRenderWidth,
    mode,
    pan,
    pathStyleDefaults,
    paths,
    pointAction,
    selBBox,
    selectedFrameIds,
    selectedImageIds,
    selectedPoints,
    selectionBox,
    selectedTextIds,
    setHoveredHandle,
    shapeType,
    showBackgroundAids,
    showNodes,
    strokeWidth,
    svgRef,
    texts,
    zoom
  } = useEditor();

  // --- DYNAMIC PATTERN GENERATION ---
  const circularRayCount = Math.max(1, Math.ceil(360 / effectiveCircularStep));
  const s = effectiveGridSize;
  let patternW = s;
  let patternH = s;
  let patternContent = null;
  const showPixelGrid = zoom >= PIXEL_GRID_MIN_ZOOM;
  const showBackgroundGridPattern = showBackgroundAids && gridConfig.type !== 'none' && gridConfig.type !== 'circular';
  const showCircularGrid = showBackgroundAids && gridConfig.type === 'circular';
  const showPixelGridOverlay = showBackgroundAids && showPixelGrid;

  if (gridConfig.type === 'dots') {
    patternW = s;
    patternH = s;
    patternContent = <circle cx={1/zoom} cy={1/zoom} r={1.5/zoom} fill={THEME.gridline} />;
  } else if (gridConfig.type === 'circles') {
    patternW = s;
    patternH = s;
    patternContent = <circle cx={s/2} cy={s/2} r={s / 2} fill="none" stroke={THEME.gridline} strokeWidth={1/zoom} />;
  } else if (gridConfig.type === 'lines') {
    if (gridConfig.edges === 4) {
      patternW = s;
      patternH = s;
      patternContent = <path d={`M ${s} 0 L 0 0 L 0 ${s}`} fill="none" stroke={THEME.gridline} strokeWidth={1/zoom} />;
    } else if (gridConfig.edges === 3) {
      patternW = s;
      patternH = s * Math.sqrt(3);
      patternContent = <path d={`M 0 0 L ${patternW} 0 M 0 ${patternH/2} L ${patternW} ${patternH/2} M 0 ${patternH/2} L ${patternW/2} 0 M ${patternW/2} ${patternH} L ${patternW} ${patternH/2} M ${patternW/2} 0 L ${patternW} ${patternH/2} M 0 ${patternH/2} L ${patternW/2} ${patternH}`} fill="none" stroke={THEME.gridline} strokeWidth={1/zoom} />;
    } else if (gridConfig.edges === 6) {
      patternW = s * Math.sqrt(3);
      patternH = s * 3;
      patternContent = <path d={`M 0 ${0.5*s} L ${patternW/2} 0 L ${patternW} ${0.5*s} L ${patternW} ${1.5*s} L ${patternW/2} ${2*s} L 0 ${1.5*s} Z M ${patternW/2} ${2*s} L ${patternW/2} ${3*s}`} fill="none" stroke={THEME.gridline} strokeWidth={1/zoom} />;
    }
  }

  return (
      <svg 
        ref={svgRef}
        className={`w-full h-full ${dynamicCursor}`}
        onPointerDown={handlePointerDown}
        onPointerMove={handlePointerMove}
        onPointerUp={handlePointerUp}
        onPointerCancel={handlePointerUp}
        onContextMenu={handleCanvasContextMenu}
      >
        <defs>
          {showPixelGridOverlay && (
            <pattern
              id="pixel-grid"
              width={zoom}
              height={zoom}
              patternUnits="userSpaceOnUse"
              patternTransform={`translate(${pan.x}, ${pan.y})`}
            >
              <g transform={`scale(${zoom})`}>
                <path
                  d="M 1 0 L 0 0 L 0 1"
                  fill="none"
                  stroke={THEME.gridlineStrong}
                  strokeOpacity="0.22"
                  strokeWidth={1 / zoom}
                />
              </g>
            </pattern>
          )}
        </defs>

        {/* Transform Group for Pan & Zoom */}
        <g transform={`translate(${pan.x}, ${pan.y}) scale(${zoom})`}>

          {/* Frames (artboards) paint below ALL content; the design grid is
              contained inside each frame (Figma-style); names stay screen-sized */}
          {layers.slice().reverse().map(layer => {
            if (!layer.visible) return null;
            return (
              <g key={`frame-layer-${layer.id}`}>
                {frames.map(frame => {
                  if (frame.layerId !== layer.id) return null;
                  const fl = frame.x - frame.width / 2;
                  const ft = frame.y - frame.height / 2;
                  const frameSvgId = toSafeSvgId(frame.id);
                  const frameDiag = Math.hypot(frame.width, frame.height);
                  return (
                    <g key={`frame-${frame.id}`} pointerEvents="none">
                      <rect x={fl} y={ft} width={frame.width} height={frame.height} fill={frame.fill} />

                      {/* Design grid: tiled from the frame's top-left, clipped to the frame rect */}
                      {showBackgroundGridPattern && (
                        <>
                          <defs>
                            <pattern
                              id={`fg-${frameSvgId}`}
                              x={fl}
                              y={ft}
                              width={patternW}
                              height={patternH}
                              patternUnits="userSpaceOnUse"
                            >
                              {patternContent}
                            </pattern>
                          </defs>
                          <rect x={fl} y={ft} width={frame.width} height={frame.height} fill={`url(#fg-${frameSvgId})`} />
                        </>
                      )}
                      {showCircularGrid && (
                        <g className="opacity-60">
                          <defs>
                            <clipPath id={`fgc-${frameSvgId}`}>
                              <rect x={fl} y={ft} width={frame.width} height={frame.height} />
                            </clipPath>
                          </defs>
                          <g clipPath={`url(#fgc-${frameSvgId})`}>
                            {Array.from({ length: Math.ceil(frameDiag / (2 * s)) + 1 }).map((_, i) => (
                              <circle key={`fgc-c-${i}`} cx={frame.x} cy={frame.y} r={(i + 1) * s} stroke={THEME.gridline} strokeWidth={1 / zoom} fill="none" />
                            ))}
                            {Array.from({ length: circularRayCount }).map((_, i) => {
                              const angle = (i * effectiveCircularStep * Math.PI) / 180;
                              return (
                                <line
                                  key={`fgc-r-${i}`}
                                  x1={frame.x - frameDiag * Math.cos(angle)}
                                  y1={frame.y - frameDiag * Math.sin(angle)}
                                  x2={frame.x + frameDiag * Math.cos(angle)}
                                  y2={frame.y + frameDiag * Math.sin(angle)}
                                  stroke={THEME.gridline}
                                  strokeWidth={1 / zoom}
                                />
                              );
                            })}
                          </g>
                        </g>
                      )}

                      <text
                        x={fl}
                        y={ft - 6 / zoom}
                        fontSize={11 / zoom}
                        fill={THEME.handle}
                        style={{ userSelect: 'none' }}
                      >
                        {frame.name}
                      </text>
                    </g>
                  );
                })}
              </g>
            );
          })}

          {/* Global Composite Fills (one winding-based path per fill color, layer paint order) */}
          {compositeFillGroups.map(group => (
            <path
              key={group.key}
              d={group.d}
              fill={group.color}
              fillOpacity={group.opacity}
              fillRule="nonzero"
            />
          ))}

          {/* Finished Paths and Layer-bound Images */}
          {layers.slice().reverse().map(layer => {
            if (!layer.visible) return null;

            return (
            <g key={`layer-group-${layer.id}`}>
              
              {/* Layer Images */}
              {images.map(img => {
                if (img.layerId !== layer.id) return null;
                return (
                  <g key={img.id}>
                    <image
                      href={img.url}
                      x={-img.width / 2}
                      y={-img.height / 2}
                      width={img.width}
                      height={img.height}
                      opacity={img.opacity}
                      imageRendering={showPixelGridOverlay ? 'pixelated' : 'auto'}
                      style={showPixelGridOverlay ? { imageRendering: 'pixelated' } : undefined}
                      pointerEvents="none"
                      transform={`translate(${img.x}, ${img.y}) scale(${img.scale}) rotate(${img.rotation})`}
                    />

                    {/* Bounding Box for active edit mode image */}
                    {selectedImageIds.includes(img.id) && !layer.locked && !img.locked && mode === 'edit' && (
                       <g transform={`translate(${img.x}, ${img.y}) rotate(${img.rotation})`} pointerEvents="none">
                           <rect
                               x={-img.width * img.scale / 2}
                               y={-img.height * img.scale / 2}
                               width={img.width * img.scale}
                               height={img.height * img.scale}
                               fill="none"
                               stroke={THEME.accent} 
                               strokeWidth={1.5/zoom}
                           />
                           {selectedImageIds.length === 1 && selectedTextIds.length === 0 && [
                             {x: -1, y: -1}, {x: 1, y: -1}, {x: 1, y: 1}, {x: -1, y: 1}
                           ].map((c, i) => (
                               <rect
                                 key={i}
                                 x={(c.x * img.width * img.scale / 2) - 4/zoom}
                                 y={(c.y * img.height * img.scale / 2) - 4/zoom}
                                 width={8/zoom}
                                 height={8/zoom}
                                 fill="white"
                                 stroke={THEME.accent}
                                 strokeWidth={1.5/zoom}
                               />
                           ))}
                       </g>
                    )}
                  </g>
                );
              })}

              {/* Layer Texts (the one being edited renders in the overlay instead) */}
              {texts.map(text => {
                if (text.layerId !== layer.id) return null;
                if (text.id === editingTextId) return null;
                return (
                  <TextObject
                    key={text.id}
                    text={text}
                    zoom={zoom}
                    showSelectionChrome={selectedTextIds.includes(text.id) && !layer.locked && !text.locked && mode === 'edit'}
                    showHandles={selectedTextIds.length === 1 && selectedImageIds.length === 0}
                  />
                );
              })}

              {/* Layer Paths */}
              {paths.map((path, i) => {
                if (path.layerId !== layer.id) return null;
                if (mode === 'draw' && currentPath.length > 0 && currentPathInfo?.resumePathId === path.id) return null;
                const pathD = pointsToPath(path.points, path.isClosed);
                const isSinglePointPath = path.points.length === 1;
                const pathStroke = getPathStrokeStyle(path);
                const renderStrokeWidth = pathStroke.strokeWidth / zoom;
                const canOffsetStroke = pathStroke.strokeEnabled && path.isClosed && !isSinglePointPath;
                const effectiveStrokeAlign = canOffsetStroke ? pathStroke.strokeAlign : 'center';
                const strokeRenderIdBase = `stroke-${toSafeSvgId(path.id)}-${i}`;

                return (
                  <g key={path.id}>
                    {/* Path ink — opacity group fades the fill/stroke without
                        touching the editing handles rendered below. */}
                    <g strokeOpacity={pathStroke.strokeOpacity} fillOpacity={pathStroke.strokeOpacity}>
                    {isSinglePointPath ? (
                      pathStroke.strokeEnabled ? (
                        <circle
                          cx={path.points[0].x}
                          cy={path.points[0].y}
                          r={Math.max(2, pathStroke.strokeWidth * 1.5) / zoom}
                          fill={pathStroke.strokeColor}
                          stroke={pathStroke.strokeColor}
                          strokeWidth={1 / zoom}
                          vectorEffect="non-scaling-stroke"
                        />
                      ) : null
                    ) : (
                      <>
                        {pathStroke.strokeEnabled && effectiveStrokeAlign === 'inside' && (
                          <>
                            <defs>
                              <clipPath id={`${strokeRenderIdBase}-inside-clip`}>
                                <path d={pathD} />
                              </clipPath>
                            </defs>
                            <path
                              d={pathD}
                              fill="none"
                              stroke={pathStroke.strokeColor}
                              strokeWidth={(renderStrokeWidth * 2)}
                              strokeLinejoin="round"
                              strokeLinecap="round"
                              clipPath={`url(#${strokeRenderIdBase}-inside-clip)`}
                            />
                          </>
                        )}
                        {pathStroke.strokeEnabled && effectiveStrokeAlign === 'outside' && (
                          <>
                            <defs>
                              <mask id={`${strokeRenderIdBase}-outside-mask`}>
                                <rect x="-200000" y="-200000" width="400000" height="400000" fill="white" />
                                <path d={pathD} fill="black" />
                              </mask>
                            </defs>
                            <path
                              d={pathD}
                              fill="none"
                              stroke={pathStroke.strokeColor}
                              strokeWidth={(renderStrokeWidth * 2)}
                              strokeLinejoin="round"
                              strokeLinecap="round"
                              mask={`url(#${strokeRenderIdBase}-outside-mask)`}
                            />
                          </>
                        )}
                        {pathStroke.strokeEnabled && effectiveStrokeAlign === 'center' && (
                          <path
                            d={pathD}
                            fill="none"
                            stroke={pathStroke.strokeColor}
                            strokeWidth={renderStrokeWidth}
                            strokeLinejoin="round"
                            strokeLinecap="round"
                          />
                        )}
                      </>
                    )}
                    
                    </g>
                    {/* Nodes and Handles (controlled by Show Nodes, hidden only in pencil mode, and when unlocked) */}
                    {showNodes && (mode === 'edit' || mode === 'draw') && !layer.locked && activeEditGroupId != null && isPathInActiveEditContext(path) && (
                      <g>
                        {/* Draw Bezier Handles for ALL Points (Persistent) */}
                        {path.points.map((p, j) => {
                          const hasIn = p.hIn && Math.hypot(p.hIn.x - p.x, p.hIn.y - p.y) > 0.1;
                          const hasOut = p.hOut && Math.hypot(p.hOut.x - p.x, p.hOut.y - p.y) > 0.1;
                          const inHovered = hoveredHandle?.pathIndex === i && hoveredHandle?.pointIndex === j && hoveredHandle?.type === 'hIn';
                          const outHovered = hoveredHandle?.pathIndex === i && hoveredHandle?.pointIndex === j && hoveredHandle?.type === 'hOut';
                          
                          return (
                            <g key={`handles-${j}`}>
                              {hasIn && (
                                <g
                                  className="cursor-pointer"
                                  onPointerEnter={() => setHoveredHandle({ pathIndex: i, pointIndex: j, type: 'hIn' })}
                                  onPointerLeave={() => setHoveredHandle(prev => (
                                    prev?.pathIndex === i && prev?.pointIndex === j && prev?.type === 'hIn' ? null : prev
                                  ))}
                                >
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hIn.x}
                                    y2={p.hIn.y}
                                    stroke={inHovered ? THEME.accentStrong : THEME.main}
                                    strokeWidth={(inHovered ? 1.1 : 0.8) / zoom}
                                    className="transition-all duration-150"
                                  />
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hIn.x}
                                    y2={p.hIn.y}
                                    stroke="rgba(0,0,0,0)"
                                    strokeWidth={(isMobile ? 16 : 10) / zoom}
                                    pointerEvents="stroke"
                                  />
                                  <circle
                                    cx={p.hIn.x}
                                    cy={p.hIn.y}
                                    r={2.5 / zoom}
                                    fill={inHovered ? "white" : THEME.nodeFill}
                                    stroke={inHovered ? THEME.accentStrong : THEME.main}
                                    strokeWidth={1 / zoom}
                                    className="transition-colors duration-150"
                                  />
                                </g>
                              )}
                              {hasOut && (
                                <g
                                  className="cursor-pointer"
                                  onPointerEnter={() => setHoveredHandle({ pathIndex: i, pointIndex: j, type: 'hOut' })}
                                  onPointerLeave={() => setHoveredHandle(prev => (
                                    prev?.pathIndex === i && prev?.pointIndex === j && prev?.type === 'hOut' ? null : prev
                                  ))}
                                >
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hOut.x}
                                    y2={p.hOut.y}
                                    stroke={outHovered ? THEME.accentStrong : THEME.main}
                                    strokeWidth={(outHovered ? 1.1 : 0.8) / zoom}
                                    className="transition-all duration-150"
                                  />
                                  <line
                                    x1={p.x}
                                    y1={p.y}
                                    x2={p.hOut.x}
                                    y2={p.hOut.y}
                                    stroke="rgba(0,0,0,0)"
                                    strokeWidth={(isMobile ? 16 : 10) / zoom}
                                    pointerEvents="stroke"
                                  />
                                  <circle
                                    cx={p.hOut.x}
                                    cy={p.hOut.y}
                                    r={2.5 / zoom}
                                    fill={outHovered ? "white" : THEME.nodeFill}
                                    stroke={outHovered ? THEME.accentStrong : THEME.main}
                                    strokeWidth={1 / zoom}
                                    className="transition-colors duration-150"
                                  />
                                </g>
                              )}
                            </g>
                          );
                        })}
                        
                        {/* Draw Anchor Points (Squares for corners, Circles for smooth) */}
                        {path.points.map((p, j) => {
                          const isSelected = selectedPoints.some(sp => sp.pathIndex === i && sp.pointIndex === j);
                          const corner = isCorner(p);
                          const fill = isSelected ? THEME.main : THEME.nodeFill;
                          
                          if (corner) {
                            return (
                              <rect 
                                key={`anchor-${j}`} 
                                x={p.x - 3.5/zoom} 
                                y={p.y - 3.5/zoom} 
                                width={7/zoom} 
                                height={7/zoom} 
                                fill={fill} 
                                stroke={THEME.main} 
                                strokeWidth={1.5/zoom}
                                className=""
                              />
                            );
                          } else {
                            return (
                              <circle 
                                key={`anchor-${j}`} 
                                cx={p.x} 
                                cy={p.y} 
                                r={3.5/zoom} 
                                fill={fill} 
                                stroke={THEME.main} 
                                strokeWidth={1.5/zoom}
                                className=""
                              />
                            );
                          }
                        })}
                      </g>
                    )}
                  </g>
                );
              })}
            </g>
          )})}

          {/* Frame selection chrome + corner handles (above all content) */}
          {mode === 'edit' && frames.map(frame => {
            if (!selectedFrameIds.includes(frame.id)) return null;
            const frameLayer = layers.find(l => l.id === frame.layerId);
            if (!frameLayer || !frameLayer.visible || frameLayer.locked || frame.locked) return null;
            const frameLeft = frame.x - frame.width / 2;
            const frameTop = frame.y - frame.height / 2;
            return (
              <g key={`frame-chrome-${frame.id}`} data-frame-chrome={frame.id} pointerEvents="none">
                <rect
                  x={frameLeft}
                  y={frameTop}
                  width={frame.width}
                  height={frame.height}
                  fill="none"
                  stroke={THEME.accent}
                  strokeWidth={1.5 / zoom}
                />
                {selectedFrameIds.length === 1 && [
                  { x: frameLeft, y: frameTop },
                  { x: frameLeft + frame.width, y: frameTop },
                  { x: frameLeft + frame.width, y: frameTop + frame.height },
                  { x: frameLeft, y: frameTop + frame.height }
                ].map((corner, i) => (
                  <rect
                    key={i}
                    x={corner.x - 4 / zoom}
                    y={corner.y - 4 / zoom}
                    width={8 / zoom}
                    height={8 / zoom}
                    fill="white"
                    stroke={THEME.accent}
                    strokeWidth={1.5 / zoom}
                  />
                ))}
              </g>
            );
          })}

          {/* Frame Drawing Preview */}
          {mode === 'frame' && drawingFrame && (
            <rect
              x={Math.min(drawingFrame.startX, drawingFrame.currentX)}
              y={Math.min(drawingFrame.startY, drawingFrame.currentY)}
              width={Math.abs(drawingFrame.currentX - drawingFrame.startX)}
              height={Math.abs(drawingFrame.currentY - drawingFrame.startY)}
              fill={THEME.accentFaint}
              stroke={THEME.accent}
              strokeWidth={1.5 / zoom}
              strokeDasharray={`${4 / zoom} ${4 / zoom}`}
              pointerEvents="none"
            />
          )}

          {/* Drawing Shape Preview (Live Render) */}
          {mode === 'shape' && drawingShape && (
            <path
              d={pointsToPath(
                 generateShapePath(drawingShape.startX, drawingShape.startY, drawingShape.currentX, drawingShape.currentY, shapeType, drawingShape.shiftKey).points, 
                 shapeType !== 'line'
              )}
              fill="none"
              stroke={defaultStrokeEnabled ? defaultStrokeRenderColor : 'none'}
              strokeWidth={defaultStrokeEnabled ? defaultStrokeRenderWidth : 0}
              strokeLinejoin="round"
              strokeLinecap="round"
            />
          )}

          {/* Selection Box (Draw to select multiple) */}
          {selectionBox && mode === 'edit' && (
            <rect
              x={Math.min(selectionBox.startX, selectionBox.currentX)}
              y={Math.min(selectionBox.startY, selectionBox.currentY)}
              width={Math.abs(selectionBox.currentX - selectionBox.startX)}
              height={Math.abs(selectionBox.currentY - selectionBox.startY)}
              fill={THEME.marqueeFill}
              stroke={THEME.accent}
              strokeWidth={1/zoom}
            />
          )}

          {/* Active Selection Bounding Box (Paths) */}
          {(() => {
             let bboxTransform = "";
             if (selBBox && pointAction) {
                if (pointAction.action.startsWith('rotate-')) {
                   bboxTransform = `rotate(${pointAction.angle || 0} ${(selBBox.minX + selBBox.maxX)/2} ${(selBBox.minY + selBBox.maxY)/2})`;
                } else if (pointAction.action.startsWith('scale-')) {
                   const ox = pointAction.origin?.x || 0;
                   const oy = pointAction.origin?.y || 0;
                   const s = pointAction.scale || 1;
                   bboxTransform = `translate(${ox} ${oy}) scale(${s}) translate(${-ox} ${-oy})`;
                }
             }

             return selBBox && mode === 'edit' && !selectionBox && (
                 <g pointerEvents="none" transform={bboxTransform}>
                   <rect
                       x={selBBox.minX}
                       y={selBBox.minY}
                       width={selBBox.maxX - selBBox.minX}
                       height={selBBox.maxY - selBBox.minY}
                       fill={THEME.accentFaint}
                       stroke={THEME.accent}
                       strokeWidth={1.5}
                       vectorEffect="non-scaling-stroke"
                   />
                   {[
                     {x: selBBox.minX, y: selBBox.minY},
                     {x: selBBox.maxX, y: selBBox.minY},
                     {x: selBBox.maxX, y: selBBox.maxY},
                     {x: selBBox.minX, y: selBBox.maxY}
                   ].map((c, i) => (
                       <rect
                         key={`sel-handle-${i}`}
                         x={c.x - 4/zoom}
                         y={c.y - 4/zoom}
                         width={8/zoom}
                         height={8/zoom}
                         fill="white"
                         stroke={THEME.accent}
                         strokeWidth={1.5}
                         vectorEffect="non-scaling-stroke"
                       />
                   ))}
                 </g>
             );
          })()}

          {/* Current Drawing Path */}
          {currentPath.length > 0 && mode !== 'shape' && (
            <g>
              {/* Actual accepted segments */}
              <path 
                d={pointsToPath(currentPath, isDrawingCurve === 'closing')} 
                fill="none" 
                stroke={livePathStroke.strokeEnabled ? livePathStroke.strokeColor : 'none'} 
                strokeWidth={livePathStroke.strokeEnabled ? livePathStrokeRenderWidth : 0}
                strokeLinejoin="round"
                strokeLinecap="round"
              />
              
              {/* Ghost segment to mouse cursor (only for pen tool) */}
              {ghostPoint && !isDrawingCurve && mode === 'draw' && (
                <path 
                  d={`M ${currentPath[currentPath.length - 1].x} ${currentPath[currentPath.length - 1].y} C ${currentPath[currentPath.length - 1].hOut ? currentPath[currentPath.length - 1].hOut.x : currentPath[currentPath.length - 1].x} ${currentPath[currentPath.length - 1].hOut ? currentPath[currentPath.length - 1].hOut.y : currentPath[currentPath.length - 1].y}, ${ghostPoint.x} ${ghostPoint.y}, ${ghostPoint.x} ${ghostPoint.y}`}
                  fill="none"
                  stroke={THEME.ghost} 
                  strokeWidth={strokeWidth}
                  strokeDasharray={`${4/zoom},${4/zoom}`}
                />
              )}

              {/* Handles of the active drawing point (only for pen tool) */}
              {isDrawingCurve && showNodes && mode === 'draw' && (
                <g>
                  {(() => {
                    const activeP = isDrawingCurve === 'closing' ? currentPath[0] : currentPath[currentPath.length - 1];
                    return (
                      <>
                        {activeP.hIn && <line x1={activeP.x} y1={activeP.y} x2={activeP.hIn.x} y2={activeP.hIn.y} stroke={THEME.main} strokeWidth={0.8/zoom} />}
                        {activeP.hOut && <line x1={activeP.x} y1={activeP.y} x2={activeP.hOut.x} y2={activeP.hOut.y} stroke={THEME.main} strokeWidth={0.8/zoom} />}
                        {activeP.hIn && <circle cx={activeP.hIn.x} cy={activeP.hIn.y} r={2.5/zoom} fill={THEME.nodeFill} stroke={THEME.main} strokeWidth={1/zoom} className="cursor-pointer transition-colors duration-150 hover:fill-white hover:stroke-accent-strong" />}
                        {activeP.hOut && <circle cx={activeP.hOut.x} cy={activeP.hOut.y} r={2.5/zoom} fill={THEME.nodeFill} stroke={THEME.main} strokeWidth={1/zoom} className="cursor-pointer transition-colors duration-150 hover:fill-white hover:stroke-accent-strong" />}
                      </>
                    );
                  })()}
                </g>
              )}

              {/* Nodes for current path (only for pen tool to reduce visual noise while freehand drawing) */}
              {showNodes && mode === 'draw' && currentPath.map((p, i) => {
                const corner = isCorner(p);
                const isStart = i === 0;
                
                if (corner) {
                   return (
                     <rect 
                       key={i} 
                       x={p.x - (isStart && hoveredStartPoint ? 4.5/zoom : 3.5/zoom)} 
                       y={p.y - (isStart && hoveredStartPoint ? 4.5/zoom : 3.5/zoom)} 
                       width={isStart && hoveredStartPoint ? 9/zoom : 7/zoom} 
                       height={isStart && hoveredStartPoint ? 9/zoom : 7/zoom} 
                       fill={isStart && hoveredStartPoint ? THEME.success : THEME.nodeFill} 
                       stroke={isStart && hoveredStartPoint ? THEME.successStrong : THEME.main} 
                       strokeWidth={1.5/zoom}
                     />
                   );
                } else {
                   return (
                     <circle 
                       key={i} 
                       cx={p.x} 
                       cy={p.y} 
                       r={isStart && hoveredStartPoint ? 5/zoom : 3.5/zoom} 
                       fill={isStart && hoveredStartPoint ? THEME.success : THEME.nodeFill} 
                       stroke={isStart && hoveredStartPoint ? THEME.successStrong : THEME.main} 
                       strokeWidth={1.5/zoom}
                     />
                   );
                }
              })}
              
              {/* Ghost Node */}
              {ghostPoint && !hoveredStartPoint && !isDrawingCurve && showNodes && mode === 'draw' && (
                <rect x={ghostPoint.x - 3/zoom} y={ghostPoint.y - 3/zoom} width={6/zoom} height={6/zoom} fill={THEME.ghost} />
              )}
            </g>
          )}
          
          {/* Draw Hover Indicator */}
          {drawHover && mode === 'draw' && showNodes && !isDrawingCurve && (
            <circle 
              cx={drawHover.x} 
              cy={drawHover.y} 
              r={drawHover.type === 'endpoint' ? 5/zoom : 4/zoom} 
              fill={drawHover.type === 'endpoint' ? THEME.success : THEME.nodeFill} 
              stroke={drawHover.type === 'endpoint' ? THEME.successStrong : THEME.main} 
              strokeWidth={1.5/zoom}
              className="pointer-events-none"
            />
          )}
        </g>

        {/* Pixel Grid Overlay (Visible from 800%+) */}
        {showPixelGridOverlay && (
          <rect
            width="100%"
            height="100%"
            fill="url(#pixel-grid)"
            pointerEvents="none"
          />
        )}
      </svg>
  );
}
