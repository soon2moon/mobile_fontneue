// Text measurement for live text objects, shared by canvas rendering,
// hit-testing, selection bounds, layer previews, and export (which must also
// measure texts on hidden layers that have no live DOM node).
//
// Line widths are measured on a lazy singleton hidden SVG <text> node at a
// fixed reference size and scaled linearly by fontSize, so continuous
// corner-drag font scaling hits the cache instead of re-measuring per frame.
// The singleton is created at call time (not in an effect) and never torn
// down, which keeps it StrictMode-safe.

const XML_NS = 'http://www.w3.org/XML/1998/namespace';
const SVG_NS = 'http://www.w3.org/2000/svg';
const REFERENCE_SIZE = 100;
const LINE_CACHE_MAX = 500;

// Fallback ascent/descent ratios when fontBoundingBox metrics are unavailable.
const FALLBACK_ASCENT = 0.9;
const FALLBACK_DESCENT = 0.2;

let measureTextNode = null;
const lineWidthCache = new Map();
const fontMetricsCache = new Map();

const getMeasureTextNode = () => {
  if (measureTextNode && measureTextNode.isConnected) return measureTextNode;
  const svg = document.createElementNS(SVG_NS, 'svg');
  svg.setAttribute('aria-hidden', 'true');
  svg.style.position = 'absolute';
  svg.style.left = '-99999px';
  svg.style.top = '0';
  svg.style.width = '0';
  svg.style.height = '0';
  svg.style.overflow = 'hidden';
  const text = document.createElementNS(SVG_NS, 'text');
  text.setAttributeNS(XML_NS, 'xml:space', 'preserve');
  svg.appendChild(text);
  document.body.appendChild(svg);
  measureTextNode = text;
  return text;
};

const measureLineWidthAtReference = (line, fontFamily, fontWeight) => {
  const key = `${fontFamily}|${fontWeight}|${line}`;
  if (lineWidthCache.has(key)) return lineWidthCache.get(key);

  const node = getMeasureTextNode();
  node.setAttribute('font-family', fontFamily);
  node.setAttribute('font-weight', fontWeight);
  node.setAttribute('font-size', REFERENCE_SIZE);
  node.textContent = line;
  const width = line.length === 0 ? 0 : node.getComputedTextLength();

  if (lineWidthCache.size >= LINE_CACHE_MAX) {
    lineWidthCache.delete(lineWidthCache.keys().next().value);
  }
  lineWidthCache.set(key, width);
  return width;
};

// Ascent/descent as ratios of fontSize, measured once per font via canvas 2D.
const getFontMetrics = (fontFamily, fontWeight) => {
  const key = `${fontFamily}|${fontWeight}`;
  if (fontMetricsCache.has(key)) return fontMetricsCache.get(key);

  let ascent = FALLBACK_ASCENT;
  let descent = FALLBACK_DESCENT;
  try {
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d');
    if (ctx) {
      ctx.font = `${fontWeight} ${REFERENCE_SIZE}px ${fontFamily}`;
      const metrics = ctx.measureText('Mg');
      if (Number.isFinite(metrics.fontBoundingBoxAscent) && metrics.fontBoundingBoxAscent > 0) {
        ascent = metrics.fontBoundingBoxAscent / REFERENCE_SIZE;
      }
      if (Number.isFinite(metrics.fontBoundingBoxDescent) && metrics.fontBoundingBoxDescent > 0) {
        descent = metrics.fontBoundingBoxDescent / REFERENCE_SIZE;
      }
    }
  } catch (err) {
    // Keep fallback ratios.
  }
  const result = { ascent, descent };
  fontMetricsCache.set(key, result);
  return result;
};

export const measureTextBlock = (content, { fontSize, fontFamily, fontWeight, lineHeight }) => {
  const rawLines = String(content ?? '').split('\n');
  const scale = fontSize / REFERENCE_SIZE;
  const lines = rawLines.map(text => ({
    text,
    width: measureLineWidthAtReference(text, fontFamily, fontWeight) * scale
  }));
  const width = lines.reduce((max, line) => Math.max(max, line.width), 0);
  const lineHeightPx = fontSize * lineHeight;
  const height = lines.length * lineHeightPx;
  return { width, height, lineHeightPx, lines };
};

// Layout in object-local coordinates with the block centered on the origin:
// per-line tspan x (by textAlign) and baseline y. Used identically by the
// canvas renderer and the SVG export so they stay WYSIWYG.
export const getTextLocalLayout = (text) => {
  const block = measureTextBlock(text.content, text);
  const { ascent, descent } = getFontMetrics(text.fontFamily, text.fontWeight);
  const halfW = block.width / 2;
  const halfH = block.height / 2;
  const innerLeading = (block.lineHeightPx - text.fontSize * (ascent + descent)) / 2;

  const lines = block.lines.map((line, index) => {
    let x = -halfW;
    if (text.textAlign === 'center') x = -line.width / 2;
    else if (text.textAlign === 'right') x = halfW - line.width;
    const y = -halfH + index * block.lineHeightPx + innerLeading + text.fontSize * ascent;
    return { x, y, text: line.text, width: line.width };
  });

  return { halfW, halfH, width: block.width, height: block.height, lineHeightPx: block.lineHeightPx, lines };
};
