// --- THEME ---
// Canvas-side colors rendered through SVG presentation attributes, which
// cannot read CSS variables. UI chrome colors live as CSS variables in
// index.css (:root) and are exposed as Tailwind tokens in tailwind.config.js
// — keep the two in sync when retuning the palette. Modeled on Figma: an
// off-white canvas (#f5f5f5) with #2c2c2c chrome and a #007eea accent. Anchors
// are dark with white centers so they read against the light canvas.
export const THEME = {
  main: "#1e1e1e",        // node/anchor ink + pen preview (dark on light canvas)
  nodeFill: "#ffffff",    // anchor center, inside the dark ring
  bg: "#f5f5f5",          // page tone + JPG export background (matches canvas)
  handle: "#8c8c8c",      // frame name label
  ghost: "#8c8c8c",
  gridline: "#e0e0e0",
  gridlineStrong: "#bdbdbd",
  accent: "#007eea",      // selection chrome + active elements
  accentStrong: "#339bff",
  accentFaint: "rgba(0, 126, 234, 0.08)",
  success: "#10b981",
  successStrong: "#059669",
  marqueeFill: "rgba(0, 126, 234, 0.08)"
};
