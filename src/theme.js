// --- THEME ---
// Canvas-side colors rendered through SVG presentation attributes, which
// cannot read CSS variables. UI chrome colors live as CSS variables in
// index.css (:root) and are exposed as Tailwind tokens in tailwind.config.js
// — keep the two in sync when retuning the palette. Dark theme modeled on
// Figma's UI (canvas #1e1e1e, accent #0d99ff, white anchors).
export const THEME = {
  main: "#ffffff",        // node/anchor ink + pen preview
  nodeFill: "#1e1e1e",
  bg: "#1e1e1e",          // page tone + JPG export background
  handle: "#b3b3b3",
  ghost: "#8c8c8c",
  gridline: "#383838",
  gridlineStrong: "#8c8c8c",
  accent: "#0d99ff",      // selection chrome
  accentStrong: "#4cb2ff",
  accentFaint: "rgba(13, 153, 255, 0.05)",
  success: "#10b981",
  successStrong: "#059669",
  marqueeFill: "rgba(255, 255, 255, 0.06)"
};
