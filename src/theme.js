// --- THEME ---
// Canvas-side colors rendered through SVG presentation attributes, which
// cannot read CSS variables. UI chrome colors live as CSS variables in
// index.css (:root) and are exposed as Tailwind tokens in tailwind.config.js
// — keep the two in sync when retuning the palette.
export const THEME = {
  main: "#344054",        // node/anchor ink
  nodeFill: "#e4e7ec",
  bg: "#f2f4f7",          // page tone + JPG export background
  handle: "#667085",
  ghost: "#98a2b3",
  gridline: "#d0d5dd",
  gridlineStrong: "#667085",
  accent: "#3b82f6",      // selection chrome
  accentStrong: "#2563eb",
  accentFaint: "rgba(59, 130, 246, 0.03)",
  success: "#10b981",
  successStrong: "#059669",
  marqueeFill: "rgba(74, 38, 34, 0.08)"
};
