import { Layers, SlidersHorizontal, Grid3x3, Download } from 'lucide-react';

export const PANELS_CONFIG = [
  { id: 'layers', title: 'Layers', icon: Layers },
  { id: 'inspector', title: 'Design', icon: SlidersHorizontal },
  { id: 'grid', title: 'Canvas Grid', icon: Grid3x3 },
  { id: 'export', title: 'Export', icon: Download }
];

export const CLOSED_PANELS = { grid: false, inspector: false, layers: false, export: false };
