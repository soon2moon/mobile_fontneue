/** @type {import('tailwindcss').Config} */
// Color tokens resolve through the CSS variables defined in src/index.css
// (:root). RGB-triplet form so Tailwind opacity modifiers keep working
// (e.g. bg-scrim/[0.08], hover:bg-edge/50).
export default {
  content: ['./index.html', './src/**/*.{js,ts,jsx,tsx}'],
  theme: {
    extend: {
      colors: {
        canvas: 'rgb(var(--color-canvas) / <alpha-value>)',
        raised: 'rgb(var(--color-raised) / <alpha-value>)',
        sunken: 'rgb(var(--color-sunken) / <alpha-value>)',
        pressed: 'rgb(var(--color-pressed) / <alpha-value>)',
        edge: 'rgb(var(--color-edge) / <alpha-value>)',
        'edge-strong': 'rgb(var(--color-edge-strong) / <alpha-value>)',
        ink: 'rgb(var(--color-ink) / <alpha-value>)',
        secondary: 'rgb(var(--color-secondary) / <alpha-value>)',
        muted: 'rgb(var(--color-muted) / <alpha-value>)',
        accent: 'rgb(var(--color-accent) / <alpha-value>)',
        'accent-strong': 'rgb(var(--color-accent-strong) / <alpha-value>)',
        danger: 'rgb(var(--color-danger) / <alpha-value>)',
        'danger-bg': 'rgb(var(--color-danger-bg) / <alpha-value>)',
        chip: 'rgb(var(--color-chip) / <alpha-value>)',
        tooltip: 'rgb(var(--color-tooltip) / <alpha-value>)',
        'tooltip-ink': 'rgb(var(--color-tooltip-ink) / <alpha-value>)',
        'tooltip-chip': 'rgb(var(--color-tooltip-chip) / <alpha-value>)',
        scrim: 'rgb(var(--color-scrim) / <alpha-value>)'
      },
      boxShadow: {
        card: '0 14px 28px rgb(var(--color-shadow) / 0.45)',
        menu: '0 12px 24px rgb(var(--color-shadow) / 0.45)',
        popover: '0 14px 28px rgb(var(--color-shadow) / 0.5)',
        sheet: '0 14px 32px rgb(var(--color-shadow) / 0.45)',
        float: '0 12px 28px rgb(var(--color-shadow) / 0.45)'
      }
    }
  },
  plugins: []
};
