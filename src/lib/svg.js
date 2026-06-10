export const escapeXml = (value) => String(value)
  .replace(/&/g, '&amp;')
  .replace(/"/g, '&quot;')
  .replace(/'/g, '&apos;')
  .replace(/</g, '&lt;')
  .replace(/>/g, '&gt;');

export const toSafeSvgId = (value) => String(value).replace(/[^a-zA-Z0-9_-]/g, '_');

export const generateEditGroupId = () => `group-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
