import { run, APP_URL } from './client.mjs';

run(async (page) => {
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });

  // Paste a synthetic PNG; the app's document-level paste handler inserts it as an image.
  await page.evaluate(async () => {
    const canvas = document.createElement('canvas');
    canvas.width = 80; canvas.height = 60;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#ff0000';
    ctx.fillRect(0, 0, 80, 60);
    const blob = await new Promise(res => canvas.toBlob(res, 'image/png'));
    const file = new File([blob], 'test.png', { type: 'image/png' });
    const dt = new DataTransfer();
    dt.items.add(file);
    const ev = new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true });
    document.dispatchEvent(ev);
  });
  await new Promise(r => setTimeout(r, 800)); // image onload + state update

  const report = await page.evaluate(() => {
    const imgs = [...document.querySelectorAll('svg image')];
    return {
      svgImageCount: imgs.length,
      opacities: imgs.map(i => i.getAttribute('opacity') ?? i.style.opacity ?? '(none)')
    };
  });

  await page.screenshot({ path: '/tmp/shots/phase15-image.png' });

  // Clean up: remove pasted image so later checks start clean (fresh storage).
  await page.evaluate(() => localStorage.removeItem('vector-editor-session-v1'));
  return report;
});
