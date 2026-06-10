import { run, APP_URL } from './client.mjs';

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });

  const getTransform = () => page.evaluate(() => {
    const g = document.querySelector('svg g[transform]');
    return g ? g.getAttribute('transform') : null;
  });

  report.initialTransform = await getTransform();

  // Wheel zoom at a point — pan/zoom transform must change.
  await page.mouse.move(700, 400);
  await page.mouse.wheel({ deltaY: -480 });
  await new Promise(r => setTimeout(r, 250));
  report.afterWheelZoom = await getTransform();
  report.zoomChanged = report.initialTransform !== report.afterWheelZoom;

  // Image paste still lands centered + full opacity (exercises panRef/zoomRef in async onload).
  await page.evaluate(async () => {
    const canvas = document.createElement('canvas');
    canvas.width = 60; canvas.height = 40;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#00aa44';
    ctx.fillRect(0, 0, 60, 40);
    const blob = await new Promise(res => canvas.toBlob(res, 'image/png'));
    const dt = new DataTransfer();
    dt.items.add(new File([blob], 't.png', { type: 'image/png' }));
    document.dispatchEvent(new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true }));
  });
  await new Promise(r => setTimeout(r, 700));
  report.imageInserted = await page.evaluate(() => document.querySelectorAll('svg image').length === 1);

  // Undo removes the image; redo restores it.
  await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
  await new Promise(r => setTimeout(r, 200));
  report.afterUndoImages = await page.evaluate(() => document.querySelectorAll('svg image').length);
  await page.keyboard.down('Control'); await page.keyboard.press('y'); await page.keyboard.up('Control');
  await new Promise(r => setTimeout(r, 200));
  report.afterRedoImages = await page.evaluate(() => document.querySelectorAll('svg image').length);

  await page.evaluate(() => localStorage.clear());
  return report;
});
