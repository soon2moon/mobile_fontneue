import { run, APP_URL } from './client.mjs';

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });

  const countPaths = () => page.evaluate(() => {
    // Count real geometry paths inside the canvas (exclude UI/icons): the pan/zoom <g> holds them.
    const svg = document.querySelector('svg.touch-none, svg');
    return svg ? [...svg.querySelectorAll('g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length : 0;
  });

  report.initialPaths = await countPaths();

  // Rectangle tool via 'r', then drag on canvas.
  await page.keyboard.press('r');
  await new Promise(r => setTimeout(r, 150));
  await page.mouse.move(500, 300);
  await page.mouse.down();
  await page.mouse.move(700, 450, { steps: 8 });
  await page.mouse.up();
  await new Promise(r => setTimeout(r, 300));
  report.afterRectDraw = await countPaths();

  // Undo / redo round trip.
  await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
  await new Promise(r => setTimeout(r, 200));
  report.afterUndo = await countPaths();
  await page.keyboard.down('Control'); await page.keyboard.press('y'); await page.keyboard.up('Control');
  await new Promise(r => setTimeout(r, 200));
  report.afterRedo = await countPaths();

  // Session round trip.
  await new Promise(r => setTimeout(r, 500)); // allow save effect
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await new Promise(r => setTimeout(r, 300));
  report.afterReload = await countPaths();
  report.sessionPathCount = await page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? (JSON.parse(raw).paths || []).length : null;
  });

  await page.screenshot({ path: '/tmp/shots/smoke-draw.png' });
  return report;
});
