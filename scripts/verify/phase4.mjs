import { run, APP_URL } from './client.mjs';

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });

  const countVisiblePaths = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length
  );

  // Draw two shapes -> two layers.
  await page.keyboard.press('r');
  await page.mouse.move(400, 250); await page.mouse.down();
  await page.mouse.move(550, 360, { steps: 6 }); await page.mouse.up();
  await new Promise(r => setTimeout(r, 200));
  await page.keyboard.press('o'); // ellipse
  await page.mouse.move(650, 300); await page.mouse.down();
  await page.mouse.move(800, 430, { steps: 6 }); await page.mouse.up();
  await new Promise(r => setTimeout(r, 250));
  report.pathsAfterTwoShapes = await countVisiblePaths();

  // Open layers panel via its toolbar button, expand it.
  await page.click('button[aria-label="Layers"]');
  await new Promise(r => setTimeout(r, 300));
  report.layerRows = await page.evaluate(() =>
    document.querySelectorAll('button[title="Hide Layer"], button[title="Show Layer"]').length
  );

  // Hide the first layer -> one path disappears.
  await page.evaluate(() => document.querySelectorAll('button[title="Hide Layer"]')[0]?.click());
  await new Promise(r => setTimeout(r, 250));
  report.pathsAfterHide = await countVisiblePaths();

  // Show it again.
  await page.evaluate(() => document.querySelector('button[title="Show Layer"]')?.click());
  await new Promise(r => setTimeout(r, 250));
  report.pathsAfterShow = await countVisiblePaths();

  // Lock the first layer.
  await page.evaluate(() => document.querySelectorAll('button[title="Lock Layer"]')[0]?.click());
  await new Promise(r => setTimeout(r, 200));
  report.lockedBadge = await page.evaluate(() =>
    document.querySelectorAll('button[title="Unlock Layer"]').length
  );
  await page.evaluate(() => document.querySelector('button[title="Unlock Layer"]')?.click());

  // Delete the second layer (with content) -> path count drops, undo restores.
  await page.evaluate(() => document.querySelectorAll('button[title="Delete Layer"]')[1]?.click());
  await new Promise(r => setTimeout(r, 250));
  report.pathsAfterLayerDelete = await countVisiblePaths();
  await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
  await new Promise(r => setTimeout(r, 250));
  report.pathsAfterUndoDelete = await countVisiblePaths();

  // Session round trip with layers.
  await new Promise(r => setTimeout(r, 500));
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await new Promise(r => setTimeout(r, 300));
  report.afterReload = await countVisiblePaths();
  report.sessionLayerCount = await page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? (JSON.parse(raw).layers || []).length : null;
  });

  await page.screenshot({ path: '/tmp/shots/phase4-layers.png' });
  await page.evaluate(() => localStorage.clear());
  return report;
});
