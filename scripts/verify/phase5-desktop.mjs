import { run, APP_URL } from './client.mjs';

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });

  const pathCount = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length
  );
  const pause = (ms = 200) => new Promise(r => setTimeout(r, ms));
  const click = async (x, y) => { await page.mouse.move(x, y); await page.mouse.down(); await page.mouse.up(); };

  // 1. PEN: three corner clicks, then click the start point to close.
  await page.keyboard.press('p'); await pause();
  await click(400, 300); await pause(80);
  await click(560, 280); await pause(80);
  await click(540, 420); await pause(80);
  await click(400, 300); await pause(250); // close on start point
  report.penPaths = await pathCount();

  // 2. PEN curve: click, then click-drag to pull handles, Enter to finish open path.
  await page.keyboard.press('p'); await pause();
  await click(700, 300); await pause(80);
  await page.mouse.move(840, 320); await page.mouse.down();
  await page.mouse.move(900, 380, { steps: 6 }); await page.mouse.up(); await pause(80);
  await page.keyboard.press('Enter'); await pause(250);
  report.penCurvePaths = await pathCount();
  report.curveHasC = await page.evaluate(() => {
    const ds = [...document.querySelectorAll('svg g path[d]')].map(p => p.getAttribute('d'));
    return ds.some(d => /C/.test(d));
  });

  // 3. PENCIL freehand.
  await page.keyboard.press('f'); await pause();
  await page.mouse.move(300, 500); await page.mouse.down();
  for (let i = 1; i <= 12; i++) {
    await page.mouse.move(300 + i * 18, 500 + Math.sin(i / 2) * 60, { steps: 2 });
  }
  await page.mouse.up(); await pause(350);
  report.pencilPaths = await pathCount();

  // 4. SHAPE rect with Shift (square).
  await page.keyboard.press('r'); await pause();
  await page.keyboard.down('Shift');
  await page.mouse.move(900, 500); await page.mouse.down();
  await page.mouse.move(1020, 580, { steps: 5 }); await page.mouse.up();
  await page.keyboard.up('Shift'); await pause(250);
  report.shapePaths = await pathCount();

  // 5. EDIT: marquee-select the square area and drag it.
  await page.keyboard.press('v'); await pause();
  await page.mouse.move(870, 470); await page.mouse.down();
  await page.mouse.move(1060, 640, { steps: 5 }); await page.mouse.up(); await pause(200);
  const before = await page.evaluate(() => {
    const ds = [...document.querySelectorAll('svg g path[d]')].map(p => p.getAttribute('d'));
    return ds[ds.length - 1];
  });
  await page.mouse.move(960, 540); await page.mouse.down();
  await page.mouse.move(1010, 590, { steps: 6 }); await page.mouse.up(); await pause(250);
  const after = await page.evaluate(() => {
    const ds = [...document.querySelectorAll('svg g path[d]')].map(p => p.getAttribute('d'));
    return ds[ds.length - 1];
  });
  report.dragMovedPath = before !== after;

  // 6. Undo chain: every op above unwinds without errors.
  for (let i = 0; i < 6; i++) {
    await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
    await pause(120);
  }
  report.pathsAfterUndoChain = await pathCount();

  // 7. Redo twice.
  for (let i = 0; i < 2; i++) {
    await page.keyboard.down('Control'); await page.keyboard.press('y'); await page.keyboard.up('Control');
    await pause(120);
  }
  report.pathsAfterRedo = await pathCount();

  await page.screenshot({ path: '/tmp/shots/phase5-desktop.png' });
  return report;
});
