import { run, APP_URL } from './client.mjs';

// Phase 8F.3: frame editing. A click on a frame body selects it; dragging a
// selected frame's body moves it; a corner handle resizes width/height
// independently (non-uniform); dragging the name label of an unselected
// frame selects + moves it; a marquee that crosses content sitting on a
// frame selects the CONTENT, not the board; Delete + undo work.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const frameChromeVisible = () => page.evaluate(() =>
    !!document.querySelector('[data-frame-chrome]'));
  const firstFrame = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    const f = raw ? (JSON.parse(raw).frames || [])[0] : null;
    return f ? { x: f.x, y: f.y, width: f.width, height: f.height } : null;
  });
  const frameWorldRect = () => page.evaluate(() => {
    const r = [...document.querySelectorAll('svg rect')].find(rr => rr.getAttribute('fill') === '#ffffff');
    if (!r) return null;
    const b = r.getBoundingClientRect();
    return { left: b.left, top: b.top, right: b.right, bottom: b.bottom, cx: b.left + b.width / 2, cy: b.top + b.height / 2 };
  });

  // Draw a frame (returns to Move, selected).
  await page.keyboard.press('f');
  await pause(150);
  await page.mouse.move(300, 250);
  await page.mouse.down();
  await page.mouse.move(600, 500, { steps: 8 });
  await page.mouse.up();
  await pause(400);
  expect('drawnFrameSelected', await frameChromeVisible());

  // 1. Escape deselects.
  await page.keyboard.press('Escape');
  await pause(250);
  expect('escapeDeselects', !(await frameChromeVisible()));

  // 2. Click the frame body re-selects it.
  let rect = await frameWorldRect();
  await page.mouse.click(rect.cx, rect.cy);
  await pause(250);
  expect('clickBodySelects', await frameChromeVisible());

  // 3. Drag the selected frame body moves it (x and y).
  const before = await firstFrame();
  rect = await frameWorldRect();
  await page.mouse.move(rect.cx, rect.cy);
  await page.mouse.down();
  await page.mouse.move(rect.cx + 80, rect.cy + 50, { steps: 8 });
  await page.mouse.up();
  await pause(400);
  const afterMove = await firstFrame();
  expect('bodyDragMoves',
    Math.abs(afterMove.x - before.x - 80) < 6 && Math.abs(afterMove.y - before.y - 50) < 6
    && afterMove.width === before.width);

  // 4. SE corner handle resizes width/height independently.
  rect = await frameWorldRect();
  await page.mouse.move(rect.right, rect.bottom); // SE handle
  await page.mouse.down();
  await page.mouse.move(rect.right + 120, rect.bottom + 20, { steps: 8 });
  await page.mouse.up();
  await pause(400);
  const afterResize = await firstFrame();
  expect('cornerResizeNonUniform',
    afterResize.width > afterMove.width + 80
    && Math.abs(afterResize.height - afterMove.height) < 40);

  // 5. Deselect, then drag the name label of the (now unselected) frame.
  await page.keyboard.press('Escape');
  await pause(250);
  expect('deselectedBeforeLabel', !(await frameChromeVisible()));
  const labelBefore = await firstFrame();
  rect = await frameWorldRect();
  await page.mouse.move(rect.left + 20, rect.top - 8); // name strip
  await page.mouse.down();
  await page.mouse.move(rect.left + 20 + 40, rect.top - 8 + 30, { steps: 6 });
  await page.mouse.up();
  await pause(400);
  expect('labelDragSelectsAndMoves',
    (await frameChromeVisible()) && Math.abs((await firstFrame()).x - labelBefore.x - 40) < 8);

  // 6. A marquee across content on the frame selects the CONTENT, not the board.
  await page.keyboard.press('Escape');
  await pause(200);
  rect = await frameWorldRect();
  await page.keyboard.press('r');
  await pause(150);
  await page.mouse.move(rect.cx - 30, rect.cy - 30);
  await page.mouse.down();
  await page.mouse.move(rect.cx + 30, rect.cy + 30, { steps: 6 });
  await page.mouse.up();
  await pause(300);
  await page.keyboard.press('v');
  await pause(150);
  await page.mouse.move(rect.left - 10, rect.top - 10);
  await page.mouse.down();
  await page.mouse.move(rect.right + 10, rect.bottom + 10, { steps: 10 });
  await page.mouse.up();
  await pause(300);
  // The board must NOT be selected (no frame chrome); a path is instead.
  expect('marqueeSelectsContentNotFrame',
    !(await frameChromeVisible()) && await page.evaluate(() => !!document.querySelector('svg circle')));

  // 7. Delete the frame, undo restores it.
  await page.keyboard.press('Escape');
  await pause(200);
  await page.keyboard.press('v');
  await pause(150);
  rect = await frameWorldRect();
  await page.mouse.click(rect.left + 20, rect.bottom - 20);
  await pause(200);
  await page.keyboard.press('Delete');
  await pause(400);
  expect('deleteRemovesFrame', (await firstFrame()) === null);
  await page.keyboard.down('Control');
  await page.keyboard.press('z');
  await page.keyboard.up('Control');
  await pause(400);
  expect('undoRestoresFrame', (await firstFrame()) !== null);

  await page.screenshot({ path: '/tmp/shots/phase8f3-frame-edit.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
