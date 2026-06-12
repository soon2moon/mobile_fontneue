import { run, APP_URL } from './client.mjs';

// Phase 8F.2: the Frame tool. F arms it (crosshair); dragging draws a named
// white board that paints BELOW content; a plain click drops a 100x100
// frame; committing returns to Move with the frame selected (accent chrome
// + handles); undo removes frame + layer; sessions round-trip; the mobile
// toolbar gets a Frame button and touch-drag works.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const frameRects = () => page.evaluate(() =>
    [...document.querySelectorAll('svg rect')]
      .filter(r => r.getAttribute('fill') === '#ffffff')
      .map(r => ({ width: Number(r.getAttribute('width')), height: Number(r.getAttribute('height')) })));
  const svgTexts = () => page.evaluate(() =>
    [...document.querySelectorAll('svg text')].map(t => t.textContent));
  const buttonActive = (aria) => page.evaluate((a) => {
    const b = document.querySelector(`button[aria-label="${a}"]`);
    return !!b && b.className.includes('bg-pressed');
  }, aria);
  const session = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? JSON.parse(raw) : null;
  });

  // 1. F arms the Frame tool with a crosshair cursor.
  await page.keyboard.press('f');
  await pause(200);
  expect('fArmsFrameTool', await buttonActive('Frame (F)'));
  expect('crosshairCursor', await page.evaluate(() =>
    document.querySelector('svg').classList.contains('cursor-crosshair')));

  // 2. Drag draws a named white board; tool returns to Move with chrome.
  await page.mouse.move(300, 200);
  await page.mouse.down();
  await page.mouse.move(700, 500, { steps: 8 });
  await page.mouse.up();
  await pause(400);
  const rects1 = await frameRects();
  expect('dragDrawsFrame', rects1.length === 1 && Math.round(rects1[0].width) === 400 && Math.round(rects1[0].height) === 300);
  expect('frameNameOnCanvas', (await svgTexts()).some(t => t === 'Frame 1'));
  expect('returnsToMoveSelected', (await buttonActive('Move (V)'))
    && await page.evaluate(() => !!document.querySelector('svg rect[stroke="#0d99ff"]')));

  // 3. A plain click drops a 100x100 frame.
  await page.keyboard.press('f');
  await pause(200);
  await page.mouse.click(950, 250);
  await pause(400);
  const rects2 = await frameRects();
  expect('clickDrops100Frame', rects2.length === 2 && rects2.some(r => r.width === 100 && r.height === 100));

  // 4. Content drawn after still paints ABOVE the frame (frame is bottom).
  await page.keyboard.press('r');
  await pause(150);
  await page.mouse.move(350, 250);
  await page.mouse.down();
  await page.mouse.move(500, 350, { steps: 6 });
  await page.mouse.up();
  await pause(400);
  expect('framePaintsBelowContent', await page.evaluate(() => {
    const frameRect = [...document.querySelectorAll('svg rect')].find(r => r.getAttribute('fill') === '#ffffff');
    const fillPath = document.querySelector('svg path[fill-rule="nonzero"]');
    if (!frameRect || !fillPath) return false;
    return !!(frameRect.compareDocumentPosition(fillPath) & Node.DOCUMENT_POSITION_FOLLOWING);
  }));

  // 5. Undo chain removes the shape, then the click-frame and its layer.
  const undo = async () => {
    await page.keyboard.down('Control');
    await page.keyboard.press('z');
    await page.keyboard.up('Control');
    await pause(400);
  };
  await undo(); // shape
  await undo(); // click-frame
  await pause(600);
  const savedAfterUndo = await session();
  expect('undoRemovesFrameAndLayer',
    savedAfterUndo?.frames?.length === 1
    && (savedAfterUndo?.layers ?? []).filter(l => l.itemType === 'frame').length === 1);

  // 6. Reload round-trips the remaining frame.
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  expect('reloadRoundTrips', (await frameRects()).length === 1
    && (await svgTexts()).some(t => t === 'Frame 1'));

  // 7. Mobile: toolbar Frame button + touch drag draws a frame.
  await page.setViewport({ width: 390, height: 844, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  const frameBtn = await page.evaluate(() => {
    const b = document.querySelector('button[title="Frame"]');
    if (!b) return null;
    const r = b.getBoundingClientRect();
    return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
  });
  expect('mobileFrameButton', !!frameBtn);
  await page.touchscreen.tap(frameBtn.x, frameBtn.y);
  await pause(300);
  const drag = await page.touchscreen.touchStart(60, 300);
  for (let i = 1; i <= 6; i++) {
    await drag.move(60 + i * 33, 300 + i * 25);
    await pause(30);
  }
  await drag.end();
  await pause(400);
  expect('mobileDragDrawsFrame', (await frameRects()).length === 1);

  await page.screenshot({ path: '/tmp/shots/phase8f2-frame-tool.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
