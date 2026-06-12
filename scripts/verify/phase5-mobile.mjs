import { run, APP_URL } from './client.mjs';

// Mobile touch gestures against the extracted usePointerInteraction hook:
// pinch zoom, two-finger pan, one-finger shape draw, multi-touch draw
// rollback, and the 520ms long-press context menu.
// Uses puppeteer's TouchHandle API (touchscreen.touchStart returns a handle;
// concurrent handles = multi-touch).
run(async (page) => {
  const report = {};
  const pause = (ms = 200) => new Promise(r => setTimeout(r, ms));

  await page.setViewport({ width: 390, height: 700, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const pathCount = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length
  );
  const getTransform = () => page.evaluate(() => {
    const g = document.querySelector('svg g[transform]');
    return g ? g.getAttribute('transform') : null;
  });
  const getScale = async () => {
    const t = await getTransform();
    const m = t && t.match(/scale\(([\d.]+)\)/);
    return m ? Number(m[1]) : null;
  };

  report.mobileUiActive = await page.evaluate(() => window.innerWidth <= 900);

  // 1. One-finger shape draw (rect mode via hotkey; handler is on window).
  await page.keyboard.press('r'); await pause();
  const draw = await page.touchscreen.touchStart(80, 200);
  for (let i = 1; i <= 6; i++) {
    await draw.move(80 + i * 25, 200 + i * 18);
    await pause(30);
  }
  await draw.end();
  await pause(350);
  report.pathsAfterTouchDraw = await pathCount();

  // 2. Pinch zoom: two fingers diverging.
  const scaleBefore = await getScale();
  const p1 = await page.touchscreen.touchStart(170, 350);
  const p2 = await page.touchscreen.touchStart(220, 350);
  for (let i = 1; i <= 8; i++) {
    await p1.move(170 - i * 12, 350);
    await p2.move(220 + i * 12, 350);
    await pause(25);
  }
  await p1.end(); await p2.end();
  await pause(300);
  const scaleAfterPinch = await getScale();
  report.pinchZoom = { before: scaleBefore, after: scaleAfterPinch, changed: scaleAfterPinch !== scaleBefore };

  // 3. Two-finger pan (parallel movement).
  const tBefore = await getTransform();
  const q1 = await page.touchscreen.touchStart(150, 300);
  const q2 = await page.touchscreen.touchStart(240, 300);
  for (let i = 1; i <= 6; i++) {
    await q1.move(150 + i * 15, 300 + i * 10);
    await q2.move(240 + i * 15, 300 + i * 10);
    await pause(25);
  }
  await q1.end(); await q2.end();
  await pause(300);
  report.twoFingerPanChanged = (await getTransform()) !== tBefore;

  // 4. Multi-touch rollback: start a one-finger draw, then add a second
  //    finger mid-gesture -> pinch takes over, the in-progress draw rolls back.
  const pathsBeforeRollback = await pathCount();
  const r1 = await page.touchscreen.touchStart(100, 450);
  await r1.move(140, 480);
  await pause(60);
  const r2 = await page.touchscreen.touchStart(250, 520);
  for (let i = 1; i <= 5; i++) {
    await r1.move(140 - i * 10, 480);
    await r2.move(250 + i * 10, 520);
    await pause(25);
  }
  await r1.end(); await r2.end();
  await pause(350);
  const pathsAfterRollback = await pathCount();
  report.rollback = {
    pathsBefore: pathsBeforeRollback,
    pathsAfter: pathsAfterRollback,
    noStrayPath: pathsAfterRollback === pathsBeforeRollback
  };

  // 5. Long-press (edit mode, hold one finger still 750ms) -> context menu.
  await page.keyboard.press('v'); await pause();
  const lp = await page.touchscreen.touchStart(200, 350);
  await pause(750);
  report.longPressMenu = await page.evaluate(() =>
    !!document.querySelector('[role="menu"][aria-label="Canvas actions"]')
  );
  await lp.end();
  // Wait out the Popover's 400ms outside-press guard (it keeps the
  // touchend's compatibility click from instantly dismissing the menu),
  // then an outside tap on empty canvas closes it.
  await pause(400);
  await page.touchscreen.tap(320, 250);
  await pause(250);
  report.menuClosedAfterTap = await page.evaluate(() =>
    !document.querySelector('[role="menu"][aria-label="Canvas actions"]')
  );

  await page.screenshot({ path: '/tmp/shots/phase5-mobile.png' });

  await page.evaluate(() => localStorage.clear());
  await page.close(); // fresh page per run; don't leave the touch viewport behind
  return report;
}, { fresh: true });
