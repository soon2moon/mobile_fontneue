import { run, APP_URL } from './client.mjs';

// Phase 8D: quiet UI. Ctrl+\ hides all chrome (canvas keeps working) and
// restores it; open panels fade out and become click-through while a
// canvas gesture is in flight, then restore on release; Ctrl+\ typed
// inside a text input does nothing; mobile gets a drawer "Hide UI" and a
// floating "Show UI" pill as the escape hatch.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const chromeVisible = () => page.evaluate(() => ({
    toolbar: !!document.querySelector('.absolute.bottom-8'),
    panels: [...document.querySelectorAll('h3')].length > 0
  }));
  const pathCount = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length);
  const pressHideUi = async () => {
    await page.keyboard.down('Control');
    await page.keyboard.press('\\');
    await page.keyboard.up('Control');
    await pause(250);
  };

  // 1. Ctrl+\ hides all chrome; drawing still works; Ctrl+\ restores.
  await pressHideUi();
  const hidden = await chromeVisible();
  expect('ctrlBackslashHidesChrome', !hidden.toolbar);
  await page.keyboard.press('r');
  await pause(150);
  const before = await pathCount();
  await page.mouse.move(500, 300);
  await page.mouse.down();
  await page.mouse.move(650, 400, { steps: 6 });
  await page.mouse.up();
  await pause(300);
  expect('canvasWorksWhileHidden', (await pathCount()) === before + 1);
  await pressHideUi();
  expect('ctrlBackslashRestoresChrome', (await chromeVisible()).toolbar);

  // 2. Open panel fades + becomes click-through during a canvas gesture.
  await page.click('button[aria-label="Design"]');
  await pause(300);
  const cardStyle = () => page.evaluate(() => {
    const header = [...document.querySelectorAll('h3')].find(h => h.textContent.trim() === 'Design');
    const card = header?.closest('.rounded-2xl');
    if (!card) return null;
    const cs = getComputedStyle(card);
    return { opacity: Number(cs.opacity), pointerEvents: cs.pointerEvents };
  });
  await page.keyboard.press('v');
  await pause(150);
  await page.mouse.move(300, 500);
  await page.mouse.down();
  await page.mouse.move(420, 560, { steps: 6 });
  await pause(500); // fade has a 100ms delay + 300ms transition
  report.duringDrag = await cardStyle();
  await page.mouse.up();
  await pause(450);
  report.afterDrag = await cardStyle();
  expect('panelFadesDuringWork',
    !!report.duringDrag && report.duringDrag.opacity < 0.5 && report.duringDrag.pointerEvents === 'none');
  expect('panelRestoresAfterWork',
    !!report.afterDrag && report.afterDrag.opacity > 0.99 && report.afterDrag.pointerEvents !== 'none');

  // 3. Ctrl+\ inside a text input must not hide the UI.
  await page.click('input[title="Stroke Color (Hex)"]');
  await pause(150);
  await pressHideUi();
  expect('inputGuardKeepsUi', (await chromeVisible()).toolbar);
  await page.keyboard.press('Escape');
  await pause(150);

  // 4. Mobile: drawer Hide UI -> chrome gone + Show UI pill -> restore.
  await page.setViewport({ width: 390, height: 844, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  const tapTitle = async (t) => {
    const r = await page.evaluate((wanted) => {
      const b = document.querySelector(`button[title="${wanted}"]`);
      if (!b) return null;
      const x = b.getBoundingClientRect();
      return { x: x.x + x.width / 2, y: x.y + x.height / 2 };
    }, t);
    if (!r) throw new Error(`no button ${t}`);
    await page.touchscreen.tap(r.x, r.y);
    await pause(350);
  };
  await tapTitle('Menu');
  await tapTitle('Hide UI');
  report.mobileHidden = await page.evaluate(() => ({
    menuGone: !document.querySelector('button[title="Menu"]'),
    pill: [...document.querySelectorAll('button')].some(b => b.textContent.trim() === 'Show UI')
  }));
  expect('mobileHideUi', report.mobileHidden.menuGone && report.mobileHidden.pill);
  await page.evaluate(() => {
    [...document.querySelectorAll('button')].find(b => b.textContent.trim() === 'Show UI')?.click();
  });
  await pause(300);
  expect('mobileShowUiPillRestores', await page.evaluate(() =>
    !!document.querySelector('button[title="Menu"]')));

  await page.screenshot({ path: '/tmp/shots/phase8d-quietui.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
