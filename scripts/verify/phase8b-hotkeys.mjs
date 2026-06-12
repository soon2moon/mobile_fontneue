import { run, APP_URL } from './client.mjs';

// Phase 8B: Figma-aligned hotkeys + wording. H = Hand, Shift+P = Pencil,
// L = Line tool (the Layers panel moved to its toolbar button), modified
// keys (Ctrl+letter) no longer hijack tool switching, the dead B hotkey
// stays dead, and the visible wording matches Figma (Pen / Move / Hand /
// Place Image / Design / Canvas Grid; stroke Weight + Position).
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const buttonActive = (aria) => page.evaluate((a) => {
    const b = document.querySelector(`button[aria-label="${a}"]`);
    return !!b && b.className.includes('bg-pressed');
  }, aria);
  const pathCount = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length);
  const panelHeaders = () => page.evaluate(() =>
    [...document.querySelectorAll('h3')].map(h => h.textContent.trim()));

  // 1. H activates the Hand tool.
  await page.keyboard.press('h');
  await pause();
  expect('hActivatesHand', await buttonActive('Hand (H)'));

  // 2. Shift+P activates Pencil; freehand drawing works.
  await page.keyboard.down('Shift');
  await page.keyboard.press('P');
  await page.keyboard.up('Shift');
  await pause();
  expect('shiftPActivatesPencil', await buttonActive('Pencil (Shift+P)'));
  const pathsBeforePencil = await pathCount();
  await page.mouse.move(300, 400);
  await page.mouse.down();
  for (let i = 1; i <= 10; i++) {
    await page.mouse.move(300 + i * 15, 400 + Math.sin(i) * 30, { steps: 2 });
  }
  await page.mouse.up();
  await pause(350);
  expect('pencilDraws', (await pathCount()) === pathsBeforePencil + 1);

  // 3. Plain P returns to the Pen.
  await page.keyboard.press('p');
  await pause();
  expect('pActivatesPen', await buttonActive('Pen (P)'));

  // 4. Ctrl+P must NOT switch tools.
  await page.keyboard.press('v');
  await pause();
  await page.keyboard.down('Control');
  await page.keyboard.press('p');
  await page.keyboard.up('Control');
  await pause();
  expect('ctrlPDoesNotSwitch', await buttonActive('Move (V)'));

  // 5. L arms the Line tool (not the Layers panel) and draws a line.
  await page.keyboard.press('l');
  await pause();
  expect('lArmsShapeTool', await buttonActive('Shape Tool (R/O)'));
  expect('noLayersPanelFromL', !(await panelHeaders()).includes('Layers'));
  const pathsBeforeLine = await pathCount();
  await page.mouse.move(300, 600);
  await page.mouse.down();
  await page.mouse.move(520, 650, { steps: 6 });
  await page.mouse.up();
  await pause(350);
  expect('lineDraws', (await pathCount()) === pathsBeforeLine + 1);

  // 6. The dead B/G keys open nothing.
  await page.keyboard.press('v');
  await pause(150);
  await page.keyboard.press('b');
  await pause();
  await page.keyboard.press('g');
  await pause();
  expect('bgOpenNoPanels', !(await panelHeaders()).includes('Canvas Grid'));

  // 7. Layers opens via its toolbar button; Design wording everywhere.
  await page.click('button[aria-label="Layers"]');
  await pause();
  expect('layersViaButton', (await panelHeaders()).includes('Layers'));
  await page.click('button[aria-label="Design"]');
  await pause();
  const headers = await panelHeaders();
  expect('designHeader', headers.includes('Design') && !headers.includes('Inspector'));
  expect('strokeWording', await page.evaluate(() =>
    !!document.querySelector('input[title="Stroke Weight"]')
    && !!document.querySelector('select[title="Stroke Position"]')));

  // 8. Mobile toolbar wording: Move / Pen / Hand.
  await page.setViewport({ width: 390, height: 844, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  expect('mobileLabels', await page.evaluate(() =>
    !!document.querySelector('button[title="Move"]')
    && !!document.querySelector('button[title="Pen"]')
    && !!document.querySelector('button[title="Hand"]')));

  await page.screenshot({ path: '/tmp/shots/phase8b-hotkeys.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
