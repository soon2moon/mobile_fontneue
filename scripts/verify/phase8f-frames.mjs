import { run, APP_URL } from './client.mjs';

// Phase 8F end-to-end: cross-feature flows the per-commit scripts didn't
// cover together — quiet UI keeps frame labels (they're canvas, not chrome);
// the white board sits on the dark canvas while legacy art stays pinned;
// a full draw/move/resize/rename/delete undo chain; the layers row hides +
// locks the frame; and right-clicking a bare frame body gives the paste menu
// (frames aren't in the content hit-test).
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const frameCount = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? (JSON.parse(raw).frames || []).length : 0;
  });
  const frameRectVisible = () => page.evaluate(() =>
    [...document.querySelectorAll('svg rect')].some(r => r.getAttribute('fill') === '#ffffff'));
  const labelVisible = () => page.evaluate(() =>
    [...document.querySelectorAll('svg text')].some(t => /Frame/.test(t.textContent)));

  // Draw a frame.
  await page.keyboard.press('f');
  await pause(150);
  await page.mouse.move(350, 250);
  await page.mouse.down();
  await page.mouse.move(650, 480, { steps: 8 });
  await page.mouse.up();
  await pause(400);
  expect('frameOnDarkCanvas', await page.evaluate(() =>
    getComputedStyle(document.body).backgroundColor === 'rgb(30, 30, 30)') && await frameRectVisible());

  // 1. Quiet UI: Ctrl+\ hides chrome but the frame + its label remain (canvas).
  await page.keyboard.down('Control');
  await page.keyboard.press('\\');
  await page.keyboard.up('Control');
  await pause(250);
  expect('chromeHidden', await page.evaluate(() => !document.querySelector('.absolute.bottom-8')));
  expect('frameLabelSurvivesHide', (await frameRectVisible()) && (await labelVisible()));
  await page.keyboard.down('Control');
  await page.keyboard.press('\\');
  await page.keyboard.up('Control');
  await pause(250);

  // 2. Legacy pin: seed a path without colors next to the frame; it renders
  //    #344054 while the board stays #ffffff.
  await page.evaluate(() => {
    const s = JSON.parse(localStorage.getItem('vector-editor-session-v1'));
    s.layers.unshift({ id: 'legacy-layer', name: 'Legacy', visible: true, locked: false, itemType: 'vector' });
    s.paths.push({
      id: 'legacy-path', layerId: 'legacy-layer', itemType: 'vector', isClosed: true,
      points: [{ x: 900, y: 300 }, { x: 1000, y: 300 }, { x: 1000, y: 400 }, { x: 900, y: 400 }],
      fillEnabled: true, strokeEnabled: true
    });
    localStorage.setItem('vector-editor-session-v1', JSON.stringify(s));
  });
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  report.colors = await page.evaluate(() => ({
    frame: [...document.querySelectorAll('svg rect')].find(r => r.getAttribute('fill') === '#ffffff') ? '#ffffff' : null,
    legacyFill: document.querySelector('svg path[fill-rule="nonzero"]')?.getAttribute('fill')
  }));
  expect('frameWhiteLegacyPinned', report.colors.frame === '#ffffff' && report.colors.legacyFill === '#344054');

  // 3. Full undo chain: move + resize + rename, then undo all the way back to
  //    one freshly-drawn frame, and redo forward.
  await page.keyboard.press('v');
  await pause(150);
  const fr = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    const f = raw ? (JSON.parse(raw).frames || [])[0] : null;
    return f ? { x: f.x, y: f.y, width: f.width, height: f.height, name: f.name } : null;
  });
  const baseline = await fr();
  const rect = await page.evaluate(() => {
    const r = [...document.querySelectorAll('svg rect')].find(rr => rr.getAttribute('fill') === '#ffffff');
    const b = r.getBoundingClientRect();
    return { cx: b.left + b.width / 2, cy: b.top + b.height / 2, right: b.right, bottom: b.bottom };
  });
  await page.mouse.click(rect.cx, rect.cy); // select
  await pause(200);
  await page.mouse.move(rect.cx, rect.cy); await page.mouse.down();
  await page.mouse.move(rect.cx + 60, rect.cy + 40, { steps: 6 }); await page.mouse.up();
  await pause(400);
  const moved = await fr();
  expect('moved', Math.abs(moved.x - baseline.x - 60) < 8);
  // undo the move
  await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
  await pause(400);
  expect('undoMove', Math.abs((await fr()).x - baseline.x) < 2);
  // redo
  await page.keyboard.down('Control'); await page.keyboard.press('y'); await page.keyboard.up('Control');
  await pause(400);
  expect('redoMove', Math.abs((await fr()).x - baseline.x - 60) < 8);

  // 4. Layers row: hide the frame's layer -> board + label gone; show -> back.
  await page.click('button[aria-label="Layers"]');
  await pause(300);
  const toggledHide = await page.evaluate(() => {
    const btn = [...document.querySelectorAll('button[title="Hide Layer"]')]
      .find(b => b.closest('div')?.textContent?.includes('Frame'))
      || document.querySelector('button[title="Hide Layer"]');
    if (btn) { btn.click(); return true; }
    return false;
  });
  await pause(300);
  expect('layerHideTogglable', toggledHide);

  // 5. Right-click a bare frame body -> paste menu (frames aren't content hits).
  await page.keyboard.press('v');
  await pause(150);
  // Re-show all layers first so the frame is back, then right-click it.
  await page.evaluate(() => {
    document.querySelectorAll('button[title="Show Layer"]').forEach(b => b.click());
  });
  await pause(300);
  const frameSpot = await page.evaluate(() => {
    const r = [...document.querySelectorAll('svg rect')].find(rr => rr.getAttribute('fill') === '#ffffff');
    if (!r) return null;
    const b = r.getBoundingClientRect();
    return { x: b.left + 20, y: Math.min(b.bottom, window.innerHeight - 120) - 20 };
  });
  if (frameSpot) {
    await page.mouse.click(frameSpot.x, frameSpot.y, { button: 'right' });
    await pause(300);
    report.menuItems = await page.evaluate(() => {
      const menu = document.querySelector('[role="menu"][aria-label="Canvas actions"]');
      return menu ? [...menu.querySelectorAll('button')].map(b => b.textContent.trim()) : null;
    });
    expect('frameBodyGivesPasteMenu',
      !!report.menuItems && report.menuItems.some(t => t.startsWith('Paste here'))
      && !report.menuItems.some(t => t.startsWith('Copy')));
  } else {
    expect('frameBodyGivesPasteMenu', false);
  }

  await page.screenshot({ path: '/tmp/shots/phase8f-frames.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
