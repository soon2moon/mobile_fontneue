import { run, APP_URL } from './client.mjs';

// Phase 8E (updated): the canvas context menu is shared by desktop right-click
// and mobile long-press. Right-clicking an object selects it and offers
// Copy/Cut/Duplicate/Delete plus an "Arrange" submenu for layer reordering
// (with shortcut hints); right-clicking empty canvas offers "Paste here"
// (recenters the paste on the pressed point) and "Show/Hide UI". Escape closes
// the menu without touching the selection (Popover contract).
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const menuState = () => page.evaluate(() => {
    const menu = document.querySelector('[role="menu"][aria-label="Canvas actions"]');
    if (!menu) return null;
    return [...menu.querySelectorAll('button')].map(b => b.textContent.trim());
  });
  const drawRect = async (x0, y0, x1, y1) => {
    await page.keyboard.press('r');
    await pause(150);
    await page.mouse.move(x0, y0);
    await page.mouse.down();
    await page.mouse.move(x1, y1, { steps: 6 });
    await page.mouse.up();
    await pause(300);
  };
  const clickItem = async (label) => {
    const clicked = await page.evaluate((wanted) => {
      const menu = document.querySelector('[role="menu"][aria-label="Canvas actions"]');
      const btn = menu && [...menu.querySelectorAll('button')].find(b => b.textContent.trim().startsWith(wanted));
      if (btn) btn.click();
      return !!btn;
    }, label);
    if (!clicked) throw new Error(`menu item not found: ${label}`);
    await pause(300);
  };
  const openArrange = async () => {
    const box = await page.evaluate(() => {
      const menu = document.querySelector('[role="menu"][aria-label="Canvas actions"]');
      const btn = menu && [...menu.querySelectorAll('button')].find(b => b.textContent.trim().startsWith('Arrange'));
      if (!btn) return null;
      const r = btn.getBoundingClientRect();
      return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
    });
    if (box) { await page.mouse.move(box.x, box.y); await pause(300); }
  };
  const pathCount = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g g path[d]')].filter(p => (p.getAttribute('d') || '').length > 10).length);

  // 1. Right-click an object: full actions menu with shortcut hints.
  await drawRect(500, 300, 650, 400);
  await page.keyboard.press('v');
  await pause(150);
  await page.mouse.click(575, 350, { button: 'right' });
  await pause(350);
  const items = await menuState();
  report.items = items;
  expect('actionsMenuOnObject',
    !!items
    && items.some(t => t.startsWith('Copy'))
    && items.some(t => t.startsWith('Cut'))
    && items.some(t => t.startsWith('Duplicate'))
    && items.some(t => t.startsWith('Delete'))
    && items.some(t => t.startsWith('Arrange')));
  expect('shortcutHints', !!items && items.some(t => t.includes('Ctrl+C')) && items.some(t => t.includes('Del')));

  // 2. Copy, then Paste here far away: the copy lands centered on the point.
  await clickItem('Copy');
  await pause(500); // outlive the menu's outside-press guard before reopening
  await page.mouse.click(1000, 600, { button: 'right' });
  await pause(350);
  const pasteItems = await menuState();
  expect('pasteHereOnEmptyCanvas', !!pasteItems && pasteItems.some(t => t.startsWith('Paste here')));
  const beforePaste = await pathCount();
  await clickItem('Paste here');
  expect('pasteAddsPath', (await pathCount()) === beforePaste + 1);
  report.pasteCenter = await page.evaluate(() => {
    const strokes = [...document.querySelectorAll('svg g g path[d]')]
      .filter(p => (p.getAttribute('d') || '').length > 10);
    const r = strokes[strokes.length - 1].getBoundingClientRect();
    return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
  });
  expect('pasteLandsAtPoint',
    Math.abs(report.pasteCenter.x - 1000) < 25 && Math.abs(report.pasteCenter.y - 600) < 25);

  // 3. Bring forward / Send backward reorder the target's layer.
  const layerOrder = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? (JSON.parse(raw).layers || []).map(l => l.id) : null;
  });
  await pause(700); // session save settle
  const orderBefore = await layerOrder();
  await pause(500);
  await page.mouse.click(575, 350, { button: 'right' });
  await pause(350);
  await openArrange();
  await clickItem('Bring forward');
  await pause(700);
  const orderAfter = await layerOrder();
  expect('bringForwardReorders',
    !!orderBefore && !!orderAfter && orderBefore.join() !== orderAfter.join());

  // 4. Escape closes the menu first; the selection survives.
  await pause(500);
  await page.mouse.click(575, 350, { button: 'right' });
  await pause(350);
  await page.keyboard.press('Escape');
  await pause(250);
  expect('escClosesMenu', (await menuState()) === null);
  expect('selectionSurvivesEsc', await page.evaluate(() =>
    !!document.querySelector('svg rect[stroke="#007eea"]')));

  // 5. Delete via the menu removes the object.
  await page.mouse.click(1000, 600, { button: 'right' });
  await pause(350);
  const beforeDelete = await pathCount();
  await clickItem('Delete');
  expect('deleteRemovesObject', (await pathCount()) === beforeDelete - 1);

  // 6. Mobile regression mirror: long-press still opens the same menu.
  await page.setViewport({ width: 390, height: 844, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  await page.keyboard.press('v');
  await pause(150);
  const lp = await page.touchscreen.touchStart(200, 400);
  await pause(750);
  const mobileMenu = await menuState();
  await lp.end();
  await pause(250);
  expect('mobileLongPressMenu', !!mobileMenu && mobileMenu.some(t => t.startsWith('Paste here')));

  await page.screenshot({ path: '/tmp/shots/phase8e-contextmenu.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
