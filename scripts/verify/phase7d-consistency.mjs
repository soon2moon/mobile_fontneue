import { run, APP_URL } from './client.mjs';

// Phase 7D: consistency pass. Floating tooltips render portaled with
// label + hotkey; the shape flyout is a Popover (Esc closes it); Escape
// with a popover open is consumed by the popover and leaves the canvas
// selection alone; the mobile long-press menu stays fully on-screen near
// viewport edges and survives the touchend compatibility click; the export
// scope/format controls still work after the context renames.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);
  await page.evaluate(() => {
    window.__downloads = [];
    HTMLAnchorElement.prototype.click = function () {
      window.__downloads.push({ href: this.href, download: this.download });
    };
  });

  const clickByText = async (text) => {
    const clicked = await page.evaluate((label) => {
      const target = [...document.querySelectorAll('button')]
        .find(b => b.textContent.trim().toLowerCase() === label.toLowerCase());
      if (target) target.click();
      return !!target;
    }, text);
    if (!clicked) throw new Error(`button not found: ${text}`);
    await pause(150);
  };
  const flyoutOpen = () => page.evaluate(() =>
    [...document.querySelectorAll('button')].some(b => b.textContent.includes('Rectangle')));

  // 1. Tooltip: portaled, label + hotkey, gone after mouse-away.
  await page.hover('button[aria-label="Path Tool (P)"]');
  await pause(450);
  report.tooltip = await page.evaluate(() => {
    const tip = document.querySelector('[role="tooltip"]');
    if (!tip) return null;
    const toolbar = document.querySelector('.absolute.bottom-8');
    return {
      text: tip.textContent,
      portaled: !!toolbar && !toolbar.contains(tip),
      visible: tip.getBoundingClientRect().height > 0
    };
  });
  expect('tooltipPortaledWithHotkey',
    !!report.tooltip
    && report.tooltip.text.includes('Path Tool') && report.tooltip.text.includes('P')
    && report.tooltip.portaled && report.tooltip.visible);
  await page.mouse.move(400, 200);
  await pause(300);
  expect('tooltipGoneAfterMouseAway', await page.evaluate(() => !document.querySelector('[role="tooltip"]')));

  // 2. Shape flyout (Popover): chevron opens, Escape closes.
  await page.click('button[aria-label="Shape Options"]');
  await pause(250);
  expect('shapeFlyoutOpens', await flyoutOpen());
  await page.keyboard.press('Escape');
  await pause(250);
  expect('escClosesShapeFlyout', !(await flyoutOpen()));

  // 3. Escape with a color popover open: the popover consumes it, the
  //    path selection survives; only the NEXT Escape clears the selection.
  await page.keyboard.press('r');
  await pause(150);
  await page.mouse.move(500, 300);
  await page.mouse.down();
  await page.mouse.move(650, 400, { steps: 6 });
  await page.mouse.up();
  await pause(300);
  await page.keyboard.press('v');
  await pause(150);
  await page.mouse.click(575, 300);
  await pause(250);
  await page.click('button[aria-label="Inspector"]');
  await pause(250);
  await page.click('button[title="Stroke Color"]');
  await pause(300);
  expect('pickerOpen', await page.evaluate(() => !!document.querySelector('.react-colorful')));
  await page.keyboard.press('Escape');
  await pause(300);
  expect('escClosesPicker', await page.evaluate(() => !document.querySelector('.react-colorful')));
  expect('selectionSurvivesEsc', await page.evaluate(() =>
    !/Nothing selected/i.test(document.body.innerText)));
  await page.keyboard.press('Escape');
  await pause(300);
  expect('nextEscClearsSelection', await page.evaluate(() =>
    /Nothing selected/i.test(document.body.innerText)));

  // 4. Export still works through the renamed context (scope -> Canvas,
  //    format -> svg).
  await page.click('button[aria-label="Export"]');
  await pause(200);
  await clickByText('Canvas');
  await clickByText('svg');
  await clickByText('Export SVG');
  await pause(300);
  report.export = await page.evaluate(async () => {
    const entry = window.__downloads[window.__downloads.length - 1];
    if (!entry) return null;
    const text = entry.href.startsWith('blob:') ? await (await fetch(entry.href)).text() : null;
    return { download: entry.download, nonEmpty: !!text && text.startsWith('<svg') };
  });
  expect('exportScopeWorksPostRename',
    report.export?.download === 'canvas.svg' && report.export?.nonEmpty === true);

  // 5. Mobile: a long-press near the right edge opens the menu fully
  //    on-screen (flip/shift instead of the old manual clamps), it survives
  //    the touchend compatibility click, and a later outside tap closes it.
  await page.setViewport({ width: 390, height: 844, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  await page.keyboard.press('v');
  await pause(150);
  const press = await page.touchscreen.touchStart(375, 500);
  await pause(750);
  const menuWhileHeld = await page.evaluate(() =>
    !!document.querySelector('[role="menu"][aria-label="Canvas actions"]'));
  await press.end();
  await pause(250);
  report.edgeMenu = await page.evaluate(() => {
    const menu = document.querySelector('[role="menu"][aria-label="Canvas actions"]');
    if (!menu) return null;
    const r = menu.getBoundingClientRect();
    return { left: r.left, right: r.right, top: r.top, bottom: r.bottom };
  });
  expect('edgeMenuOpensWhileHeld', menuWhileHeld);
  expect('edgeMenuSurvivesCompatClick', !!report.edgeMenu);
  expect('edgeMenuFullyOnScreen',
    !!report.edgeMenu
    && report.edgeMenu.left >= 7
    && report.edgeMenu.right <= 390 - 7
    && report.edgeMenu.top >= 7
    && report.edgeMenu.bottom <= 844 - 7);
  await page.touchscreen.tap(100, 250);
  await pause(300);
  expect('edgeMenuOutsideTapDismisses', await page.evaluate(() =>
    !document.querySelector('[role="menu"][aria-label="Canvas actions"]')));

  await page.screenshot({ path: '/tmp/shots/phase7d-consistency.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
