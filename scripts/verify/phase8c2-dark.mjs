import { run, APP_URL } from './client.mjs';

// Phase 8C.2 (updated for the light-canvas pass): off-white canvas (#f5f5f5)
// with #2c2c2c panels and a #007eea accent; new shapes default to dark content
// (#1e1e1e stroke / #d9d9d9 fill, fill ON), new texts are dark, tooltips stay
// dark — while LEGACY art without stamped colors still renders the original
// pinned #344054.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  // 1. Dark chrome.
  report.bodyBg = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  expect('lightCanvas', report.bodyBg === 'rgb(245, 245, 245)');
  await page.click('button[aria-label="Design"]');
  await pause(300);
  report.cardBg = await page.evaluate(() => {
    const header = [...document.querySelectorAll('h3')].find(h => h.textContent.trim() === 'Design');
    const card = header?.closest('.rounded-2xl');
    return card ? getComputedStyle(card).backgroundColor : null;
  });
  expect('darkPanels', report.cardBg === 'rgb(44, 44, 44)');

  // 2. New shapes: white stroke, light gray fill (fill on by default).
  await page.keyboard.press('r');
  await pause(150);
  await page.mouse.move(500, 300);
  await page.mouse.down();
  await page.mouse.move(650, 400, { steps: 6 });
  await page.mouse.up();
  await pause(300);
  report.newShape = await page.evaluate(() => {
    const stroke = [...document.querySelectorAll('svg g g path[d]')]
      .find(p => (p.getAttribute('d') || '').length > 10);
    const fillGroup = document.querySelector('svg path[fill-rule="nonzero"]');
    return { stroke: stroke?.getAttribute('stroke'), fill: fillGroup?.getAttribute('fill') };
  });
  expect('newShapeDarkStroke', report.newShape.stroke === '#1e1e1e');
  expect('newShapeLightFill', report.newShape.fill === '#d9d9d9');

  // 3. Selection chrome uses the Figma blue.
  await page.keyboard.press('v');
  await pause(150);
  await page.mouse.click(575, 300);
  await pause(250);
  expect('accentSelectionChrome', await page.evaluate(() =>
    !!document.querySelector('svg rect[stroke="#007eea"]')));
  await page.keyboard.press('Escape');
  await pause(200);

  // 4. New texts default to white.
  await page.keyboard.press('t');
  await pause(150);
  await page.mouse.click(850, 200);
  await pause(250);
  await page.keyboard.type('Aa', { delay: 15 });
  await page.keyboard.press('Escape');
  await pause(300);
  expect('newTextDark', await page.evaluate(() =>
    document.querySelector('svg g text')?.getAttribute('fill') === '#1e1e1e'));

  // 5. Tooltips are dark.
  await page.mouse.move(400, 500);
  await pause(250);
  await page.hover('button[aria-label="Pen (P)"]');
  await pause(450);
  report.tooltipBg = await page.evaluate(() => {
    const tip = document.querySelector('[role="tooltip"]');
    return tip ? getComputedStyle(tip).backgroundColor : null;
  });
  expect('darkTooltip', report.tooltipBg === 'rgb(30, 30, 30)');
  await page.mouse.move(400, 500);
  await pause(200);

  // 6. LEGACY PIN: strip the stamped colors from the saved session — the
  //    art must render the original #344054, not the new defaults.
  await page.evaluate(() => {
    const session = JSON.parse(localStorage.getItem('vector-editor-session-v1'));
    session.paths.forEach(path => {
      delete path.fillColor;
      delete path.strokeColor;
    });
    localStorage.setItem('vector-editor-session-v1', JSON.stringify(session));
  });
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  report.legacy = await page.evaluate(() => {
    const stroke = [...document.querySelectorAll('svg g g path[d]')]
      .find(p => (p.getAttribute('d') || '').length > 10);
    const fillGroup = document.querySelector('svg path[fill-rule="nonzero"]');
    return { stroke: stroke?.getAttribute('stroke'), fill: fillGroup?.getAttribute('fill') };
  });
  expect('legacyStrokePinned', report.legacy.stroke === '#344054');
  expect('legacyFillPinned', report.legacy.fill === '#344054');

  await page.screenshot({ path: '/tmp/shots/phase8c2-dark.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
