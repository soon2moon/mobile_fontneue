import { run, APP_URL } from './client.mjs';

// Phase 8C.1: every UI color resolves through the CSS-variable tokens —
// body/canvas and panel chrome track the :root variables (theme-agnostic),
// no hardcoded hex-color utility classes remain in the rendered DOM, and
// newly drawn shapes use the themed content defaults.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const resolvedTokens = await page.evaluate(() => {
    const css = getComputedStyle(document.documentElement);
    const rgb = (name) => `rgb(${css.getPropertyValue(name).trim().split(/\s+/).join(', ')})`;
    return { canvas: rgb('--color-canvas'), raised: rgb('--color-raised') };
  });
  report.resolvedTokens = resolvedTokens;
  report.bodyBg = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  expect('bodyUsesCanvasToken', report.bodyBg === resolvedTokens.canvas);

  report.varResolves = await page.evaluate(() =>
    getComputedStyle(document.documentElement).getPropertyValue('--color-raised').trim());
  expect('rootVarResolves', /^\d+ \d+ \d+$/.test(report.varResolves));

  await page.click('button[aria-label="Design"]');
  await pause(300);
  report.cardBg = await page.evaluate(() => {
    const header = [...document.querySelectorAll('h3')].find(h => h.textContent.trim() === 'Design');
    const card = header?.closest('.rounded-2xl');
    return card ? getComputedStyle(card).backgroundColor : null;
  });
  expect('panelCardUsesRaisedToken', report.cardBg === resolvedTokens.raised);

  report.toolbarBg = await page.evaluate(() => {
    const tb = document.querySelector('.absolute.bottom-8');
    return tb ? getComputedStyle(tb).backgroundColor : null;
  });
  expect('toolbarUsesRaisedToken', report.toolbarBg === resolvedTokens.raised);

  // No hardcoded color classes left anywhere in the live DOM.
  report.hexClassCount = await page.evaluate(() => {
    const re = /(bg|text|border|ring|stroke)-\[#/;
    return [...document.querySelectorAll('[class]')]
      .filter(el => typeof el.className === 'string' && re.test(el.className)).length;
  });
  expect('noHexUtilityClasses', report.hexClassCount === 0);

  // New shapes pick up the themed content defaults.
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
  report.gridStroke = await page.evaluate(() => {
    const path = [...document.querySelectorAll('svg g g path[d]')]
      .find(p => (p.getAttribute('d') || '').length > 10);
    return path?.getAttribute('stroke') ?? null;
  });
  expect('newShapeUsesThemedStroke', report.gridStroke === '#1e1e1e');

  await page.screenshot({ path: '/tmp/shots/phase8c1-tokens.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
