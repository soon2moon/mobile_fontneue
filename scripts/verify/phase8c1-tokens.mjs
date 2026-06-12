import { run, APP_URL } from './client.mjs';

// Phase 8C.1: every UI color resolves through the CSS-variable tokens with
// ZERO visual change — body/canvas and panel cards still render the exact
// light-palette values, the :root variables resolve, and no hardcoded
// hex-color utility classes remain in the rendered DOM.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  report.bodyBg = await page.evaluate(() => getComputedStyle(document.body).backgroundColor);
  expect('bodyStillLightCanvas', report.bodyBg === 'rgb(242, 244, 247)');

  report.varResolves = await page.evaluate(() =>
    getComputedStyle(document.documentElement).getPropertyValue('--color-raised').trim());
  expect('rootVarResolves', report.varResolves === '248 250 252');

  await page.click('button[aria-label="Design"]');
  await pause(300);
  report.cardBg = await page.evaluate(() => {
    const header = [...document.querySelectorAll('h3')].find(h => h.textContent.trim() === 'Design');
    const card = header?.closest('.rounded-2xl');
    return card ? getComputedStyle(card).backgroundColor : null;
  });
  expect('panelCardStillRaisedLight', report.cardBg === 'rgb(248, 250, 252)');

  report.toolbarBg = await page.evaluate(() => {
    const tb = document.querySelector('.absolute.bottom-8');
    return tb ? getComputedStyle(tb).backgroundColor : null;
  });
  expect('toolbarStillRaisedLight', report.toolbarBg === 'rgb(248, 250, 252)');

  // No hardcoded color classes left anywhere in the live DOM.
  report.hexClassCount = await page.evaluate(() => {
    const re = /(bg|text|border|ring|stroke)-\[#/;
    return [...document.querySelectorAll('[class]')]
      .filter(el => typeof el.className === 'string' && re.test(el.className)).length;
  });
  expect('noHexUtilityClasses', report.hexClassCount === 0);

  // Selection chrome still draws the same accent (THEME swap is value-neutral).
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
  expect('strokeStillLegacyInk', report.gridStroke === '#344054');

  await page.screenshot({ path: '/tmp/shots/phase8c1-tokens.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
