import { run, APP_URL } from './client.mjs';

// Phase 8A: the Inspector card no longer overflows or focus-scrolls (the
// hex input's intrinsic width used to floor the 1fr grid track past the
// card edge, and focusing an input scrolled the overflow-hidden card), and
// the four non-ToolButton toolbar buttons (shape, shape options,
// auto-correct, clear) use the shared portaled Tooltip instead of native
// titles.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  const cardState = () => page.evaluate(() => {
    const header = [...document.querySelectorAll('h3')].find(h => /Inspector|Design/.test(h.textContent));
    const card = header?.closest('.rounded-2xl');
    if (!card) return null;
    const input = document.querySelector('input[title="Stroke Width"], input[title="Stroke Weight"]');
    const cardR = card.getBoundingClientRect();
    const inputR = input?.getBoundingClientRect() ?? null;
    return {
      scrollLeft: card.scrollLeft,
      contentFits: card.scrollWidth <= card.clientWidth,
      headerX: Math.round(header.getBoundingClientRect().x),
      inputInsideCard: inputR ? inputR.right <= cardR.right + 0.5 : null
    };
  });

  // 1. Desktop: content fits, focusing inputs cannot scroll the card.
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);
  await page.click('button[aria-label="Design"]');
  await pause(300);
  const before = await cardState();
  expect('desktopContentFits', !!before && before.contentFits && before.inputInsideCard === true);
  await page.click('input[title="Stroke Width"], input[title="Stroke Weight"]');
  await pause(300);
  const afterWidthFocus = await cardState();
  await page.click('input[title="Stroke Color (Hex)"]');
  await pause(300);
  const afterHexFocus = await cardState();
  expect('desktopNoFocusScroll',
    afterWidthFocus.scrollLeft === 0 && afterHexFocus.scrollLeft === 0
    && afterWidthFocus.headerX === before.headerX && afterHexFocus.headerX === before.headerX);

  // 2. Tooltips on the four formerly-native-title buttons.
  const hoverTooltip = async (ariaLabel, expectText) => {
    await page.mouse.move(400, 200);
    await pause(250);
    await page.hover(`button[aria-label="${ariaLabel}"]`);
    await pause(450);
    return page.evaluate((wanted) => {
      const tip = document.querySelector('[role="tooltip"]');
      const toolbar = document.querySelector('.absolute.bottom-8');
      return !!tip && tip.textContent.includes(wanted) && !!toolbar && !toolbar.contains(tip);
    }, expectText);
  };
  expect('shapeToolTooltip', await hoverTooltip('Shape Tool (R/O)', 'Shape Tool'));
  expect('shapeOptionsTooltip', await hoverTooltip('Shape Options', 'Shape Options'));
  expect('autoCorrectTooltip', await hoverTooltip('Auto-Correct Path Directions', 'Auto-Correct'));
  expect('clearCanvasTooltip', await hoverTooltip('Clear Canvas', 'Clear Canvas'));
  expect('noNativeTitlesLeft', await page.evaluate(() =>
    !document.querySelector('[title="Shape Options"], [title="Shape Tool (R/O)"], [title="Clear Canvas"], [title="Auto-Correct Path Directions"]')));

  // 3. Mobile sheet: same no-overflow/no-scroll invariants.
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
  await tapTitle('Design');
  const mobileBefore = await cardState();
  expect('mobileContentFits', !!mobileBefore && mobileBefore.contentFits && mobileBefore.inputInsideCard === true);
  const inputPos = await page.evaluate(() => {
    const i = document.querySelector('input[title="Stroke Width"], input[title="Stroke Weight"]');
    if (!i) return null;
    const r = i.getBoundingClientRect();
    return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
  });
  await page.touchscreen.tap(inputPos.x, inputPos.y);
  await pause(400);
  const mobileAfter = await cardState();
  expect('mobileNoFocusScroll', mobileAfter.scrollLeft === 0 && mobileAfter.headerX === mobileBefore.headerX);

  await page.screenshot({ path: '/tmp/shots/phase8a-consistency.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
