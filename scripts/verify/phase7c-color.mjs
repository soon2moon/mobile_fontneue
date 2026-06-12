import { run, APP_URL } from './client.mjs';

// Phase 7C: independent fillColor + per-color composite fills. Two rects
// share one winding group until one is recolored; undo/redo walk the split;
// a full picker drag is a single undo step; the export carries the same
// per-color nonzero groups (fills below stroke-only outlines); a same-color
// donut keeps its hole; legacy sessions without fillColor stay #344054 even
// when the next-path default is changed.
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

  const drawRect = async (x0, y0, x1, y1) => {
    await page.keyboard.press('r');
    await pause(150);
    await page.mouse.move(x0, y0);
    await page.mouse.down();
    await page.mouse.move(x1, y1, { steps: 6 });
    await page.mouse.up();
    await pause(300);
  };
  const clickPathEdge = async (x, y) => {
    await page.keyboard.press('v');
    await pause(150);
    await page.mouse.click(x, y);
    await pause(250);
  };
  const setInputValue = async (title, value) => {
    await page.click(`input[title="${title}"]`);
    await page.keyboard.down('Control');
    await page.keyboard.press('a');
    await page.keyboard.up('Control');
    await page.keyboard.type(String(value), { delay: 15 });
    await page.keyboard.press('Enter');
    await pause(300);
  };
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
  const undo = async () => {
    await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
    await pause(300);
  };
  const redo = async () => {
    await page.keyboard.down('Control'); await page.keyboard.press('y'); await page.keyboard.up('Control');
    await pause(300);
  };
  const compositeFills = () => page.evaluate(() =>
    [...document.querySelectorAll('svg path[fill-rule="nonzero"]')].map(p => p.getAttribute('fill')));

  // 1. Fill enabled on the defaults; two rects share ONE composite group.
  await page.click('button[aria-label="Design"]');
  await pause(250);
  await page.click('button[title="Enable Fill"]');
  await pause(250);
  await drawRect(500, 300, 650, 400);
  await drawRect(300, 480, 420, 580);
  report.singleColorGroups = await compositeFills();
  expect('singleGroupForSingleColor',
    report.singleColorGroups.length === 1 && report.singleColorGroups[0] === '#344054');

  // 2. Recolor rect B -> exactly two groups, paint order = first encounter
  //    (rect A's layer is below rect B's, so #344054 stays first).
  await clickPathEdge(360, 480);
  await setInputValue('Fill Color (Hex)', '2e90fa');
  report.twoColorGroups = await compositeFills();
  expect('perColorGroups',
    report.twoColorGroups.length === 2
    && report.twoColorGroups[0] === '#344054'
    && report.twoColorGroups[1] === '#2e90fa');

  // 3. Undo collapses back to one group; redo restores the split.
  await undo();
  expect('undoMergesGroups', (await compositeFills()).join(',') === '#344054');
  await redo();
  expect('redoSplitsGroups', (await compositeFills()).join(',') === '#344054,#2e90fa');

  // 4. A full picker drag commits exactly ONE undo step.
  await clickPathEdge(360, 480);
  await page.click('button[title="Fill Color"]');
  await pause(300);
  const satBox = await (await page.$('.react-colorful__saturation')).boundingBox();
  await page.mouse.move(satBox.x + satBox.width * 0.5, satBox.y + satBox.height * 0.5);
  await page.mouse.down();
  await page.mouse.move(satBox.x + satBox.width * 0.9, satBox.y + satBox.height * 0.15, { steps: 8 });
  await page.mouse.up();
  await pause(300);
  const fillsAfterDrag = await compositeFills();
  report.dragColor = fillsAfterDrag[1] ?? null;
  expect('dragChangedColor', fillsAfterDrag.length === 2 && fillsAfterDrag[1] !== '#2e90fa');
  // Close via outside press, NOT Escape (popovers consume Escape from 7D on).
  await page.mouse.click(150, 150);
  await pause(250);
  await undo();
  expect('dragIsOneUndoStep', (await compositeFills()).join(',') === '#344054,#2e90fa');

  // 5. SVG export: same per-color nonzero groups, fills below the
  //    stroke-only outlines, no legacy per-path fills.
  await page.click('button[aria-label="Export"]');
  await pause(200);
  await clickByText('Canvas');
  await clickByText('svg');
  await clickByText('Export SVG');
  await pause(300);
  const svgText = await page.evaluate(async () => {
    const entry = window.__downloads[window.__downloads.length - 1];
    if (!entry || !entry.href.startsWith('blob:')) return null;
    return await (await fetch(entry.href)).text();
  });
  report.exportFillRuleCount = (svgText?.match(/fill-rule="nonzero"/g) || []).length;
  expect('exportHasBothFillGroups',
    report.exportFillRuleCount === 2
    && svgText.includes('fill="#344054"')
    && svgText.includes('fill="#2e90fa"'));
  expect('exportHasStrokeOnlyPaths',
    svgText.includes('fill="none" stroke="#344054"'));
  expect('exportFillsBelowStrokes',
    svgText.indexOf('fill-rule="nonzero"') < svgText.indexOf('fill="none"'));

  // 6. Same-color donut: two nested rects + auto-correct directions keep a
  //    real hole inside ONE composite group.
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);
  await page.click('button[aria-label="Design"]');
  await pause(250);
  await page.click('button[title="Enable Fill"]');
  await pause(250);
  await drawRect(400, 300, 700, 560);
  await drawRect(480, 370, 620, 490);
  await page.keyboard.press('v');
  await pause(150);
  await page.mouse.click(150, 150); // deselect so the button is in auto-correct mode
  await pause(250);
  await page.click('button[aria-label="Auto-Correct Path Directions"]');
  await pause(300);
  const donutFills = await compositeFills();
  expect('donutSingleGroup', donutFills.length === 1 && donutFills[0] === '#344054');
  report.donut = await page.evaluate(({ ringPt, holePt }) => {
    const worldGroup = [...document.querySelectorAll('svg g[transform]')]
      .find(g => (g.getAttribute('transform') || '').includes('scale('));
    const m = /translate\((-?[\d.]+),\s*(-?[\d.]+)\)\s*scale\((-?[\d.]+)\)/
      .exec(worldGroup.getAttribute('transform'));
    const tx = Number(m[1]); const ty = Number(m[2]); const s = Number(m[3]);
    const toWorld = (p) => ({ x: (p.x - tx) / s, y: (p.y - ty) / s });
    const path = document.querySelector('svg path[fill-rule="nonzero"]');
    const ring = toWorld(ringPt);
    const hole = toWorld(holePt);
    return {
      subpathCount: (path.getAttribute('d').match(/M/g) || []).length,
      ringFilled: path.isPointInFill(new DOMPoint(ring.x, ring.y)),
      holeFilled: path.isPointInFill(new DOMPoint(hole.x, hole.y))
    };
  }, { ringPt: { x: 440, y: 430 }, holePt: { x: 550, y: 430 } });
  expect('donutHasTwoSubpaths', report.donut.subpathCount === 2);
  expect('donutRingFilled', report.donut.ringFilled === true);
  expect('donutHoleIsHole', report.donut.holeFilled === false);

  // 7. Legacy sessions: strip fillColor from saved paths and point the
  //    defaults at red -> existing art still renders #344054 (read-time
  //    fallback is fixed), while the NEXT drawn path picks up the red.
  await page.evaluate(() => {
    const session = JSON.parse(localStorage.getItem('vector-editor-session-v1'));
    session.paths.forEach(path => { delete path.fillColor; });
    session.pathStyleDefaults = { ...session.pathStyleDefaults, fillColor: '#ff0000' };
    localStorage.setItem('vector-editor-session-v1', JSON.stringify(session));
  });
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  report.legacyFills = await compositeFills();
  expect('legacyPathsKeepOriginalColor',
    report.legacyFills.length === 1 && report.legacyFills[0] === '#344054');
  await drawRect(900, 300, 1000, 380);
  report.fillsWithRedDefault = await compositeFills();
  expect('newPathUsesEditedDefault', report.fillsWithRedDefault.includes('#ff0000'));

  await page.screenshot({ path: '/tmp/shots/phase7c-color.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
