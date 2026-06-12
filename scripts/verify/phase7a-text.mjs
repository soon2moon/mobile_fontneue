import { run, APP_URL } from './client.mjs';

// Phase 7A: live text objects, desktop. Tool arming (T), in-place editor
// commit, session/undo/reload round-trips, double-click re-edit, body drag,
// corner fontSize scaling, SVG export markup, empty-draft discard semantics,
// and texts surviving unrelated undos.
run(async (page) => {
  const report = {};
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const svgText = () => page.evaluate(() => {
    const t = document.querySelector('svg g text');
    if (!t) return null;
    const m = (t.closest('g').getAttribute('transform') || '').match(/translate\(([-\d.]+), ([-\d.]+)\) rotate\(([-\d.]+)\)/);
    return {
      tspans: [...t.querySelectorAll('tspan')].map(ts => ts.textContent),
      content: [...t.querySelectorAll('tspan')].map(ts => ts.textContent).join('\n'),
      fontSize: Number(t.getAttribute('font-size')),
      x: m ? Number(m[1]) : null
    };
  });
  const textCount = () => page.evaluate(() => document.querySelectorAll('svg g text').length);
  const chromeHandles = () => page.evaluate(() =>
    [...document.querySelectorAll('svg rect[stroke="#3b82f6"]')].filter(r => Number(r.getAttribute('width')) < 20).length
  );
  const seHandle = () => page.evaluate(() => {
    const handles = [...document.querySelectorAll('svg rect[stroke="#3b82f6"]')]
      .filter(r => Number(r.getAttribute('width')) < 20);
    if (handles.length === 0) return null;
    const centers = handles.map(h => {
      const b = h.getBoundingClientRect();
      return { x: b.x + b.width / 2, y: b.y + b.height / 2 };
    });
    centers.sort((a, b) => (b.x + b.y) - (a.x + a.y));
    return centers[0];
  });
  const textScreenCenter = () => page.evaluate(() => {
    const b = document.querySelector('svg g text').getBoundingClientRect();
    return { x: b.x + b.width / 2, y: b.y + b.height / 2 };
  });
  const session = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? JSON.parse(raw) : null;
  });
  const undo = async () => {
    await page.keyboard.down('Control'); await page.keyboard.press('z'); await page.keyboard.up('Control');
    await pause(150);
  };
  const redo = async () => {
    await page.keyboard.down('Control'); await page.keyboard.press('y'); await page.keyboard.up('Control');
    await pause(150);
  };

  // 1. T arms the tool; click opens a focused textarea; typing + Esc commits.
  await page.keyboard.press('t');
  await pause(150);
  expect('toolCursor', await page.evaluate(() => document.querySelector('svg').classList.contains('cursor-text')));
  await page.mouse.click(500, 300);
  await pause(250);
  expect('editorFocused', await page.evaluate(() => document.activeElement?.tagName === 'TEXTAREA'));
  await page.keyboard.type('Hello\nWorld', { delay: 15 });
  await page.keyboard.press('Escape');
  await pause(300);
  const committed = await svgText();
  expect('twoTspans', committed && committed.tspans.length === 2 && committed.tspans[0] === 'Hello' && committed.tspans[1] === 'World');
  expect('selectionChrome', (await chromeHandles()) === 4);
  expect('backInEditMode', await page.evaluate(() => !document.querySelector('svg').classList.contains('cursor-text')));

  // 2. Session payload: content + a text layer.
  await pause(600);
  const s = await session();
  expect('sessionContent', s && s.texts?.[0]?.content === 'Hello\nWorld');
  expect('sessionTextLayer', s && s.layers?.some(l => l.itemType === 'text'));

  // 3. Undo removes, redo restores.
  await undo();
  expect('undoRemoves', (await textCount()) === 0);
  await redo();
  expect('redoRestores', (await textCount()) === 1);

  // 4. Reload survives.
  await pause(600);
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  const reloaded = await svgText();
  expect('reloadSurvives', reloaded && reloaded.content === 'Hello\nWorld' && reloaded.fontSize === 96);

  // 5. Click selects (the app boots in pan mode); body drag moves by the
  //    pointer delta.
  await page.keyboard.press('v');
  await pause(150);
  let c = await textScreenCenter();
  await page.mouse.click(c.x, c.y);
  await pause(450); // leave the double-click window
  const beforeDrag = await svgText();
  c = await textScreenCenter();
  await page.mouse.move(c.x, c.y);
  await page.mouse.down();
  await page.mouse.move(c.x + 60, c.y, { steps: 8 });
  await page.mouse.up();
  await pause(250);
  const afterDrag = await svgText();
  expect('bodyDragDx', Math.abs(afterDrag.x - beforeDrag.x - 60) < 0.5);

  // 6. SE-corner drag grows fontSize (content untouched).
  const se = await seHandle();
  await page.mouse.move(se.x, se.y);
  await page.mouse.down();
  await page.mouse.move(se.x + 80, se.y + 55, { steps: 8 });
  await page.mouse.up();
  await pause(250);
  const scaled = await svgText();
  expect('cornerScaleGrowsFont', scaled.fontSize > afterDrag.fontSize && scaled.content === 'Hello\nWorld');

  // 7. Double-click re-edits in place; the edit is one undo step.
  await pause(450);
  c = await textScreenCenter();
  await page.mouse.click(c.x, c.y);
  await pause(80);
  await page.mouse.click(c.x, c.y);
  await pause(300);
  const editor = await page.evaluate(() => {
    const ta = document.querySelector('textarea');
    return ta ? { value: ta.value, focused: document.activeElement === ta } : null;
  });
  expect('dblClickEditorPreloaded', editor && editor.value === 'Hello\nWorld' && editor.focused);
  await page.keyboard.press('End');
  await page.keyboard.type(' again', { delay: 15 });
  await page.keyboard.press('Escape');
  await pause(300);
  expect('reEditCommitted', (await svgText()).content === 'Hello\nWorld again');
  await undo();
  expect('reEditIsOneUndoStep', (await svgText()).content === 'Hello\nWorld');
  await redo();
  expect('reEditRedo', (await svgText()).content === 'Hello\nWorld again');

  // 8. SVG export carries the live text markup.
  await page.evaluate(() => {
    window.__downloads = [];
    HTMLAnchorElement.prototype.click = function () {
      window.__downloads.push({ href: this.href, download: this.download });
    };
  });
  const clickByText = async (label) => {
    const clicked = await page.evaluate((wanted) => {
      const target = [...document.querySelectorAll('button')]
        .find(b => b.textContent.trim().toLowerCase() === wanted.toLowerCase());
      if (target) target.click();
      return !!target;
    }, label);
    if (!clicked) throw new Error(`button not found: ${label}`);
    await pause(150);
  };
  await page.click('button[aria-label="Export"]');
  await pause(200);
  await clickByText('Canvas');
  await clickByText('svg');
  await clickByText('Export SVG');
  await pause(300);
  const exported = await page.evaluate(async () => {
    const entry = window.__downloads[window.__downloads.length - 1];
    if (!entry || !entry.href.startsWith('blob:')) return null;
    return await (await fetch(entry.href)).text();
  });
  expect('exportHasText', !!exported && exported.includes('<text') && exported.includes('Hello'));
  await page.click('button[aria-label="Export"]'); // close the panel again
  await pause(200);

  // 9. Empty draft discards without a history entry: the next undo still
  //    reverts the re-edit, not a phantom step.
  await page.keyboard.press('t');
  await pause(150);
  await page.mouse.click(950, 600);
  await pause(250);
  await page.keyboard.press('Escape');
  await pause(250);
  expect('emptyCommitNoObject', (await textCount()) === 1);
  await undo();
  expect('emptyCommitNoHistory', (await svgText()).content === 'Hello\nWorld');
  await redo();

  // 10. Unrelated undo preserves texts: draw a rect, undo it.
  await page.keyboard.press('r');
  await pause(150);
  await page.mouse.move(900, 200);
  await page.mouse.down();
  await page.mouse.move(1050, 320, { steps: 6 });
  await page.mouse.up();
  await pause(300);
  await undo();
  expect('textsSurviveUnrelatedUndo', (await textCount()) === 1);

  await page.screenshot({ path: '/tmp/shots/phase7a-text.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close(); // fresh page per run (anchor.click is patched)

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
