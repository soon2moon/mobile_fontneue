import { run, APP_URL } from './client.mjs';

// Phase 7B: the unified Inspector replaces the Stroke + Image Settings
// panels. Path selection drives live stroke fields, edits hit attrs,
// mixed selections show indeterminate placeholders, image transform edits
// move the <image>, empty selections edit the next-path defaults, and the
// toolbar Image button / U hotkey open the file chooser directly.
run(async (page) => {
  const report = {};
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

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
  const inputByTitle = (title) => `input[title="${title}"]`;
  const setInputValue = async (title, value) => {
    await page.click(inputByTitle(title));
    await page.keyboard.down('Control');
    await page.keyboard.press('a');
    await page.keyboard.up('Control');
    await page.keyboard.type(String(value), { delay: 15 });
    await page.keyboard.press('Enter');
    await pause(250);
  };
  const strokeWidths = () => page.evaluate(() =>
    [...document.querySelectorAll('svg g g path[d]')]
      .filter(p => (p.getAttribute('d') || '').length > 10)
      .map(p => p.getAttribute('stroke-width'))
  );

  // 1. Draw a rect, select it, open the Inspector: stroke fields are live.
  await drawRect(500, 300, 650, 400);
  await clickPathEdge(575, 300);
  await page.click('button[title="Inspector"]');
  await pause(250);
  report.widthValueForSelection = await page.evaluate((sel) =>
    document.querySelector(sel)?.value ?? null, inputByTitle('Stroke Width'));
  expect('strokeFieldsLive', report.widthValueForSelection === '1.5');

  // 2. Width 4 commits to the selected path's rendered attribute.
  await setInputValue('Stroke Width', '4');
  expect('widthEditHitsAttr', (await strokeWidths())[0] === '4');

  // 3. Second rect with a different color; marquee both -> Mixed placeholders.
  await drawRect(300, 480, 420, 580);
  await clickPathEdge(360, 480);
  await setInputValue('Stroke Color (Hex)', 'ff0000');
  expect('colorEditApplied', (await page.evaluate(() =>
    [...document.querySelectorAll('svg g g path[d]')]
      .filter(p => (p.getAttribute('d') || '').length > 10)
      .map(p => p.getAttribute('stroke'))
  )).includes('#ff0000'));
  await page.mouse.move(250, 250);
  await page.mouse.down();
  await page.mouse.move(700, 620, { steps: 8 });
  await page.mouse.up();
  await pause(300);
  report.mixedPlaceholders = await page.evaluate((widthSel, hexSel) => ({
    width: { value: document.querySelector(widthSel)?.value, placeholder: document.querySelector(widthSel)?.placeholder },
    hex: { value: document.querySelector(hexSel)?.value, placeholder: document.querySelector(hexSel)?.placeholder }
  }), inputByTitle('Stroke Width'), inputByTitle('Stroke Color (Hex)'));
  expect('mixedColorIndeterminate',
    report.mixedPlaceholders.hex.value === '' && report.mixedPlaceholders.hex.placeholder === 'Mixed');
  expect('mixedWidthIndeterminate',
    report.mixedPlaceholders.width.value === '' && report.mixedPlaceholders.width.placeholder === 'Mixed');

  // 4. Paste an image: it opens the Inspector; X/Scale edits move <image>.
  await page.mouse.click(150, 150); // deselect (left side, clear of panel + shapes)
  await pause(250);
  await page.evaluate(async () => {
    const canvas = document.createElement('canvas');
    canvas.width = 60; canvas.height = 40;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#0044aa';
    ctx.fillRect(0, 0, 60, 40);
    const blob = await new Promise(res => canvas.toBlob(res, 'image/png'));
    const dt = new DataTransfer();
    dt.items.add(new File([blob], 't.png', { type: 'image/png' }));
    document.dispatchEvent(new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true }));
  });
  await pause(700);
  const imageTransform = () => page.evaluate(() =>
    document.querySelector('svg image')?.getAttribute('transform') || null);
  expect('imageTransformSection', await page.evaluate((sel) =>
    !!document.querySelector(sel), inputByTitle('X')));
  await setInputValue('X', '50');
  expect('imageXEdit', (await imageTransform())?.startsWith('translate(50,'));
  await setInputValue('Scale', '30');
  expect('imageScaleEdit', (await imageTransform())?.includes('scale(0.3)'));

  // 5. Nothing selected -> edits write the defaults for the next path.
  await page.mouse.click(150, 150);
  await pause(250);
  await setInputValue('Stroke Width', '7');
  await drawRect(900, 480, 1020, 580);
  const widths = await strokeWidths();
  expect('defaultsAffectNextPath', widths[widths.length - 1] === '7');

  // 5b. A text selection shows the Text section; Font Size edits apply live.
  await page.keyboard.press('t');
  await pause(150);
  await page.mouse.click(850, 200);
  await pause(250);
  await page.keyboard.type('Tt', { delay: 15 });
  await page.keyboard.press('Escape');
  await pause(300);
  expect('textSection', await page.evaluate((sel) =>
    !!document.querySelector(sel), inputByTitle('Font Size')));
  await setInputValue('Font Size', '120');
  expect('textFontSizeEdit', await page.evaluate(() =>
    document.querySelector('svg g text')?.getAttribute('font-size') === '120'));
  await page.mouse.click(150, 150); // deselect + blur before the hotkey check
  await pause(250);

  // 6. The old panel headers are gone; the Inspector header exists.
  const headers = await page.evaluate(() =>
    [...document.querySelectorAll('h3')].map(h => h.textContent.trim()));
  report.headers = headers;
  expect('noOldHeaders', !headers.includes('Image Settings') && !headers.includes('Stroke'));
  expect('inspectorHeader', headers.includes('Inspector'));

  // 7. Toolbar Image button and the U hotkey open the file chooser.
  await page.evaluate(() => {
    window.__fileClicks = 0;
    const fileInput = document.querySelector('input[type="file"]');
    fileInput.click = () => { window.__fileClicks += 1; };
  });
  await page.click('button[title="Upload Image (U)"]');
  await pause(150);
  await page.keyboard.press('u');
  await pause(150);
  expect('uploadChooser', (await page.evaluate(() => window.__fileClicks)) === 2);

  await page.screenshot({ path: '/tmp/shots/phase7b-inspector.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close(); // fresh page per run (file input click is patched)

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
