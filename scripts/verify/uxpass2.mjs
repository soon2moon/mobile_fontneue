import { run, APP_URL } from './client.mjs';

// Verifies the "Figma-alignment pass #2" changes: light canvas + #007EEA accent,
// tight selection box, fill opacity, frame nesting (move-together), frame
// rename, and the restyled context menu with the Arrange submenu.
const sleep = (ms) => new Promise(r => setTimeout(r, ms));

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await sleep(300);

  const reload = async () => {
    await page.evaluate(() => localStorage.clear());
    await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
    await sleep(300);
  };
  const drag = async (x1, y1, x2, y2) => {
    await page.mouse.move(x1, y1);
    await page.mouse.down();
    await page.mouse.move(x2, y2, { steps: 10 });
    await page.mouse.up();
    await sleep(250);
  };
  const session = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? JSON.parse(raw) : null;
  });
  const pathCenter = (p) => {
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const pt of p.points || []) {
      minX = Math.min(minX, pt.x); minY = Math.min(minY, pt.y);
      maxX = Math.max(maxX, pt.x); maxY = Math.max(maxY, pt.y);
    }
    return { x: (minX + maxX) / 2, y: (minY + maxY) / 2 };
  };

  // --- A. Theme: off-white canvas + #007EEA accent ---
  try {
    report.theme = await page.evaluate(() => {
      const root = getComputedStyle(document.documentElement);
      const shell = document.querySelector('.bg-canvas');
      return {
        canvasVar: root.getPropertyValue('--color-canvas').trim(),
        accentVar: root.getPropertyValue('--color-accent').trim(),
        shellBg: shell ? getComputedStyle(shell).backgroundColor : null
      };
    });
    report.theme.ok = report.theme.canvasVar === '245 245 245'
      && report.theme.accentVar === '0 126 234'
      && report.theme.shellBg === 'rgb(245, 245, 245)';
  } catch (e) { report.theme = { error: String(e) }; }

  // --- B. Tight selection box (no padding) ---
  try {
    await page.keyboard.press('r');
    await sleep(120);
    await drag(500, 320, 700, 460);
    await page.keyboard.press('v');
    await sleep(120);
    await page.mouse.click(600, 390); // select the rectangle
    await sleep(250);
    report.selectionBox = await page.evaluate(() => {
      const svg = document.querySelector('svg');
      const rects = [...svg.querySelectorAll('rect')];
      const selRect = rects.find(r => (r.getAttribute('fill') || '').includes('0, 126, 234'));
      const shapePath = [...svg.querySelectorAll('g g path[d]')]
        .filter(p => (p.getAttribute('d') || '').length > 10)
        .sort((a, b) => b.getBBox().width - a.getBBox().width)[0];
      if (!selRect || !shapePath) return { found: false };
      const sb = selRect.getBBox();
      const pb = shapePath.getBBox();
      const dashed = !!selRect.getAttribute('stroke-dasharray');
      return {
        found: true, dashed,
        selW: Math.round(sb.width), pathW: Math.round(pb.width),
        widthDelta: Math.round(Math.abs(sb.width - pb.width))
      };
    });
    report.selectionBox.ok = report.selectionBox.found
      && report.selectionBox.widthDelta <= 1
      && report.selectionBox.dashed === false;
  } catch (e) { report.selectionBox = { error: String(e) }; }

  // --- C. Fill & stroke opacity round-trip through a persisted path ---
  // The inspector input can't be driven headlessly (quiet-UI unmounts the
  // chrome after a canvas gesture), so instead patch the saved path's
  // fillOpacity/strokeOpacity, reload, and read the rendered SVG. This proves
  // model → resolver → compositeFill/stroke render AND session persistence.
  try {
    await reload();
    await page.keyboard.press('r');
    await sleep(120);
    await drag(500, 320, 700, 460);
    await sleep(700); // allow the debounced session save
    const patched = await page.evaluate(() => {
      const raw = localStorage.getItem('vector-editor-session-v1');
      if (!raw) return false;
      const s = JSON.parse(raw);
      if (!s.paths || !s.paths.length) return false;
      s.paths[0].fillEnabled = true;
      s.paths[0].fillOpacity = 0.4;
      s.paths[0].strokeEnabled = true;
      s.paths[0].strokeOpacity = 0.3;
      localStorage.setItem('vector-editor-session-v1', JSON.stringify(s));
      return true;
    });
    await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
    await sleep(450);
    report.opacity = await page.evaluate((didPatch) => {
      const fillOps = [...document.querySelectorAll('svg path[fill-opacity]')].map(p => p.getAttribute('fill-opacity'));
      const strokeOps = [...document.querySelectorAll('svg g[stroke-opacity]')].map(g => g.getAttribute('stroke-opacity'));
      return { patched: didPatch, fillOps, strokeOps };
    }, patched);
    report.opacity.ok = report.opacity.patched
      && report.opacity.fillOps.some(o => Math.abs(parseFloat(o) - 0.4) < 0.01)
      && report.opacity.strokeOps.some(o => Math.abs(parseFloat(o) - 0.3) < 0.01);
  } catch (e) { report.opacity = { error: String(e) }; }

  // --- D. Nesting: dragging the frame carries the child rectangle ---
  try {
    await reload();
    await page.keyboard.press('f');     // frame tool
    await sleep(120);
    await drag(250, 180, 820, 600);     // big frame
    await page.keyboard.press('r');     // rectangle tool
    await sleep(120);
    await drag(420, 360, 540, 460);     // rectangle inside the frame
    await page.keyboard.press('v');
    await sleep(150);

    const before = await session();
    const frameBefore = before.frames[0];
    const rectBefore = pathCenter(before.paths[0]);

    await page.mouse.click(310, 540);   // select the frame (empty area inside it)
    await sleep(200);
    await drag(310, 540, 410, 600);     // move the frame by ~ (100,60) screen
    await sleep(650);

    const after = await session();
    const frameAfter = after.frames[0];
    const rectAfter = pathCenter(after.paths[0]);
    const frameDelta = { x: frameAfter.x - frameBefore.x, y: frameAfter.y - frameBefore.y };
    const rectDelta = { x: rectAfter.x - rectBefore.x, y: rectAfter.y - rectBefore.y };
    report.nesting = {
      frameDelta: { x: Math.round(frameDelta.x), y: Math.round(frameDelta.y) },
      rectDelta: { x: Math.round(rectDelta.x), y: Math.round(rectDelta.y) }
    };
    report.nesting.ok = Math.hypot(frameDelta.x, frameDelta.y) > 5
      && Math.abs(frameDelta.x - rectDelta.x) < 1
      && Math.abs(frameDelta.y - rectDelta.y) < 1;
  } catch (e) { report.nesting = { error: String(e) }; }

  // --- E. Frame rename via double-click on the title label ---
  try {
    await reload();
    await page.keyboard.press('f');
    await sleep(120);
    await drag(300, 240, 760, 560);
    await page.keyboard.press('v');
    await sleep(150);
    const nameBefore = (await session()).frames[0].name;
    // Double-click the label (just above the frame's top-left corner).
    await page.mouse.click(330, 232);
    await sleep(90);
    await page.mouse.click(330, 232);
    await sleep(250);
    const editorOpen = await page.evaluate(() => !!document.activeElement
      && document.activeElement.tagName === 'INPUT'
      && document.activeElement.getAttribute('ring') !== undefined || true);
    // Type a new name and commit.
    await page.evaluate(() => {
      const inp = document.activeElement;
      if (inp && inp.tagName === 'INPUT') {
        const setter = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, 'value').set;
        setter.call(inp, 'Renamed Board');
        inp.dispatchEvent(new Event('input', { bubbles: true }));
      }
    });
    await page.keyboard.press('Enter');
    await sleep(650);
    const nameAfter = (await session()).frames[0].name;
    report.rename = { nameBefore, nameAfter };
    report.rename.ok = nameAfter === 'Renamed Board' && nameAfter !== nameBefore;
  } catch (e) { report.rename = { error: String(e) }; }

  // --- F. Context menu restyle + Arrange submenu ---
  try {
    await reload();
    await page.keyboard.press('r');
    await sleep(120);
    await drag(520, 340, 680, 460);
    await page.keyboard.press('v');
    await sleep(120);
    await page.mouse.click(600, 400);   // select rect
    await sleep(150);
    await page.mouse.click(600, 400, { button: 'right' });
    await sleep(300);
    const menu = await page.evaluate(() => {
      const items = [...document.querySelectorAll('[role="menu"] button')].map(b => b.textContent.trim());
      return { items };
    });
    // Hover the Arrange item to open the submenu.
    const arrangeBox = await page.evaluate(() => {
      const b = [...document.querySelectorAll('[role="menu"] button')].find(x => x.textContent.includes('Arrange'));
      if (!b) return null;
      const r = b.getBoundingClientRect();
      return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
    });
    let submenu = [];
    if (arrangeBox) {
      await page.mouse.move(arrangeBox.x, arrangeBox.y);
      await sleep(300);
      submenu = await page.evaluate(() =>
        [...document.querySelectorAll('[role="menu"] button')].map(b => b.textContent.trim()));
    }
    report.contextMenu = { items: menu.items, submenuIncludesBringToFront: submenu.some(t => t.includes('Bring to front')) };
    report.contextMenu.ok = menu.items.some(t => t.includes('Copy'))
      && menu.items.some(t => t.includes('Arrange'))
      && report.contextMenu.submenuIncludesBringToFront;
  } catch (e) { report.contextMenu = { error: String(e) }; }

  await page.screenshot({ path: '/tmp/shots/uxpass2.png' });
  report.allOk = ['theme', 'selectionBox', 'opacity', 'nesting', 'rename', 'contextMenu']
    .every(k => report[k] && report[k].ok);
  return report;
});
