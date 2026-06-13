import { run, APP_URL } from './client.mjs';

// Phase 8F.4: frame Design section + presets + frame export. The Frame tool
// with nothing selected shows a preset list that drops a sized board;
// renaming via the Design panel updates the on-canvas label; the fill
// control recolors the board; exporting scope "Frame" crops the SVG to the
// frame rect with the frame fill as background and any overlapping content
// included.
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

  const firstFrame = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    const f = raw ? (JSON.parse(raw).frames || [])[0] : null;
    return f ? { name: f.name, width: f.width, height: f.height, fill: f.fill } : null;
  });
  const svgTexts = () => page.evaluate(() => [...document.querySelectorAll('svg text')].map(t => t.textContent));
  const clickByText = async (text) => {
    const clicked = await page.evaluate((label) => {
      const t = [...document.querySelectorAll('button')].find(b => b.textContent.trim().toLowerCase() === label.toLowerCase());
      if (t) t.click();
      return !!t;
    }, text);
    if (!clicked) throw new Error(`button not found: ${text}`);
    await pause(150);
  };

  // 1. Frame tool -> preset list -> Phone drops a 390x844 board.
  await page.keyboard.press('f');
  await pause(250);
  await page.evaluate(() => {
    const btn = [...document.querySelectorAll('button')].find(b => /Phone/.test(b.textContent) && /390/.test(b.textContent));
    if (btn) btn.click();
  });
  await pause(400);
  const created = await firstFrame();
  expect('presetDropsFrame', !!created && created.width === 390 && created.height === 844);

  // 2. Rename via the Design panel updates the on-canvas label.
  await page.evaluate(() => {
    const input = document.querySelector('input[title="Frame Name"]');
    if (input) {
      const setter = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, 'value').set;
      setter.call(input, 'Hero');
      input.dispatchEvent(new Event('input', { bubbles: true }));
      input.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', bubbles: true }));
      input.blur();
    }
  });
  await pause(400);
  expect('renameUpdatesLabel', (await firstFrame()).name === 'Hero' && (await svgTexts()).includes('Hero'));

  // 3. Fill control recolors the board (hex field in the popover).
  await page.click('button[title="Frame Fill"]');
  await pause(300);
  await page.evaluate(() => {
    const input = document.querySelector('input[title="Frame Fill (Hex)"]');
    if (input) {
      const setter = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, 'value').set;
      setter.call(input, '333333');
      input.dispatchEvent(new Event('input', { bubbles: true }));
      input.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', bubbles: true }));
      input.blur();
    }
  });
  await pause(400);
  expect('fillRecolorsFrame', (await firstFrame()).fill === '#333333');
  await page.mouse.click(60, 700); // close popover (away from panel)
  await pause(250);

  // 4. Draw a rectangle overlapping the frame so it lands in the export.
  await page.keyboard.press('r');
  await pause(150);
  const frameRect = await page.evaluate(() => {
    const r = [...document.querySelectorAll('svg rect')].find(rr => rr.getAttribute('width') >= 380);
    const b = r.getBoundingClientRect();
    return { cx: b.left + b.width / 2, cy: b.top + b.height / 2 };
  });
  await page.mouse.move(frameRect.cx - 40, frameRect.cy - 40);
  await page.mouse.down();
  await page.mouse.move(frameRect.cx + 40, frameRect.cy + 40, { steps: 6 });
  await page.mouse.up();
  await pause(300);

  // 5. Select the frame (click a clear spot inside, away from the rect +
  //    label), then export scope Frame.
  await page.keyboard.press('v');
  await pause(150);
  const clearSpot = await page.evaluate(() => {
    const r = [...document.querySelectorAll('svg rect')].find(rr => Number(rr.getAttribute('width')) >= 380);
    const b = r.getBoundingClientRect();
    // Left band of the frame, mid of the on-screen portion: inside the board,
    // clear of the centered rect and the (possibly off-screen) name label.
    const visTop = Math.max(b.top, 80);
    const visBottom = Math.min(b.bottom, window.innerHeight - 80);
    return { x: b.left + 24, y: (visTop + visBottom) / 2 };
  });
  await page.mouse.click(clearSpot.x, clearSpot.y);
  await pause(300);
  expect('frameSelectedForExport', await page.evaluate(() => !!document.querySelector('[data-frame-chrome]')));

  await page.click('button[aria-label="Export"]');
  await pause(200);
  await clickByText('Frame');
  await clickByText('svg');
  await clickByText('Export SVG');
  await pause(300);
  const svgText = await page.evaluate(async () => {
    const entry = window.__downloads[window.__downloads.length - 1];
    if (!entry || !entry.href.startsWith('blob:')) return null;
    return { download: entry.download, text: await (await fetch(entry.href)).text() };
  });
  report.exportName = svgText?.download;
  expect('frameExportCropped',
    !!svgText && svgText.text.includes('width="390"') && svgText.text.includes('height="844"'));
  expect('frameExportBackgroundFirst',
    !!svgText && svgText.text.includes('fill="#333333"')
    && svgText.text.indexOf('fill="#333333"') < svgText.text.indexOf('fill-rule="nonzero"'));
  expect('frameExportName', svgText?.download === 'hero.svg');

  // 6. PNG variant rasterizes.
  await clickByText('png');
  await clickByText('Export PNG');
  await pause(800);
  expect('framePng', await page.evaluate(() => {
    const entry = window.__downloads[window.__downloads.length - 1];
    return !!entry && entry.href.startsWith('data:image/png') && entry.download === 'hero.png';
  }));

  await page.screenshot({ path: '/tmp/shots/phase8f4-frame-export.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
