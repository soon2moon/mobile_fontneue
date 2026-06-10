import { run, APP_URL } from './client.mjs';

// Export pipeline: draw a rect, export canvas as SVG (assert markup) and as
// PNG (assert data URL). Downloads are intercepted by patching anchor.click.
run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });

  await page.evaluate(() => {
    window.__downloads = [];
    HTMLAnchorElement.prototype.click = function () {
      window.__downloads.push({ href: this.href, download: this.download });
    };
  });

  // Draw a rectangle so there is something to export.
  await page.keyboard.press('r');
  await new Promise(r => setTimeout(r, 150));
  await page.mouse.move(500, 300);
  await page.mouse.down();
  await page.mouse.move(700, 450, { steps: 8 });
  await page.mouse.up();
  await new Promise(r => setTimeout(r, 300));

  const clickByText = async (text) => {
    const clicked = await page.evaluate((label) => {
      const target = [...document.querySelectorAll('button')]
        .find(b => b.textContent.trim().toLowerCase() === label.toLowerCase());
      if (target) target.click();
      return !!target;
    }, text);
    if (!clicked) throw new Error(`button not found: ${text}`);
    await new Promise(r => setTimeout(r, 150));
  };

  // Open the Export panel, scope it to the whole canvas.
  await page.click('button[title="Export"]');
  await new Promise(r => setTimeout(r, 200));
  await clickByText('Canvas');

  // SVG export: blob URL, fetch it back and check the markup.
  await clickByText('svg');
  await clickByText('Export SVG');
  await new Promise(r => setTimeout(r, 300));
  const svgDownload = await page.evaluate(async () => {
    const entry = window.__downloads[window.__downloads.length - 1];
    if (!entry) return null;
    const text = entry.href.startsWith('blob:') ? await (await fetch(entry.href)).text() : null;
    return { download: entry.download, hasPath: !!text && text.includes('<path'), isSvgDoc: !!text && text.startsWith('<svg') };
  });
  report.svg = svgDownload;

  // PNG export: rasterized through an offscreen canvas into a data URL.
  await clickByText('png');
  await clickByText('Export PNG');
  await new Promise(r => setTimeout(r, 800));
  report.png = await page.evaluate(() => {
    const entry = window.__downloads[window.__downloads.length - 1];
    return entry ? { download: entry.download, isPngDataUrl: entry.href.startsWith('data:image/png') } : null;
  });

  report.downloadCount = await page.evaluate(() => window.__downloads.length);

  if (!report.svg || report.svg.download !== 'canvas.svg' || !report.svg.hasPath || !report.svg.isSvgDoc) {
    throw new Error(`svg export failed: ${JSON.stringify(report.svg)}`);
  }
  if (!report.png || report.png.download !== 'canvas.png' || !report.png.isPngDataUrl) {
    throw new Error(`png export failed: ${JSON.stringify(report.png)}`);
  }

  await page.screenshot({ path: '/tmp/shots/export.png' });
  return report;
}, { fresh: true });
