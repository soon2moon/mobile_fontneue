import { run, APP_URL } from './client.mjs';

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });

  // Open Layers panel via its toolbar button — renders LayerIcon rows; session still has the smoke rect.
  await page.click('button[aria-label="Layers"]');
  await new Promise(r => setTimeout(r, 250));
  report.layersPanel = await page.evaluate(() => /Layers/i.test(document.body.innerText));

  // Open the Inspector via its toolbar button (replaced the Stroke panel in 7B).
  report.inspectorOpened = await page.evaluate(() => {
    const btn = document.querySelector('button[aria-label="Design"]');
    if (!btn) return false;
    btn.click();
    return true;
  });
  await new Promise(r => setTimeout(r, 250));
  report.inspectorInputs = await page.evaluate(() => {
    return [...document.querySelectorAll('input[type="text"]')].length;
  });

  await page.screenshot({ path: '/tmp/shots/phase2-panels.png' });
  return report;
});
