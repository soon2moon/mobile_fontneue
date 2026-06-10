import { run, APP_URL } from './client.mjs';

run(async (page) => {
  const report = {};
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });

  // Open Layers panel (L) — renders LayerIcon rows; session still has the smoke rect.
  await page.keyboard.press('l');
  await new Promise(r => setTimeout(r, 250));
  report.layersPanel = await page.evaluate(() => /Layers/i.test(document.body.innerText));

  // Open Stroke panel via its toolbar button (title contains "Stroke Settings").
  report.strokeOpened = await page.evaluate(() => {
    const btn = [...document.querySelectorAll('button[title]')].find(b => /stroke settings/i.test(b.title));
    if (!btn) return false;
    btn.click();
    return true;
  });
  await new Promise(r => setTimeout(r, 250));
  report.strokeInputs = await page.evaluate(() => {
    // ScrubbableNumberInput renders a text input with font-mono inside the stroke panel.
    return [...document.querySelectorAll('input[type="text"]')].length;
  });

  await page.screenshot({ path: '/tmp/shots/phase2-panels.png' });
  return report;
});
