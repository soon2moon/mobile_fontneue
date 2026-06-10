import { run, APP_URL } from './client.mjs';

const LEGACY_KEY = 'typolab-session-v1';
const NEW_KEY = 'vector-editor-session-v1';

run(async (page) => {
  const report = {};

  // Seed a legacy (font-era) session containing guides fields + one square path.
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(([legacyKey, newKey]) => {
    localStorage.removeItem(newKey);
    const layer = { id: 'layer-test-1', name: 'Vector 1', visible: true, locked: false, itemType: 'vector' };
    const payload = {
      layers: [layer],
      paths: [{
        id: 1234567,
        layerId: layer.id,
        closed: true,
        fillEnabled: false,
        points: [
          { x: -100, y: -100 }, { x: 100, y: -100 },
          { x: 100, y: 100 }, { x: -100, y: 100 }
        ]
      }],
      images: [],
      currentPath: [],
      currentPathInfo: null,
      gridConfig: { type: 'lines', size: 50, snapToGrid: true },
      guides: { capHeight: 300, xHeight: 200, descender: 100 },
      showGuides: true,
      showBackgroundAids: true,
      activeLayerId: layer.id
    };
    localStorage.setItem(legacyKey, JSON.stringify(payload));
  }, [LEGACY_KEY, NEW_KEY]);

  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await new Promise(r => setTimeout(r, 600)); // let the save effect run

  report.storage = await page.evaluate(([legacyKey, newKey]) => {
    const raw = localStorage.getItem(newKey);
    const parsed = raw ? JSON.parse(raw) : null;
    return {
      legacyKeyRemoved: localStorage.getItem(legacyKey) === null,
      newKeyExists: raw !== null,
      hasGuidesField: parsed ? ('guides' in parsed) : null,
      hasShowGuidesField: parsed ? ('showGuides' in parsed) : null,
      pathCount: parsed?.paths?.length ?? 0,
      gridType: parsed?.gridConfig?.type ?? null,
      snapToGrid: parsed?.gridConfig?.snapToGrid ?? null
    };
  }, [LEGACY_KEY, NEW_KEY]);

  // Migrated square should render as an SVG path in the canvas.
  report.pathRendered = await page.evaluate(() =>
    document.querySelectorAll('svg path[d]').length > 0
  );

  // No Guides UI anywhere (buttons carried title/label "Guides Config" / "Show Guides" / "Hide Guides").
  report.guidesUi = await page.evaluate(() => {
    const titles = [...document.querySelectorAll('[title]')].map(el => el.getAttribute('title'));
    const texts = document.body.innerText;
    return {
      guidesTitledControls: titles.filter(t => /guides/i.test(t || '')),
      guidesTextPresent: /guides config|show guides|hide guides/i.test(texts)
    };
  });

  // 'G' hotkey must do nothing; 'B' must still toggle the Background Config panel.
  await page.keyboard.press('g');
  await new Promise(r => setTimeout(r, 250));
  report.afterG = await page.evaluate(() => document.body.innerText.match(/Guides Config/i) ? 'guides-panel-opened' : 'nothing');
  await page.keyboard.press('b');
  await new Promise(r => setTimeout(r, 250));
  report.afterB = await page.evaluate(() => /Background Config/i.test(document.body.innerText) ? 'grid-panel-open' : 'no-panel');
  await page.keyboard.press('b'); // close it again

  await page.screenshot({ path: '/tmp/shots/phase05-desktop.png' });
  return report;
});
