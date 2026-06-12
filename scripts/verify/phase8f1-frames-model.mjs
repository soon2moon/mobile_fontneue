import { run, APP_URL } from './client.mjs';

// Phase 8F.1: the frame object model is threaded (inert — no tool/render
// yet). A seeded session round-trips its frames array and shows the frame's
// layer row; history commits carry frames so undo of an unrelated edit
// preserves them; sessions without frames load clean.
run(async (page) => {
  const report = {};
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));

  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());

  // 1. Seed a session containing a frame + its layer.
  await page.evaluate(() => {
    localStorage.setItem('vector-editor-session-v1', JSON.stringify({
      layers: [{ id: 'layer-frame-1', name: 'Frame 1', visible: true, locked: false, itemType: 'frame' }],
      paths: [],
      images: [],
      texts: [],
      frames: [{
        id: 'frame-seed-1', layerId: 'layer-frame-1', name: 'Frame 1',
        x: 400, y: 300, width: 200, height: 150, fill: '#ffffff', rotation: 0, locked: false
      }],
      currentPath: [],
      currentPathInfo: null,
      activeLayerId: 'layer-frame-1'
    }));
  });
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);

  await page.click('button[aria-label="Layers"]');
  await pause(300);
  expect('frameLayerRowRenders', await page.evaluate(() =>
    document.body.innerText.includes('Frame 1')));

  // 2. An unrelated edit + save keeps the frame in the session.
  await page.keyboard.press('r');
  await pause(150);
  await page.mouse.move(700, 500);
  await page.mouse.down();
  await page.mouse.move(820, 580, { steps: 6 });
  await page.mouse.up();
  await pause(800); // session save settle
  const session = () => page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? JSON.parse(raw) : null;
  });
  let saved = await session();
  expect('framesSurviveSave',
    saved?.frames?.length === 1 && saved.frames[0].width === 200 && saved.frames[0].name === 'Frame 1');
  expect('rectAlsoSaved', saved?.paths?.length === 1);

  // 3. Undo of the rect must NOT wipe the frames array (history carries it).
  await page.keyboard.down('Control');
  await page.keyboard.press('z');
  await page.keyboard.up('Control');
  await pause(800);
  saved = await session();
  expect('undoPreservesFrames', saved?.frames?.length === 1 && saved?.paths?.length === 0);
  await page.keyboard.down('Control');
  await page.keyboard.press('y');
  await page.keyboard.up('Control');
  await pause(800);
  saved = await session();
  expect('redoPreservesFrames', saved?.frames?.length === 1 && saved?.paths?.length === 1);

  // 4. Reload round-trips; a frameless legacy session also loads clean.
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  saved = await session();
  expect('reloadRoundTrips', saved?.frames?.length === 1);
  await page.evaluate(() => {
    const s = JSON.parse(localStorage.getItem('vector-editor-session-v1'));
    delete s.frames;
    localStorage.setItem('vector-editor-session-v1', JSON.stringify(s));
  });
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(400);
  saved = await session();
  expect('framelessSessionLoadsClean', Array.isArray(saved?.frames) && saved.frames.length === 0);

  await page.screenshot({ path: '/tmp/shots/phase8f1-frames-model.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close();

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
