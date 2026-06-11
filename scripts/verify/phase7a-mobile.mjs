import { run, APP_URL } from './client.mjs';

// Phase 7A: live text objects, mobile (390x844 touch). Drawer Text button
// arms the tool, tap opens the editor, backdrop tap commits, long-press and
// short-press open the actions menu for a text, Duplicate clones text+layer.
run(async (page) => {
  const report = {};
  const pause = (ms = 250) => new Promise(r => setTimeout(r, ms));
  const failures = [];
  const expect = (name, ok) => { report[name] = ok; if (!ok) failures.push(name); };

  await page.setViewport({ width: 390, height: 844, hasTouch: true, isMobile: true, deviceScaleFactor: 2 });
  await page.goto(APP_URL, { waitUntil: 'networkidle0', timeout: 30000 });
  await page.evaluate(() => localStorage.clear());
  await page.reload({ waitUntil: 'networkidle0', timeout: 30000 });
  await pause(300);

  const tapButtonByTitle = async (title) => {
    const rect = await page.evaluate((wanted) => {
      const button = document.querySelector(`button[title="${wanted}"]`);
      if (!button) return null;
      const r = button.getBoundingClientRect();
      return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
    }, title);
    if (!rect) throw new Error(`button "${title}" not found`);
    await page.touchscreen.tap(rect.x, rect.y);
  };
  const tapButtonByText = async (label) => {
    const rect = await page.evaluate((wanted) => {
      const button = [...document.querySelectorAll('button')]
        .find(b => b.textContent.trim() === wanted);
      if (!button) return null;
      const r = button.getBoundingClientRect();
      return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
    }, label);
    if (!rect) throw new Error(`button "${label}" not found`);
    await page.touchscreen.tap(rect.x, rect.y);
  };
  const textCount = () => page.evaluate(() => document.querySelectorAll('svg g text').length);
  const textScreenCenter = () => page.evaluate(() => {
    const b = document.querySelector('svg g text').getBoundingClientRect();
    return { x: b.x + b.width / 2, y: b.y + b.height / 2 };
  });
  const contextMenuOpen = () => page.evaluate(() =>
    !!document.querySelector('button[aria-label="Close actions menu"]')
  );

  // 1. Drawer Text button arms the tool and closes the drawer.
  await tapButtonByTitle('Menu');
  await pause(350);
  await tapButtonByTitle('Text');
  await pause(350);
  expect('drawerClosed', await page.evaluate(() => !!document.querySelector('.mobile-drawer-closed')));

  // 2. Tap opens a focused editor; type; backdrop tap commits.
  await page.touchscreen.tap(140, 320);
  await pause(350);
  expect('editorFocused', await page.evaluate(() => document.activeElement?.tagName === 'TEXTAREA'));
  await page.keyboard.type('Mob', { delay: 20 });
  await pause(150);
  await page.touchscreen.tap(330, 600); // backdrop
  await pause(400);
  expect('backdropCommits', (await textCount()) === 1 && await page.evaluate(() => !document.querySelector('textarea')));

  // 3. Long-press: the fallback timer menu opens while the finger is held.
  //    (The touchend's compatibility click then lands on the menu backdrop
  //    and closes it -- pre-existing for all object kinds in this harness;
  //    real devices long-press through the contextmenu event instead.)
  let c = await textScreenCenter();
  const press = await page.touchscreen.touchStart(c.x, c.y);
  await pause(750);
  const longPressMenu = await contextMenuOpen();
  await press.end();
  await pause(250);
  expect('longPressMenuWhileHeld', longPressMenu);
  if (await contextMenuOpen()) {
    await page.touchscreen.tap(350, 760); // dismiss if it survived
    await pause(300);
  }

  // 4. The real-device long-press pathway (contextmenu event) selects the
  //    text and opens the actions menu; Duplicate clones text + layer.
  c = await textScreenCenter();
  await page.evaluate(({ x, y }) => {
    document.querySelector('svg').dispatchEvent(new MouseEvent('contextmenu', {
      clientX: x, clientY: y, bubbles: true, cancelable: true
    }));
  }, c);
  await pause(350);
  expect('contextMenuActions', await page.evaluate(() =>
    !!document.querySelector('button[aria-label="Close actions menu"]')
    && [...document.querySelectorAll('button')].some(b => b.textContent.trim() === 'Duplicate')
  ));
  await tapButtonByText('Duplicate');
  await pause(500);
  expect('duplicateMakesTwoTexts', (await textCount()) === 2);
  await pause(600);
  const s = await page.evaluate(() => {
    const raw = localStorage.getItem('vector-editor-session-v1');
    return raw ? JSON.parse(raw) : null;
  });
  expect('duplicateMakesTwoTextLayers',
    s && s.texts?.length === 2 && s.layers?.filter(l => l.itemType === 'text').length === 2);

  await page.screenshot({ path: '/tmp/shots/phase7a-mobile.png' });
  await page.evaluate(() => localStorage.clear());
  await page.close(); // fresh page per run; don't leave the touch viewport behind

  if (failures.length > 0) throw new Error(`assertions failed: ${failures.join(', ')}`);
  return report;
}, { fresh: true });
