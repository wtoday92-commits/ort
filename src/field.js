/* ORT — поле.
 *
 * Одно поле на все четыре этапа. Конечное и зацикленное по обеим осям: около
 * восьми экранов в ширину и четырнадцати в высоту. Огромная карта оказалась
 * ошибкой: уехав далеко, обратно добираться приходилось бесконечно. Когда
 * карта забивается следами работы, корабль переезжает на новую.
 *
 * Мир переключаемый: у навигационной и лорной вкладки свои поля, и всё
 * состояние поля можно снять одним объектом и подменить целиком.
 *
 * Камера считается В ЯЧЕЙКАХ, а не в пикселях. Это нужно для зума: размер
 * ячейки меняется, и привязка камеры к пикселям ломала бы положение поля.
 *
 * Ощущение собирается из движений, которые не синхронны друг с другом:
 *   1. дрейф всей сетки, направление медленно поворачивает;
 *   2. дыхание каждого глифа со своей фазой и периодом;
 *   3. волна увеличения за курсором, каждый глиф тянется к цели пружиной,
 *      поэтому волна догоняет курсор с запозданием;
 *   4. повадка якоря — то, чем нужный символ выдаёт себя. Не цвет и не яркость,
 *      только поведение, и у каждого вида якоря оно своё.
 */
(function (root) {
  'use strict';

  var G = root.Glyphs;

  var W = 192, H = 192;
  var BASE = 54;                  // пиксели на ячейку при единичном зуме
  var CELL = BASE;
  var zoom = 1;
  var zoomWant = 1;                // куда масштаб едет: скачков быть не должно
  var ZMIN = 0.35, ZMAX = 2.0;
  var SEED = 0x5f3a71;

  /* Плотность блоков. Решётка частая, вероятность пары высокая: так разброс
     числа блоков на экране мал. Пусто почти никогда, пять штук разом редко,
     обычно два-три. Редкая решётка с низкой вероятностью дала бы то же
     среднее, но с провалами и кучами.
     COARSE обязан делить размер мира нацело, иначе решётка не сходится на
     склейке тора. 192 делится на 8. */
  var COARSE = 8;
  var KN = (W / COARSE) | 0;
  var PAIR_P = 0.78;

  var WAVE_R = 195;
  var WAVE_A = 1.10;

  var EDGE = 120;
  var PAN_MAX = 900;

  var VOID_GID = 0;               // три гребёнки: знак вычеркнутого места.
                                  // Линзы читались как ноль, а цифр в игре нет

  function wrap(v, n) { var r = v % n; return r < 0 ? r + n : r; }

  /* Гладкий шум по клеткам. Нужен для того, чтобы качание знаков было СВЯЗНЫМ
     по области: соседи ходят примерно вместе, как трава на ветру. На таком
     фоне неподвижный знак виден как гвоздь в ткани, а при независимых фазах
     он терялся в общей ряби. */
  function vnoise(x, y, sd) {
    var x0 = Math.floor(x), y0 = Math.floor(y);
    var fx = x - x0, fy = y - y0;
    var ux = fx * fx * (3 - 2 * fx), uy = fy * fy * (3 - 2 * fy);
    var a = G.rand3(wrap(x0, 4096), wrap(y0, 4096), sd);
    var b = G.rand3(wrap(x0 + 1, 4096), wrap(y0, 4096), sd);
    var c = G.rand3(wrap(x0, 4096), wrap(y0 + 1, 4096), sd);
    var d = G.rand3(wrap(x0 + 1, 4096), wrap(y0 + 1, 4096), sd);
    return (a * (1 - ux) + b * ux) * (1 - uy) + (c * (1 - ux) + d * ux) * uy;
  }
  function wrapS(v, n) { var r = wrap(v, n); return r > n / 2 ? r - n : r; }
  function ckey(x, y) { return x * 8192 + y; }

  // --- якорные пары ----------------------------------------------------------

  var nodes = new Map();
  var cells = new Map();
  var consumed = new Set();       // пары, уже собранные: их якоря не возвращаются

  function put(x, y, rec) {
    var k = ckey(x, y);
    var cur = cells.get(k);
    if (cur && !(rec.role && !cur.role)) return;
    cells.set(k, rec);
  }

  function buildNode(kx, ky) {
    kx = wrap(kx, KN); ky = wrap(ky, KN);
    var nk = kx * 65536 + ky + 1;
    if (nodes.has(nk)) return nodes.get(nk);

    var pair = null;
    if (G.rand3(kx, ky, SEED + 21) < PAIR_P) {
      var gid = Math.floor(G.rand3(kx, ky, SEED + 22) * G.COUNT);
      if (gid === VOID_GID) gid = (gid + 7) % G.COUNT;
      var kind = Math.floor(G.rand3(kx, ky, SEED + 23) * 5);

      /* Оба конца пары и все её обманки лежат СТРОГО внутри своего блока
         решётки. Блоки не пересекаются, поэтому два узла физически не могут
         писать в одну ячейку, и у пары никогда не пропадает второй край. */
      var ox = 3 + Math.floor(G.rand3(kx, ky, SEED + 24) * 3);
      var oy = 2 + Math.floor(G.rand3(kx, ky, SEED + 25) * 3);
      var ax = Math.floor(G.rand3(kx, ky, SEED + 26) * (COARSE - ox));
      var ay = Math.floor(G.rand3(kx, ky, SEED + 27) * (COARSE - oy));
      var bx = ax + ox, by = ay + oy, sw;
      if (G.rand3(kx, ky, SEED + 28) < 0.5) { sw = COARSE - 1 - bx; bx = COARSE - 1 - ax; ax = sw; }
      if (G.rand3(kx, ky, SEED + 29) < 0.5) { sw = COARSE - 1 - by; by = COARSE - 1 - ay; ay = sw; }

      var ox0 = kx * COARSE, oy0 = ky * COARSE;
      pair = {
        gid: gid, kind: kind, pid: nk,
        a: { x: wrap(ox0 + ax, W), y: wrap(oy0 + ay, H) },
        b: { x: wrap(ox0 + bx, W), y: wrap(oy0 + by, H) }
      };
      put(pair.a.x, pair.a.y, { gid: gid, kind: kind, pid: nk, role: 1, mate: pair.b });
      put(pair.b.x, pair.b.y, { gid: gid, kind: kind, pid: nk, role: 2, mate: pair.a });

      var dn = 1 + Math.floor(G.rand3(kx, ky, SEED + 30) * 2);
      for (var i = 0; i < dn; i++) {
        var dx = Math.floor(G.rand3(kx * 17 + i, ky, SEED + 31) * COARSE);
        var dy = Math.floor(G.rand3(kx, ky * 17 + i, SEED + 32) * COARSE);
        if ((dx === ax && dy === ay) || (dx === bx && dy === by)) continue;
        put(wrap(ox0 + dx, W), wrap(oy0 + dy, H), { gid: gid, kind: kind, pid: 0, role: 0, mate: null });
      }
    }
    nodes.set(nk, pair);
    return pair;
  }

  function ensure(x0, y0, x1, y1) {
    if (cells.size > 300000) { cells.clear(); nodes.clear(); }
    var k0x = Math.floor(x0 / COARSE) - 1, k1x = Math.floor(x1 / COARSE) + 1;
    var k0y = Math.floor(y0 / COARSE) - 1, k1y = Math.floor(y1 / COARSE) + 1;
    for (var ky = k0y; ky <= k1y; ky++)
      for (var kx = k0x; kx <= k1x; kx++) buildNode(kx, ky);
  }

  /* Особые знаки поле хранит вечно и никому не отдаёт. Пустота, отработанное
     анализом, разложенное, утилизированное, осколки, глюки — всё это остаётся
     на карте и не участвует ни в сборе, ни в цепочках, ни в утилизации.
     Пустота есть пустота. */
  function isSpecial(wx, wy) {
    var k = ckey(wx, wy);
    if (voids.has(k) || spent.has(k) || glitch.has(k) || purged.has(k) || shards.has(k) || spin.has(k)) return true;
    return rawGlyph(wx, wy) === VOID_GID;
  }

  function rawGlyph(wx, wy) {
    if (over.has(ckey(wx, wy))) return over.get(ckey(wx, wy));
    var a = cells.get(ckey(wx, wy));
    if (a) return a.gid;
    return G.hash3(wx, wy, SEED) % G.COUNT;
  }

  function anchorAt(wx, wy) {
    var a = cells.get(ckey(wx, wy));
    if (!a) return null;
    if (a.pid && consumed.has(a.pid)) return null;
    if (isSpecial(wx, wy)) return null;      // особый знак якорем не бывает
    return a;
  }

  /* Какой знак стоит в ячейке. У якоря глиф задан парой, у остальных выводится
     из сида. Нужно всем, кто рисует знак вне общего прохода: полёту в сосуд,
     цепочкам анализа. */
  function glyphAt(wx, wy) { return rawGlyph(wx, wy); }

  /* Поиск обычных клеток с заданным начертанием вокруг камеры. Этапы обязаны
     брать то, что на поле УЖЕ есть, а не подставлять новое. */
  var lastVW = 1400, lastVH = 860;

  /* Центр ВИДИМОГО поля в клетках. camCX/camCY — это левый верхний угол
     экрана, а не его середина. Поиск раньше центрировался именно на углу, и
     материал этапов систематически находился вверху слева: существо тянуло
     туда поле, и за каждый круг вся работа уезжала вверх-влево. */
  function viewCentre() {
    return { x: camCX + lastVW / 2 / CELL, y: camCY + (lastVH - 110) / 2 / CELL };
  }

  /* Поиск обычных клеток с заданным начертанием вокруг центра экрана. Находки
     упорядочены по удалённости с небольшим разбросом, а не по порядку обхода:
     обход сверху вниз сам по себе давал крен вверх. need = 0 — вернуть все. */
  function findGlyph(gid, need, spanW, spanH, avoid) {
    var cc = viewCentre();
    var x0 = Math.floor(cc.x) - (spanW >> 1), y0 = Math.floor(cc.y) - (spanH >> 1);
    var hits = [];
    for (var j = 0; j < spanH; j++) {
      for (var i = 0; i < spanW; i++) {
        var wx = wrap(x0 + i, W), wy = wrap(y0 + j, H);
        if (rawGlyph(wx, wy) !== gid) continue;
        if (isSpecial(wx, wy)) continue;
        if (avoid && avoid[ckey(wx, wy)]) continue;
        hits.push({ wx: wx, wy: wy,
          d: Math.abs(i - spanW / 2) + Math.abs(j - spanH / 2) + Math.random() * 4 });
      }
    }
    hits.sort(function (p, q) { return p.d - q.d; });
    return need ? hits.slice(0, need) : hits;
  }

  /* Ближайшее окно указанного размера, где нужное начертание встречается
     достаточно часто. Отсюда берётся блок сортировки. */
  function findRegion(gid, need, bw, bh, spanW, spanH) {
    var cc = viewCentre();
    var x0 = Math.floor(cc.x) - (spanW >> 1), y0 = Math.floor(cc.y) - (spanH >> 1);
    var hits = [];
    for (var j = 0; j < spanH; j++) {
      for (var i = 0; i < spanW; i++) {
        var wx = wrap(x0 + i, W), wy = wrap(y0 + j, H);
        if (rawGlyph(wx, wy) === gid && !isSpecial(wx, wy)) hits.push({ x: x0 + i, y: y0 + j });
      }
    }
    if (hits.length < need) return null;
    var best = null, bestScore = -Infinity;   // оценка отрицательная
    for (var h = 0; h < hits.length; h++) {
      var ox = hits[h].x - (bw >> 1), oy = hits[h].y - (bh >> 1);
      var n = 0;
      for (var k = 0; k < hits.length; k++) {
        if (hits[k].x >= ox && hits[k].x < ox + bw && hits[k].y >= oy && hits[k].y < oy + bh) n++;
      }
      if (n < need) continue;
      /* Целимся в четыре дубля: меньше двух собирать нечего, а десяток
         превращает сортировку в бесконечную возню. Ближе к центру — лучше. */
      var d = Math.abs(hits[h].x - cc.x) + Math.abs(hits[h].y - cc.y);
      var score = -Math.abs(n - 4) * 260 - d;
      if (score > bestScore) { bestScore = score; best = { ox: ox, oy: oy, w: bw, h: bh, n: n }; }
    }
    return best;
  }

  // --- пустоты ---------------------------------------------------------------
  /* Собранный блок не оставляет дыру. На его месте проступают знаки пустоты,
     каждый со своей задержкой и своей манерой появления, и остаются НАВСЕГДА.
     Раньше пустота медленно зарастала обычными знаками. Теперь карта копит
     следы работы, и именно по ним корабль решает, что пора переезжать. */

  var voids = new Map();

  function consume(list, pid) {
    if (pid) consumed.add(pid);
    var cx = 0, cy = 0, i;
    for (i = 0; i < list.length; i++) { cx += list[i].x; cy += list[i].y; }
    cx /= list.length || 1; cy /= list.length || 1;
    for (i = 0; i < list.length; i++) {
      var c = list[i];
      var d = Math.sqrt((c.x - cx) * (c.x - cx) + (c.y - cy) * (c.y - cy));
      voids.set(c.key, {
        born: t + 0.25 + d / 420 + G.rand3(c.wx, c.wy, SEED + 41) * 0.55,
        style: G.hash3(c.wx, c.wy, SEED + 42) % 3
      });
    }
  }

  function voidState(v, wx, wy) {
    var age = t - v.born;
    if (age < 0) return null;                       // ещё не проступил
    var inn = Math.min(1, age / 0.85);
    var e = 1 - Math.pow(1 - inn, 3);
    var s = 1, a = e, sy = 1;
    if (v.style === 0) s = 0.45 + e * 0.55 + Math.sin(inn * Math.PI) * 0.14;
    else if (v.style === 1) { s = 1; a = e * e; }
    else { sy = 0.06 + e * 0.94; }
    return { s: s, a: a, sy: sy };
  }

  // --- состояние -------------------------------------------------------------

  var camCX = 0, camCY = 0;        // камера в ЯЧЕЙКАХ, левый верхний угол
  var driftAng = 1.1, driftSpd = 5.2;
  var driftVX = 0, driftVY = 0;    // px/s
  var panVX = 0, panVY = 0;
  var lagVX = 0, lagVY = 0;        // снос отстающих: при заморозке замирает, а не обнуляется
  var freeze = 0;
  var t = 0;

  var states = new Map();
  var atlas = null;
  var sel = null, dimOthers = 0, liftSel = 0;
  var hot = 0;                     // доля ярко поднятых знаков: её слышно в звуке
  var boost = null;
  var marks = null;                // накладка этапа: цепочки и доска сортировки
  var over = new Map();            // следы работы игрока: знаки, переставленные навсегда
  var spent = new Set();           // отработанные на анализе: осели вдвое и поблёкли
  var glitch = new Set();          // якоря-глюки: сортировка сомкнула разные группы
  var purged = new Map();          // утилизированные: белый круг со знаком внутри
  var shards = new Set();          // расщеплённые: серые осколки в клетке
  var outlines = [];               // рамки вокруг разложенных групп
  var sortedCells = 0;             // сколько клеток легло в разложенные группы: заполненность
  var beacon = -1;                 // знак, которым корабль сигналит о переезде
  var streak = 0, streakX = 0, streakY = 0;   // шлейф быстрого перемещения
  var conDim = 0;                  // гашение поля в режиме ввода команды
  var fadeAll = 1;                 // общее проявление поля: переезд, выброс
  var glide = null;                // куда плывёт центр камеры, в клетках
  var spin = new Map();            // крутящиеся знаки: сбой на краю собранного блока
  var sortedOf = new Map();        // клетка -> контур разложенной группы, в которую она входит
  var selBoard = false;            // рамка — это доска сортировки: знаки у кромки не отжимать
  var traceFn = null;              // кому сообщать о новых особых знаках: хранилище данных

  /* Сила повадок. Выдают себя ТОЛЬКО настоящие якоря: обманки молчат, иначе
     игрок раз за разом находит знак с повадкой, держит на нём три секунды и
     получает пустоту.

     Величина эта ПЛАВНАЯ и меняется за пару секунд. Резкое переключение было
     хуже самой болезни: на смене этапа и на нажатии кнопки все отстающие и
     уклоняющиеся разом прыгали в центр своих клеток и тем себя выдавали.
     Поэтому на сборе она просто всегда единица, а вне сбора медленно тает. */
  var behWant = 1, behAmt = 1;

  function init() {
    // атлас печётся с запасом по детали, чтобы держать зум до двукратного
    atlas = G.buildAtlas(BASE, 'rgb(255,158,58)', BASE * 0.10, 0.64, 2);
    camCX = W * 0.5; camCY = H * 0.5;
  }

  /* Всё состояние поля одним объектом. Карты и множества передаются ссылками,
     поэтому снятый мир продолжает жить своей жизнью, пока его не вернут. */
  function saveWorld() {
    return {
      W: W, H: H, SEED: SEED, PAIR_P: PAIR_P,
      camCX: camCX, camCY: camCY, zoom: zoom, zoomWant: zoomWant,
      driftAng: driftAng, driftVX: driftVX, driftVY: driftVY,
      panVX: panVX, panVY: panVY, lagVX: lagVX, lagVY: lagVY,
      t: t, states: states, over: over, spent: spent, glitch: glitch,
      purged: purged, shards: shards, outlines: outlines, voids: voids,
      nodes: nodes, cells: cells, consumed: consumed, behWant: behWant, behAmt: behAmt,
      shardId: shardId, sortedCells: sortedCells, beacon: beacon, spin: spin, sortedOf: sortedOf
    };
  }

  function loadWorld(o) {
    W = o.W; H = o.H; SEED = o.SEED; PAIR_P = o.PAIR_P;
    KN = (W / COARSE) | 0;
    camCX = o.camCX; camCY = o.camCY; zoom = o.zoom; zoomWant = o.zoomWant; CELL = BASE * zoom;
    driftAng = o.driftAng; driftVX = o.driftVX; driftVY = o.driftVY;
    panVX = o.panVX; panVY = o.panVY; lagVX = o.lagVX; lagVY = o.lagVY;
    t = o.t; states = o.states; over = o.over; spent = o.spent; glitch = o.glitch;
    purged = o.purged; shards = o.shards; outlines = o.outlines; voids = o.voids;
    nodes = o.nodes; cells = o.cells; consumed = o.consumed;
    behWant = o.behWant; behAmt = o.behAmt;
    shardId = o.shardId; sortedCells = o.sortedCells; beacon = o.beacon;
    spin = o.spin || new Map(); sortedOf = o.sortedOf || new Map();
    marks = null; boost = null; sel = null; glide = null; streak = 0;
  }

  /* Совсем новый мир: другой сид, ни одного следа, камера в середине. */
  function freshWorld(opt) {
    var z = opt.zoom || zoom || 1;
    return {
      W: opt.w, H: opt.h, SEED: opt.seed, PAIR_P: opt.pairP === undefined ? 0.78 : opt.pairP,
      camCX: opt.w * 0.5, camCY: opt.h * 0.5, zoom: z, zoomWant: z,
      driftAng: Math.random() * 6.28, driftVX: 0, driftVY: 0, panVX: 0, panVY: 0, lagVX: 0, lagVY: 0,
      t: 0, states: new Map(), over: new Map(), spent: new Set(), glitch: new Set(),
      purged: new Map(), shards: new Set(), outlines: [], voids: new Map(),
      nodes: new Map(), cells: new Map(), consumed: new Set(), behWant: 1, behAmt: 1,
      shardId: new Map(), sortedCells: 0, beacon: -1, spin: new Map(), sortedOf: new Map()
    };
  }

  /* Мир навигации между запусками. Сохраняются только следы работы: сами
     якоря заново строятся из сида, а знаки начинают анимацию с покоя.
     Контур разложенной группы помнит номер своей фигуры в хранилище. */
  function worldToJSON(o) {
    function mp(m) { var a = []; m.forEach(function (v, k) { a.push([k, v]); }); return a; }
    function st(s) { return Array.from(s); }
    return {
      W: o.W, H: o.H, SEED: o.SEED, PAIR_P: o.PAIR_P,
      camCX: o.camCX, camCY: o.camCY, zoom: o.zoomWant, driftAng: o.driftAng, t: o.t,
      over: mp(o.over), spent: st(o.spent), glitch: st(o.glitch), purged: mp(o.purged),
      shards: st(o.shards), voids: mp(o.voids), consumed: st(o.consumed), shardId: mp(o.shardId),
      spin: mp(o.spin), sortedCells: o.sortedCells,
      outlines: o.outlines.map(function (ol) {
        return { c: ol.list.map(function (c) { return [c.wx, c.wy]; }), inv: ol.invId || 0 };
      })
    };
  }

  function worldFromJSON(j) {
    var o = freshWorld({ w: j.W, h: j.H, seed: j.SEED, pairP: j.PAIR_P, zoom: j.zoom || 1 });
    o.camCX = j.camCX; o.camCY = j.camCY; o.driftAng = j.driftAng || 0; o.t = j.t || 0;
    o.over = new Map(j.over || []); o.spent = new Set(j.spent || []); o.glitch = new Set(j.glitch || []);
    o.purged = new Map(j.purged || []); o.shards = new Set(j.shards || []); o.voids = new Map(j.voids || []);
    o.consumed = new Set(j.consumed || []); o.shardId = new Map(j.shardId || []); o.spin = new Map(j.spin || []);
    o.sortedCells = j.sortedCells || 0;
    (j.outlines || []).forEach(function (s) {
      var list = s.c.map(function (p) { return { wx: p[0], wy: p[1] }; }), set = {};
      list.forEach(function (c) { set[c.wx + '|' + c.wy] = 1; });
      var ol = { list: list, set: set, invId: s.inv || 0 };
      o.outlines.push(ol);
      list.forEach(function (c) { o.sortedOf.set(ckey(c.wx, c.wy), ol); });
    });
    return o;
  }

  /* Заполненность карты следами работы: пустота, утилизированное, осколки,
     глюки, разложенные группы и выбранные пары. Корабль переезжает по ней. */
  function fill() {
    var traces = voids.size + purged.size + shards.size + glitch.size + sortedCells;
    var pairs = KN * KN * PAIR_P || 1;
    return Math.max(traces / (W * H), consumed.size / pairs * 0.5);
  }

  function isVoidCell(wx, wy) {
    var k = ckey(wx, wy), v = voids.get(k);
    if (v) return t >= v.born;
    if (purged.has(k) || shards.has(k)) return false;
    return rawGlyph(wx, wy) === VOID_GID;
  }

  /* Ближайшая к точке экрана клетка: у знаков есть разброс внутри клетки,
     поэтому простое деление на размер клетки промахивается. */
  function cellNear(x, y) {
    var c = screenToCell(x, y), best = null, bd = Infinity;
    for (var dy = -1; dy <= 1; dy++) {
      for (var dx = -1; dx <= 1; dx++) {
        var wx = wrap(c.x + dx, W), wy = wrap(c.y + dy, H);
        var p = cellCenter(wx, wy);
        var d2 = (p.x - x) * (p.x - x) + (p.y - y) * (p.y - y);
        if (d2 < bd) { bd = d2; best = { wx: wx, wy: wy, x: p.x, y: p.y, d: Math.sqrt(d2) }; }
      }
    }
    return best;
  }

  /* Знак пустоты под курсором: и оставшийся от сбора, и стоявший на карте
     изначально. С него начинается ввод команды. */
  function voidNear(x, y, tol) {
    var c = screenToCell(x, y), best = null, bd = tol * tol;
    for (var dy = -1; dy <= 1; dy++) {
      for (var dx = -1; dx <= 1; dx++) {
        var wx = wrap(c.x + dx, W), wy = wrap(c.y + dy, H);
        if (!isVoidCell(wx, wy)) continue;
        var p = cellCenter(wx, wy);
        var d2 = (p.x - x) * (p.x - x) + (p.y - y) * (p.y - y);
        if (d2 < bd) { bd = d2; best = { wx: wx, wy: wy, x: p.x, y: p.y }; }
      }
    }
    return best;
  }

  /* Все знаки пустоты на экране: существу надо найти, откуда начать команду. */
  function voidsOnScreen(vw, vh) {
    var x0c = Math.floor(camCX), y0c = Math.floor(camCY);
    var nx = Math.ceil(vw / CELL) + 1, ny = Math.ceil(vh / CELL) + 1;
    var res = [];
    for (var j = 0; j < ny; j++) {
      for (var i = 0; i < nx; i++) {
        var wx = wrap(x0c + i, W), wy = wrap(y0c + j, H);
        if (!isVoidCell(wx, wy)) continue;
        var p = cellCenter(wx, wy);
        res.push({ wx: wx, wy: wy, x: p.x, y: p.y });
      }
    }
    return res;
  }

  function setFreeze(v) { freeze = v; }
  function setSel(r, dim, lift, board) { sel = r; dimOthers = dim || 0; liftSel = lift || 0; selBoard = !!board; }
  function setBoost(m) { boost = m; }
  function setMarks(m) { marks = m; }
  function setHunting(m) { behWant = m ? 1 : 0; }
  function setOverride(k, id) { over.set(k, id); }
  function setSpent(k) { spent.add(k); }
  function emit(ev) { if (traceFn) traceFn(ev); }
  function keyXY(k) { return { wx: Math.floor(k / 8192), wy: k % 8192 }; }
  function setGlitch(k) {
    if (glitch.has(k)) return;
    glitch.add(k);
    var c = keyXY(k);
    emit({ type: 'glitch', key: k, id: rawGlyph(c.wx, c.wy) });
  }
  function isGlitch(k) { return glitch.has(k); }
  function setPurged(k, id) {
    purged.set(k, id);
    var c = keyXY(k);
    emit({ type: 'purged', key: k, id: id, wx: c.wx, wy: c.wy, outline: sortedOf.get(k) || null });
  }
  function setShards(k, id) { shards.add(k); shardGlyph(k, id); emit({ type: 'shard', key: k, id: id }); }

  /* Рамка вокруг разложенной группы. Обводим не габарит, а сам контур: рисуем
     только те грани клеток, за которыми группы уже нет. */
  function addOutline(cells) {
    sortedCells += cells.length;
    var set = {};
    for (var i = 0; i < cells.length; i++) set[cells[i].wx + '|' + cells[i].wy] = 1;
    var ol = { list: cells, set: set };
    outlines.push(ol);
    // клетки разложенной группы запоминаются навсегда: следующая сортировка их не тронет
    for (var j = 0; j < cells.length; j++) sortedOf.set(ckey(cells[j].wx, cells[j].wy), ol);
    if (outlines.length > 60) outlines.shift();
    emit({ type: 'outline', outline: ol, cells: cells, W: W, H: H });
  }

  /* Зум колесом. Точка мира под курсором остаётся на месте, иначе поле
     выпрыгивает из-под руки. */
  function setZoom(z, ax, ay) {
    z = Math.max(ZMIN, Math.min(ZMAX, z));
    zoomWant = z;
    var wx = camCX + ax / CELL, wy = camCY + ay / CELL;
    zoom = z; CELL = BASE * zoom;
    camCX = wrap(wx - ax / CELL, W);
    camCY = wrap(wy - ay / CELL, H);
  }

  function edgePan(cursor, vw, vh, dt, allow) {
    var tx = 0, ty = 0;
    if (allow && cursor) {
      if (cursor.x < EDGE) tx = -Math.pow((EDGE - cursor.x) / EDGE, 1.7);
      else if (cursor.x > vw - EDGE) tx = Math.pow((cursor.x - (vw - EDGE)) / EDGE, 1.7);
      if (cursor.y < EDGE) ty = -Math.pow((EDGE - cursor.y) / EDGE, 1.7);
      else if (cursor.y > vh - EDGE) ty = Math.pow((cursor.y - (vh - EDGE)) / EDGE, 1.7);
    }
    panVX += (tx * PAN_MAX - panVX) * Math.min(1, dt * 2.6);
    panVY += (ty * PAN_MAX - panVY) * Math.min(1, dt * 2.6);
  }

  function update(dt, cursor, vw, vh, allowPan) {
    t += dt;
    lastVW = vw; lastVH = vh;
    var live = 1 - freeze;
    driftAng += Math.sin(t * 0.043) * 0.16 * dt + Math.sin(t * 0.017 + 2.1) * 0.09 * dt;
    driftVX += (Math.cos(driftAng) * driftSpd - driftVX) * Math.min(1, dt * 1.4);
    driftVY += (Math.sin(driftAng) * driftSpd - driftVY) * Math.min(1, dt * 1.4);
    // снос отстающих держится на замороженной скорости: иначе при нажатии
    // мыши все они разом возвращались бы в сетку и выдавали себя
    lagVX += (driftVX - lagVX) * Math.min(1, dt * 1.4) * live;
    lagVY += (driftVY - lagVY) * Math.min(1, dt * 1.4) * live;
    // повадки гаснут и возвращаются за пару секунд, а не мгновенно
    behAmt += (behWant - behAmt) * Math.min(1, dt * 0.55);
    if (Math.abs(zoomWant - zoom) > 0.002) {
      var nz = zoom + (zoomWant - zoom) * Math.min(1, dt * 2.6);
      var keep = zoomWant;
      setZoom(nz, vw / 2, (vh - 110) / 2);
      zoomWant = keep;
    }
    edgePan(cursor, vw, vh, dt, allowPan);
    // дрейф замирает вместе с полем, а прокрутка краем работает всегда:
    // материал этапа может лежать за экраном, и до него надо доехать
    camCX = wrap(camCX + (driftVX * live + panVX) * dt / CELL, W);
    camCY = wrap(camCY + (driftVY * live + panVY) * dt / CELL, H);

    // камера плывёт к заданной точке: переезд и лорные этапы подводят к блоку
    if (glide) {
      var gx0 = glide.x - lastVW / 2 / CELL, gy0 = glide.y - (lastVH - 110) / 2 / CELL;
      var ddx = wrapS(gx0 - camCX, W), ddy = wrapS(gy0 - camCY, H);
      var gk = Math.min(1, dt * 2.2);
      camCX = wrap(camCX + ddx * gk, W); camCY = wrap(camCY + ddy * gk, H);
      if (Math.abs(ddx) + Math.abs(ddy) < 0.05) glide = null;
    }
  }

  var dt_ = 0.016;
  function setDt(d) { dt_ = d; }

  /* Повадки якорей. Ни одна не меняет ни цвет, ни яркость: только поведение,
     и каждая требует своего рода внимания.
       0 затаившийся — не дышит вовсе;
       1 отстающий   — отстаёт от дрейфа, виден на его повороте;
       2 тяжёлый     — волна доходит позже и поднимает выше;
       3 сбойный     — дышит, но раз в несколько секунд спотыкается. */
  /* Каждая повадка домножена на силу, поэтому включается и гаснет плавно. */
  function behave(kind, o) {
    var w = behAmt;
    switch (kind) {
      // затаившийся: не дышит и не качается вовсе. Соседи ходят связной
      // волной, и окаменевший знак в ней виден сразу
      /* Затаившийся ещё и не поднимается на волне. Одной неподвижности было
         мало: соседи качаются очень медленно, и замерший знак среди них
         не читался вовсе. Теперь курсор проходит, всё вокруг раздувается, а
         он остаётся плоским, как пятно. */
      case 0: o.breath = 1 - w; o.rot = 1 - w; o.waveMul = 1 - 0.92 * w; break;
      // отстающий: заметно сносится против общего хода
      case 1: o.lag = 6.2 * w; break;
      // тяжёлый: волна доходит поздно, поднимает высоко и опадает долго.
      // Именно долгое опадание его и выдаёт: курсор уже ушёл, а знак
      // ещё стоит раздутым, когда все соседи давно сложились. Опадание
      // растянуто втрое: при прежнем его было не отличить от соседей
      case 2:
        o.waveMul = 1 + 1.3 * w;
        o.rise = 9.5 + (1.8 - 9.5) * w;
        o.fall = 9.5 + (0.27 - 9.5) * w;
        break;
      // сбойный: качается, но раз в пару секунд спотыкается и дёргается
      case 3:
        var c = (t * 0.45 + o.ph * 0.16) % 1;
        if (c < 0.22) { o.breathFreeze = w > 0.5 ? 1 : 0; o.kick = (0.22 - c) * 9 * w; }
        break;
      // уклоняющийся: уходит от курсора вбок, лишь бы не попасть под волну
      case 4: o.evade = w; break;
    }
  }

  var out = {};

  function each(vw, vh, cursor, fn) {
    var x0c = Math.floor(camCX) - 1, y0c = Math.floor(camCY) - 1;
    var nx = Math.ceil(vw / CELL) + 3, ny = Math.ceil(vh / CELL) + 3;
    ensure(x0c, y0c, x0c + nx, y0c + ny);

    var cxp = cursor ? cursor.x : -1e9, cyp = cursor ? cursor.y : -1e9;
    var live = 1 - freeze;
    var breathDamp = 1 - 0.66 * freeze;
    var zs = CELL / BASE;

    for (var j = 0; j < ny; j++) {
      for (var i = 0; i < nx; i++) {
        var gx = x0c + i, gy = y0c + j;
        var wx = wrap(gx, W), wy = wrap(gy, H);
        var key = ckey(wx, wy);

        var mk = marks ? marks.get(key) : null;
        var vd = voids.get(key), vs = null;
        // доска сортировки сама решает, что лежит в клетке: пустоту там сдвигают
        if (vd && mk && mk.id !== undefined) vd = null;
        if (vd) {
          vs = voidState(vd, wx, wy);
          if (!vs) continue;                       // место ещё пустое
        }

        var sx = (gx - camCX) * CELL + CELL / 2 + jitterX(wx, wy);
        var sy = (gy - camCY) * CELL + CELL / 2 + jitterY(wx, wy);

        var anc = vd ? null : anchorAt(wx, wy);
        var id = anc ? anc.gid : (G.hash3(wx, wy, SEED) % G.COUNT);
        if (over && over.has(key)) id = over.get(key);

        /* И фаза, и ПЕРИОД качания берутся из гладкого шума. Связной была
           только фаза, а период оставался случайным на клетку: соседи
           расходились за несколько секунд, и обычный знак начинал биться
           против всех, изображая повадку. Это и были ложные якоря. */
        var ph = (vnoise(wx / 7, wy / 7, SEED + 6) * 0.86
                + G.rand3(wx, wy, SEED + 1) * 0.14) * Math.PI * 2;
        var rt = 0.24 + vnoise(wx / 9, wy / 9, SEED + 8) * 0.22
               + G.rand3(wx, wy, SEED + 2) * 0.05;

        var px0 = 0, py0 = 0;
        out.breath = 1; out.lag = 0; out.waveMul = 1;
        out.rise = 0; out.fall = 0; out.evade = 0;
        out.breathFreeze = 0; out.kick = 0; out.rot = 1;
        out.ph = ph;
        if (anc && anc.role && behAmt > 0.002) behave(anc.kind, out);

        var bt = out.breathFreeze ? Math.floor(t * 1.6) / 1.6 : t;
        var amp = 3.6 * zs * out.breath * breathDamp;
        var ox = Math.sin(bt * rt * 2 * Math.PI * 0.16 + ph) * amp;
        var oy = Math.cos(bt * rt * 2 * Math.PI * 0.13 + ph * 1.7) * amp;
        if (out.kick) { ox += Math.sin(ph * 5.1) * out.kick * zs * 2.4; }
        if (out.lag) { ox -= lagVX * out.lag * zs; oy -= lagVY * out.lag * zs; }

        /* Качание знака. Поворот читается глазом куда лучше, чем сдвиг на
           полтора пикселя, поэтому именно на нём держится вся заметность
           повадок: у затаившегося он ровно нулевой. */
        var rot = Math.sin(bt * rt * 2 * Math.PI * 0.11 + ph) * 0.125
                * out.rot * breathDamp;

        if (mk) {
          if (mk.id !== undefined) id = mk.id;
          if (mk.hide) continue;
          /* Накладка двигает знак сама: подтяг узла к следующему в анализе и
             всё перетаскивание в сортировке живут здесь. Раньше поле читало
             из накладки только поворот, поэтому знак под курсором не ехал
             вовсе, и перетаскивания просто не было видно. */
          px0 = mk.px || 0; py0 = mk.py || 0;
          // на доске сортировки знак стоит в клетке ровно: ни дыхания, ни
          // повадок, иначе соседи наползают друг на друга
          if (mk.still) { ox = 0; oy = 0; rot = 0; }
          rot += mk.lean || 0;
          if (mk.head && !mk.still) ox += Math.sin(t * 2.1 + ph) * 2.2 * zs;
        }

        // сбойный знак на краю собранного блока крутится в своей клетке
        if (spin.has(key)) rot = t * 1.9 + (key % 7);

        var px = sx + ox + px0, py = sy + oy + py0;

        var inSel = 0;
        if (sel) {
          var insideX = px > sel.x0 && px < sel.x1, insideY = py > sel.y0 && py < sel.y1;
          inSel = (insideX && insideY) ? 1 : 0;
          var eb = selBoard ? 0 : 15;
          if (insideY && eb) {
            if (Math.abs(px - sel.x0) < eb) px += (eb - Math.abs(px - sel.x0)) * 0.22;
            if (Math.abs(px - sel.x1) < eb) px -= (eb - Math.abs(px - sel.x1)) * 0.22;
          }
          if (insideX && eb) {
            if (Math.abs(py - sel.y0) < eb) py += (eb - Math.abs(py - sel.y0)) * 0.22;
            if (Math.abs(py - sel.y1) < eb) py -= (eb - Math.abs(py - sel.y1)) * 0.22;
          }
        }

        var wr = WAVE_R * Math.min(1.4, Math.max(0.6, zs));
        var dx = px - cxp, dy = py - cyp;
        var d = Math.sqrt(dx * dx + dy * dy) || 1e-4;

        /* Уклоняющийся отходит от курсора и сам же уводит себя из-под волны:
           со стороны это выглядит как испуг. Сила уклонения зависит от
           СКОРОСТИ курсора: на быстром проходе знак отпрыгивает, а стоит
           замереть, и он возвращается на место. Иначе нажать на него было бы
           нельзя вовсе, а проверка выдержкой и так требует неподвижности. */
        if (out.evade && d < wr) {
          var spd = cursor && cursor.spd ? Math.min(1, cursor.spd / 380) : 0;
          var push = Math.pow(1 - d / wr, 1.5) * 32 * zs * spd * out.evade;
          px += (dx / d) * push; py += (dy / d) * push;
          dx = px - cxp; dy = py - cyp;
          d = Math.sqrt(dx * dx + dy * dy) || 1e-4;
        }

        var f = d < wr ? Math.pow(1 - d / wr, 2.1) : 0;
        // накладка этапа просит тишины: волна курсора знак не раздувает
        if (mk && mk.calm) f = 0;

        var st = states.get(key);
        if (!st) { st = { s: 1, seen: 0 }; states.set(key, st); }
        var tgt = 1 + f * WAVE_A * out.waveMul;
        // подъём и спад считаются раздельно: у тяжёлого знака спад медленный,
        // и это его главная примета
        var kk = tgt > st.s ? (out.rise || 9.5) : (out.fall || 9.5);
        st.s += (tgt - st.s) * Math.min(1, dt_ * kk);
        st.seen = t;

        var dim = 0.62 + G.rand3(wx, wy, SEED + 3) * 0.38;
        var bo = boost ? (boost.get(key) || 0) : 0;

        /* Глюк-якорь дрожит быстро и мелко и мерцает не в такт ничему. Он
           обязан читаться как сбой, а не как повадка. */
        var gl = glitch.has(key) ? 1 : 0;
        if (gl) {
          px += Math.sin(t * 41 + key) * 2.6 * zs;
          py += Math.cos(t * 37 + key * 1.7) * 1.8 * zs;
        }

        fn(gx, gy, wx, wy, key, id, px, py, st.s, f, dim, inSel, bo, anc, vs, rot, mk, spent.has(key) ? 1 : 0, gl,
           purged.has(key) ? purged.get(key) : -1, shards.has(key) ? 1 : 0);
      }
    }
    if (states.size > 9000) {
      states.forEach(function (v, k2) { if (t - v.seen > 3) states.delete(k2); });
    }
  }

  function jitterX(wx, wy) { return (G.rand3(wx, wy, SEED + 4) - 0.5) * CELL * 0.26; }
  function jitterY(wx, wy) { return (G.rand3(wx, wy, SEED + 5) - 0.5) * CELL * 0.22; }

  /* Базовое преобразование холста на время отрисовки поля. Поворот знака
     задаётся прямо матрицей: три тысячи пар save/restore в кадр были
     заметной долей всей работы. */
  var baseT = null;

  function blit(ctx, id, px, py, s, sy, a, box, rot) {
    var w = box * s, h = box * s * sy;
    ctx.globalAlpha = Math.min(1, a);
    if (!rot) { atlas.draw(ctx, id, px - w / 2, py - h / 2, w, h); return; }
    if (baseT) {
      var B = baseT, c = Math.cos(rot), sn = Math.sin(rot);
      ctx.setTransform(B.a * c + B.c * sn, B.b * c + B.d * sn, B.c * c - B.a * sn, B.d * c - B.b * sn,
                       B.a * px + B.c * py + B.e, B.b * px + B.d * py + B.f);
      atlas.draw(ctx, id, -w / 2, -h / 2, w, h);
      ctx.setTransform(B.a, B.b, B.c, B.d, B.e, B.f);
      return;
    }
    ctx.save();
    ctx.translate(px, py);
    ctx.rotate(rot);
    atlas.draw(ctx, id, -w / 2, -h / 2, w, h);
    ctx.restore();
  }

  /* Утилизационная метка. Белая, и потому обязана светиться: тонкий белый
     контур на амбровом поле выглядит чужой наклейкой, а не частью записи. */
  /* Готовые картинки для знаков со свечением. Размытие тени — самая дорогая
     операция холста. Раньше оно считалось заново для каждого утилизированного
     знака в каждом кадре, и чем больше их копилось на карте, тем тяжелее
     становился кадр, пока браузер не вставал. Теперь свечение рисуется один
     раз на начертание и размер клетки. */
  var sheet = null;

  function sprite(key, drawFn) {
    if (!sheet) sheet = new G.SpriteSheet(2048);
    var size = Math.max(8, Math.round(CELL / 4) * 4);
    var dim = Math.ceil(size * 1.9);
    return sheet.get(key + '|' + size, dim, dim, function (c) { drawFn(c, size); });
  }

  function drawPurged(ctx, px, py, id, s, a) {
    var sp = sprite('pu' + id, function (c, S) {
      var r = S * 0.34;
      c.globalCompositeOperation = 'lighter';
      c.shadowColor = 'rgba(214,232,255,0.95)';
      c.shadowBlur = S * 0.30;
      c.globalAlpha = 0.8;
      c.strokeStyle = 'rgba(226,238,255,0.75)';
      c.lineWidth = Math.max(1.6, S * 0.05);
      c.beginPath(); c.arc(0, 0, r, 0, Math.PI * 2); c.stroke();
      G.drawGlyph(c, id, r * 1.3, Math.max(1.4, S * 0.040));
      // резкое ядро поверх свечения
      c.shadowBlur = 0;
      c.globalAlpha = 1;
      c.strokeStyle = 'rgba(248,252,255,0.98)';
      c.lineWidth = Math.max(1.1, S * 0.030);
      c.beginPath(); c.arc(0, 0, r, 0, Math.PI * 2); c.stroke();
      G.drawGlyph(c, id, r * 1.3, Math.max(0.9, S * 0.024));
    });
    var w = sp.w * (CELL / Math.max(8, Math.round(CELL / 4) * 4)) * s;
    ctx.globalAlpha = Math.min(1, a);
    sheet.draw(ctx, sp, px - w / 2, py - w / 2, w, w);
  }

  /* Осколки. Ломается ИМЕННО ТОТ знак, который передержали: его три регистра
     разъезжаются, кренятся и трескаются, но знак остаётся узнаваемым. Случайные
     палки на его месте не годились: все уникальные знаки игроку ещё предстоит
     различать в лицо.

     Разлёт считается от координат клетки, поэтому два одинаковых знака
     ломаются по-разному. */
  var shardId = new Map();
  function shardGlyph(k, id) { if (id !== undefined) shardId.set(k, id); return shardId.get(k); }

  function drawShards(ctx, px, py, key, s, a) {
    var id = shardId.get(key);
    if (id === undefined) id = G.hash3(key, 3, SEED) % G.COUNT;
    var ink = CELL * 0.62 * s, rh = ink / 3;
    var flash = Math.pow(Math.max(0, Math.sin(t * 0.5 + (key % 19))), 12);
    var col = flash > 0.04
      ? 'rgba(255,206,130,' + (0.45 + flash * 0.5) + ')'
      : 'rgba(172,172,178,0.82)';
    ctx.save();
    ctx.translate(px, py);
    ctx.globalAlpha = Math.min(1, a * 1.05);
    ctx.strokeStyle = col;
    for (var i = 0; i < 3; i++) {
      var dx = (G.rand3(key, i, SEED + 62) - 0.5) * CELL * 0.30 * s;
      var dy = (G.rand3(key, i, SEED + 63) - 0.5) * CELL * 0.22 * s;
      var rot = (G.rand3(key, i, SEED + 64) - 0.5) * 0.9;
      ctx.save();
      ctx.translate(dx, (i - 1) * rh + dy);
      ctx.rotate(rot);
      G.drawRegister(ctx, id, i, ink, Math.max(0.9, CELL * 0.022 * s));
      ctx.restore();
    }
    // трещины между обломками
    ctx.globalAlpha = Math.min(1, a * 0.5);
    ctx.lineWidth = Math.max(0.6, CELL * 0.012 * s);
    for (var c = 0; c < 2; c++) {
      var ax = (G.rand3(key, c + 7, SEED + 65) - 0.5) * CELL * 0.7 * s;
      var ay = (G.rand3(key, c + 7, SEED + 66) - 0.5) * CELL * 0.7 * s;
      ctx.beginPath();
      ctx.moveTo(ax, ay);
      ctx.lineTo(ax + (G.rand3(key, c, SEED + 67) - 0.5) * CELL * 0.5 * s,
                 ay + (G.rand3(key, c, SEED + 68) - 0.5) * CELL * 0.5 * s);
      ctx.stroke();
    }
    ctx.restore();
  }

  /* Контуры разложенных групп: сразу видно, что уже отсортировано. */
  function drawOutlines(ctx, vw, vh) {
    if (!outlines.length) return;
    var h = CELL * 0.5;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    // рамки разложенных групп: широкий мягкий подслой и яркое ядро поверх
    var passes = [[Math.max(5, CELL * 0.12), 'rgba(255,170,90,0.26)'], [Math.max(2.2, CELL * 0.05), 'rgba(255,214,150,0.9)']];
    for (var pass = 0; pass < 2; pass++) {
    ctx.lineWidth = passes[pass][0];
    ctx.strokeStyle = passes[pass][1];
    for (var o = 0; o < outlines.length; o++) {
      var ol = outlines[o];
      var c0 = cellCenter(ol.list[0].wx, ol.list[0].wy);
      if (c0.x < -600 || c0.y < -600 || c0.x > vw + 600 || c0.y > vh + 600) continue;
      ctx.beginPath();
      for (var i = 0; i < ol.list.length; i++) {
        var cc = ol.list[i], p = cellCenter(cc.wx, cc.wy);
        if (!ol.set[cc.wx + '|' + (cc.wy - 1)]) { ctx.moveTo(p.x - h, p.y - h); ctx.lineTo(p.x + h, p.y - h); }
        if (!ol.set[cc.wx + '|' + (cc.wy + 1)]) { ctx.moveTo(p.x - h, p.y + h); ctx.lineTo(p.x + h, p.y + h); }
        if (!ol.set[(cc.wx - 1) + '|' + cc.wy]) { ctx.moveTo(p.x - h, p.y - h); ctx.lineTo(p.x - h, p.y + h); }
        if (!ol.set[(cc.wx + 1) + '|' + cc.wy]) { ctx.moveTo(p.x + h, p.y - h); ctx.lineTo(p.x + h, p.y + h); }
      }
      ctx.stroke();
    }
    }
    ctx.restore();
  }

  function draw(ctx, vw, vh, cursor) {
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    baseT = ctx.getTransform();
    var box = atlas.box * (CELL / BASE);
    var lit = 0, seen = 0;
    each(vw, vh, cursor, function (gx, gy, wx, wy, key, id, px, py, s, f, dim, inSel, bo, anc, vs, rot, mk, sp, gl, pu, sh) {
      if (px < -CELL * 2 || py < -CELL * 2 || px > vw + CELL * 2 || py > vh + CELL * 2) return;
      seen++;
      if (f > 0.4) lit++;
      var a = (0.34 + f * 0.66) * dim * fadeAll;
      if (dimOthers > 0) a *= inSel ? 1 : (1 - dimOthers);
      // режим ввода команды: всё тускнеет, кроме нажатого
      if (conDim > 0 && !mk) a *= 1 - conDim;
      if (inSel && dimOthers > 0 && !selBoard) a = Math.min(1.15, a * 1.7);
      a += bo;
      if (a <= 0.012) return;
      var ss = s * (1 + liftSel * inSel);

      if (vs) {
        var va = a * vs.a * 0.55, vss = ss * vs.s;
        if (mk && mk.grow) { vss *= 1 + 0.34 * mk.grow; va = Math.min(1.25, (va + 0.25) * (1 + 1.3 * mk.grow)); }
        blit(ctx, VOID_GID, px, py, vss, vs.sy, va, box, rot);
        return;
      }

      /* Узлы цепочки анализа светятся сами. Это не подсказка: игрок только что
         сам положил сюда обломки, и загадка не в том, где они, а в каком
         порядке их брать. Голова цепочки дышит яркостью заметнее прочих. */
      /* Утилизированное место: белый круг, а внутри уменьшенный знак, который
         тут был. Не из атласа: тот жёлтый, а этот знак должен быть белым. */
      if (pu >= 0) {
        drawPurged(ctx, px, py, pu, s, a);
        return;
      }
      if (sh) { drawShards(ctx, px, py, key, s, a); return; }

      /* Отработанное на анализе оседает вдвое и блёкнет. Но если на клетке
         лежит накладка этапа, она главнее: иначе знаки утилизации, которые как
         раз и берутся из отработанной цепочки, рисовались крошечными и почти
         невидимыми, и найти их было нельзя. */
      if (sp && !mk) { ss *= 0.5; a *= 0.42; }
      if (gl) {
        a *= 0.55 + 0.45 * (Math.sin(t * 23 + key) > 0.2 ? 1 : 0.2);
        ss *= 0.94 + 0.12 * Math.sin(t * 31 + key);
      }
      if (mk) {
        if (mk.lit) { a = Math.min(1.25, a * 2.4); ss *= 1.12; }
        else {
          a = Math.min(1.1, a * 1.7 + 0.16);
          if (mk.head) a = Math.min(1.15, a * (1 + 0.34 * (0.5 + 0.5 * Math.sin(t * 2.4))));
        }
        if (mk.grow) { ss *= 1 + 0.36 * mk.grow; a = Math.min(1.25, a * (1 + 0.75 * mk.grow)); }
        // взятый в руку знак уменьшается, остальное вокруг гаснет
        if (mk.grab) { ss *= 0.68; a = Math.min(1.3, a * 1.25); }
        if (mk.scale) ss *= mk.scale;
        if (mk.dim) a *= 1 - mk.dim;
        // пустота, которую двигают на доске, светит так же тускло, как на поле
        if (id === VOID_GID) a *= 0.55;
      }
      /* Маяк переезда: один и тот же знак вспыхивает по всей карте разом.
         Так корабль предупреждает, что скоро уходит с этого места. */
      if (beacon >= 0 && id === beacon && !mk) {
        var bp = 0.5 + 0.5 * Math.sin(t * 3.1 + (wx + wy) * 0.02);
        a = Math.min(1.3, 0.95 + bp * 0.35) * fadeAll * (1 - conDim);
        ss *= 1.18 + bp * 0.16;
        ctx.save();
        ctx.globalAlpha = (0.22 + bp * 0.34) * fadeAll;
        ctx.strokeStyle = 'rgba(255,226,176,1)';
        ctx.lineWidth = 1.2;
        ctx.beginPath(); ctx.arc(px, py, CELL * (0.5 + bp * 0.22), 0, Math.PI * 2); ctx.stroke();
        ctx.restore();
      }

      /* Шлейф быстрого перемещения: каждый знак тянет хвост против хода. */
      if (streak > 0.01) {
        ctx.save();
        ctx.globalAlpha = Math.min(0.9, a * streak);
        ctx.strokeStyle = 'rgba(255,190,110,1)';
        ctx.lineWidth = Math.max(1, CELL * 0.045);
        ctx.beginPath();
        ctx.moveTo(px, py);
        ctx.lineTo(px - streakX * streak * CELL * 5, py - streakY * streak * CELL * 5);
        ctx.stroke();
        ctx.restore();
        ss *= 1 - streak * 0.35;
      }

      blit(ctx, id, px, py, ss, 1, a, box, rot);
      if (a > 0.72 || f > 0.5) blit(ctx, id, px, py, ss, 1, Math.min(0.85, (a - 0.5) * 1.1 + f * 0.5), box, rot);
    });
    hot = seen ? Math.min(1, lit / 14) : 0;
    baseT = null;
    ctx.restore();
    drawOutlines(ctx, vw, vh);
  }

  function cellCenter(wx, wy) {
    return {
      x: wrapS(wx - camCX, W) * CELL + CELL / 2 + jitterX(wx, wy),
      y: wrapS(wy - camCY, H) * CELL + CELL / 2 + jitterY(wx, wy)
    };
  }

  function screenToCell(x, y) {
    return { x: wrap(Math.floor(camCX + x / CELL), W), y: wrap(Math.floor(camCY + y / CELL), H) };
  }

  function anchorNear(x, y, tol, pred) {
    var c = screenToCell(x, y), best = null, bd = tol * tol;
    for (var dy = -1; dy <= 1; dy++) {
      for (var dx = -1; dx <= 1; dx++) {
        var wx = wrap(c.x + dx, W), wy = wrap(c.y + dy, H);
        var a = anchorAt(wx, wy);
        if (!a || (pred && !pred(a))) continue;
        var p = cellCenter(wx, wy);
        var d2 = (p.x - x) * (p.x - x) + (p.y - y) * (p.y - y);
        if (d2 < bd) { bd = d2; best = { wx: wx, wy: wy, rec: a, x: p.x, y: p.y }; }
      }
    }
    return best;
  }

  function anchorsOnScreen(vw, vh, pred, margin) {
    margin = margin || 0;
    var x0c = Math.floor(camCX) - 1, y0c = Math.floor(camCY) - 1;
    var nx = Math.ceil(vw / CELL) + 3, ny = Math.ceil(vh / CELL) + 3;
    ensure(x0c, y0c, x0c + nx, y0c + ny);
    var res = [];
    for (var j = 0; j < ny; j++) {
      for (var i = 0; i < nx; i++) {
        var wx = wrap(x0c + i, W), wy = wrap(y0c + j, H);
        var a = anchorAt(wx, wy);
        if (!a || (pred && !pred(a))) continue;
        var p = cellCenter(wx, wy);
        if (p.x < 34 + margin || p.y < 34 + margin ||
            p.x > vw - 34 - margin || p.y > vh - 116 - margin) continue;
        res.push({ wx: wx, wy: wy, rec: a, x: p.x, y: p.y });
      }
    }
    return res;
  }

  /* Забираем ТОЛЬКО обычные знаки. Всё особое в рамке остаётся на месте. */
  function snapshot(vw, vh, rect) {
    var list = [];
    each(vw, vh, null, function (gx, gy, wx, wy, key, id, px, py, s) {
      if (px <= rect.x0 || px >= rect.x1 || py <= rect.y0 || py >= rect.y1) return;
      if (isSpecial(wx, wy)) return;
      list.push({ key: key, wx: wx, wy: wy, id: id, x: px, y: py, s: s });
    });
    return list;
  }

  root.Field = {
    init: init, update: update, draw: draw, each: each, setDt: setDt,
    setFreeze: setFreeze, setSel: setSel, setBoost: setBoost, setMarks: setMarks,
    setOverride: setOverride, setHunting: setHunting,
    setSpent: setSpent, setGlitch: setGlitch, isGlitch: isGlitch,
    setPurged: setPurged, setShards: setShards, addOutline: addOutline,
    setZoom: setZoom, consume: consume,
    saveWorld: saveWorld, loadWorld: loadWorld, freshWorld: freshWorld,
    worldToJSON: worldToJSON, worldFromJSON: worldFromJSON,
    fill: fill, voidNear: voidNear, voidsOnScreen: voidsOnScreen, cellNear: cellNear,
    isVoidCell: isVoidCell,
    isSorted: function (wx, wy) { return sortedOf.has(ckey(wx, wy)); },
    spinAt: function (wx, wy) { return spin.get(ckey(wx, wy)); },
    outlineAt: function (wx, wy) { return sortedOf.get(ckey(wx, wy)) || null; },
    /* Крутящийся знак переезжает в клетку разложенной группы: на старом месте
       остаётся пустота, в новой клетке знак замещает прежний. */
    moveSpin: function (fromK, toK) {
      var g = spin.get(fromK);
      if (g === undefined) return false;
      spin.delete(fromK);
      over.set(fromK, VOID_GID);
      voids.set(fromK, { born: t - 5, style: G.hash3(fromK, 1, SEED + 42) % 3 });
      spin.set(toK, g);
      over.set(toK, g);
      return true;
    },
    setSpin: function (k, gid) {
      voids.delete(k); over.set(k, gid); spin.set(k, gid);
      emit({ type: 'spin', key: k, id: gid });
    },
    onTrace: function (fn) { traceFn = fn; },
    /* Изработанная клетка: особый знак или место, где уже раскладывали. */
    isWorked: function (wx, wy) { return isSpecial(wx, wy) || over.has(ckey(wx, wy)); },
    setVoidAt: function (k, on) {
      if (on) { if (!voids.has(k)) voids.set(k, { born: t - 5, style: G.hash3(k, 1, SEED + 42) % 3 }); }
      else voids.delete(k);
    },
    isGone: function (wx, wy) { var k = ckey(wx, wy); return purged.has(k) || shards.has(k); },
    setBeacon: function (g) { beacon = g; },
    setStreak: function (k, dx, dy) { streak = k; streakX = dx; streakY = dy; },
    setConsoleDim: function (v) { conDim = v; },
    setFade: function (v) { fadeAll = v; },
    glideTo: function (cx, cy) { glide = { x: cx, y: cy }; },
    VOID_GID: VOID_GID,
    setCam: function (cx, cy) { camCX = wrap(cx, W); camCY = wrap(cy, H); },
    screenToCell: screenToCell, cellCenter: cellCenter,
    // левый верхний угол клетки без разброса знаков: по нему строится сетка записи
    cellOrigin: function (wx, wy) { return { x: wrapS(wx - camCX, W) * CELL, y: wrapS(wy - camCY, H) * CELL }; },
    jitter: function (wx, wy) { return { x: jitterX(wx, wy), y: jitterY(wx, wy) }; },
    anchorAt: anchorAt, anchorNear: anchorNear, anchorsOnScreen: anchorsOnScreen,
    snapshot: snapshot, ckey: ckey, glyphAt: glyphAt,
    isSpecial: isSpecial, findGlyph: findGlyph, findRegion: findRegion,
    countGlyph: function (reg, gid) {
      var n = 0;
      for (var j = 0; j < reg.h; j++) for (var i = 0; i < reg.w; i++) {
        var wx = wrap(reg.ox + i, W), wy = wrap(reg.oy + j, H);
        if (rawGlyph(wx, wy) === gid && !isSpecial(wx, wy)) n++;
      }
      return n;
    },
    /* Масштаб едет плавно. Прыжок камеры читался как телепортация существа:
       оно будто оказывалось в другом месте карты, хотя просто менялся вид. */
    easeZoom: function (z) { zoomWant = Math.max(ZMIN, Math.min(ZMAX, z)); },
    get camCell() { return { x: camCX, y: camCY }; },
    get CELL() { return CELL; },
    get zoom() { return zoom; },
    get ZMIN() { return ZMIN; },
    get ZMAX() { return ZMAX; },
    get atlas() { return atlas; },
    get atlasBox() { return atlas.box * (CELL / BASE); },
    get voidCount() { return voids.size; },
    // для проверок памяти: сколько записей в каждой карте поля
    sizes: function () {
      return { states: states.size, cells: cells.size, nodes: nodes.size, over: over.size, voids: voids.size,
               spent: spent.size, glitch: glitch.size, purged: purged.size, shards: shards.size, outlines: outlines.length,
               sortedOf: sortedOf.size, consumed: consumed.size, spin: spin.size, shardId: shardId.size };
    },
    voidCells: function () { var o = []; voids.forEach(function (v, k) { o.push({ wx: Math.floor(k / 8192), wy: k % 8192 }); }); return o; },
    get hot() { return hot; },
    get W() { return W; },
    get H() { return H; },
    get SEED() { return SEED; },
    get beacon() { return beacon; },
    get t() { return t; }
  };
})(window);
