/* ORT — лорная вкладка: журнал корабля.
 *
 * На лорном поле спрятаны записи. Первыми открываются белые — журнал корабля:
 * из них игрок узнаёт, где он и что происходит. Позже появятся записи
 * других цветов, но сейчас только белые.
 *
 * Серые точки с навигации копятся шкалой под папками. Первая папка — выбор
 * записи: запись забирает из шкалы свою цену, и проступает рамка. Первая
 * фигура в рамке закрепляет запись; до её прочтения остальные ждут. Дальше
 * каждый этап тратит ячейки своей папки и кладёт в следующую (см. раздел 76
 * проектного документа). Ниже — исходное описание этапов:
 *
 *   1. РАМКА. Четыре угловых знака пульсируют белым. Нажав все четыре, игрок
 *      вызывает рамку, и в неё уходят все накопленные стаки ошибок: они
 *      становятся зарядом. Рамку надо без щелей замостить фигурами разложенных
 *      групп из хранилища. Каждая фигура гасит ячейку заряда, фигура,
 *      увеличенная вдвое, — две. Сколько ячеек потрачено, столько уходит
 *      во второй этап. Это поверхность, на которой наш язык сможет писать.
 *   2. ВОССТАНОВЛЕНИЕ. Белые точки медленно стирают знаки записи. На их места
 *      надо вернуть те же знаки, но утилизированные, из хранилища. Верно
 *      возвращённые остаются белыми кругами: они делят запись на предложения.
 *   3. СЛОГИ. По предложениям пробегает волна. В каждом по два знака, которые
 *      есть в хранилище якорей: нажатый знак становится слогом. Из слогов в
 *      нужных предложениях надо собрать слова.
 *   4. ЛИНИИ. Запись проступает, но дрожит и не читается. Оставшиеся знаки
 *      надо соединить одной замкнутой линией без пересечений, тратя знаки
 *      пустоты. Тогда текст становится читаемым.
 *
 * Выйти из этапа можно в любой момент: пройденные этапы сохраняются навсегда,
 * начатый откатывается, ячейки возвращаются. Всё, что этап берёт из
 * хранилища, из хранилища и пропадает.
 */
(function (root) {
  'use strict';

  var G = root.Glyphs, F = root.Field, S = root.Sound, T = root.LoreText;
  function INV() { return root.Inventory; }
  function NUM() { return root.Numeral; }

  var LCAP = 6, TOL = 28;
  var LORE_W = 128, LORE_SEED = 0x2b91c4;
  var SLOT_ICON = [121, 196, 58, 7];
  var BY_ORDER = ['c', 'p'];             // журнал корабля берёт сперва из хранилища существа
  var FONT = '15px Consolas, "Courier New", monospace';

  var env = null, world = null, built = false, dirty = false, saved = null;
  var errs = 0;                           // стаки ошибок, тёмные ячейки первой папки
  var file = [0, 0, 0, 0];                // file[0] — заряд рамки, дальше ячейки этапов
  var flare = [0, 0, 0, 0];
  var creatureNo = 9;                     // первое встреченное существо — старик под номером 9
  var lives = 1;                          // сколько существ сменилось за пультом при игроке
  var sector = 14, ejectSector = 14;      // текущий сектор; сектор, где выброшена последняя капсула
  var objInst = [], objRead = {}, objLost = {}, objFlags = {}, objUid = 1;
  var ejects = 0, ejectedNo = 0;          // сколько существ уже выброшено и номер последнего
  /* Серые точки с навигации копятся шкалой под папками (не больше ERR_CAP).
     Выбранная запись забирает из шкалы свою цену в первую папку. */
  var layout = {};                       // место каждой появившейся записи: id -> {x, y, w, h}
  var ERR_CAP = 12, COST = { white: 3, blue: 4, green: 5 }, lackAt = -99, crashAt = -99;
  // шанс срыва шкалы, когда она доходит до этой точки
  var CRASH_P = { 7: 0.15, 8: 0.35, 9: 0.6, 10: 0.92, 11: 0.98, 12: 1 };
  var stats = { errors: 0, denied: 0, loreTime: 0, objects: 0, ineffMoves: 0 };
  var blocks = [], ship = [], shipSeq = 0;
  var journal = { open: false, scroll: 0, fresh: 0, k: 0, max: 0, sel: null, hits: [] };
  var marks = new Map();
  var ses = null;                         // этап, который сейчас идёт
  var btn = { x: 0, y: 0, r: 21, hot: 0, live: false };
  var fx = [];
  var now = 0;
  var wordGid = {};
  var measure = null;

  function rnd(a, b) { return a + Math.random() * (b - a); }
  function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }
  function shuffle(a) {
    for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(Math.random() * (i + 1)); var q = a[i]; a[i] = a[j]; a[j] = q; }
    return a;
  }
  function textWidth(s) {
    if (!measure) { measure = document.createElement('canvas').getContext('2d'); measure.font = FONT; }
    return measure.measureText(s).width;
  }

  function assignGlyphs() {
    var reserved = {};
    (T.reserved || []).forEach(function (g) { reserved[g] = 1; });
    Object.keys(T.commands).forEach(function (k) { T.commands[k].forEach(function (g) { reserved[g] = 1; }); });
    var pool = [];
    for (var g = 1; g < G.COUNT; g++) if (!G.isParasite(g) && !reserved[g]) pool.push(g);
    pool.sort(function (a, b) { return G.hash3(a, 7, 991) - G.hash3(b, 7, 991); });
    Object.keys(T.words).forEach(function (w, i) { wordGid[w] = pool[i]; });
  }

  // --- геометрия блока ---------------------------------------------------------

  function cellKey(bl, k) { return F.ckey((bl.ox + k % bl.w) % F.W, (bl.oy + ((k / bl.w) | 0)) % F.H); }
  function org(bl) { return F.cellOrigin(bl.ox, bl.oy); }
  function rectOf(bl) {
    var o = org(bl), c = F.CELL;
    return { x0: o.x, y0: o.y, x1: o.x + bl.w * c, y1: o.y + bl.h * c };
  }
  function cellXY(bl, k) {
    var o = org(bl), c = F.CELL;
    return { x: o.x + (k % bl.w + 0.5) * c, y: o.y + (((k / bl.w) | 0) + 0.5) * c };
  }
  function cellAt(bl, x, y) {
    var o = org(bl), c = F.CELL;
    var cx = Math.floor((x - o.x) / c), cy = Math.floor((y - o.y) / c);
    if (cx < 0 || cy < 0 || cx >= bl.w || cy >= bl.h) return -1;
    return cy * bl.w + cx;
  }
  function corners(bl) { return [0, bl.w - 1, bl.n - bl.w, bl.n - 1]; }

  function setCell(bl, k, g) { bl.cells[k] = g; F.setOverride(cellKey(bl, k), g); }

  function fillerGid(wx, wy) {
    for (var k = 0; k < 60; k++) {
      var g = G.hash3(wx + k * 31, wy, 0x77e1) % G.COUNT;
      if (g !== F.VOID_GID && !G.isParasite(g)) return g;
    }
    return 1;
  }

  function makeBlock(d, i, extra) {
    var bl = {
      i: i, def: d, id: d.id, w: d.w, h: d.h, n: d.w * d.h,
      ox: ((F.W >> 1) + d.at[0] + F.W) % F.W, oy: ((F.H >> 1) + d.at[1] + F.H) % F.H,
      stage: 0, cells: null, tiles: [], targets: null, restored: {}, dots: [], num: 0, words: null,
      sec: 0, onum: 0, inst: null
    };
    if (extra) for (var ek in extra) bl[ek] = extra[ek];
    var sv = saved && saved[d.id];
    if (sv) {
      bl.stage = sv.stage | 0; bl.cells = sv.cells || null; bl.tiles = sv.tiles || [];
      bl.targets = sv.targets || null; bl.restored = sv.restored || {}; bl.dots = sv.dots || []; bl.num = sv.num || 0; bl.ejn = sv.ejn || 0; bl.words = sv.words || null;
      bl.sec = sv.sec || bl.sec;
      bl.draft = sv.draft || null; bl.pin = sv.pin || 0;
      // прочитанные раньше записи уже лежали в журнале
      bl.inJ = sv.inJ === undefined ? bl.stage >= 5 : !!sv.inJ;
    }
    if (!bl.cells || bl.cells.length !== bl.n) {
      bl.cells = [];
      for (var k = 0; k < bl.n; k++) bl.cells.push(fillerGid(bl.ox + k % bl.w, bl.oy + ((k / bl.w) | 0)));
    }
    for (var q = 0; q < bl.n; q++) F.setOverride(cellKey(bl, q), bl.cells[q]);
    blocks.push(bl);
    return bl;
  }

  function buildBlocks() {
    // на поле сразу ложатся только записи, которые уже начаты или прочитаны
    T.logs.forEach(function (d, i) {
      var sv = saved && saved[d.id];
      if ((sv && (sv.stage | 0) > 0) || layout[d.id]) materializeBase(i);
    });
  }

  /* --- записи найденных объектов ------------------------------------------- */
  /* Собранный на навигации объект оставляет в лорной вкладке заготовку своей
     записи: символы её границы мигают цветом класса — зелёные крутятся (сделанное),
     синие медленно проступают и гаснут (природное). Открывается запись теми же
     этапами. Не дочитанная до следующей смены существа — теряется: природная
     возвращается в пул и может встретиться снова, рукотворная — навсегда. */
  /* Раскладка записей: немного хаотично, но близко — от двух до четырёх
     клеток между соседними, со сдвигом вверх-вниз. Журнал корабля всегда
     ложится одинаково; находки подстраиваются под всё, что уже лежит. */
  function rng32(a) {
    return function () {
      a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function placeRect(rects, w, h, rng) {
    if (!rects.length) return { x: -Math.floor(w / 2), y: -2, w: w, h: h };
    for (var a = 0; a < 600; a++) {
      var ref = rects[Math.floor(rng() * rects.length)], side = Math.floor(rng() * 4), gap = 2 + Math.floor(rng() * 3), x, y;
      if (side === 0) { x = ref.x + ref.w + gap; y = ref.y + Math.round((rng() - 0.5) * 4); }
      else if (side === 1) { x = ref.x - gap - w; y = ref.y + Math.round((rng() - 0.5) * 4); }
      else if (side === 2) { y = ref.y + ref.h + gap; x = ref.x + Math.round((rng() - 0.5) * 6); }
      else { y = ref.y - gap - h; x = ref.x + Math.round((rng() - 0.5) * 6); }
      if (Math.abs(x + w / 2) > 48 || Math.abs(y + h / 2) > 48) continue;
      var ok = rects.every(function (e) {
        return x >= e.x + e.w + 2 || x + w + 2 <= e.x || y >= e.y + e.h + 2 || y + h + 2 <= e.y;
      });
      if (ok) return { x: x, y: y, w: w, h: h };
    }
    return { x: -50, y: -50 + rects.length * 5, w: w, h: h };
  }

  /* Место записи выбирается, когда она появляется, рядом с уже лежащими.
     Записи, которые ещё не открылись, места не занимают — иначе видимые
     разъезжались бы вокруг пустых мест. */
  function placeFor(id, w, h) {
    if (!layout[id]) {
      layout[id] = placeRect(Object.keys(layout).map(function (k) { return layout[k]; }), w, h, Math.random);
      dirty = true;
    }
    return layout[id];
  }

  function blockById(id) {
    for (var i = 0; i < blocks.length; i++) if (blocks[i].id === id) return blocks[i];
    return null;
  }

  function materializeBase(i) {
    var d = T.logs[i], b = blockById(d.id);
    if (b) return b;
    var r = placeFor(d.id, d.w, d.h);
    return makeBlock(Object.assign({}, d, { at: [r.x, r.y] }), i);
  }

  // формы записей находок: разные, а площадь почти одна
  var OBJ_SIZES = [[8, 3], [6, 4], [5, 5], [4, 6], [7, 3], [5, 4], [3, 7]];

  function objDef(inst) {
    var od = T.objects[inst.type], tx = od.texts[0];
    od.texts.forEach(function (x) { if (x.id === inst.text) tx = x; });
    return { id: 'obj:' + inst.uid, color: od.cls === 'art' ? 'green' : 'blue',
             at: inst.at || [-18 + (inst.slot % 2) * 28, -2 + inst.slot * 3],
             w: inst.w || 8, h: inst.h || 3, sentences: tx.sentences, extra: [] };
  }

  function syncObjBlocks() {
    objInst.forEach(function (inst) {
      if (blocks.some(function (b) { return b.inst === inst; })) return;
      if (!inst.at) {
        var pr = placeFor('obj:' + inst.uid, inst.w || 8, inst.h || 3);
        inst.at = [pr.x, pr.y]; inst.w = pr.w; inst.h = pr.h;
      }
      makeBlock(objDef(inst), blocks.length, { inst: inst, onum: inst.onum || 0, sec: inst.sec || 0 });
    });
  }

  function objTextFree(type) {
    var od = T.objects[type];
    if (!od) return [];
    return od.texts.filter(function (x) {
      if (od.repeat) return true;
      if (objRead[x.id] || objLost[x.id]) return false;
      return !objInst.some(function (i) { return i.text === x.id; });
    });
  }

  function addObject(o) {
    var free = objTextFree(o.type);
    if (!free.length) return false;
    var tx = free[Math.floor(Math.random() * free.length)];
    var sz = OBJ_SIZES[Math.floor(Math.random() * OBJ_SIZES.length)], uid = objUid++;
    var pr = placeFor('obj:' + uid, sz[0], sz[1]);
    objInst.push({ uid: uid, type: o.type, text: tx.id, onum: o.onum || 0, sec: sector,
                   at: [pr.x, pr.y], w: sz[0], h: sz[1] });
    stats.objects++;
    flare[0] = 1;
    dirty = true;
    if (built && env && env.active()) syncObjBlocks();
    return true;
  }

  function blockOf(inst) {
    for (var i = 0; i < blocks.length; i++) if (blocks[i].inst === inst) return blocks[i];
    return null;
  }

  /* Смена существа: недочитанные записи объектов теряются. */
  function dropObjects() {
    objInst = objInst.filter(function (inst) {
      var bl = blockOf(inst), sv = saved && saved['obj:' + inst.uid];
      var st = bl ? bl.stage : (sv ? sv.stage | 0 : 0);
      // начатая (укладка с фигурами и дальше) запись уже не пропадёт
      if (st >= 5 || (bl && isCommitted(bl))) return true;
      var od = T.objects[inst.type];
      if (od && od.cls === 'art' && !od.repeat) objLost[inst.text] = 1;
      if (bl) blocks.splice(blocks.indexOf(bl), 1);
      delete layout['obj:' + inst.uid];
      return false;
    });
  }

  function numTok(bl, tok) {
    if (tok === '#creature') return bl.num || creatureNo;
    if (tok === '#ejected') return bl.ejn || ejectedNo;
    if (tok === '#objnum') return bl.onum || 0;
    if (tok === '#sector') return bl.sec || ejectSector;
    return null;
  }

  function objColor(bl, a) {
    if (bl.def.color === 'green') return 'rgba(120,255,170,' + a + ')';
    if (bl.def.color === 'blue') return 'rgba(130,185,255,' + a + ')';
    return 'rgba(240,244,255,' + a + ')';
  }

  /* Предложения: знаки от начала до первой белой точки, между точками и от
     последней точки до конца, в порядке чтения. */
  function sentences(bl) {
    var dots = bl.dots.slice().sort(function (a, b) { return a - b; }), out = [], cur = [];
    for (var k = 0; k < bl.n; k++) {
      if (dots.indexOf(k) >= 0) { out.push(cur); cur = []; }
      else cur.push(k);
    }
    out.push(cur);
    return out;
  }

  function sentenceDefs(bl, s) {
    var keyed = bl.def.sentences.filter(function (q) { return q.key; });
    var plain = bl.def.sentences.filter(function (q) { return !q.key; });
    var res = keyed.slice(0, Math.max(0, s - 1));
    res.push(plain[0] || { text: ['…'], key: null });
    while (res.length < s) res.splice(res.length - 1, 0, { text: ['…'], key: null });
    return res;
  }

  /* Точки делят запись так, чтобы в каждом предложении осталось не меньше
     двух знаков. */
  function dividePositions(n, r) {
    var out = [];
    for (var k = 0; k < r; k++) out.push(Math.round((k + 1) * (n + 1) / (r + 1)) - 1);
    return out;
  }
  function maxR(n) { return Math.max(1, Math.floor((n - 2) / 3)); }

  function invList(kind, exclude) {
    var all = INV().items(), res = [];
    BY_ORDER.forEach(function (by) {
      for (var i = 0; i < all.length; i++) {
        var it = all[i];
        if (it.k === kind && (it.by || 'c') === by && (!exclude || exclude.indexOf(it) < 0)) res.push(it);
      }
    });
    return res;
  }

  // --- частицы -----------------------------------------------------------------

  function fly(x0, y0, x1, y1, opt) {
    opt = opt || {};
    fx.push({
      kind: 'dot', x0: x0, y0: y0, x1: x1, y1: y1,
      cx: (x0 + x1) / 2 + rnd(-150, 150), cy: Math.min(y0, y1) - rnd(30, 150),
      d: opt.d || 0, dur: opt.dur || 0.9, t: 0, col: opt.col || 'white', r: opt.r || 3, done: opt.done || null, rung: false
    });
  }

  function stepFx(dt) {
    for (var i = fx.length - 1; i >= 0; i--) {
      var p = fx[i];
      if (p.d > 0) { p.d -= dt; continue; }
      p.t += dt / p.dur;
      if (p.t >= 1 && !p.rung) { p.rung = true; if (p.done) p.done(); }
      if (p.t >= (p.kind === 'cross' ? 1 : 1.2)) fx.splice(i, 1);
    }
  }

  function drawFx(ctx) {
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (var i = 0; i < fx.length; i++) {
      var p = fx[i];
      if (p.kind === 'cross') {
        var a = 1 - p.t, s = p.s;
        ctx.save();
        ctx.translate(p.x, p.y);
        ctx.globalAlpha = Math.max(0, a);
        ctx.strokeStyle = 'rgba(238,246,255,0.9)';
        ctx.lineWidth = 1.6;
        ctx.beginPath(); ctx.arc(0, 0, s * 0.36, 0, Math.PI * 2); ctx.stroke();
        G.drawGlyph(ctx, p.g, s * 0.46, 1.3);
        ctx.strokeStyle = 'rgba(255,90,50,0.95)';
        ctx.lineWidth = 2.4;
        ctx.beginPath(); ctx.moveTo(-s * 0.42, -s * 0.42); ctx.lineTo(s * 0.42, s * 0.42);
        ctx.moveTo(s * 0.42, -s * 0.42); ctx.lineTo(-s * 0.42, s * 0.42); ctx.stroke();
        ctx.restore();
        continue;
      }
      if (p.d > 0) continue;
      var u = Math.min(1, p.t), e = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2, m = 1 - e;
      var x = m * m * p.x0 + 2 * m * e * p.cx + e * e * p.x1;
      var y = m * m * p.y0 + 2 * m * e * p.cy + e * e * p.y1;
      var al = p.t > 1 ? Math.max(0, 1 - (p.t - 1) / 0.2) : 1;
      var col = p.col === 'grey' ? '192,190,184' : p.col === 'amber' ? '255,196,120' : '248,250,255';
      ctx.fillStyle = 'rgba(' + col + ',' + 0.16 * al + ')';
      ctx.beginPath(); ctx.arc(x, y, p.r * 2.6, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = 'rgba(' + col + ',' + 0.95 * al + ')';
      ctx.beginPath(); ctx.arc(x, y, p.r, 0, Math.PI * 2); ctx.fill();
    }
    ctx.restore();
  }

  // --- этапы -------------------------------------------------------------------

  /* Камера подводит запись к середине и приближает, но так, чтобы запись
     и меню сбоку поместились на экране. */
  function focus(bl, z) {
    var v = env.view();
    var fit = Math.min((v.w - 520) / (bl.w * 54), (v.h - 300) / (bl.h * 54));
    F.glideTo(bl.ox + bl.w / 2, bl.oy + bl.h / 2);
    F.easeZoom(Math.max(0.6, Math.min(z || 1.7, fit)));
  }

  /* Цена фигур в ячейках заряда: три фигуры — одна ячейка. Начатая тройка
     уже занимает свою ячейку. */
  function costOf(list) {
    var small = 0, big = 0;
    list.forEach(function (p) { if (p.scale === 2) big++; else small++; });
    return Math.ceil(small / 3) + big;
  }

  function btnReset() { btn = { x: 0, y: 0, r: 21, hot: 0, live: false }; if (env) env.setButton(null); }

  function slotOf(stage) { return stage <= 1 ? 0 : Math.min(3, stage - 1); }

  /* Лорная работа идёт над одной записью за раз.
     Первая папка — выбор: подсвечиваются доступные записи (очередная из
     журнала корабля и все заготовки находок). Нажатие по записи забирает из
     шкалы её цену (белая — 3 точки, синяя — 4, зелёная — 5) в первую папку, и
     проступает рамка. Пока в рамке нет ни одной фигуры, выбор можно отменить:
     точки вернутся в шкалу. Первая же фигура закрепляет запись — дальше
     остальные записи ждут, пока эта не будет прочитана, а сама она уже не
     пропадёт. Каждый этап тратит ячейки своей папки и кладёт в следующую. */
  function folderClick(slot) {
    var cur = ses ? (ses.choose ? ses.slot : slotOf(ses.stage)) : -1;
    if (ses) { abandon(); if (cur === slot) { S.consoleOff(); return; } }
    var work = current();
    if (work) {
      if (slotOf(work.stage) !== slot) { reject(); flare[slotOf(work.stage)] = 1; return; }
      S.phase(slot);
      startSlot(slot, work);
      return;
    }
    if (slot !== 0) { S.nothing(); flare[slot] = 0.5; return; }
    var cands = seeds();
    if (!cands.length) { S.nothing(); flare[0] = 0.5; return; }
    S.phase(0);
    ses = { choose: cands, slot: 0, stage: -1, bl: null };
    btnReset();
  }

  function baseEligible(d) {
    var need = d.minEjects || (d.requires === 'eject' ? 1 : 0);
    if (ejects < need) return false;
    if (d.minLives && lives < d.minLives) return false;
    if (d.when) for (var k in d.when) if ((stats[k] || 0) < d.when[k]) return false;
    return true;
  }

  function baseStage(i) {
    var d = T.logs[i], b = blockById(d.id), sv = saved && saved[d.id];
    return b ? b.stage : (sv ? sv.stage | 0 : 0);
  }

  /* Очередная запись журнала корабля: одна, по порядку; реакции вне очереди.
     Появляясь, она занимает место рядом с уже лежащими записями. */
  function nextBase() {
    var best = -1, bp = 0;
    T.logs.forEach(function (d, i) {
      var stg = baseStage(i);
      if (stg >= 5 || (stg === 0 && !baseEligible(d))) return;
      var pr = d.priority || 0;
      if (best < 0 || pr > bp) { best = i; bp = pr; }
    });
    if (best < 0 || !built || !env || !env.active()) return null;
    return materializeBase(best);
  }

  function seeds() {
    var nb = nextBase(), out = nb && nb.stage === 0 ? [nb] : [];
    return out.concat(blocks.filter(function (b) { return b.inst && b.stage === 0; }));
  }

  function isCommitted(b) {
    return (b.stage >= 2 && b.stage < 5) || (b.stage === 1 && !!(b.draft && b.draft.length));
  }

  function current() {
    for (var i = 0; i < blocks.length; i++) if (isCommitted(blocks[i])) return blocks[i];
    return null;
  }

  function costFor(bl) { return COST[bl.def.color] || 3; }

  function saveDraft(s) {
    s.bl.draft = s.placed.map(function (p) {
      return { id: p.item.id, rot: p.rot || 0, x: p.x, y: p.y,
               c: p.cells.map(function (q) { return [p.x + q[0], p.y + q[1]]; }) };
    });
    dirty = true;
  }

  /* Выбор отменён: точки из первой папки улетают обратно в шкалу. */
  function uncommit(bl) {
    var n = file[0], from = env.folderPos(0);
    for (var i = 0; i < n; i++) {
      var sp = env.scalePos(errs + i, errs + n);
      fly(from.x, from.y - 8, sp.x, sp.y, { d: i * 0.08, col: 'grey', r: 2.6 });
    }
    errs = Math.min(ERR_CAP, errs + n);
    file[0] = 0;
    bl.stage = 0; bl.draft = null; bl.tiles = [];
    dirty = true;
  }

  function startSlot(slot, bl) {
    if (slot === 0) { if (bl.stage === 0) startPick(bl); else startTiling(bl); }
    else if (slot === 1) startRestore(bl);
    else if (slot === 2) startWords(bl);
    else startLines(bl);
  }

  function pressChoose(x, y) {
    var s = ses;
    for (var i = 0; i < s.choose.length; i++) {
      var bl = s.choose[i];
      if (cellAt(bl, x, y) < 0) continue;
      var cost = costFor(bl);
      if (errs < cost) {
        // не хватает: точки шкалы вспыхивают — видно, сколько есть и сколько нужно
        lackAt = now;
        S.lack();
        env.reject(0.4);
        return;
      }
      var to = env.folderPos(0), before = errs;
      errs -= cost;
      file[0] = cost;
      dirty = true;
      for (var j = 0; j < cost; j++) {
        var sp = env.scalePos(before - cost + j, before);
        fly(sp.x, sp.y, to.x, to.y - 8, { d: j * 0.1, col: 'grey', r: 2.6, done: function () { flare[0] = 1; S.tick(1, 3); } });
      }
      ses = null;
      startPick(bl);
      return;
    }
    S.nothing();
  }

  /* --- кнопка журнала ------------------------------------------------------- */
  /* У прочитанной записи в правом верхнем углу горит знак. Нажатие по нему
     тратит такой же знак из хранилища, и запись появляется во вкладке журнала.
     Там её можно выделить и тем же знаком отвязать обратно. */
  function pinPos(bl) {
    var r = rectOf(bl);
    return { x: r.x1 + F.CELL * 0.12, y: r.y0 - F.CELL * 0.12 };
  }

  function haveGlyph(g) {
    return INV().items().some(function (it) { return it.k !== 'shape' && it.g === g; });
  }

  function spendGlyph(g) {
    var all = INV().items();
    for (var i = 0; i < all.length; i++) {
      if (all[i].k !== 'shape' && all[i].g === g) { INV().remove(all[i]); return true; }
    }
    return false;
  }

  function pinToJournal(bl) {
    if (!spendGlyph(bl.pin)) { reject(0.4); return; }
    bl.inJ = true;
    journal.fresh = 1;
    dirty = true;
    var p = pinPos(bl);
    env.pulse(p.x, p.y, true);
    S.bloom();
  }

  function unpin(bl) {
    if (!spendGlyph(bl.pin)) { reject(0.4); return; }
    bl.inJ = false;
    journal.sel = null;
    dirty = true;
    S.dissolve();
  }

  function drawPin(ctx, bl) {
    var p = pinPos(bl), s = Math.max(22, F.CELL * 0.62), ok = haveGlyph(bl.pin), pu = 0.5 + 0.5 * Math.sin(now * 2.4);
    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.fillStyle = 'rgba(9,7,4,0.9)';
    ctx.fillRect(-s / 2, -s / 2, s, s);
    ctx.globalCompositeOperation = 'lighter';
    glowStroke(ctx, ok ? 'rgba(255,236,200,' + (0.5 + 0.4 * pu).toFixed(3) + ')' : 'rgba(150,130,110,0.45)', ok ? 12 : 0, 1.4);
    ctx.strokeRect(-s / 2, -s / 2, s, s);
    G.drawGlyph(ctx, bl.pin, s * 0.7, 1.3);
    ctx.restore();
  }

  /* Выход из этапа: начатое откатывается, ячейки возвращаются в папку.
     Пройденные этапы остаются как были. */
  function abandon() {
    if (!ses) return;
    var s = ses;
    // выбор без единой фигуры отменяется целиком
    if (s.stage === 0 || (s.stage === 1 && !s.placed.length)) uncommit(s.bl);
    if (s.stage === 2) file[1] = Math.min(LCAP, file[1] + s.spent);
    if (s.stage === 3) {
      file[2] = Math.min(LCAP, file[2] + s.spent);
    }
    if (s.stage === 4 && s.done < 0) file[3] = Math.min(LCAP, file[3] + s.spent);
    endSession();
  }

  function endSession() {
    ses = null;
    btnReset();
  }

  function reject(k) {
    S.reject();
    if (env) env.reject(k || 0.6);
  }

  /* --- 1а. Выбранная запись: проступает рамка ---------------------------------- */

  function startPick(bl) {
    focus(bl, 1.5);
    // рамка проступает, когда точки долетят до папки
    ses = { stage: 0, bl: bl, forming: -0.9 };
    btnReset();
    var from = env.folderPos(0), r = rectOf(bl), n = file[0], count = Math.min(24, n * 4);
    var w = r.x1 - r.x0, h = r.y1 - r.y0, per = 2 * (w + h);
    for (var i = 0; i < count; i++) {
      var d = (i / count) * per, px, py;
      if (d < w) { px = r.x0 + d; py = r.y0; }
      else if (d < w + h) { px = r.x1; py = r.y0 + d - w; }
      else if (d < 2 * w + h) { px = r.x1 - (d - w - h); py = r.y1; }
      else { px = r.x0; py = r.y1 - (d - 2 * w - h); }
      fly(from.x + rnd(-14, 14), from.y - 8, px, py, { d: 0.9 + i * 0.04, dur: 0.8, col: 'grey', r: 2.4 });
    }
    setTimeout(function () { if (ses && ses.bl === bl) S.frameOn(); }, 900);
  }

  /* --- 1б. Мостим рамку фигурами ------------------------------------------- */

  function startTiling(bl) {
    focus(bl, 1.7);
    // разложенные раньше фигуры возвращаются на свои места
    var placed = [];
    (bl.draft || []).forEach(function (d) {
      var it = INV().byId(d.id);
      if (!it) return;
      placed.push({ item: it, scale: 1, rot: d.rot || 0, cells: tileCells(it, d.rot || 0), x: d.x, y: d.y, shake: 0 });
    });
    ses = { stage: 1, bl: bl, placed: placed, scroll: 0, drag: null, used: 0, usedAnim: placed.length / 3 };
    btnReset();
  }

  /* Клетки фигуры, повёрнутой rot раз на 90° по часовой стрелке. Порядок
     клеток сохраняется, поэтому крутящийся знак остаётся в своей клетке. */
  function tileCells(item, rot) {
    var c = item.c.map(function (q) { return [q[0], q[1]]; }), h = item.h;
    for (var r = 0; r < ((rot || 0) % 4); r++) {
      var nh = 0;
      c = c.map(function (q) { return [h - 1 - q[1], q[0]]; });
      c.forEach(function (q) { nh = Math.max(nh, q[1] + 1); });
      h = nh;
    }
    return c;
  }

  function fits(cells, x, y, exclude) {
    var bl = ses.bl, occ = {}, ok = true, inside = true;
    ses.placed.forEach(function (p) {
      if (p === exclude) return;
      p.cells.forEach(function (q) { occ[(p.x + q[0]) + ',' + (p.y + q[1])] = 1; });
    });
    cells.forEach(function (q) {
      var cx = x + q[0], cy = y + q[1];
      if (cx < 0 || cy < 0 || cx >= bl.w || cy >= bl.h) inside = false;
      else if (occ[cx + ',' + cy]) ok = false;
    });
    return { ok: ok && inside, inside: inside };
  }

  function coverage() {
    var n = 0;
    ses.placed.forEach(function (p) { n += p.cells.length; });
    return n;
  }

  function snapFor(cells, x, y) {
    var o = org(ses.bl), c = F.CELL, sw = 0, sh = 0;
    cells.forEach(function (q) { sw = Math.max(sw, q[0] + 1); sh = Math.max(sh, q[1] + 1); });
    return { x: Math.round((x - o.x) / c - sw / 2), y: Math.round((y - o.y) / c - sh / 2) };
  }

  function dotPos(p) {
    var o = org(ses.bl), c = F.CELL, minX = 99, maxX = 0, minY = 99;
    p.cells.forEach(function (q) { minX = Math.min(minX, q[0]); maxX = Math.max(maxX, q[0] + 1); minY = Math.min(minY, q[1]); });
    return { x: o.x + (p.x + (minX + maxX) / 2) * c, y: o.y + (p.y + minY) * c - 12 };
  }

  /* Фигура с крутящимся знаком внутри поворачивается на 90° по часовой
     стрелке нажатием на белую точку над ней. */
  function canRotate(p) { return !!(p.item.s && p.item.s.length); }

  function rotateTile(p) {
    var nr = ((p.rot || 0) + 1) % 4, cells = tileCells(p.item, nr), f = fits(cells, p.x, p.y, p);
    if (!f.ok) { reject(0.4); p.shake = 0.45; return; }
    p.rot = nr; p.cells = cells;
    if (ses) saveDraft(ses);
    S.zoom(1);
  }

  /* Поле сформировано: запись закреплена навсегда. Точки первой папки
     потрачены целиком, во вторую папку уходит ровно столько, сколько нужно
     следующему этапу. */
  function finishTiling() {
    var s = ses, bl = s.bl, r = rectOf(bl), to = env.folderPos(1);
    bl.tiles = s.placed.map(function (p) { return { c: p.cells.map(function (q) { return [p.x + q[0], p.y + q[1]]; }) }; });
    s.placed.forEach(function (p) { INV().remove(p.item); });
    var out = Math.min(3, maxR(bl.n));
    file[0] = 0;
    for (var i = 0; i < out; i++) {
      fly(rnd(r.x0, r.x1), rnd(r.y0, r.y1), to.x, to.y - 8, { d: i * 0.12, done: function () { flare[1] = 1; S.tick(1, 4); } });
    }
    file[1] = Math.min(LCAP, out);
    bl.draft = null;
    bl.stage = 2;
    dirty = true;
    S.sorted(0, 3);
    endSession();
  }

  /* --- 2. Восстановление утилизированными знаками ----------------------------- */

  function randomGlyph(avoid) {
    var g;
    do { g = 1 + Math.floor(Math.random() * (G.COUNT - 1)); } while (G.isParasite(g) || (avoid && avoid.indexOf(g) >= 0));
    return g;
  }

  function startRestore(bl) {
    if (!bl.targets) {
      var r0 = Math.min(3, maxR(bl.n), file[1]);
      if (r0 < 1) { reject(); flare[1] = 1; return; }
      bl.targets = dividePositions(bl.n, r0);
      dirty = true;
    }
    var rem = bl.targets.filter(function (k) { return !bl.restored[k]; });
    if (!rem.length) { completeRestore(bl); return; }
    if (file[1] < rem.length) { reject(); flare[1] = 1; return; }
    focus(bl, 1.7);
    var spent = file[1];
    file[1] = 0;

    /* Стираются по возможности те знаки, чьи утилизированные двойники есть
       в хранилище: иначе вернуть их было бы нечем. */
    var pool = invList('purged'), used = [], ids = [];
    rem.forEach(function (k) {
      for (var i = 0; i < pool.length; i++) {
        if (used.indexOf(pool[i]) < 0 && ids.indexOf(pool[i].g) < 0) {
          used.push(pool[i]); ids.push(pool[i].g); setCell(bl, k, pool[i].g);
          return;
        }
      }
    });
    var menu = rem.map(function (k) {
      var it = null;
      for (var i = 0; i < used.length; i++) if (used[i].g === bl.cells[k]) it = used[i];
      return { g: bl.cells[k], item: it, dim: !it, slot: -1, shake: 0 };
    });
    var targetsG = rem.map(function (k) { return bl.cells[k]; });
    var decoys = invList('purged', used).filter(function (it) { return targetsG.indexOf(it.g) < 0; });
    for (var d = 0; d < rem.length; d++) {
      var di = decoys.length ? decoys.splice(Math.floor(Math.random() * decoys.length), 1)[0] : null;
      if (di) menu.push({ g: di.g, item: di, dim: false, slot: -1, shake: 0 });
      else menu.push({ g: randomGlyph(targetsG), item: null, dim: false, virtual: true, slot: -1, shake: 0 });
    }
    /* Десять секунд знаки, которые будут стёрты, пульсируют, светятся и
       покачиваются: запомнить, какие они и где. Потом точки их очень медленно
       стирают. */
    var SHOW = 10;
    ses = { stage: 2, bl: bl, rem: rem, menu: shuffle(menu), spent: spent, removal: {}, slots: {}, drag: null, sel: null, scroll: 0, showUntil: now + SHOW, showStart: now };
    var from = env.folderPos(1), me = ses;
    rem.forEach(function (k, i) {
      var p = cellXY(bl, k);
      fly(from.x, from.y - 10, p.x, p.y, { d: SHOW - 1 + i * 0.3, dur: 1.0, done: function () { if (ses === me) { me.removal[k] = now; S.dissolve(); } } });
    });
    for (var e = rem.length; e < spent; e++) {
      var c0 = cellXY(bl, rem[e % rem.length]);
      fly(from.x, from.y - 10, c0.x + rnd(-60, 60), c0.y - 70, { d: SHOW - 1 + e * 0.3, r: 2 });
    }
    btnReset();
  }

  var FADE = 4.8;                        // стирание знака, втрое плавнее прежнего
  function removedDone(k) { return ses.removal[k] !== undefined && now - ses.removal[k] > FADE; }

  function placeEntry(entry, k) {
    var s = ses;
    if (s.slots[k] && s.slots[k] !== entry) s.slots[k].slot = -1;
    if (entry.slot >= 0) delete s.slots[entry.slot];
    s.slots[k] = entry; entry.slot = k;
    s.sel = null;
    S.settle(1, 3);
  }

  function evaluateRestore() {
    var s = ses, bl = s.bl, wrong = [], right = [];
    s.rem.forEach(function (k) { (s.slots[k].g === bl.cells[k] ? right : wrong).push(k); });
    right.forEach(function (k) { bl.restored[k] = true; if (s.slots[k].item) INV().remove(s.slots[k].item); });
    wrong.forEach(function (k) {
      var e = s.slots[k], p = cellXY(bl, k);
      if (e.item) INV().remove(e.item);            // перечёркнутый знак потерян
      fx.push({ kind: 'cross', x: p.x, y: p.y, s: F.CELL, g: e.g, t: 0, dur: 1.1, d: 0 });
      setCell(bl, k, randomGlyph([bl.cells[k]]));  // на этом месте проступает уже другой знак
    });
    dirty = true;
    if (!wrong.length && bl.targets.every(function (k) { return bl.restored[k]; })) { completeRestore(bl); return; }
    file[1] = Math.min(LCAP, file[1] + wrong.length);
    env.shake(0.9);
    S.error();
    endSession();
  }

  function completeRestore(bl) {
    var to = env.folderPos(2);
    bl.targets.forEach(function (k, i) {
      var p = cellXY(bl, k);
      // знак внутри круга превращается в белую точку и улетает в папку
      fly(p.x, p.y, to.x, to.y - 8, { d: 0.3 + i * 0.2, done: function () { flare[2] = 1; S.tick(i, 3); } });
    });
    file[2] = Math.min(LCAP, file[2] + bl.targets.length);
    bl.dots = bl.targets.slice();
    bl.stage = 3;
    dirty = true;
    S.sorted(1, 3);
    endSession();
  }

  /* --- 3. Слова ---------------------------------------------------------------- */

  /* Внутри мысли мы думаем словами. Слово записи — это НАСТОЯЩИЙ узел
     подстрочника, а не случайная нарезка клеток: сколько в предложении узлов,
     столько на его клетках и слов. Связи ⟨…⟩ клеток не занимают вовсе — они
     живут на линиях между узлами и проступают на четвёртом этапе.

     Знаки одного слова двигаются ОДНОЙ ПОВАДКОЙ — той же, какой выдают себя
     якоря на карте, — а у соседних слов повадки всегда разные. Поэтому границу
     слова видно тем же зрением, которым игрок полчаса искал якорь, и объяснять
     тут нечего (раздел 30: повадка означает участие). Прежде слова отличались
     друг от друга только фазой дыхания в двенадцать сотых, и разглядеть их было
     нельзя — ровно та ошибка, которую мы уже чинили в разделе 23.

     Якорь из хранилища — камертон. Потраченный, он НЕ решает слово: он
     заставляет все знаки своей повадки в записи зазвучать во весь голос на
     несколько секунд. Тон даёт камертон, слова обводит игрок. */

  var RING_T = 6.5;                      // сколько звучит повадка под камертоном
  /* Сила повадки — доля от той, с какой якорь ведёт себя на карте, и больше
     единицы быть не может: у тяжёлого от этого скорость спада уходит в минус,
     и знак разносит. Камертон добавляет громкость размером и светом, а не
     силой сверх предела. */
  var BEH_IDLE = 0.7;                    // обычная сила повадки в записи
  var BEH_RING = 1;                      // под камертоном

  function isLink(tok) { return tok.charAt(0) === '⟨'; }

  /* Сколько клеток заслуживает слово: длинному слову — больше места. */
  function tokWeight(bl, tok) {
    if (numTok(bl, tok) !== null) return 1;
    if (tok.indexOf('#cmd:') === 0) return 2;
    return clamp(Math.round(tok.length / 4), 1, 3);
  }

  /* Раздать total единиц по весам, ничего не потеряв (наибольший остаток). */
  function shareOut(total, weights) {
    var sum = 0, base = [], rem = [], used = 0;
    weights.forEach(function (w) { sum += w; });
    weights.forEach(function (w, i) {
      var exact = sum > 0 ? total * w / sum : 0, v = Math.max(0, Math.floor(exact));
      base.push(v); used += v; rem.push({ i: i, r: exact - v });
    });
    rem.sort(function (a, b) { return b.r - a.r; });
    for (var k = 0; used < total && rem.length; k++, used++) base[rem[k % rem.length].i]++;
    return base;
  }

  /* Строки предложения. Слово не переходит со строки на строку: иначе по нему
     не провести курсором одним движением. */
  function rowRuns(bl, cells) {
    var runs = [];
    cells.forEach(function (k) {
      var last = runs.length ? runs[runs.length - 1] : null, prev = last ? last[last.length - 1] : -9;
      if (last && prev === k - 1 && ((prev / bl.w) | 0) === ((k / bl.w) | 0)) last.push(k);
      else runs.push([k]);
    });
    return runs;
  }

  /* У соседних слов повадки не совпадают: иначе граница между ними исчезает.
     Считается по порядку чтения и по соседству на сетке. */
  function assignKinds(bl, words) {
    var byCell = {};
    words.forEach(function (w, i) { w.c.forEach(function (k) { byCell[k] = i; }); });
    words.forEach(function (w, i) {
      var taken = {}, free = [], z;
      if (i > 0) taken[words[i - 1].kind] = 1;
      w.c.forEach(function (k) {
        var x = k % bl.w;
        [x > 0 ? k - 1 : -1, x < bl.w - 1 ? k + 1 : -1, k - bl.w, k + bl.w].forEach(function (q) {
          if (q < 0) return;
          var j = byCell[q];
          if (j !== undefined && j !== i && words[j].kind !== undefined) taken[words[j].kind] = 1;
        });
      });
      for (z = 0; z < 5; z++) if (!taken[z]) free.push(z);
      if (!free.length) for (z = 0; z < 5; z++) free.push(z);
      w.kind = free[G.hash3(bl.ox + i * 3 + 1, bl.oy + i + 1, 31) % free.length];
    });
  }

  /* Раскладка слов по клеткам записи. Выводится из точек-разделителей и текста
     записи, поэтому одинакова при каждом запуске, и хранить её незачем. */
  function planWords(bl) {
    var sents = sentences(bl), defs = sentenceDefs(bl, sents.length), out = [];
    sents.forEach(function (cells, si) {
      var d = defs[si];
      if (!d || !cells.length) return;
      var toks = d.text, nodes = [], i;
      toks.forEach(function (tok, ti) { if (!isLink(tok)) nodes.push(ti); });
      if (!nodes.length) return;
      var runs = rowRuns(bl, cells), caps = runs.map(function (r) { return r.length; });
      var per = shareOut(Math.min(nodes.length, cells.length), caps), over = 0;
      for (i = 0; i < per.length; i++) if (per[i] > caps[i]) { over += per[i] - caps[i]; per[i] = caps[i]; }
      for (i = 0; i < per.length && over > 0; i++) {
        var room = Math.min(caps[i] - per[i], over);
        per[i] += room; over -= room;
      }
      var at = 0, first = out.length;
      runs.forEach(function (run, ri) {
        if (!per[ri]) return;
        var mine = nodes.slice(at, at + per[ri]);
        at += per[ri];
        var cut = shareOut(run.length - mine.length, mine.map(function (ti) { return tokWeight(bl, toks[ti]); }));
        var p = 0;
        mine.forEach(function (ti, j) {
          var take = cut[j] + 1;
          out.push({ s: si, tis: [ti], c: run.slice(p, p + take) });
          p += take;
        });
      });
      // узлов оказалось больше, чем клеток: лишние дописываются к последнему слову
      if (at < nodes.length && out.length > first) {
        var tail = out[out.length - 1];
        for (i = at; i < nodes.length; i++) tail.tis.push(nodes[i]);
      }
    });
    assignKinds(bl, out);
    return out;
  }

  function wordPlan(bl) {
    var key = bl.dots.join(',') + '|' + bl.n;
    if (!bl._plan || bl._planKey !== key) { bl._plan = planWords(bl); bl._planKey = key; }
    return bl._plan;
  }

  /* Слова дочитанной записи. Старые сохранения хранили только клетки, без
     узлов; такая запись раскладывается заново — раскладка от сида. */
  function wordsOf(bl) {
    if (bl.words && bl.words.length && bl.words[0] && bl.words[0].tis) return bl.words;
    return wordPlan(bl);
  }

  /* --- мелкое поле разметки слов --------------------------------------------- */

  /* На время третьего этапа внутренность записи сменяется полем ВТРОЕ мельче:
     на месте каждой клетки оказывается девять. Знаков становится в девять раз
     больше, и слова приходится именно ИСКАТЬ, водя курсором, а не перебирать
     всё подряд: раньше знаков было два десятка, и игрок просто выделял все.
     Сама запись остаётся того же размера, круги-разделители и границы фигур
     стоят где стояли. Колесо приближает поле вместе с записью, как везде.

     Смена вида идёт помехой-линией, пробегающей по записи снизу вверх или
     сверху вниз (направление выбирается случайно), и тем же способом вид
     возвращается обратно, когда слова размечены. */

  var FINE = 3;                          // во сколько раз мельче клетки разметки
  var SWEEP_T = 1.15;                    // сколько бежит помеха-линия
  var SHRINK_T = 1.0;                    // за сколько знаки садятся в своих клетках
  var SHRINK_TO = 0.7;                   // и насколько: вокруг знака нужен воздух

  function fineW(bl) { return bl.w * FINE; }
  function fineH(bl) { return bl.h * FINE; }
  function fineSize() { return F.CELL / FINE; }

  /* У поля разметки СВОЯ крупность, отдельная от карты: запись остаётся того
     же размера и на том же месте, а письмо в ней растёт. Всё поле тогда в
     рамку не влезает, и его водят курсором у кромки — тем же жестом, каким
     водят саму карту. */
  var FZMIN = 1, FZMAX = 4.2, FZ0 = 1.6;

  function fineU(s) { return fineSize() * s.fz; }
  function fineOrg(s) {
    var r = rectOf(s.bl);
    return { x: r.x0 + s.fx, y: r.y0 + s.fy, u: fineU(s) };
  }
  function clampPan(s) {
    var r = rectOf(s.bl), u = fineU(s);
    var cw = fineW(s.bl) * u, ch = fineH(s.bl) * u;
    var rw = r.x1 - r.x0, rh = r.y1 - r.y0;
    s.fx = cw <= rw ? (rw - cw) / 2 : clamp(s.fx, rw - cw, 0);
    s.fy = ch <= rh ? (rh - ch) / 2 : clamp(s.fy, rh - ch, 0);
  }
  function finePos(s, k) {
    var o = fineOrg(s), w = fineW(s.bl);
    return { x: o.x + (k % w + 0.5) * o.u, y: o.y + (((k / w) | 0) + 0.5) * o.u };
  }
  function fineAt(s, x, y) {
    var bl = s.bl, r = rectOf(bl), o = fineOrg(s), w = fineW(bl);
    if (x < r.x0 || x > r.x1 || y < r.y0 || y > r.y1) return -1;
    var fx = Math.floor((x - o.x) / o.u), fy = Math.floor((y - o.y) / o.u);
    if (fx < 0 || fy < 0 || fx >= w || fy >= fineH(bl)) return -1;
    return fy * w + fx;
  }
  // клетка записи в том же виде: под ней лежит FINE x FINE мелких
  function coarseBox(s, k) {
    var o = fineOrg(s), c = o.u * FINE, bl = s.bl;
    return { x: o.x + (k % bl.w) * c, y: o.y + (((k / bl.w) | 0)) * c, c: c,
             cx: o.x + (k % bl.w + 0.5) * c, cy: o.y + (((k / bl.w) | 0) + 0.5) * c };
  }

  /* Точка под курсором остаётся на месте, иначе поле выпрыгивает из-под руки
     (то же правило, что и у зума карты, раздел 17). */
  function fineZoom(s, dy, x, y) {
    var o = fineOrg(s), gx = (x - o.x) / o.u, gy = (y - o.y) / o.u;
    var z = clamp(s.fz * (dy > 0 ? 0.82 : 1.22), FZMIN, FZMAX);
    if (Math.abs(z - s.fz) < 1e-4) return;
    s.fz = z;
    var r = rectOf(s.bl), u = fineU(s);
    s.fx = x - r.x0 - gx * u;
    s.fy = y - r.y0 - gy * u;
    clampPan(s);
    S.zoom(dy > 0 ? -1 : 1);
  }
  // в какой клетке записи лежит мелкая клетка
  function coarseOf(bl, k) {
    var w = fineW(bl);
    return (((((k / w) | 0) / FINE) | 0) * bl.w) + ((((k % w) / FINE) | 0));
  }
  function fineGid(bl, k) {
    var w = fineW(bl), fx = k % w, fy = (k / w) | 0;
    for (var i = 0; i < 40; i++) {
      var g = G.hash3(bl.ox * FINE + fx + i * 37, bl.oy * FINE + fy, 0x3b9a) % G.COUNT;
      if (g !== F.VOID_GID && !G.isParasite(g)) return g;
    }
    return 1;
  }

  /* Под кругом-разделителем и под восстановленным знаком мелкого письма нет:
     эти метки принадлежат записи и должны читаться целиком. */
  function fineBlocked(bl, k) {
    var c = coarseOf(bl, k);
    return bl.dots.indexOf(c) >= 0 || !!bl.restored[c];
  }

  /* Слова растаскиваются по предложению. Иначе они могли бы случайно сойтись в
     одном углу, и поиск терял бы смысл: найдя два слова до точки, игрок вправе
     решить, что дальше там пусто, и уйти искать за неё. */
  function planFine(bl, plan, rnd2) {
    var w = fineW(bl), out = [], bySent = {}, sents = sentences(bl), used = {};
    plan.forEach(function (p, i) { (bySent[p.s] = bySent[p.s] || []).push(i); });
    Object.keys(bySent).forEach(function (sk) {
      var si = +sk, list = bySent[sk], own = {};
      (sents[si] || []).forEach(function (c) { own[c] = 1; });
      // все мелкие клетки предложения в порядке чтения
      var all = [], fy, fx;
      for (fy = 0; fy < fineH(bl); fy++) {
        for (fx = 0; fx < w; fx++) {
          var k = fy * w + fx;
          if (own[coarseOf(bl, k)] && !fineBlocked(bl, k)) all.push(k);
        }
      }
      if (!all.length) return;
      /* Предложение режется на столько долей, сколько в нём слов, и каждое
         слово встаёт в СВОЮ долю. Иначе слова могли бы случайно сойтись в
         одном углу, и поиск терял бы смысл: найдя два слова до точки, игрок
         вправе решить, что дальше там пусто, и уйти искать за неё. */
      var slice = all.length / list.length;
      list.forEach(function (wi, j) {
        var len = clamp(plan[wi].c.length + 1, 2, 4);
        var lo = Math.floor(j * slice), hi = Math.floor((j + 1) * slice);
        var run = pickRun(all, lo, hi, len, w, rnd2, used) || pickRun(all, 0, all.length, len, w, rnd2, used);
        out[wi] = run || all.slice(0, Math.min(len, all.length));
        /* Между словами обязателен зазор. Впритык они сливаются в одну серию:
           курсор переходит с конца одного на начало другого, выделение
           выходит длиннее слова, и верный на вид ход даёт отказ. */
        out[wi].forEach(function (k) {
          [0, -1, 1, -w, w, -w - 1, -w + 1, w - 1, w + 1].forEach(function (d) { used[k + d] = 1; });
        });
      });
    });
    plan.forEach(function (p, i) { if (!out[i]) out[i] = [0, 1]; });
    return out;
  }

  /* Горизонтальный отрезок нужной длины внутри доли: по слову должно быть
     удобно провести курсором одним движением. */
  function pickRun(all, lo, hi, len, w, rnd2, used) {
    var cands = [], p, q, ok;
    for (p = lo; p + len <= hi; p++) {
      ok = true;
      for (q = 0; q < len && ok; q++) {
        if (used && used[all[p + q]]) ok = false;
        else if (q && (all[p + q] !== all[p + q - 1] + 1 || ((all[p + q] / w) | 0) !== ((all[p] / w) | 0))) ok = false;
      }
      if (ok) cands.push(p);
    }
    if (!cands.length) return null;
    var at = cands[Math.floor(rnd2() * cands.length)];
    return all.slice(at, at + len);
  }

  /* Движение мелкого знака — то же, что у поля: связное качание, дыхание и
     волна от курсора. Слово обязано выдавать себя ПОВАДКОЙ, а не тем, что оно
     единственное шевелится среди неподвижных. */
  function stepFine(s, dt) {
    var bl = s.bl, w = fineW(bl), n = w * fineH(bl), P = env.pointer;
    var c = fineSize(), zs = c / F.BASE, amp = 3.6 * zs;
    var wr = F.WAVE_R * Math.min(1.4, Math.max(0.6, zs));
    var lag = F.lagV, out = s._out || (s._out = {});
    var cx = P ? P.x : -1e5, cy = P ? P.y : -1e5;
    if (!s.fine || s.fine.length !== n) {
      s.fine = [];
      for (var q = 0; q < n; q++) s.fine.push({ s: 1, ox: 0, oy: 0, rot: 0 });
    }
    for (var k = 0; k < n; k++) {
      var st = s.fine[k];
      if (s.blocked[k]) { st.hide = 1; continue; }
      st.hide = 0;
      var fx = k % w, fy = (k / w) | 0;
      var ph = (F.vnoise(fx / 21, fy / 21, F.SEED + 6) * 0.86 + G.rand3(fx, fy, F.SEED + 1) * 0.14) * Math.PI * 2;
      var rt = 0.24 + F.vnoise(fx / 27, fy / 27, F.SEED + 8) * 0.22 + G.rand3(fx, fy, F.SEED + 2) * 0.05;
      out.breath = 1; out.lag = 0; out.waveMul = 1;
      out.rise = 0; out.fall = 0; out.evade = 0;
      out.breathFreeze = 0; out.kick = 0; out.rot = 1; out.ph = ph;
      var wd = s.byCell[k];
      if (wd !== undefined) {
        var word = s.words[wd];
        if (word.live && !word.done) F.behave(word.kind, out, ringNow(word.kind) ? BEH_RING : BEH_IDLE);
      }
      var bt = out.breathFreeze ? Math.floor(now * 1.6) / 1.6 : now;
      var ox = Math.sin(bt * rt * 2 * Math.PI * 0.16 + ph) * amp * out.breath;
      var oy = Math.cos(bt * rt * 2 * Math.PI * 0.13 + ph * 1.7) * amp * out.breath;
      if (out.kick) ox += Math.sin(ph * 5.1) * out.kick * zs * 2.4;
      if (out.lag) { ox -= lag.x * out.lag * zs; oy -= lag.y * out.lag * zs; }
      var rot = Math.sin(bt * rt * 2 * Math.PI * 0.11 + ph) * 0.125 * out.rot;
      var px = finePos(s, k), sx = px.x + ox, sy = px.y + oy;
      var dx = sx - cx, dy = sy - cy, d = Math.sqrt(dx * dx + dy * dy) || 1e-4;
      if (out.evade && d < wr) {
        var push = Math.pow(1 - d / wr, 1.5) * 32 * zs * out.evade * Math.min(1, s.spd / 380);
        sx += dx / d * push; sy += dy / d * push;
        dx = sx - cx; dy = sy - cy; d = Math.sqrt(dx * dx + dy * dy) || 1e-4;
      }
      var f = d < wr ? Math.pow(1 - d / wr, 2.1) : 0;
      var tgt = 1 + f * F.WAVE_A * out.waveMul;
      var kk = tgt > st.s ? (out.rise || 9.5) : (out.fall || 9.5);
      st.s += (tgt - st.s) * Math.min(1, dt * kk);
      st.ox = sx - px.x; st.oy = sy - px.y; st.rot = rot;
    }
  }

  /* Помеха-линия: вид записи сменяется не разом, а полосой, пробегающей по ней. */
  function sweepY(s, bl) {
    if (!s.sweep) return null;
    var r = rectOf(bl), u = clamp((now - s.sweep.t0) / SWEEP_T, 0, 1);
    var e = u * u * (3 - 2 * u);
    return { y: s.sweep.dir > 0 ? r.y0 + (r.y1 - r.y0) * e : r.y1 - (r.y1 - r.y0) * e, u: u, dir: s.sweep.dir };
  }
  // прошла ли помеха эту точку: позади неё уже новый вид
  function swept(s, bl, y) {
    var sw = sweepY(s, bl);
    if (!sw) return true;
    return sw.dir > 0 ? y < sw.y : y > sw.y;
  }

  function startWords(bl) {
    if (file[2] < 1) { reject(); flare[2] = 1; return; }
    var plan = wordPlan(bl);
    if (plan.length < 1) { reject(); flare[2] = 1; return; }
    focus(bl, 1.9);
    var spent = file[2];
    file[2] = 0;

    var seed = (bl.ox * 7349 + bl.oy * 911 + plan.length) >>> 0;
    var rnd2 = rng32(seed);
    var fine = planFine(bl, plan, rnd2);

    /* Камертоны. Часть слов ЗАПЕРТА: их знаки стоят мёртво, повадки у них нет,
       и даже верно обведённое запертое слово считается ошибкой. Чтобы его
       открыть, надо найти в записи знак, в точности повторяющий знак из меню,
       и перенести камертон на него. Тогда слово оживает и ведёт себя как якорь
       той повадки, какая была у камертона. Так меню обязательно к делу: без
       него этап не пройти, а ошибиться и потерять камертон можно — он уходит
       на любой знак, на который его уронили. */
    var menu = invList('glyph').map(function (it, i) {
      return { g: it.g, item: it, kind: it.kind !== undefined ? it.kind : G.hash3(it.g, 5, 77) % 5,
               used: false, shake: 0, i0: i };
    });
    /* Запертых слов на одно меньше, чем камертонов: один остаётся про запас,
       чтобы одна ошибка не заперла этап намертво. Совсем без запаса — только
       когда камертон всего один. Да и выход из этапа возвращает потраченные. */
    var lockN = menu.length >= 2
      ? Math.min(menu.length - 1, Math.floor(plan.length / 2))
      : Math.min(menu.length, Math.floor(plan.length / 2));
    menu = menu.slice(0, Math.min(menu.length, lockN + 2));

    var words = [], byCell = {}, over = {}, li = 0;
    plan.forEach(function (p, i) {
      var cells = fine[i] || [];
      // запираются слова вразбивку, чтобы поиск на глаз и поиск знаком чередовались
      var lock = li < lockN && (i % 2 === 1 || plan.length - i <= lockN - li);
      var ent = lock ? menu[li++] : null;
      var w = { wi: i, cells: cells, kind: ent ? ent.kind : p.kind,
                locked: !!ent, live: !ent, key: ent ? cells[0] : -1,
                done: false, doneAt: 0 };
      if (ent && cells.length) over[cells[0]] = ent.g;
      cells.forEach(function (k) { byCell[k] = words.length; });
      words.push(w);
    });

    /* Начертания мелкого поля и закрытые клетки считаются один раз: иначе на
       каждый кадр приходилось бы по нескольку тысяч хешей. */
    var fn = fineW(bl) * fineH(bl), gids = [], blocked = [], fk;
    for (fk = 0; fk < fn; fk++) {
      var bk = fineBlocked(bl, fk);
      blocked.push(bk);
      gids.push(bk ? 0 : fineGid(bl, fk));
    }

    ses = { stage: 3, bl: bl, plan: plan, words: words, byCell: byCell, over: over,
            gids: gids, blocked: blocked,
            menu: menu, spent: spent, spentItems: [],
            sel: null, bad: null, ring: null, tap: null, drag: null,
            sweep: { dir: Math.random() < 0.5 ? 1 : -1, t0: now, back: false },
            shrink: 1, spd: 0, px: 0, py: 0, fine: null, scroll: 0,
            fz: FZ0, fx: 0, fy: 0 };
    clampPan(ses);
    S.glitch();
    btnReset();
  }

  function cellsAbs(bl, list) { return list.map(function (k) { return [k % bl.w, (k / bl.w) | 0]; }); }

  function ringNow(kind) { return !!(ses.ring && ses.ring.kind === kind && now - ses.ring.t < RING_T); }

  /* Камертон потрачен: вся его повадка в записи звучит во весь голос. Сам якорь
     уходит из хранилища, только когда этап закончен: выход и перезагрузка его
     не сжигают. */
  function burn(entry) {
    entry.used = true;
    if (entry.item) ses.spentItems.push(entry.item);
  }

  /* Камертон уронили на знак записи. Попал в тот самый — слово оживает и
     звучит; не в тот — камертон потерян. */
  function dropTuner(entry, k) {
    var s = ses;
    if (k < 0) { S.nothing(); return; }                 // мимо записи: вернулся в меню
    var hit = -1;
    for (var i = 0; i < s.words.length; i++) {
      var w = s.words[i];
      if (w.locked && !w.live && w.key === k && s.over[k] === entry.g) { hit = i; break; }
    }
    burn(entry);
    if (hit < 0) { reject(0.5); env.shake(0.3); entry.shake = 0.5; return; }
    var w2 = s.words[hit];
    w2.live = true;
    s.ring = { kind: w2.kind, t: now };
    var p = finePos(s, k);
    env.pulse(p.x, p.y, true);
    S.tuning(w2.kind, RING_T);
    S.bloom();
  }

  function adjacentFine(bl, a, b) {
    var w = fineW(bl);
    var ax = a % w, ay = (a / w) | 0, bx = b % w, by = (b / w) | 0;
    return Math.abs(ax - bx) + Math.abs(ay - by) === 1;
  }

  function pressWords(x, y, mh) {
    var s = ses;
    if (s.sweep) { S.nothing(); return; }               // пока идёт помеха, записи ещё нет
    if (mh && mh.e) { s.drag = { entry: mh.e, x: x, y: y, x0: x, y0: y }; S.grip(true); return; }
    if (mh) return;
    var k = fineAt(s, x, y);
    if (k < 0 || s.blocked[k]) { S.nothing(); return; }
    var wd = s.byCell[k], w = wd === undefined ? null : s.words[wd];
    if (w && w.done) { S.nothing(); return; }
    s.sel = { cells: [k], kind: w && w.live ? w.kind : -1, t0: now };
    S.key(0);
  }

  /* Взятые знаки подстраиваются под повадку первого. Чужой знак в общий ход не
     входит, и серия на нём рвётся. */
  function moveWords(x, y) {
    var s = ses;
    if (s.drag) { s.drag.x = x; s.drag.y = y; return; }
    if (!s.sel) return;
    var k = fineAt(s, x, y);
    if (k < 0 || s.sel.cells.indexOf(k) >= 0) return;
    if (!adjacentFine(s.bl, s.sel.cells[s.sel.cells.length - 1], k)) return;
    if (s.blocked[k]) { breakSel(k); return; }
    var wd = s.byCell[k], w = wd === undefined ? null : s.words[wd];
    var kind = w && w.live && !w.done ? w.kind : -1;
    if (kind !== s.sel.kind) { breakSel(k); return; }
    s.sel.cells.push(k);
    S.key(s.sel.cells.length % 4);
  }
  function breakSel(k) {
    var s = ses;
    s.bad = { cells: s.sel.cells.concat(k >= 0 ? [k] : []), t: now };
    s.sel = null;
    reject(0.35);
  }

  /* Слово закрепляется, только если выделение совпало с ним в точности.
     Запертое слово даёт ошибку даже при верном выделении: без камертона оно
     не звучит, и корабль его не принимает. */
  /* d приходит снаружи: общий обработчик отпускания снимает перетаскивание
     раньше, чем доходит до этапа. */
  function releaseWords(x, y, d) {
    var s = ses;
    if (d && d.entry) { dropTuner(d.entry, fineAt(s, x, y)); return; }
    if (!s.sel) return;
    var sel = s.sel.cells.slice().sort(function (a, b) { return a - b; });
    s.sel = null;
    var wd = s.byCell[sel[0]], w = wd === undefined ? null : s.words[wd];
    var exact = !!w && !w.done && w.cells.length === sel.length &&
                w.cells.slice().sort(function (a, b) { return a - b; }).every(function (k, i) { return k === sel[i]; });
    if (exact && w.live) {
      w.done = true; w.doneAt = now;
      var p = finePos(s, w.cells[0]);
      env.pulse(p.x, p.y, true);
      S.wordLock(w.kind);
      return;
    }
    s.bad = { cells: sel, t: now };
    reject(0.4);
  }

  /* Слова размечены: помеха бежит обратно, и запись возвращается к своему виду
     уже со словами на местах. */
  function finishWords() {
    var s = ses;
    if (s.sweep) return;
    s.sweep = { dir: Math.random() < 0.5 ? 1 : -1, t0: now, back: true };
    S.glitch();
    btnReset();
  }

  function completeWords() {
    var s = ses, bl = s.bl, to = env.folderPos(3), n = s.plan.length;
    bl.words = s.plan.map(function (w) { return { s: w.s, tis: w.tis, c: w.c, kind: w.kind }; });
    s.spentItems.forEach(function (it) { INV().remove(it); });
    s.plan.forEach(function (w, i) {
      var p = cellXY(bl, w.c[0]);
      fly(p.x, p.y, to.x, to.y - 8, { d: i * 0.1, done: function () { flare[3] = 1; S.tick(i, n); } });
    });
    file[3] = Math.min(LCAP, file[3] + n);
    bl.stage = 4;
    dirty = true;
    S.sorted(2, 3);
    endSession();
  }

  // --- отрисовка мелкого поля ---------------------------------------------------

  /* Заливка клетки: выделение проступает НЕ СРАЗУ, а через долю секунды и
     плавно — иначе оно дёргается вслед за курсором и читается как мусор.
     Собранное слово остаётся залитым навсегда: игрок всегда видит, что уже
     сделано. Знак внутри залитой клетки вырезается из заливки и оттого
     выглядит чёрным. */
  var SEL_LAG = 0.14, SEL_UP = 0.3, BAD_DOWN = 1.0;

  function fineFill(s, k) {
    var w = s.byCell[k] !== undefined ? s.words[s.byCell[k]] : null;
    if (w && w.done) return { a: 1, hot: clamp((now - w.doneAt) / 0.6, 0, 1) };
    if (s.sel && s.sel.cells.indexOf(k) >= 0) {
      return { a: clamp((now - s.sel.t0 - SEL_LAG) / SEL_UP, 0, 1), hot: 0 };
    }
    if (s.bad && s.bad.cells.indexOf(k) >= 0) {
      return { a: clamp(1 - (now - s.bad.t) / BAD_DOWN, 0, 1), hot: -1 };
    }
    return null;
  }

  function drawFine(ctx, s) {
    if (!s.fine) return;
    var bl = s.bl, w = fineW(bl), n = w * fineH(bl), c = fineU(s);
    // и знак, и заливка живут в крупности САМОГО поля записи, а не карты
    var box = F.atlasBox * c / F.CELL, back = !!(s.sweep && s.sweep.back);
    var r = rectOf(bl);
    ctx.save();
    ctx.beginPath(); ctx.rect(r.x0, r.y0, r.x1 - r.x0, r.y1 - r.y0); ctx.clip();
    for (var k = 0; k < n; k++) {
      var st = s.fine[k];
      if (!st || st.hide) continue;
      var p = finePos(s, k), px = p.x + st.ox, py = p.y + st.oy;
      // впереди помехи мелкого письма ещё нет, а на обратном ходу его уже нет
      if (swept(s, bl, py) === back) continue;
      var gid = s.over[k] !== undefined ? s.over[k] : s.gids[k];
      var fill = fineFill(s, k);
      var bw = box * st.s * s.shrink;
      ctx.save();
      if (st.rot) {
        ctx.translate(px, py); ctx.rotate(st.rot); ctx.translate(-px, -py);
      }
      ctx.globalAlpha = 1;
      F.atlas.draw(ctx, gid, px - bw / 2, py - bw / 2, bw, bw);
      if (fill && fill.a > 0.01) {
        // собранное слово остаётся залитым СВЕТЛЫМ, а тёплым его только обводит:
        // так видно и что сделано, и что делается прямо сейчас
        var col = fill.hot < 0 ? '255,120,80' : fill.hot > 0 ? '246,240,230' : '236,240,248';
        ctx.globalAlpha = fill.a * 0.92;
        ctx.fillStyle = 'rgba(' + col + ',1)';
        ctx.fillRect(p.x - c / 2, p.y - c / 2, c, c);
        // знак вырезается из заливки: внутри светлой клетки он читается чёрным
        ctx.globalCompositeOperation = 'destination-out';
        ctx.globalAlpha = fill.a;
        F.atlas.draw(ctx, gid, px - bw / 2, py - bw / 2, bw, bw);
      }
      ctx.restore();
    }
    // собранные слова обведены тёплым: видно всё, что уже сделано
    ctx.globalCompositeOperation = 'lighter';
    s.words.forEach(function (wd) {
      if (!wd.done) return;
      var a = clamp((now - wd.doneAt) / 0.6, 0, 1);
      fineEdges(ctx, s, wd.cells, 'rgba(255,190,110,' + (0.45 + 0.45 * a).toFixed(3) + ')', 2);
    });
    if (s.bad) {
      var ba = 1 - clamp((now - s.bad.t) / BAD_DOWN, 0, 1);
      fineEdges(ctx, s, s.bad.cells, 'rgba(255,80,50,' + ba.toFixed(3) + ')', 2);
    }
    ctx.restore();
    drawSweep(ctx, s);
  }

  function fineEdges(ctx, s, cells, col, lw) {
    var bl = s.bl, o = fineOrg(s), c = o.u, w = fineW(bl), set = {};
    cells.forEach(function (k) { set[k] = 1; });
    ctx.save();
    glowStroke(ctx, col, 9, lw);
    ctx.beginPath();
    cells.forEach(function (k) {
      var x = k % w, y = (k / w) | 0, X = o.x + x * c, Y = o.y + y * c;
      if (!set[k - 1] || x === 0) { ctx.moveTo(X, Y); ctx.lineTo(X, Y + c); }
      if (!set[k + 1] || x === w - 1) { ctx.moveTo(X + c, Y); ctx.lineTo(X + c, Y + c); }
      if (!set[k - w]) { ctx.moveTo(X, Y); ctx.lineTo(X + c, Y); }
      if (!set[k + w]) { ctx.moveTo(X, Y + c); ctx.lineTo(X + c, Y + c); }
    });
    ctx.stroke();
    ctx.restore();
  }

  /* Сама помеха: яркая полоса со штрихами шума, как вертикальный сбой у
     старого существа, только поперёк записи. */
  function drawSweep(ctx, s) {
    var sw = sweepY(s, s.bl);
    if (!sw || sw.u >= 1) return;
    var r = rectOf(s.bl), h = Math.max(3, F.CELL * 0.12);
    ctx.save();
    ctx.beginPath(); ctx.rect(r.x0, r.y0, r.x1 - r.x0, r.y1 - r.y0); ctx.clip();
    ctx.globalCompositeOperation = 'lighter';
    var g = ctx.createLinearGradient(0, sw.y - h * 3, 0, sw.y + h * 3);
    g.addColorStop(0, 'rgba(255,190,120,0)');
    g.addColorStop(0.5, 'rgba(255,230,190,0.85)');
    g.addColorStop(1, 'rgba(255,190,120,0)');
    ctx.fillStyle = g;
    ctx.fillRect(r.x0, sw.y - h * 3, r.x1 - r.x0, h * 6);
    ctx.fillStyle = 'rgba(255,240,210,0.9)';
    for (var i = 0; i < 26; i++) {
      var x = r.x0 + Math.random() * (r.x1 - r.x0), ww = 4 + Math.random() * 40;
      ctx.globalAlpha = 0.2 + Math.random() * 0.6;
      ctx.fillRect(x, sw.y + (Math.random() - 0.5) * h * 2.2, ww, Math.max(1, h * 0.25));
    }
    ctx.restore();
  }

  /* --- 4. Смысл ---------------------------------------------------------------- */

  /* Запись не подменяется текстом и никуда не девается. Узлы — те самые слова,
     которые игрок разметил на третьем этапе, и они остаются на своих клетках;
     фигуры первого этапа и круги второго лежат под ними, как лежали.

     Мысль — это порядок, в котором узлы связаны (раздел 8: узел, связь, узел).
     Каждая связь стоит знака пустоты из хранилища, и на проведённой линии
     проступает её ⟨текст⟩: линия, которую игрок тянет, И ЕСТЬ отношение,
     которое он вскрывает. Куда мысль идёт дальше, узел показывает креном — тем
     же, каким узел цепочки на анализе подаётся в сторону следующего. */

  /* Шрифт графа записи. Полужирный: тонкий моноширинный через постобработку
     с аберрацией и зерном расплывался и читался плохо. */
  var GFONT = 'Consolas, "Courier New", monospace', GFONT_W = '600';
  function gfont(fs) { return GFONT_W + ' ' + fs.toFixed(1) + 'px ' + GFONT; }

  var w100 = {};
  function widthAt(tok, fs) {
    if (w100[tok] === undefined) {
      if (!measure) measure = document.createElement('canvas').getContext('2d');
      measure.font = GFONT_W + ' 100px ' + GFONT;
      w100[tok] = measure.measureText(tok).width;
    }
    return w100[tok] * fs / 100;
  }

  function wordBox(bl, w) {
    var x0 = 1e9, y0 = 1e9, x1 = -1e9, y1 = -1e9, h = F.CELL / 2;
    w.c.forEach(function (k) {
      var p = cellXY(bl, k);
      x0 = Math.min(x0, p.x - h); x1 = Math.max(x1, p.x + h);
      y0 = Math.min(y0, p.y - h); y1 = Math.max(y1, p.y + h);
    });
    return { x0: x0, y0: y0, x1: x1, y1: y1, cx: (x0 + x1) / 2, cy: (y0 + y1) / 2 };
  }

  function defsOf(bl) { return sentenceDefs(bl, sentences(bl).length); }

  /* Текст узла — его токены подряд. */
  function nodeTokens(bl, w) {
    var d = defsOf(bl)[w.s];
    if (!d) return [];
    return w.tis.map(function (ti) { return d.text[ti]; }).filter(function (t) { return t !== undefined; });
  }

  /* Текст связи — то, что стоит в записи между двумя соседними узлами, в том
     числе через точку-разделитель. */
  function linkTokens(bl, a, b) {
    var defs = defsOf(bl), out = [];
    for (var si = a.s; si <= b.s && si < defs.length; si++) {
      var toks = defs[si].text;
      var s0 = si === a.s ? a.tis[a.tis.length - 1] + 1 : 0;
      var s1 = si === b.s ? b.tis[0] : toks.length;
      for (var ti = s0; ti < s1; ti++) if (isLink(toks[ti])) out.push(toks[ti]);
    }
    return out;
  }

  function spendVoid() {
    if (!INV().spendVoid(BY_ORDER)) { reject(0.5); env.shake(0.3); return false; }
    return true;
  }

  var LINE_T = 0.45;                     // линия тянется от узла к узлу, а не появляется разом
  var LINK_SHOW = 3.2;                   // сколько текст свежей связи виден сам по себе

  function startLines(bl) {
    if (file[3] < 1) { reject(); flare[3] = 1; return; }
    var chain = wordsOf(bl);
    if (chain.length < 2) { reject(); flare[3] = 1; return; }
    focus(bl, 1.9);
    var spent = file[3];
    file[3] = 0;
    ses = { stage: 4, bl: bl, chain: chain, at: -1, links: [], spent: spent,
            miss: null, done: -1, t0: now };
    btnReset();
  }

  function finishLines() {
    var s = ses, bl = s.bl;
    bl.stage = 5;
    // знак кнопки журнала берётся из того, что есть в хранилище
    var have = INV().items().filter(function (it) { return it.k !== 'shape' && it.g; });
    bl.pin = have.length ? have[Math.floor(Math.random() * have.length)].g : randomGlyph();
    if (bl.inst && !T.objects[bl.inst.type].repeat) objRead[bl.inst.text] = 1;
    dirty = true;
    journal.fresh = 1;
    S.decode();
    S.sorted(2, 3);
  }

  function pressLines(x, y) {
    var s = ses, bl = s.bl;
    if (s.done >= 0) { if (now - s.done > 1.2) endSession(); return; }
    var hit = -1;
    s.chain.forEach(function (w, i) {
      var b = wordBox(bl, w);
      if (x > b.x0 - 5 && x < b.x1 + 5 && y > b.y0 - 5 && y < b.y1 + 5) hit = i;
    });
    if (hit < 0) { S.nothing(); return; }
    if (hit !== s.at + 1) { s.miss = { i: hit, t: now }; reject(0.4); env.shake(0.2); return; }
    if (!spendVoid()) return;
    if (s.at >= 0) s.links.push({ a: s.at, b: hit, born: now });
    s.at = hit;
    var p = wordBox(bl, s.chain[hit]);
    env.pulse(p.cx, p.cy, true);
    if (s.at > 0) S.lineZap(); else S.keyPress(0);
    if (s.at === s.chain.length - 1) { s.done = now + LINE_T + 0.7; finishLines(); }
  }


  // --- ввод --------------------------------------------------------------------

  function hitBtn(x, y) { return btn.live && Math.hypot(x - btn.x, y - btn.y) < btn.r + 12; }

  function menuRect() {
    var r = rectOf(ses.bl), v = env.view(), w = ses.stage === 1 ? 210 : 170, h = Math.min(ses.stage === 1 ? 400 : 360, v.h - 250);
    var x = r.x1 + 40;
    if (x + w > v.w - 12) x = r.x0 - 40 - w;
    var y = clamp((r.y0 + r.y1) / 2 - h / 2, 96, v.h - 140 - h);
    return { x: x, y: y, w: w, h: h };
  }

  function menuList() {
    if (ses.stage === 1) {
      var excl = ses.placed.map(function (p) { return p.item; });
      if (ses.drag) excl.push(ses.drag.item);
      // одинаковые фигуры — одной стопкой со счётом
      return INV().stackShapes(invList('shape', excl), false);
    }
    if (ses.stage === 2) return ses.menu.filter(function (e) { return e.slot < 0 && !(ses.drag && ses.drag.entry === e); });
    if (ses.stage === 3) return ses.menu.filter(function (e) { return !e.used; });
    return [];
  }

  var MENU_ROW1 = 84;
  function menuLayout() {
    var m = menuRect(), list = menuList(), out = [];
    if (ses.stage === 1) {
      // два столбца: нужная фигура находится быстрее
      var cw = (m.w - 22) / 2;
      list.forEach(function (e, i) {
        var col = i % 2, row = (i / 2) | 0;
        var x = m.x + 8 + col * (cw + 6), y = m.y + 10 + row * MENU_ROW1 - ses.scroll;
        out.push({ e: e, x: x, y: y, w: cw, h: MENU_ROW1 - 8, cx: x + cw / 2, cy: y + (MENU_ROW1 - 8) / 2 });
      });
    } else {
      list.forEach(function (e, i) {
        var col = i % 2, row = (i / 2) | 0, cs = 66;
        var x = m.x + 12 + col * (cs + 14), y = m.y + 12 + row * (cs + 12) - ses.scroll;
        out.push({ e: e, x: x, y: y, w: cs, h: cs, cx: x + cs / 2, cy: y + cs / 2 });
      });
    }
    return { m: m, items: out };
  }

  function menuHit(x, y) {
    var L = menuLayout();
    if (x < L.m.x || x > L.m.x + L.m.w || y < L.m.y || y > L.m.y + L.m.h) return null;
    for (var i = 0; i < L.items.length; i++) {
      var it = L.items[i];
      if (x > it.x && x < it.x + it.w && y > it.y && y < it.y + it.h) return it;
    }
    return { none: true };
  }

  function press(x, y) {
    if (journal.open) {
      var sel = null, hitJ = null;
      journal.hits.forEach(function (h) {
        if (h.bl.id === journal.sel) sel = h;
        if (x >= h.x0 && x <= h.x1 && y >= h.y0 && y <= h.y1) hitJ = h;
      });
      if (sel && Math.abs(x - sel.px) < 16 && Math.abs(y - sel.py) < 16) { unpin(sel.bl); return; }
      if (hitJ) { journal.sel = journal.sel === hitJ.bl.id ? null : hitJ.bl.id; S.key(1); return; }
      journal.open = false; journal.sel = null; S.tab(1);
      return;
    }
    if (!ses || ses.choose) {
      for (var pi = 0; pi < blocks.length; pi++) {
        var pb = blocks[pi];
        if (pb.stage < 5 || pb.inJ || !pb.pin) continue;
        var pp = pinPos(pb), pr = Math.max(14, F.CELL * 0.4);
        if (Math.abs(x - pp.x) < pr && Math.abs(y - pp.y) < pr) { pinToJournal(pb); return; }
      }
    }
    if (!ses) return;
    var s = ses;
    if (s.choose) { pressChoose(x, y); return; }
    if (s.stage === 0) return;
    if (s.stage === 4) { pressLines(x, y); return; }
    if (hitBtn(x, y)) {
      if (s.stage === 1) finishTiling();
      else if (s.stage === 2) evaluateRestore();
      else if (s.stage === 3) finishWords();
      return;
    }
    var mh = menuHit(x, y);

    if (s.stage === 1) {
      for (var ri = 0; ri < s.placed.length; ri++) {
        if (!canRotate(s.placed[ri])) continue;
        var dp = dotPos(s.placed[ri]);
        if (Math.hypot(dp.x - x, dp.y - y) < 12) { rotateTile(s.placed[ri]); return; }
      }
      if (mh && mh.e) { s.drag = { item: mh.e.item, rot: 0, x: x, y: y }; S.grip(true); return; }
      var k = cellAt(s.bl, x, y);
      if (k >= 0) {
        var cx = k % s.bl.w, cy = (k / s.bl.w) | 0;
        for (var j = 0; j < s.placed.length; j++) {
          var p = s.placed[j];
          var hitP = p.cells.some(function (q) { return p.x + q[0] === cx && p.y + q[1] === cy; });
          if (hitP) {
            s.placed.splice(j, 1);
            saveDraft(s);
            S.cellShrink(false, true);
            s.drag = { item: p.item, rot: p.rot || 0, x: x, y: y };
            S.grip(true);
            return;
          }
        }
      }
      return;
    }

    if (s.stage === 2) {
      if (now < s.showUntil) return;
      if (mh && mh.e) {
        if (mh.e.dim) { reject(0.3); mh.e.shake = 0.45; return; }
        s.drag = { entry: mh.e, x: x, y: y, x0: x, y0: y };
        return;
      }
      var k2 = cellAt(s.bl, x, y);
      if (k2 >= 0 && s.rem.indexOf(k2) >= 0 && removedDone(k2)) {
        if (s.slots[k2]) {
          var en = s.slots[k2];
          delete s.slots[k2]; en.slot = -1;
          s.drag = { entry: en, x: x, y: y, x0: x, y0: y };
          return;
        }
        if (s.sel) { placeEntry(s.sel, k2); return; }
      }
      S.nothing();
      return;
    }

    if (s.stage === 3) { pressWords(x, y, mh); return; }
  }

  function move(x, y) {
    if (!ses) return;
    if (ses.drag) { ses.drag.x = x; ses.drag.y = y; }
    if (ses.stage === 3) moveWords(x, y);
  }

  function release(x, y) {
    if (!ses || (!ses.drag && !ses.sel && !ses.tap)) return;
    var s = ses, d = s.drag;
    s.drag = null;

    if (s.stage === 1) {
      var cells = tileCells(d.item, d.rot), sn = snapFor(cells, x, y);
      if (cellAt(s.bl, x, y) < 0) { S.nothing(); return; }
      var f = fits(cells, sn.x, sn.y, null);
      var np = { item: d.item, scale: 1, rot: d.rot || 0, cells: cells, x: sn.x, y: sn.y, shake: 0 };
      if (f.ok && costOf(s.placed.concat([np])) <= file[0]) {
        s.placed.push(np);
        saveDraft(s);
        S.knock();
        S.cellShrink(s.placed.length % 3 === 0, false);
      } else { reject(0.5); }
      return;
    }

    if (s.stage === 2) {
      var k = cellAt(s.bl, x, y);
      var moved = Math.hypot(x - d.x0, y - d.y0) > 8;
      if (k >= 0 && s.rem.indexOf(k) >= 0 && removedDone(k)) { placeEntry(d.entry, k); return; }
      if (!moved) { s.sel = s.sel === d.entry ? null : d.entry; S.key(1); }
      return;
    }

    if (s.stage === 3) releaseWords(x, y, d);
  }

  function wheel(dy, x, y) {
    if (journal.open) {
      journal.scroll = Math.max(0, Math.min(journal.max, journal.scroll + dy * 0.6));
      return true;
    }
    if (!ses || ses.choose) return false;
    if (ses.stage === 0 || ses.stage === 4) return true;
    var L = menuLayout();
    var overMenu = x >= L.m.x && x <= L.m.x + L.m.w && y >= L.m.y && y <= L.m.y + L.m.h;
    /* Колесо ВНУТРИ записи меняет крупность только её поля; снаружи — как
       везде, весь мир вместе с записью. */
    if (ses.stage === 3 && !overMenu) {
      var r = rectOf(ses.bl);
      if (x > r.x0 && x < r.x1 && y > r.y0 && y < r.y1) { fineZoom(ses, dy, x, y); return true; }
      return false;
    }
    if (x >= L.m.x && x <= L.m.x + L.m.w && y >= L.m.y && y <= L.m.y + L.m.h) {
      var rowH = ses.stage === 1 ? MENU_ROW1 : 78, rows = Math.ceil(L.items.length / 2);
      var maxS = Math.max(0, rows * rowH + 20 - L.m.h);
      ses.scroll = clamp(ses.scroll + (dy > 0 ? rowH : -rowH), 0, maxS);
    }
    return true;
  }

  // --- шаг -----------------------------------------------------------------------

  function stepSession(dt) {
    if (ses.choose) return;
    var s = ses, bl = s.bl, P = env.pointer, show = false, rect = null;
    if (s.stage === 0) {
      s.forming += dt;
      if (s.forming >= 1.7) {
        bl.stage = 1; bl.num = creatureNo; bl.ejn = ejectedNo;
        if (!bl.inst) bl.sec = ejectSector;
        dirty = true; startTiling(bl); return;
      }
    }
    if (s.stage === 1) {
      show = coverage() === bl.n; rect = rectOf(bl);
      // пока фигуру ведут над рамкой, ячейка уже чуть поддаётся
      var hover = s.drag && cellAt(bl, s.drag.x, s.drag.y) >= 0 ? 0.12 : 0;
      var want = (s.placed.length + hover) / 3;
      s.usedAnim += (want - s.usedAnim) * Math.min(1, dt * 5);
    }
    if (s.stage === 2) { show = s.rem.every(function (k) { return !!s.slots[k]; }); rect = rectOf(bl); }
    if (s.stage === 3) {
      // скорость курсора нужна уклоняющемуся: он отпрыгивает от быстрого хода
      if (P) {
        var vdx = P.x - s.px, vdy = P.y - s.py;
        s.spd += (Math.hypot(vdx, vdy) / Math.max(1e-3, dt) - s.spd) * Math.min(1, dt * 8);
        s.px = P.x; s.py = P.y;
      }
      if (s.sweep && now - s.sweep.t0 > SWEEP_T) {
        var back = s.sweep.back;
        s.sweep = null;
        if (back) { completeWords(); return; }
        s.shrinkT = now;                       // знаки садятся в своих клетках
      }
      if (s.shrinkT) s.shrink = 1 - (1 - SHRINK_TO) * clamp((now - s.shrinkT) / SHRINK_T, 0, 1);
      /* Курсор у кромки записи уводит её поле в эту сторону, с разгоном — тем
         же жестом, каким игрок водит саму карту (раздел 12). На выделении
         прокрутка выключена: иначе слово уезжает из-под руки. */
      if (P && !s.sweep && !s.sel) {
        var r3 = rectOf(bl), vx = 0, vy = 0;
        var mx = clamp((r3.x1 - r3.x0) * 0.1, 26, 80), my = clamp((r3.y1 - r3.y0) * 0.12, 20, 60);
        if (P.x > r3.x0 && P.x < r3.x1 && P.y > r3.y0 && P.y < r3.y1) {
          if (P.x - r3.x0 < mx) vx = (mx - (P.x - r3.x0)) / mx;
          else if (r3.x1 - P.x < mx) vx = -(mx - (r3.x1 - P.x)) / mx;
          if (P.y - r3.y0 < my) vy = (my - (P.y - r3.y0)) / my;
          else if (r3.y1 - P.y < my) vy = -(my - (r3.y1 - P.y)) / my;
        }
        if (vx || vy) {
          // чем крупнее письмо, тем длиннее поле: ход должен оставаться тем же
          var SPD = 380 * s.fz;
          s.fx += vx * Math.abs(vx) * SPD * dt;
          s.fy += vy * Math.abs(vy) * SPD * dt;
          clampPan(s);
        }
      }
      if (s.bad && now - s.bad.t > BAD_DOWN) s.bad = null;
      if (s.ring && now - s.ring.t > RING_T) s.ring = null;
      stepFine(s, dt);
      show = !s.sweep && s.words.length > 0 && s.words.every(function (w) { return w.done; });
      rect = rectOf(bl);
    }
    if (s.stage === 4) {
      if (s.miss && now - s.miss.t > 0.6) s.miss = null;
      if (s.done >= 0 && now - s.done > 4) { endSession(); return; }
    }
    [s.menu || [], s.placed || []].forEach(function (list) {
      list.forEach(function (e) { if (e.shake > 0) e.shake = Math.max(0, e.shake - dt); });
    });
    if (show && rect) {
      var tg = env.outside(rect, P.x, P.y);
      if (!btn.live) { btn.x = tg.x; btn.y = tg.y; btn.live = true; }
      else { var bk = Math.min(1, dt * 5); btn.x += (tg.x - btn.x) * bk; btn.y += (tg.y - btn.y) * bk; }
      env.setButton(btn);
    } else { btn.live = false; env.setButton(null); }
  }

  function buildMarks() {
    marks.clear();
    var nb = nextBase();
    blocks.forEach(function (bl) {
      var active = !!(ses && ses.bl === bl);
      var framed = bl.stage >= 1 || (active && ses.stage === 0 && ses.forming >= 0);
      if (framed) {
        for (var k = 0; k < bl.n; k++) {
          var wx = (bl.ox + k % bl.w) % F.W, wy = (bl.oy + ((k / bl.w) | 0)) % F.H;
          var j = F.jitter(wx, wy);
          var m = { id: bl.cells[k], still: 1, px: -j.x, py: -j.y };
          if (bl.restored[k] || bl.dots.indexOf(k) >= 0) m.hide = 1;
          // под дочитанной записью знаков больше нет: в рамке живёт только текст
          if (bl.stage >= 5) m.hide = 1;
          marks.set(F.ckey(wx, wy), m);
        }
      }
      // у заготовки записи объекта символы границы рисуются отдельно, цветом
      tiledCells(bl, active).forEach(function (k) {
        var mt = marks.get(cellKey(bl, k));
        if (mt) mt.hide = 1;
      });
      if (bl.stage === 0 && (bl.inst || bl === nb) && !framed) {
        for (var e = 0; e < bl.n; e++) {
          var ex = e % bl.w, ey = (e / bl.w) | 0;
          if (ex > 0 && ex < bl.w - 1 && ey > 0 && ey < bl.h - 1) continue;
          marks.set(cellKey(bl, e), { id: bl.cells[e], still: 1, hide: 1 });
        }
      }
      if (!active) return;
      var s = ses;
      if (s.stage === 2) {
        s.rem.forEach(function (k) {
          var m2 = marks.get(cellKey(bl, k));
          if (!m2) return;
          if (s.removal[k] === undefined) {
            // знак, который скоро сотрут: пульсирует, пока вокруг рисуется круг
            m2.grow = 0.3 + 0.2 * Math.sin(now * 2.6 + k);
            m2.lit = 1;
          } else {
            // гаснущий знак рисуется поверх поля: уменьшается и размывается
            m2.hide = 1;
          }
        });
      }
      /* Знаки слова живут своей повадкой — той же, что у якорей на карте.
         Клетки записи по умолчанию стоят неподвижно (still), и повадку надо
         отпустить; волну от курсора глушить нельзя, иначе затаившийся и
         тяжёлый себя не покажут — они только ею и выдают себя. */
      /* Крупные клетки записи гаснут там, где помеха уже прошла: на их месте
         лорный модуль рисует своё мелкое поле. */
      if (s.stage === 3) {
        for (var w3 = 0; w3 < bl.n; w3++) {
          var m3 = marks.get(cellKey(bl, w3));
          if (!m3) continue;
          var cp = cellXY(bl, w3);
          if (swept(s, bl, cp.y) !== !!(s.sweep && s.sweep.back)) m3.hide = 1;
        }
      }
      /* Узел кренится и подаётся в сторону следующего, когда курсор подходит:
         стрелок нет, есть наклон и смещение (как на анализе, раздел 21). */
      if (s.stage === 4) {
        var P4 = env.pointer, reach = F.CELL * 2.4;
        for (var q = 0; q < bl.n; q++) { var m4 = marks.get(cellKey(bl, q)); if (m4) m4.dim = 0.72; }
        s.chain.forEach(function (w, i) {
          var nx = s.chain[i + 1], nb = nx ? wordBox(bl, nx) : null;
          w.c.forEach(function (k) {
            var m = marks.get(cellKey(bl, k));
            if (!m) return;
            if (i <= s.at) { m.hide = 1; return; }          // узел уже стал словом
            m.dim = 0.1;
            if (i === s.at + 1) m.dim = 0;
            if (i === 0 && s.at < 0) { m.head = 1; m.still = 0; m.lit = 1; }
            if (s.miss && s.miss.i === i) m.px = (m.px || 0) + Math.sin(now * 55) * 5;
            if (!nb || !P4) return;
            var p = cellXY(bl, k), d = Math.hypot(p.x - P4.x, p.y - P4.y);
            var f = d < reach ? Math.pow(1 - d / reach, 1.7) : 0;
            if (f <= 0) return;
            var dx = nb.cx - p.x, dy = nb.cy - p.y, dd = Math.hypot(dx, dy) || 1;
            m.px = (m.px || 0) + dx / dd * f * F.CELL * 0.26;
            m.py = (m.py || 0) + dy / dd * f * F.CELL * 0.26;
            m.lean = (m.lean || 0) + Math.max(-0.5, Math.min(0.5, Math.atan2(dy, dx))) * 0.34 * f;
            m.lit = 1;
          });
        });
      }
    });
    F.setMarks(marks.size ? marks : null);
  }

  function step(dt) {
    now += dt;
    for (var i = 0; i < 4; i++) if (flare[i] > 0) flare[i] = Math.max(0, flare[i] - dt * 1.6);
    journal.k += ((journal.open ? 1 : 0) - journal.k) * Math.min(1, dt * 7);
    stepFx(dt);
    if (!env || !env.active()) return;
    if (ses) stepSession(dt);
    buildMarks();
  }

  // --- отрисовка ---------------------------------------------------------------

  function glowStroke(ctx, col, blur, lw) {
    ctx.shadowColor = col; ctx.shadowBlur = blur; ctx.strokeStyle = col; ctx.lineWidth = lw;
  }

  /* Светящиеся знаки рисуются из готовых картинок. Размытие свечения на
     каждый знак в каждом кадре съедало видеокарту: несколько заготовок на
     экране вешали игру. Картинка делается один раз на знак, цвет и размер. */
  var sprites = {}, spriteN = 0;
  function sprite(ctx, key, size, paint) {
    var tm = ctx.getTransform ? ctx.getTransform() : null;
    // масштаб без поворота; округлён, чтобы не плодить картинки
    var sc = tm ? Math.max(0.5, Math.round(Math.hypot(tm.a, tm.b) * 4) / 4) : 1;
    var qs = Math.max(6, Math.round(size / 4) * 4);
    var k = key + '|' + qs + '|' + sc.toFixed(2);
    var sp = sprites[k];
    if (!sp) {
      if (spriteN > 900) { sprites = {}; spriteN = 0; }
      var dim = qs * 1.9 + 24, cv = document.createElement('canvas');
      cv.width = cv.height = Math.ceil(dim * sc);
      var c2 = cv.getContext('2d');
      c2.scale(sc, sc);
      c2.translate(dim / 2, dim / 2);
      paint(c2, qs, sc);
      sp = sprites[k] = { cv: cv, dim: dim, qs: qs };
      spriteN++;
    }
    var d = sp.dim * size / sp.qs;
    ctx.drawImage(sp.cv, -d / 2, -d / 2, d, d);
  }
  // знак со свечением в текущей точке ctx; rgb — "r,g,b", a — яркость
  function glowGlyph(ctx, g, rgb, a, size, lw, blur) {
    if (a <= 0.004) return;
    var ga = ctx.globalAlpha;
    ctx.globalAlpha = ga * Math.min(1, a);
    sprite(ctx, 'g' + g + '|' + rgb + '|' + lw + '|' + blur, size, function (c2, qs, sc) {
      glowStroke(c2, 'rgb(' + rgb + ')', blur * sc, lw);
      G.drawGlyph(c2, g, qs, lw);
    });
    ctx.globalAlpha = ga;
  }
  function objRGB(bl) {
    if (bl.def.color === 'green') return '120,255,170';
    if (bl.def.color === 'blue') return '130,185,255';
    return '240,244,255';
  }
  // запись видна на экране (с запасом)
  function onScreen(bl) {
    var r = rectOf(bl), v = env.view(), m = F.CELL * 2;
    return r.x1 > -m && r.y1 > -m && r.x0 < v.w + m && r.y0 < v.h + m;
  }

  function drawFrame(ctx, bl, prog) {
    var r = rectOf(bl), w = r.x1 - r.x0, h = r.y1 - r.y0, L = 2 * (w + h) * clamp(prog, 0, 1);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    glowStroke(ctx, bl.inst ? objColor(bl, 0.95) : 'rgba(236,244,255,0.95)', 16, 3.4);
    ctx.lineCap = 'round';
    ctx.beginPath();
    ctx.moveTo(r.x0, r.y0);
    var pts = [[r.x1, r.y0, w], [r.x1, r.y1, h], [r.x0, r.y1, w], [r.x0, r.y0, h]], px = r.x0, py = r.y0;
    for (var i = 0; i < 4 && L > 0; i++) {
      var u = Math.min(1, L / pts[i][2]);
      ctx.lineTo(px + (pts[i][0] - px) * u, py + (pts[i][1] - py) * u);
      L -= pts[i][2]; px = pts[i][0]; py = pts[i][1];
    }
    ctx.stroke();
    ctx.restore();
  }

  function edgesPath(ctx, cells, ox, oy, u, keep) {
    var set = {};
    cells.forEach(function (q) { set[q[0] + ',' + q[1]] = 1; });
    if (!keep) ctx.beginPath();
    cells.forEach(function (q) {
      var x0 = ox + q[0] * u, y0 = oy + q[1] * u, x1 = x0 + u, y1 = y0 + u;
      if (!set[q[0] + ',' + (q[1] - 1)]) { ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); }
      if (!set[q[0] + ',' + (q[1] + 1)]) { ctx.moveTo(x0, y1); ctx.lineTo(x1, y1); }
      if (!set[(q[0] - 1) + ',' + q[1]]) { ctx.moveTo(x0, y0); ctx.lineTo(x0, y1); }
      if (!set[(q[0] + 1) + ',' + q[1]]) { ctx.moveTo(x1, y0); ctx.lineTo(x1, y1); }
    });
  }

  function drawTileEdges(ctx, bl, cellsAbs, col, lw) {
    drawManyEdges(ctx, bl, [cellsAbs], col, lw);
  }
  function drawManyEdges(ctx, bl, groups, col, lw, o, cell) {
    if (!groups.length) return;
    o = o || org(bl);
    cell = cell || F.CELL;
    ctx.beginPath();
    groups.forEach(function (cs) { edgesPath(ctx, cs, o.x, o.y, cell, true); });
    glowStroke(ctx, col, 8, lw);
    ctx.stroke();
  }

  /* Заготовка записи объекта: мигают символы её границы. */
  /* Клетки, уже покрытые фигурами: на этапе укладки их знаки горят цветом
     записи, и видно, где поле ещё пустое. */
  function tiledCells(bl, active) {
    var out = [];
    if (active && ses.stage === 1) {
      ses.placed.forEach(function (p) { p.cells.forEach(function (q) { out.push((p.y + q[1]) * bl.w + p.x + q[0]); }); });
    } else if (bl.stage === 1 && bl.draft) {
      bl.draft.forEach(function (d) { d.c.forEach(function (q) { out.push(q[1] * bl.w + q[0]); }); });
    }
    return out;
  }

  function drawTiled(ctx, bl, active) {
    var list = tiledCells(bl, active);
    if (!list.length) return;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    list.forEach(function (k) {
      if (k < 0 || k >= bl.n) return;
      var p = cellXY(bl, k), a = 0.85 + 0.15 * Math.sin(now * 2 + k);
      ctx.save();
      ctx.translate(p.x, p.y);
      glowGlyph(ctx, bl.cells[k], objRGB(bl), a, F.CELL * 0.66, 1.6, 12);
      ctx.restore();
    });
    ctx.restore();
  }

  function drawObjSeed(ctx, bl, hot) {
    var green = bl.def.color === 'green', white = !bl.inst;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (var k = 0; k < bl.n; k++) {
      var x = k % bl.w, y = (k / bl.w) | 0;
      if (x > 0 && x < bl.w - 1 && y > 0 && y < bl.h - 1) continue;
      var p = cellXY(bl, k), ph = k * 0.7, a, sc = 1;
      ctx.save();
      ctx.translate(p.x, p.y);
      if (white) {
        // журнал корабля светится тихо и ровно
        a = 0.2 + 0.1 * Math.sin(now * 1.3 + ph * 0.3);
      } else if (green) {
        ctx.rotate(now * 1.6 + ph);
        sc = 0.9 + 0.15 * Math.sin(now * 2.2 + ph);
        a = 0.55 + 0.35 * Math.sin(now * 3 + ph);
      } else {
        a = 0.9 * Math.max(0, Math.sin(now * 0.9 + ph));
      }
      if (hot) a = Math.min(1, a + 0.3 + 0.2 * Math.sin(now * 6));
      glowGlyph(ctx, bl.cells[k], objRGB(bl), a, F.CELL * 0.62 * sc, 1.5, 10);
      ctx.restore();
    }
    ctx.restore();
  }

  function drawPurgedAt(ctx, x, y, s, g, withGlyph, alpha) {
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.translate(x, y);
    ctx.globalAlpha *= alpha === undefined ? 1 : alpha;
    sprite(ctx, 'p' + (withGlyph ? g : '-'), s, function (c2, q, sc) {
      glowStroke(c2, 'rgba(236,244,255,0.95)', q * 0.2 * sc, Math.max(1.4, q * 0.04));
      c2.beginPath(); c2.arc(0, 0, q * 0.34, 0, Math.PI * 2); c2.stroke();
      if (withGlyph) G.drawGlyph(c2, g, q * 0.44, Math.max(1.1, q * 0.03));
    });
    ctx.restore();
  }

  function drawMenu(ctx) {
    var L = menuLayout(), m = L.m, s = ses;
    ctx.save();
    ctx.fillStyle = 'rgba(9,7,4,0.9)';
    ctx.fillRect(m.x, m.y, m.w, m.h);
    ctx.strokeStyle = 'rgba(255,170,90,0.35)';
    ctx.lineWidth = 1;
    ctx.strokeRect(m.x + 0.5, m.y + 0.5, m.w - 1, m.h - 1);
    ctx.beginPath(); ctx.rect(m.x, m.y, m.w, m.h); ctx.clip();
    ctx.globalCompositeOperation = 'lighter';
    L.items.forEach(function (li) {
      if (li.y + li.h < m.y || li.y > m.y + m.h) return;
      var e = li.e, sh = e.shake ? Math.sin(now * 60) * e.shake * 10 : 0;
      if (s.stage === 1) {
        // место под число справа сверху
        var it = e.item, sup = e.n > 1 ? 16 : 0;
        var u = Math.min(16, (li.w - 12 - sup) / it.w, (li.h - 12 - sup * 0.6) / it.h);
        var bx = li.cx + sh - it.w * u / 2 - sup / 2, by = li.cy - it.h * u / 2 + sup * 0.3;
        edgesPath(ctx, it.c, bx, by, u);
        glowStroke(ctx, (it.by || 'c') === 'p' ? 'rgba(255,210,150,0.95)' : 'rgba(255,160,70,0.9)', 8, 1.6);
        ctx.stroke();
        (it.s || []).forEach(function (sp) {
          var q = it.c[sp.i];
          if (!q) return;
          ctx.save();
          ctx.translate(bx + (q[0] + 0.5) * u, by + (q[1] + 0.5) * u);
          ctx.rotate(now * 1.9);
          G.drawGlyph(ctx, sp.g, u * 0.8, 1.1);
          ctx.restore();
        });
        if (e.n > 1) {
          ctx.shadowBlur = 0;
          NUM().sup(ctx, e.n, bx + it.w * u, by, 17, 'rgba(255,220,180,0.95)');
        }
      } else if (s.stage === 2) {
        var sel = s.sel === e;
        drawPurgedAt(ctx, li.cx + sh, li.cy, sel ? 48 : 58, e.g, true, e.dim ? 0.28 : sel ? 0.6 : 1);
      } else if (s.stage === 3) {
        /* Камертон живёт своей повадкой прямо в меню. Раньше якоря стояли тут
           неподвижными и одинаковыми, и выбирать между ними было не из чего:
           чем владеешь, становилось видно только после того, как потратишь. */
        var b = behPose(e.kind, li.cx + sh, li.cy, 40, e.i0 || 0), down = s.tap === e ? 0.86 : 1;
        ctx.save();
        ctx.globalAlpha = e.dim ? 0.28 : 1;
        ctx.translate(b.x, b.y);
        ctx.rotate(b.rot);
        glowStroke(ctx, 'rgba(255,176,90,0.95)', (10 + b.lit * 8) * down, 1.5);
        G.drawGlyph(ctx, e.g, 40 * b.s * down, 1.5);
        ctx.restore();
      }
    });
    ctx.restore();
  }

  /* Повадка знака в меню камертонов: то же поведение, каким якорь выдаёт себя
     на карте, но нарисованное на экране, а не в поле. Затаившийся читается
     только на фоне качающихся соседей, поэтому качание есть у всех остальных. */
  function behPose(kind, x, y, size, seed) {
    var t = now, ph = seed * 1.7, P = env.pointer;
    var o = { x: x, y: y + Math.cos(t * 0.9 + ph) * size * 0.05, s: 1, rot: Math.sin(t * 0.7 + ph) * 0.12, lit: 0 };
    switch (kind) {
      case 0:                                   // затаившийся: не качается вовсе
        o.rot = 0; o.y = y;
        break;
      case 1:                                   // отстающий: снесён в сторону, и снос уползает
        o.x += Math.sin(t * 0.22 + ph) * size * 0.3;
        o.y += Math.cos(t * 0.17 + ph) * size * 0.16;
        break;
      case 2:                                   // тяжёлый: поднимается высоко и опадает долго
        var u = (t * 0.33 + seed * 0.21) % 1;
        o.s = 1 + 0.34 * (u < 0.22 ? u / 0.22 : Math.pow(1 - (u - 0.22) / 0.78, 2.4));
        o.rot *= 0.4;
        o.lit = (o.s - 1) * 2;
        break;
      case 3:                                   // сбойный: раз в пару секунд спотыкается
        var c = (t * 0.45 + ph * 0.16) % 1;
        if (c < 0.16) { o.x += Math.sin(c * 90) * size * 0.2; o.rot += Math.sin(c * 70) * 0.2; }
        break;
      default:                                  // уклоняющийся: отпрыгивает от курсора
        if (P) {
          var dx = x - P.x, dy = y - P.y, d = Math.hypot(dx, dy) || 1;
          var push = Math.max(0, 1 - d / (size * 2.4)) * size * 0.45;
          o.x += dx / d * push; o.y += dy / d * push;
        }
        break;
    }
    return o;
  }

  /* Когда проведена связь, приходящая в узел i: по ней узел и проступает. */
  function linkBorn(s, i) {
    if (!s) return -1;
    for (var j = 0; j < s.links.length; j++) if (s.links[j].b === i) return s.links[j].born;
    return -1;
  }

  function distToSeg(px, py, x0, y0, x1, y1) {
    var dx = x1 - x0, dy = y1 - y0, l2 = dx * dx + dy * dy;
    var tt = l2 > 0 ? clamp(((px - x0) * dx + (py - y0) * dy) / l2, 0, 1) : 0;
    return Math.hypot(px - (x0 + dx * tt), py - (y0 + dy * tt));
  }

  /* Содержимое узла: слова текстом, числа точками, команда пульта знаками.
     Всё это встаёт в клетки узла одной строкой. */
  function nodeParts(bl, w) {
    var out = [];
    nodeTokens(bl, w).forEach(function (tok) {
      var nv = numTok(bl, tok);
      if (nv !== null) { out.push({ k: 'num', v: nv, u: 1.4 }); return; }
      if (tok.indexOf('#cmd:') === 0) {
        var cmd = T.commands[tok.slice(5)] || [];
        out.push({ k: 'cmd', v: cmd, u: 1.2 * cmd.length });
        return;
      }
      out.push({ k: 'text', v: tok, u: 0 });
    });
    return out;
  }

  /* Где и каким кеглем стоит слово узла. Нужно и при отрисовке, и чтобы
     линии и плашки связей обходили само слово.

     Слово занимает не больше трёх четвертей своих клеток: при прежних девяти
     десятых соседние слова сходились вплотную и читались одним словом. */
  var NODE_FIT = 0.74, NODE_PAD = 0.28;
  function nodeMetrics(bl, w) {
    var b = wordBox(bl, w), parts = nodeParts(bl, w);
    if (!parts.length) return null;
    var fit = (b.x1 - b.x0) * NODE_FIT;
    var fs = Math.min((b.y1 - b.y0) * 0.42, F.CELL * 0.42), total = 0, i;
    for (i = 0; i < 6; i++) {
      total = 0;
      parts.forEach(function (p) { total += p.k === 'text' ? widthAt(p.v, fs) : p.u * fs; });
      total += fs * 0.35 * (parts.length - 1);
      if (total <= fit || fs < 4) break;
      fs *= Math.max(0.55, fit / total);
    }
    var pad = fs * NODE_PAD;
    return { b: b, parts: parts, fs: fs, total: total,
             x0: b.cx - total / 2 - pad, x1: b.cx + total / 2 + pad,
             y0: b.cy - fs * 0.72 - pad * 0.5, y1: b.cy + fs * 0.72 + pad * 0.5 };
  }

  function drawNode(ctx, m, col, alpha, rise) {
    if (!m) return;
    var b = m.b, parts = m.parts, fs = m.fs, total = m.total;
    var x = b.cx - total / 2, y = b.cy + rise;
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.shadowBlur = 0;
    /* Подложка ровно под словом, а не под всеми его клетками: она прячет
       линии, проходящие насквозь, но оставляет видными фигуры и круги. */
    ctx.fillStyle = 'rgba(8,6,3,0.9)';
    ctx.fillRect(m.x0, m.y0 + rise, m.x1 - m.x0, m.y1 - m.y0);
    ctx.textBaseline = 'middle';
    ctx.textAlign = 'left';
    ctx.font = gfont(fs);
    parts.forEach(function (p) {
      if (p.k === 'text') {
        ctx.fillStyle = col;
        ctx.fillText(p.v, x, y);
        x += widthAt(p.v, fs);
      } else if (p.k === 'num') {
        NUM().draw(ctx, p.v, x + p.u * fs / 2, y, fs * 1.5, col);
        x += p.u * fs;
      } else {
        ctx.save();
        ctx.strokeStyle = 'rgba(255,200,130,0.95)';
        p.v.forEach(function (g, ci) {
          ctx.save();
          ctx.translate(x + fs * 0.6 + ci * fs * 1.2, y);
          G.drawGlyph(ctx, g, fs * 1.05, Math.max(1, fs * 0.07));
          ctx.restore();
        });
        ctx.restore();
        x += p.u * fs;
      }
      x += fs * 0.35;
    });
    ctx.restore();
  }

  /* Где луч из середины прямоугольника выходит за его край (доля пути). */
  function exitT(x, y, dx, dy, m) {
    var t = 1;
    if (dx > 0) t = Math.min(t, (m.x1 - x) / dx); else if (dx < 0) t = Math.min(t, (m.x0 - x) / dx);
    if (dy > 0) t = Math.min(t, (m.y1 - y) / dy); else if (dy < 0) t = Math.min(t, (m.y0 - y) / dy);
    return Math.max(0, t);
  }

  /* Запись как граф прямо на своих клетках. Узлы стоят там, где игрок их
     разметил на третьем этапе; связи — линии между ними, и ⟨текст⟩ связи
     проступает, пока её тянут, и потом всякий раз, когда курсор рядом.
     Держать все связи написанными разом нельзя: подстрочник длинный, и запись
     превращается в кашу. Так она остаётся чистой, и разглядывать её можно
     сколько угодно — а линейным текстом запись лежит в журнале.
     s — идущий четвёртый этап, null — уже прочитанная запись. */
  function drawRecordGraph(ctx, bl, s) {
    var chain = wordsOf(bl);
    if (!chain.length) return;
    var upto = Math.min(s ? s.at : chain.length - 1, chain.length - 1);
    var r = rectOf(bl), P = env.pointer;
    var col = bl.inst ? objColor(bl, '1') : 'rgba(250,247,240,1)';
    var links = [], i, ms = [];
    for (i = 0; i <= upto; i++) ms.push(nodeMetrics(bl, chain[i]));
    for (i = 1; i <= upto; i++) links.push({ a: i - 1, b: i, born: linkBorn(s, i) });

    ctx.save();
    ctx.beginPath(); ctx.rect(r.x0, r.y0, r.x1 - r.x0, r.y1 - r.y0); ctx.clip();

    /* Линия идёт от КРАЯ слова к краю слова, а не от середины к середине:
       раньше она зачёркивала сами слова, и читать их было нельзя. */
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineCap = 'round';
    links.forEach(function (l) {
      var A = ms[l.a], B = ms[l.b];
      if (!A || !B) return;
      var ax = A.b.cx, ay = A.b.cy, dx = B.b.cx - ax, dy = B.b.cy - ay;
      var t0 = exitT(ax, ay, dx, dy, A), t1 = 1 - exitT(B.b.cx, B.b.cy, -dx, -dy, B);
      if (t1 <= t0) return;
      l.t0 = t0; l.t1 = t1;
      var grow = l.born < 0 ? 1 : clamp((now - l.born) / LINE_T, 0, 1);
      var te = t0 + (t1 - t0) * grow;
      glowStroke(ctx, 'rgba(255,150,50,0.85)', 8, Math.max(1.4, F.CELL * 0.04));
      ctx.beginPath();
      ctx.moveTo(ax + dx * t0, ay + dy * t0);
      ctx.lineTo(ax + dx * te, ay + dy * te);
      ctx.stroke();
    });
    ctx.restore();

    // слова — поверх линий: наискосок линия проходит под словом, а не по нему
    for (i = 0; i <= upto; i++) {
      var born = i === 0 ? (s ? s.t0 : -1) : linkBorn(s, i);
      var up = born < 0 ? 1 : clamp((now - born) / 0.7, 0, 1);
      if (up <= 0.01) continue;
      // узел не подменяется текстом рывком: слово всплывает на место знаков
      drawNode(ctx, ms[i], col, up, (1 - up) * F.CELL * 0.3);
    }

    /* Плашки связей. Под курсором — одна связь, и она не отдаётся соседней,
       пока та не станет заметно ближе: в середине записи курсор почти равно
       близок к двум линиям, и «ближайшая» переключалась каждый кадр — плашки
       мигали и прыгали. Без курсора видна только самая свежая связь.
       Плашки проявляются и гаснут плавно, а место, найденное для плашки,
       держится, пока она видна: иначе она перескакивала вслед за соседней. */
    var hs = bl._hov || (bl._hov = { cur: -1, a: {}, pl: {}, t: now });
    var hdt = clamp(now - hs.t, 0, 0.1);
    hs.t = now;
    var dist = {}, freshI = -1, freshA = 0;
    links.forEach(function (l, li) {
      if (l.t0 === undefined || !linkTokens(bl, chain[l.a], chain[l.b]).length) return;
      var A = ms[l.a], B = ms[l.b], ax = A.b.cx, ay = A.b.cy, dx = B.b.cx - ax, dy = B.b.cy - ay;
      var age = l.born < 0 ? 1e9 : now - l.born;
      var fr = age < LINK_SHOW ? clamp((age - LINE_T) / 0.3, 0, 1) * clamp((LINK_SHOW - age) / 0.8, 0, 1) : 0;
      if (fr > 0 && (freshI < 0 || l.born > links[freshI].born)) { freshI = li; freshA = fr; }
      if (P) dist[li] = distToSeg(P.x, P.y, ax + dx * l.t0, ay + dy * l.t0, ax + dx * l.t1, ay + dy * l.t1);
    });
    var ENTER = F.CELL * 0.55, LEAVE = F.CELL * 0.85, SWITCH = F.CELL * 0.3;
    var best = -1, bestD = 1e9;
    Object.keys(dist).forEach(function (k) { if (dist[k] < bestD) { bestD = dist[k]; best = +k; } });
    if (hs.cur >= 0 && (dist[hs.cur] === undefined || dist[hs.cur] > LEAVE)) hs.cur = -1;
    if (hs.cur < 0) { if (best >= 0 && bestD < ENTER) hs.cur = best; }
    else if (best >= 0 && best !== hs.cur && bestD < dist[hs.cur] - SWITCH) hs.cur = best;

    var want = {};
    if (hs.cur >= 0) want[hs.cur] = 1;
    else if (freshI >= 0) want[freshI] = freshA;
    links.forEach(function (l, li) {
      var cur = hs.a[li] || 0, tg = want[li] || 0;
      cur += (tg - cur) * Math.min(1, hdt * (tg > cur ? 10 : 6));
      if (cur < 0.01 && !tg) { delete hs.a[li]; delete hs.pl[li]; }
      else hs.a[li] = cur;
    });

    ctx.save();
    ctx.textBaseline = 'middle';
    ctx.textAlign = 'center';
    ctx.shadowBlur = 0;
    var placed = [];
    function overlapArea(q, m) {
      var w = Math.min(q.x1, m.x1) - Math.max(q.x0, m.x0), h = Math.min(q.y1, m.y1) - Math.max(q.y0, m.y0);
      return w > 0 && h > 0 ? w * h : 0;
    }
    Object.keys(hs.a).forEach(function (key) {
      var li = +key, l = links[li], al = hs.a[li];
      if (!l || l.t0 === undefined) return;
      var A = ms[l.a], B = ms[l.b];
      var ax = A.b.cx, ay = A.b.cy, dx = B.b.cx - ax, dy = B.b.cy - ay;
      var txt = linkTokens(bl, chain[l.a], chain[l.b]).join(' '), fs = Math.max(9, F.CELL * 0.27);
      var wd = widthAt(txt, fs), lim = (r.x1 - r.x0) * 0.9;
      if (wd > lim) { fs *= lim / wd; wd = lim; }
      var hw = wd / 2 + fs * 0.45, hh = fs * 0.8, pick;
      // место держится в долях клетки от угла записи: едет и растёт вместе с картой
      var kept = hs.pl[li];
      if (kept) {
        var kx = r.x0 + kept.x * F.CELL, ky = r.y0 + kept.y * F.CELL;
        pick = { x0: kx - hw, x1: kx + hw, y0: ky - hh, y1: ky + hh };
      } else {
        var tm = (l.t0 + l.t1) / 2, mx = ax + dx * tm, my = ay + dy * tm;
        var rowT = Math.floor((my - r.y0) / F.CELL) * F.CELL + r.y0, rowB = rowT + F.CELL;
        var cands = [[mx, my]], step = Math.max(hw * 0.5, F.CELL * 0.5);
        for (var o = 0; o <= 6; o++) {
          [1, -1].forEach(function (sg) {
            if (!o && sg < 0) return;
            cands.push([mx + sg * o * step, rowT], [mx + sg * o * step, rowB]);
          });
        }
        var bestS = 1e18;
        cands.forEach(function (cd, ci) {
          var cx = clamp(cd[0], r.x0 + hw + 2, r.x1 - hw - 2), cy = clamp(cd[1], r.y0 + hh + 1, r.y1 - hh - 1);
          var q = { x0: cx - hw, x1: cx + hw, y0: cy - hh, y1: cy + hh }, sc = ci * 0.5;
          for (var k = 0; k < ms.length; k++) if (ms[k]) sc += overlapArea(q, ms[k]) * 3;
          for (k = 0; k < placed.length; k++) sc += overlapArea(q, placed[k]) * 2;
          if (sc < bestS) { bestS = sc; pick = q; }
        });
        hs.pl[li] = { x: ((pick.x0 + pick.x1) / 2 - r.x0) / F.CELL, y: ((pick.y0 + pick.y1) / 2 - r.y0) / F.CELL };
      }
      placed.push(pick);
      var px = (pick.x0 + pick.x1) / 2, py = (pick.y0 + pick.y1) / 2;
      ctx.globalAlpha = al;
      ctx.fillStyle = 'rgba(10,7,3,0.96)';
      ctx.fillRect(pick.x0, pick.y0, pick.x1 - pick.x0, pick.y1 - pick.y0);
      ctx.strokeStyle = 'rgba(255,170,90,0.55)';
      ctx.lineWidth = 1;
      ctx.strokeRect(pick.x0 + 0.5, pick.y0 + 0.5, pick.x1 - pick.x0 - 1, pick.y1 - pick.y0 - 1);
      ctx.font = gfont(fs);
      ctx.fillStyle = 'rgba(255,205,150,1)';
      ctx.fillText(txt, px, py);
    });
    ctx.restore();
    ctx.restore();

    if (!s || s.at + 1 >= chain.length) return;
    /* Над следующим узлом мерцает знак пустоты: связь стоит его, и это
       единственное, что тут сказано о цене. */
    var nb = wordBox(bl, chain[s.at + 1]), pu = 0.5 + 0.5 * Math.sin(now * 4);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.translate(nb.cx, nb.y0 - F.CELL * 0.5);
    glowStroke(ctx, 'rgba(236,244,255,' + (0.35 + pu * 0.45).toFixed(3) + ')', 8 + pu * 8, 1.2);
    ctx.beginPath(); ctx.arc(0, 0, F.CELL * 0.34, 0, Math.PI * 2); ctx.stroke();
    G.drawGlyph(ctx, F.VOID_GID, F.CELL * 0.42, 1.2);
    ctx.restore();
  }

  function draw(ctx, t) {
    if (!env || !env.active()) return;
    ctx.save();
    var nb = nextBase();
    blocks.forEach(function (bl) {
      var active = !!(ses && ses.bl === bl);
      if (!active && !onScreen(bl)) return;
      var choosing = !!(ses && ses.choose && ses.choose.indexOf(bl) >= 0);
      if (bl.stage === 0 && (bl.inst || bl === nb)) drawObjSeed(ctx, bl, choosing);
      if (choosing && bl.stage >= 1) {
        // запись, которую можно выбрать: вокруг неё пульсирует рамка
        var cr = rectOf(bl), cp = 0.5 + 0.5 * Math.sin(now * 5);
        ctx.save();
        ctx.globalCompositeOperation = 'lighter';
        glowStroke(ctx, bl.inst ? objColor(bl, (0.3 + 0.5 * cp).toFixed(3)) : 'rgba(255,200,130,' + (0.3 + 0.5 * cp).toFixed(3) + ')', 12, 2);
        ctx.strokeRect(cr.x0 - 6, cr.y0 - 6, cr.x1 - cr.x0 + 12, cr.y1 - cr.y0 + 12);
        ctx.restore();
      }
      if (bl.stage >= 1) drawFrame(ctx, bl, 1);
      else if (active && ses.stage === 0 && ses.forming >= 0) drawFrame(ctx, bl, ses.forming / 1.4);
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      /* Ничего из сделанного не пропадает. Фигуры, уложенные на первом этапе,
         остаются подложкой до самого конца: под дочитанной записью видно ту же
         сетку, которую игрок замостил сам. Пока идёт разметка слов, она уходит
         в тень, чтобы не спорить со словами. */
      var wordsOn = active && ses.stage === 3;
      var tileA = bl.stage >= 4 ? 0.3 : wordsOn ? 0.16 : 0.55;
      /* На разметке слов запись живёт в своей крупности: круги, следы
         восстановления и границы фигур едут и растут вместе с её полем, иначе
         предложения разъехались бы со словами, которые в них лежат. */
      var fv = wordsOn ? fineOrg(ses) : null;
      if (fv) { var tr = rectOf(bl); ctx.beginPath(); ctx.rect(tr.x0, tr.y0, tr.x1 - tr.x0, tr.y1 - tr.y0); ctx.clip(); }
      drawManyEdges(ctx, bl, bl.tiles.map(function (tl) { return tl.c; }), 'rgba(236,244,255,' + tileA + ')', 1.2,
                    fv, fv ? fv.u * FINE : 0);
      // рамки слов: на них встанут узлы графа
      if (bl.stage >= 4) drawManyEdges(ctx, bl, wordsOf(bl).map(function (w) { return cellsAbs(bl, w.c); }), 'rgba(236,244,255,0.5)', 1.2);
      // начатая укладка видна и вне этапа
      if (bl.stage === 1 && bl.draft && !(active && ses.stage === 1)) drawManyEdges(ctx, bl, bl.draft.map(function (d) { return d.c; }), 'rgba(255,190,110,0.6)', 1.6);
      drawTiled(ctx, bl, active);
      ctx.restore();
      var fv2 = active && ses.stage === 3 ? ses : null;
      if (fv2) { ctx.save(); var fr = rectOf(bl); ctx.beginPath(); ctx.rect(fr.x0, fr.y0, fr.x1 - fr.x0, fr.y1 - fr.y0); ctx.clip(); }
      Object.keys(bl.restored).forEach(function (kk) {
        var k = +kk;
        if (bl.dots.indexOf(k) >= 0) return;
        var p = fv2 ? coarseBox(fv2, k) : cellXY(bl, k);
        drawPurgedAt(ctx, fv2 ? p.cx : p.x, fv2 ? p.cy : p.y, fv2 ? p.c : F.CELL, bl.cells[k], true);
      });
      // круги и разделители предложений остаются под записью навсегда
      bl.dots.forEach(function (k) {
        var p = fv2 ? coarseBox(fv2, k) : cellXY(bl, k);
        drawPurgedAt(ctx, fv2 ? p.cx : p.x, fv2 ? p.cy : p.y, (fv2 ? p.c : F.CELL) * 0.7, 0, false);
      });
      if (fv2) ctx.restore();
      // прочитанная запись остаётся графом прямо в своей рамке на карте
      if (bl.stage >= 5 && !(active && ses.stage === 4)) drawRecordGraph(ctx, bl, null);
      if (bl.stage >= 5 && !bl.inJ && bl.pin) drawPin(ctx, bl);
      if (!active) return;
      var s = ses;
      if (s.stage === 1) {
        ctx.save();
        ctx.globalCompositeOperation = 'lighter';
        s.placed.forEach(function (p) {
          var sh = p.shake ? Math.sin(now * 60) * p.shake * 6 : 0;
          ctx.save(); ctx.translate(sh, 0);
          drawTileEdges(ctx, bl, p.cells.map(function (q) { return [p.x + q[0], p.y + q[1]]; }), 'rgba(255,190,110,0.95)', 2.2);
          ctx.restore();
          if (canRotate(p)) {
            // крутящийся знак внутри фигуры и белая точка поворота над ней
            var o0 = org(bl);
            p.item.s.forEach(function (sp) {
              var q = p.cells[sp.i];
              if (!q) return;
              ctx.save();
              ctx.translate(o0.x + (p.x + q[0] + 0.5) * F.CELL, o0.y + (p.y + q[1] + 0.5) * F.CELL);
              ctx.rotate(now * 1.9);
              glowStroke(ctx, 'rgba(255,200,130,0.95)', 8, 1.5);
              G.drawGlyph(ctx, sp.g, F.CELL * 0.5, 1.5);
              ctx.restore();
            });
            var dp = dotPos(p), pu = 0.5 + 0.5 * Math.sin(now * 4);
            ctx.fillStyle = 'rgba(248,250,255,' + (0.5 + pu * 0.5) + ')';
            ctx.shadowColor = 'rgba(248,250,255,0.9)'; ctx.shadowBlur = 8;
            ctx.beginPath(); ctx.arc(dp.x, dp.y, 3.6, 0, Math.PI * 2); ctx.fill();
            ctx.shadowBlur = 0;
          }
        });
        if (s.drag) {
          var cells = tileCells(s.drag.item, s.drag.rot);
          if (cellAt(bl, s.drag.x, s.drag.y) >= 0) {
            var sn = snapFor(cells, s.drag.x, s.drag.y), f = fits(cells, sn.x, sn.y, null);
            var ok = f.ok && costOf(s.placed.concat([{ scale: 1 }])) <= file[0];
            // вылезающая за рамку или не помещающаяся фигура светится красным
            drawTileEdges(ctx, bl, cells.map(function (q) { return [sn.x + q[0], sn.y + q[1]]; }),
              ok ? 'rgba(248,250,255,0.95)' : 'rgba(255,70,40,0.95)', 2.4);
          } else {
            var u = F.CELL, dw = 0, dh = 0;
            cells.forEach(function (q) { dw = Math.max(dw, q[0] + 1); dh = Math.max(dh, q[1] + 1); });
            edgesPath(ctx, cells, s.drag.x - dw * u / 2, s.drag.y - dh * u / 2, u);
            glowStroke(ctx, 'rgba(255,190,110,0.8)', 8, 2);
            ctx.stroke();
          }
        }
        ctx.restore();
        drawMenu(ctx);
      }
      if (s.stage === 2) {
        s.rem.forEach(function (k) {
          var p = cellXY(bl, k);
          if (s.slots[k]) drawPurgedAt(ctx, p.x, p.y, F.CELL, s.slots[k].g, true);
          else {
            /* Вокруг знака медленно рисуется оранжевый круг — ровно за время
               запоминания. Круг замкнулся, и знак начинает медленно исчезать:
               уменьшается и размывается. Сам круг остаётся метой пустого места. */
            var ring = clamp((now - s.showStart) / Math.max(0.01, s.showUntil - s.showStart), 0, 1);
            ctx.save();
            ctx.globalCompositeOperation = 'lighter';
            ctx.lineCap = 'round';
            glowStroke(ctx, 'rgba(255,160,70,' + (removedDone(k) ? 0.45 + 0.15 * Math.sin(now * 3 + k) : 0.9) + ')', 10, 2);
            ctx.beginPath(); ctx.arc(p.x, p.y, F.CELL * 0.44, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * ring); ctx.stroke();
            ctx.restore();
            if (s.removal[k] !== undefined && !removedDone(k)) {
              var u = clamp((now - s.removal[k]) / FADE, 0, 1), e = u * u * (3 - 2 * u), box = F.atlasBox * (1 - 0.65 * e);
              ctx.save();
              ctx.globalCompositeOperation = 'lighter';
              ctx.globalAlpha = 1 - e;
              ctx.filter = 'blur(' + (e * 9).toFixed(1) + 'px)';
              F.atlas.draw(ctx, bl.cells[k], p.x - box / 2, p.y - box / 2, box, box);
              ctx.restore();
            }
          }
        });
        // меню появляется, когда время запоминания вышло
        if (now >= s.showUntil) drawMenu(ctx);
        // знак в руке рисуется ПОСЛЕ меню: иначе он уезжает под его плашку,
        // стоит взять его и не увести курсор с меню
        if (s.drag) drawPurgedAt(ctx, s.drag.x, s.drag.y, 52, s.drag.entry.g, true, 0.9);
      }
      if (s.stage === 3) {
        drawFine(ctx, s);
        drawMenu(ctx);
        // камертон в руке рисуется ПОСЛЕ меню, иначе уезжает под его плашку
        if (s.drag) {
          ctx.save();
          ctx.globalCompositeOperation = 'lighter';
          ctx.translate(s.drag.x, s.drag.y);
          glowStroke(ctx, 'rgba(255,176,90,0.95)', 14, 1.6);
          G.drawGlyph(ctx, s.drag.entry.g, 44, 1.6);
          ctx.restore();
        }
      }
      if (s.stage === 4) drawRecordGraph(ctx, bl, s);
    });
    drawFx(ctx);
    ctx.restore();
  }

  // --- журнал ------------------------------------------------------------------

  /* Журнал рисуется один раз в отдельный холст и перерисовывается, только
     когда что-то в нём меняется. Раньше весь текст всех записей рисовался
     заново каждый кадр, и на нескольких записях игра начинала тормозить. */
  var jCanvas = null, jKey = '';
  function drawJournal(ctx, t) {
    if (journal.k < 0.01) return;
    var v = env.view(), dpr = Math.min(2, root.devicePixelRatio || 1);
    var selBl = journal.sel ? blockById(journal.sel) : null;
    var key = [v.w, v.h, dpr, Math.round(journal.scroll), journal.sel, shipSeq, creatureNo, ejectedNo,
      blocks.filter(function (b) { return b.stage >= 5 && b.inJ; }).map(function (b) { return b.id; }).join(','),
      selBl ? haveGlyph(selBl.pin) : ''].join('|');
    if (!jCanvas) jCanvas = document.createElement('canvas');
    if (key !== jKey) {
      jKey = key;
      jCanvas.width = Math.round(v.w * dpr);
      jCanvas.height = Math.round(v.h * dpr);
      var jc = jCanvas.getContext('2d');
      jc.setTransform(dpr, 0, 0, dpr, 0, 0);
      renderJournal(jc, t, v);
    }
    ctx.save();
    ctx.globalAlpha = journal.k;
    ctx.globalCompositeOperation = 'source-over';
    ctx.shadowBlur = 0;
    ctx.drawImage(jCanvas, 0, 0, v.w, v.h);
    ctx.restore();
  }

  function renderJournal(ctx, t, v) {
    ctx.save();
    ctx.globalAlpha = 1;
    ctx.fillStyle = 'rgba(7,6,3,0.92)';
    ctx.fillRect(0, 0, v.w, v.h);
    ctx.beginPath(); ctx.rect(0, 84, v.w, v.h - 84); ctx.clip();
    var colW = Math.min(780, v.w - 80), x0 = (v.w - colW) / 2, y = 130 - journal.scroll;
    ctx.font = FONT;
    ctx.textBaseline = 'middle';
    var any = false;
    journal.hits = [];
    blocks.forEach(function (bl) {
      if (bl.stage < 5 || !bl.inJ) return;
      any = true;
      var top = y - 20, sel = journal.sel === bl.id;
      ctx.globalAlpha = journal.sel && !sel ? 0.3 : 1;
      bl.def.sentences.forEach(function (d) {
        var x = x0 + 20;
        d.text.forEach(function (tok) {
          var isNum = numTok(bl, tok) !== null;
          var jcmd = tok.indexOf('#cmd:') === 0 ? (T.commands[tok.slice(5)] || []) : null;
          var ww = jcmd ? 22 * jcmd.length : isNum ? 28 : ctx.measureText(tok).width;
          if (x + ww > x0 + colW - 60) { x = x0 + 20; y += 28; }
          if (jcmd) {
            ctx.save(); ctx.strokeStyle = 'rgba(255,200,130,0.95)';
            jcmd.forEach(function (g, ci) { ctx.save(); ctx.translate(x + 11 + ci * 22, y); G.drawGlyph(ctx, g, 18, 1.2); ctx.restore(); });
            ctx.restore();
          }
          else if (isNum) NUM().draw(ctx, numTok(bl, tok), x + 14, y, 26, 'rgba(255,220,180,0.95)');
          else {
            ctx.fillStyle = tok.charAt(0) === '⟨' ? 'rgba(255,170,90,0.65)' : 'rgba(244,240,228,0.95)';
            ctx.fillText(tok, x, y);
          }
          x += ww + 12;
        });
        y += 36;
      });
      ctx.strokeStyle = sel ? 'rgba(255,236,200,0.95)' : (bl.inst ? objColor(bl, 0.5) : 'rgba(236,244,255,0.45)');
      ctx.lineWidth = sel ? 2.2 : 1.4;
      ctx.strokeRect(x0 + 0.5, top + 0.5, colW - 1, y - top - 10);
      var hit = { bl: bl, x0: x0, y0: top, x1: x0 + colW, y1: y - 10, px: x0 + colW - 22, py: top + 20 };
      journal.hits.push(hit);
      if (sel) {
        // тем же знаком запись отвязывается от журнала
        var ok = haveGlyph(bl.pin), pu = 0.5 + 0.5 * Math.sin(t * 3);
        ctx.save();
        ctx.translate(hit.px, hit.py);
        ctx.globalCompositeOperation = 'lighter';
        glowStroke(ctx, ok ? 'rgba(255,236,200,' + (0.5 + 0.4 * pu).toFixed(3) + ')' : 'rgba(150,130,110,0.45)', ok ? 10 : 0, 1.3);
        ctx.strokeRect(-13, -13, 26, 26);
        G.drawGlyph(ctx, bl.pin, 18, 1.2);
        ctx.restore();
      }
      y += 26;
    });
    ctx.globalAlpha = 1;
    // события корабля записаны словами, которых ещё никто не прочёл
    for (var i = ship.length - 1; i >= 0 && i >= ship.length - 12; i--) {
      var x = x0 + 20;
      ship[i].words.forEach(function (w) {
        ctx.save(); ctx.translate(x + 9, y);
        ctx.strokeStyle = 'rgba(255,158,58,0.4)';
        G.drawGlyph(ctx, wordGid[w] || 1, 16, 1.1);
        ctx.restore();
        x += 26;
      });
      y += 30;
      any = true;
    }
    if (!any) {
      ctx.save(); ctx.translate(v.w / 2, v.h / 2);
      ctx.strokeStyle = 'rgba(255,158,58,' + (0.2 + 0.1 * Math.sin(t * 1.4)) + ')';
      G.drawGlyph(ctx, 90, 34, 1.4);
      ctx.restore();
    }
    journal.max = Math.max(0, y + journal.scroll - (v.h - 60));
    ctx.restore();
  }

  // --- мир ---------------------------------------------------------------------

  function enter() {
    var v = env.view();
    if (!world) world = F.freshWorld({ w: LORE_W, h: LORE_W, seed: LORE_SEED, pairP: 0, zoom: 1 });
    F.loadWorld(world);
    if (!built) {
      buildBlocks();
      built = true;
      syncObjBlocks();
      var b0 = nextBase() || blocks[0];
      if (b0) F.setCam(b0.ox + b0.w / 2 - v.w / 2 / F.CELL, b0.oy + b0.h / 2 - (v.h - 110) / 2 / F.CELL);
    }
    syncObjBlocks();
    if (!ses) {
      // выбор, оставшийся без фигур (прежние сохранения), отменяется
      blocks.forEach(function (b) {
        if (b.stage !== 1 || (b.draft && b.draft.length)) return;
        b.stage = 0; b.tiles = [];
        errs = Math.min(ERR_CAP, errs + file[0]); file[0] = 0;
      });
      // точки в первой папке без выбранной записи возвращаются в шкалу
      if (file[0] > 0 && !current()) { errs = Math.min(ERR_CAP, errs + file[0]); file[0] = 0; }
      // начатая запись сразу открывает свой этап
      var w = current();
      if (w) folderClick(slotOf(w.stage));
    }
    S.room('lore');
  }

  function leave() {
    abandon();
    F.setMarks(null);
    journal.open = false;
    world = F.saveWorld();
    S.room('nav');
  }

  assignGlyphs();

  root.Lore = {
    LCAP: LCAP,
    init: function (e) { env = e; },
    enter: enter, leave: leave, step: step, draw: draw, drawJournal: drawJournal,
    press: press, release: release, move: move, wheel: wheel, folderClick: folderClick,
    busy: function () { return !!ses && !ses.choose; },
    /* Ошибка навигационного анализа — стак ошибок в первую лорную папку. */
    /* Новая серая точка. До шести точек шкала держит спокойно; каждая
       следующая может её сорвать — тогда пропадает половина точек (с
       округлением вниз). На десятой срыв почти неизбежен, на двенадцатой —
       неизбежен. Возврат точек из отменённого выбора сюда не идёт.
       Возвращает, сколько точек потеряно. */
    credit: function (n) {
      n = n || 1;
      var lost = 0;
      for (var i = 0; i < n; i++) {
        errs = Math.min(ERR_CAP, errs + 1);
        stats.errors++;
        var p = CRASH_P[errs] || 0;
        if (p && Math.random() < p) {
          var gone = Math.floor(errs / 2);
          if (env && env.active()) {
            for (var j = 0; j < gone; j++) {
              var sp = env.scalePos(errs - 1 - j, errs);
              fly(sp.x, sp.y, sp.x + rnd(-90, 90), sp.y + rnd(40, 120), { d: j * 0.03, dur: 0.6, col: 'amber', r: 2.4 });
            }
          }
          errs -= gone;
          lost += gone;
          crashAt = now;
        }
      }
      flare[0] = 1;
      dirty = true;
      return lost;
    },
    errs: function () { return errs; },
    stat: function (k, v) { stats[k] = (stats[k] || 0) + v; },
    /* Новое существо за пультом. Утилизация по износу — не выброс: её корабль
       выбросом не считает, и записи о сбоях от неё не открываются. */
    newCreature: function (reason) {
      ejectedNo = creatureNo; creatureNo++; lives++; ejectSector = sector;
      // серые точки принадлежат существу: новое начинает с пустой шкалой
      errs = 0;
      if (reason !== 'age') ejects++;
      dropObjects();
      dirty = true;
    },
    creature: function () { return creatureNo; },
    ejected: function () { return ejectedNo; },
    lives: function () { return lives; },
    firstEject: function () { return ejectedNo === 0; },
    nextSector: function () { sector += 1 + Math.floor(Math.random() * 3); dirty = true; },
    sector: function () { return sector; },
    addObject: addObject,
    objAvailable: function (type) { return objTextFree(type).length > 0; },
    objLogs: function () { return objInst.slice(); },
    // для проверок: где кнопка журнала у записи и что с ней
    pinAt: function (id) { var b = blockById(id); return b ? { pos: pinPos(b), pin: b.pin, inJ: b.inJ, stage: b.stage } : null; },
    journalHits: function () { return journal.hits.map(function (h) { return { id: h.bl.id, x: (h.x0 + h.x1) / 2, y: (h.y0 + h.y1) / 2, px: h.px, py: h.py }; }); },
    flag: function (k, v) { if (v !== undefined) { objFlags[k] = v; dirty = true; } return !!objFlags[k]; },
    ejects: function () { return ejects; },
    ship: function (kind) {
      var w = T.ship[kind];
      if (!w) return;
      ship.push({ kind: kind, words: w });
      shipSeq++;
      if (ship.length > 40) ship.shift();
      dirty = true;
    },
    toggleJournal: function () {
      journal.open = !journal.open;
      journal.fresh = 0;
      journal.sel = null;
      if (journal.open) journal.scroll = 0;
      S.tab(journal.open ? 1 : 0);
    },
    folderView: function () {
      // остаток первой папки дробный: верхняя ячейка тает по трети за фигуру
      var R = Math.max(0, file[0] - (ses && ses.stage === 1 ? ses.usedAnim : 0));
      var charge = Math.max(0, Math.ceil(R - 1e-3)), top = R - Math.floor(R), dark0 = [];
      if (top < 1e-3) top = 1;
      for (var i = 0; i < charge; i++) dark0.push(true);
      return {
        counts: [charge, file[1], file[2], file[3]], top0: top,
        active: ses ? (ses.choose ? ses.slot : slotOf(ses.stage)) : -1, cap: LCAP, icons: SLOT_ICON, flare: flare,
        dark: [dark0, [], [], []],
        scale: { n: errs, cap: ERR_CAP, glow: now - lackAt, crash: now - crashAt }
      };
    },
    /* Всё вне записи гаснет, пока идёт этап. На последнем этапе гаснет всё. */
    sortRect: function () {
      if (!ses || !ses.bl) return null;
      var r = rectOf(ses.bl), p = 10;
      return { x0: r.x0 - p, y0: r.y0 - p, x1: r.x1 + p, y1: r.y1 + p };
    },
    get journalOpen() { return journal.open; },
    // журнал раскрыт полностью и закрывает поле целиком
    journalCover: function () { return journal.k > 0.98; },
    get fresh() { return journal.fresh; },
    get dirty() { return dirty; },
    clean: function () { dirty = false; },
    serialize: function () {
      var logs = {};
      if (built) blocks.forEach(function (b) {
        logs[b.id] = { stage: b.stage, cells: b.cells, tiles: b.tiles, targets: b.targets, restored: b.restored, dots: b.dots, num: b.num, ejn: b.ejn, words: b.words, sec: b.sec, draft: b.draft, pin: b.pin, inJ: b.inJ };
      });
      else if (saved) logs = saved;
      /* Перезагрузка посреди этапа — то же, что выход из него: ячейки, взятые
         этапом, возвращаются. Раньше они сгорали, и запись застревала. */
      var eOut = errs, fOut = file.slice(), s = ses;
      if (s && !s.choose) {
        if (s.stage === 0 || (s.stage === 1 && !s.placed.length)) { eOut = Math.min(ERR_CAP, eOut + fOut[0]); fOut[0] = 0; }
        if (s.stage === 2) fOut[1] = Math.min(LCAP, fOut[1] + s.spent);
        if (s.stage === 3) fOut[2] = Math.min(LCAP, fOut[2] + s.spent);
        if (s.stage === 4 && s.done < 0) fOut[3] = Math.min(LCAP, fOut[3] + s.spent);
      }
      return { v: 2, errs: eOut, file: fOut, creature: creatureNo, ejects: ejects, ejected: ejectedNo, lives: lives, sector: sector, ejectSector: ejectSector,
        stats: stats, layout: layout, objs: objInst, objRead: objRead, objLost: objLost, objFlags: objFlags, objUid: objUid, ship: ship.slice(-40).map(function (s) { return s.kind; }), logs: logs };
    },
    load: function (d) {
      if (!d) return;
      if (d.v === 2) {
        errs = clamp(d.errs | 0, 0, ERR_CAP);
        if (Array.isArray(d.file) && d.file.length === 4) file = d.file.map(function (x) { return clamp(x | 0, 0, LCAP); });
        creatureNo = Math.max(1, d.creature | 0);
        ejects = d.ejects | 0; ejectedNo = d.ejected | 0;
        lives = d.lives || 1; sector = d.sector || 14; ejectSector = d.ejectSector || sector;
        objInst = Array.isArray(d.objs) ? d.objs.filter(function (i) { return i && T.objects[i.type]; }) : [];
        if (d.stats) for (var sk in d.stats) stats[sk] = d.stats[sk];
        layout = d.layout || {};
        objRead = d.objRead || {}; objLost = d.objLost || {}; objFlags = d.objFlags || {};
        objUid = d.objUid || (objInst.reduce(function (m, i) { return Math.max(m, i.uid); }, 0) + 1);
        saved = d.logs || null;
      } else if (Array.isArray(d.f)) {
        errs = clamp(d.f.reduce(function (a, b) { return a + (b | 0); }, 0), 0, LCAP);
      }
      ship = (d.ship || []).filter(function (k) { return T.ship[k]; }).map(function (k) { return { kind: k, words: T.ship[k] }; });
      dirty = false;
    },
    /* Для проверок: разложить слова записи и протащить её по этапам без игры.
       Пользуется этим только консоль на ?dev. */
    dev: {
      plan: function (li) {
        var bl = blockById(T.logs[li || 0].id);
        if (!bl) return null;
        return wordPlan(bl).map(function (w) {
          return { s: w.s, tis: w.tis.slice(), cells: w.c.slice(), kind: w.kind, text: nodeTokens(bl, w).join(' ') };
        });
      },
      links: function (li) {
        var bl = blockById(T.logs[li || 0].id);
        if (!bl) return null;
        var ws = wordsOf(bl), out = [];
        for (var i = 1; i < ws.length; i++) out.push(linkTokens(bl, ws[i - 1], ws[i]).join(' '));
        return out;
      },
      force: function (li, stage) {
        var i = li || 0, bl = materializeBase(i), k;
        bl.stage = Math.max(1, stage | 0);
        bl.num = creatureNo; bl.ejn = ejectedNo; bl.sec = ejectSector;
        bl._plan = null; bl._planKey = null;
        // рамка замощена фигурами по две клетки: под графом видна настоящая сетка
        bl.tiles = [];
        for (k = 0; k + 1 < bl.n; k += 2) {
          var x = k % bl.w, y = (k / bl.w) | 0;
          if (x + 1 >= bl.w) { k--; continue; }
          bl.tiles.push({ c: [[x, y], [x + 1, y]] });
        }
        if (bl.stage >= 3) {
          bl.targets = dividePositions(bl.n, Math.min(3, maxR(bl.n)));
          bl.dots = bl.targets.slice();
          bl.restored = {};
          bl.targets.forEach(function (q) { bl.restored[q] = true; });
        }
        bl.words = bl.stage >= 4 ? wordPlan(bl).map(function (w) {
          return { s: w.s, tis: w.tis, c: w.c, kind: w.kind };
        }) : null;
        file = [LCAP, LCAP, LCAP, LCAP];
        dirty = true;
        return { id: bl.id, stage: bl.stage, words: (bl.words || wordPlan(bl)).length };
      }
    },
    debug: function () {
      return {
        errs: errs, file: file.slice(), creature: creatureNo,
        blocks: blocks.map(function (b) { return { id: b.id, stage: b.stage, targets: b.targets, dots: b.dots, restored: Object.keys(b.restored).length, tiles: b.tiles.length }; }),
        ses: ses ? { stage: ses.stage, used: ses.placed ? costOf(ses.placed) : 0, placed: ses.placed && ses.placed.length, done: ses.done, at: ses.at, links: ses.links && ses.links.length } : null
      };
    },
    /* для проверок: где что лежит на экране */
    geom: function () {
      if (!ses) return null;
      if (ses.choose) return { stage: 'choose', slot: ses.slot, choose: ses.choose, cellOf: function (b, k) { return cellXY(b, k); } };
      var s = ses, bl = s.bl;
      return {
        stage: s.stage, w: bl.w, h: bl.h, n: bl.n, ses: s, bl: bl,
        cell: function (k) { return cellXY(bl, k); },
        corners: corners(bl).map(function (k) { return cellXY(bl, k); }),
        menu: s.stage >= 1 && s.stage <= 3 ? menuLayout().items : null,
        btn: btn.live ? { x: btn.x, y: btn.y } : null,
        words: s.stage === 3 ? s.words : null,
        chain: s.stage === 4 ? s.chain : null, wordBox: function (w) { return wordBox(bl, w); },
        fine: s.stage === 3 ? function (k) { return finePos(s, k); } : null,
        fineAt: s.stage === 3 ? function (x, y) { return fineAt(s, x, y); } : null,
        fineView: s.stage === 3 ? function () { return { fz: s.fz, fx: s.fx, fy: s.fy, u: fineU(s) }; } : null,
        ring: s.stage === 3 ? s.ring : null, removedDone: s.stage === 2 ? removedDone : null
      };
    }
  };
})(window);
