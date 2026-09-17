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

  /* --- 3. Слоги ---------------------------------------------------------------- */

  /* Внутри предложения мы мыслим словами. Знаки одного слова дышат в общем
     ритме, но еле заметно, и соседние слова дышат вразнобой. Якорь из
     хранилища — камертон: брошенный на знак, он заставляет зазвучать всё
     слово целиком, и слово закрепляется. Камертонов на этап меньше, чем
     слов; остальные слова игрок находит сам, проводя курсором по знакам,
     которые, по его мнению, дышат вместе. Повадка якоря слышна в том, как
     звучит слово. */

  var HEAR_T = 2.8;                        // сколько звучит слово после камертона
  var WAVE_STEP = 0.14;                    // шаг волны по слову, с
  var WORD_FR = [1.1, 1.9, 1.45, 2.4, 1.7];

  /* Слова не переходят со строки на строку: по ним удобно провести курсором.
     Длина слова — от одного до трёх знаков, чаще два. */
  function splitWords(bl, sents) {
    var out = [];
    sents.forEach(function (cells, si) {
      var runs = [], cur = [];
      cells.forEach(function (k) {
        var prev = cur[cur.length - 1];
        if (cur.length && (k !== prev + 1 || ((k / bl.w) | 0) !== ((prev / bl.w) | 0))) { runs.push(cur); cur = []; }
        cur.push(k);
      });
      if (cur.length) runs.push(cur);
      runs.forEach(function (run) {
        var n = Math.max(1, Math.round(run.length / 2.2)), sizes = [], i;
        for (i = 0; i < n; i++) sizes.push(1);
        for (var left = run.length - n; left > 0; left--) {
          var open = [];
          sizes.forEach(function (z, j) { if (z < 3) open.push(j); });
          sizes[open.length ? open[Math.floor(Math.random() * open.length)] : Math.floor(Math.random() * n)]++;
        }
        var at = 0;
        sizes.forEach(function (z) { out.push({ s: si, c: run.slice(at, at + z) }); at += z; });
      });
    });
    return out;
  }

  function startWords(bl) {
    if (file[2] < 1) { reject(); flare[2] = 1; return; }
    focus(bl, 1.9);
    var spent = file[2];
    file[2] = 0;
    var words = splitWords(bl, sentences(bl)).map(function (w, i) {
      return { s: w.s, c: w.c, done: false, doneAt: 0, heard: -1, from: 0, kind: 0, rung: 0,
        fr: WORD_FR[i % WORD_FR.length] * rnd(0.92, 1.08), ph: rnd(0, 6.28) };
    });
    // камертонов меньше, чем слов: часть слов игрок находит сам
    var cap = Math.max(1, words.length - 2);
    var menu = invList('glyph').slice(0, cap).map(function (it) {
      return { g: it.g, item: it, kind: it.kind !== undefined ? it.kind : G.hash3(it.g, 5, 77) % 5, used: false, shake: 0 };
    });
    ses = { stage: 3, bl: bl, words: words, menu: menu, spent: spent, spentItems: [], sel: null, bad: null, drag: null, scroll: 0 };
    btnReset();
  }

  function wordOf(k) {
    var ws = ses.words;
    for (var i = 0; i < ws.length; i++) if (ws[i].c.indexOf(k) >= 0) return ws[i];
    return null;
  }

  function open3(w) { return w && !w.done && w.heard < 0; }

  function cellsAbs(bl, list) { return list.map(function (k) { return [k % bl.w, (k / bl.w) | 0]; }); }

  /* Камертон лёг на знак: от него по слову бежит волна, и слово звучит. */
  function tune(entry, k) {
    var s = ses, w = wordOf(k);
    if (!open3(w)) { reject(0.3); entry.shake = 0.45; return; }
    entry.used = true;
    // сам якорь уходит из хранилища, когда этап закончен: выход или перезагрузка его не сжигают
    if (entry.item) s.spentItems.push(entry.item);
    w.heard = now; w.from = w.c.indexOf(k); w.kind = entry.kind; w.rung = 0;
    var p = cellXY(s.bl, k);
    env.pulse(p.x, p.y, true);
    S.bloom();
  }

  /* Слово, найденное на глаз: выделение должно совпасть с ним в точности. */
  function judgeSelection() {
    var s = ses, sel = s.sel.cells.slice().sort(function (a, b) { return a - b; });
    s.sel = null;
    var w = wordOf(sel[0]);
    var ok = open3(w) && w.c.length === sel.length && w.c.every(function (k, i) { return k === sel[i]; });
    if (ok) {
      w.done = true; w.doneAt = now;
      var p = cellXY(s.bl, w.c[0]);
      env.pulse(p.x, p.y, true);
      S.knock(); S.tick(2, 3);
      return;
    }
    s.bad = { cells: sel, t: now };
    reject(0.4);
  }

  function pressWords(x, y, mh) {
    var s = ses;
    if (mh && mh.e) { s.drag = { entry: mh.e, x: x, y: y }; S.grip(true); return; }
    if (mh) return;
    var k = cellAt(s.bl, x, y);
    if (k < 0 || !open3(wordOf(k))) { S.nothing(); return; }
    s.sel = { cells: [k] };
    S.key(0);
  }

  function moveWords(x, y) {
    var s = ses;
    if (!s.sel) return;
    var k = cellAt(s.bl, x, y);
    if (k < 0 || s.sel.cells.indexOf(k) >= 0 || !open3(wordOf(k))) return;
    s.sel.cells.push(k);
    S.key(s.sel.cells.length % 4);
  }

  function releaseWords(x, y, d) {
    var s = ses;
    if (s.sel) { judgeSelection(); return; }
    if (!d) return;
    var k = cellAt(s.bl, x, y);
    if (k >= 0) tune(d.entry, k);          // мимо записи — камертон просто вернулся
  }

  function completeWords() {
    var s = ses, bl = s.bl, to = env.folderPos(3), n = s.words.length;
    bl.words = s.words.map(function (w) { return w.c; });
    s.spentItems.forEach(function (it) { INV().remove(it); });
    s.words.forEach(function (w, i) {
      var p = cellXY(bl, w.c[0]);
      fly(p.x, p.y, to.x, to.y - 8, { d: i * 0.1, done: function () { flare[3] = 1; S.tick(i, n); } });
    });
    file[3] = Math.min(LCAP, file[3] + n);
    bl.stage = 4;
    dirty = true;
    S.sorted(2, 3);
    endSession();
  }

  /* Как звучит знак слова под камертоном: повадка якоря. */
  function heardMark(m, w, pos, age, p, P) {
    m.lit = 1;
    switch (w.kind) {
      case 0: m.grow = 0.5; break;                                          // затаившийся: замирает
      case 1: m.grow = 0.45; m.px += 5 * Math.sin(age * 4 - pos * 0.9); break; // отстающий: волна с запозданием
      case 2: m.grow = 0.55 + 0.35 * Math.sin(age * 2.2); break;             // тяжёлый: медленно и высоко
      case 3: m.grow = Math.sin(age * 13) > 0.2 ? 0.7 : 0.15; break;         // сбойный: рывками
      default: {                                                            // уклоняющийся: от курсора
        var dx = p.x - P.x, dy = p.y - P.y, d = Math.hypot(dx, dy) || 1, push = Math.max(0, 1 - d / 160) * 9;
        m.grow = 0.45; m.px += dx / d * push; m.py += dy / d * push;
      }
    }
  }

  /* --- 4. Линии ---------------------------------------------------------------- */
  /* Всё происходит в той же рамке на карте. Текст записи проступает прямо в
     ней, дрожит и не читается; часть слов закрыта знаками. Знаки надо
     соединить одной замкнутой линией без пересечений. Прочитанный текст
     остаётся в рамке навсегда. */

  var w100 = {};
  function widthAt(tok, fs) {
    if (w100[tok] === undefined) {
      if (!measure) measure = document.createElement('canvas').getContext('2d');
      measure.font = '100px Consolas, "Courier New", monospace';
      w100[tok] = measure.measureText(tok).width;
    }
    return w100[tok] * fs / 100;
  }

  /* Раскладка текста внутри рамки. Шрифт привязан к размеру клетки, поэтому
     текст приближается и отдаляется вместе с картой. */
  var textMemo = {};
  function blockText(bl) {
    var r = rectOf(bl);
    var key = F.CELL.toFixed(4) + '|' + bl.dots.length + '|' + bl.num + '|' + bl.ejn + '|' + bl.sec + '|' + creatureNo + '|' + ejectedNo + '|' + ejectSector;
    var m = textMemo[bl.id];
    if (!m || m.key !== key) m = textMemo[bl.id] = { key: key, lay: layoutText(bl, r) };
    var dx = r.x0 - m.lay.rect.x0, dy = r.y0 - m.lay.rect.y0;
    return {
      fs: m.lay.fs, lh: m.lay.lh, rect: r,
      words: m.lay.words.map(function (w) {
        return { s: w.s, text: w.text, cmd: w.cmd, num: w.num, key: w.key, rx: w.rx, ry: w.ry, w: w.w,
                 x: w.x + dx, y: w.y + dy, cx: w.cx + dx };
      })
    };
  }
  function layoutText(bl, r) {
    var defs = sentenceDefs(bl, sentences(bl).length);
    var c = F.CELL, pad = c * 0.2;
    var maxW = r.x1 - r.x0 - pad * 2, maxH = r.y1 - r.y0 - pad * 2;
    var fs = c * 0.3, words = [], lh = 0, h = 0;
    for (var it = 0; it < 8; it++) {
      words = []; lh = fs * 1.5;
      var x = 0, y = 0;
      for (var si = 0; si < defs.length; si++) {
        var d = defs[si];
        x = 0;
        for (var ti = 0; ti < d.text.length; ti++) {
          var tok = d.text[ti];
          var nv = numTok(bl, tok), isNum = nv !== null;
          var cmd = tok.indexOf('#cmd:') === 0 ? (T.commands[tok.slice(5)] || []) : null;
          var ww = cmd ? fs * 1.25 * cmd.length : isNum ? fs * 1.3 : widthAt(tok, fs);
          if (x + ww > maxW && x > 0) { x = 0; y += lh; }
          words.push({ s: si, text: (isNum || cmd) ? '' : tok, cmd: cmd,
            num: nv,
            key: !!(d.key && tok === d.key.join('')), rx: x, ry: y, w: ww });
          x += ww + fs * 0.55;
        }
        y += lh * 1.2;
      }
      h = y - lh * 0.7;
      if (h <= maxH) break;
      fs *= 0.9;
    }
    var oy = r.y0 + pad + Math.max(0, (maxH - h) / 2) + lh * 0.5;
    words.forEach(function (w) { w.x = r.x0 + pad + w.rx; w.y = oy + w.ry; w.cx = w.x + w.w / 2; });
    return { words: words, fs: fs, lh: lh, rect: r };
  }

  function segCross(a, b, c, d) {
    function orient(p, q, r) { return (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x); }
    var d1 = orient(c, d, a), d2 = orient(c, d, b), d3 = orient(a, b, c), d4 = orient(a, b, d);
    return ((d1 > 0) !== (d2 > 0)) && ((d3 > 0) !== (d4 > 0));
  }

  function startLines(bl) {
    if (file[3] < 1) { reject(); flare[3] = 1; return; }
    focus(bl, 1.9);
    var spent = file[3];
    file[3] = 0;
    var sents = sentences(bl), defs = sentenceDefs(bl, sents.length);
    var lay = blockText(bl);
    var cand = [];
    lay.words.forEach(function (w, i) { if (!w.key && w.num === null && !w.cmd) cand.push(i); });
    var plain = -1;
    defs.forEach(function (d, i) { if (!d.key && plain < 0) plain = i; });
    var left = plain >= 0 ? sents[plain] : [];
    var N = Math.max(3, Math.min(Math.max(4, left.length), 7, cand.length));
    var nodes = [], used = {};
    for (var i = 0; i < N; i++) {
      var wi = cand[Math.min(cand.length - 1, Math.floor(i * cand.length / N + cand.length / (2 * N)))];
      if (wi === undefined || used[wi]) continue;
      used[wi] = 1;
      nodes.push({ wi: wi, g: left.length ? bl.cells[left[nodes.length % left.length]] : randomGlyph() });
    }
    N = nodes.length;
    /* Порядок обхода без пересечений существует всегда: точки, отсортированные
       по углу вокруг общего центра, дают простой многоугольник. Один из двух
       предложенных знаков на каждом шаге ведёт по нему. */
    var mx = 0, my = 0;
    nodes.forEach(function (n) { var w = lay.words[n.wi]; mx += w.cx; my += w.y; });
    mx /= N; my /= N;
    var poly = nodes.map(function (n, idx) { return idx; }).sort(function (a, b) {
      var A = lay.words[nodes[a].wi], B = lay.words[nodes[b].wi];
      return Math.atan2(A.y - my, A.cx - mx) - Math.atan2(B.y - my, B.cx - mx);
    });
    ses = {
      stage: 4, bl: bl, nodes: nodes, poly: poly, spent: spent,
      start: -1, cur: -1, dir: 0, pending: -1, visited: [], lines: [], offer: [], offerT: now,
      crumble: -1, crSnd: false, done: -1, t0: now
    };
    btnReset();
  }

  function nodePos(i) {
    var lay = blockText(ses.bl), w = lay.words[ses.nodes[i].wi];
    return { x: w.cx, y: w.y, fs: lay.fs, w: w.w };
  }
  function voidPos(i) {
    var p = nodePos(i);
    return { x: p.x, y: p.y - p.fs * 2.1 };
  }

  function spendVoid() {
    if (!INV().spendVoid(BY_ORDER)) { reject(0.5); env.shake(0.3); return false; }
    return true;
  }

  function offerNext() {
    var s = ses, N = s.nodes.length;
    s.offerT = now;
    if (s.visited.length === N) { s.offer = [s.start]; return; }
    var pos = s.poly.indexOf(s.cur), correct = -1;
    for (var st = 1; st < N && correct < 0; st++) {
      var c = s.poly[((pos + s.dir * st) % N + N) % N];
      if (s.visited.indexOf(c) < 0) correct = c;
    }
    var others = [];
    for (var i = 0; i < N; i++) if (i !== correct && s.visited.indexOf(i) < 0) others.push(i);
    s.offer = shuffle([correct].concat(others.length ? [others[Math.floor(Math.random() * others.length)]] : []));
  }

  var LINE_T = 0.4;                      // линия тянется от знака к знаку, а не появляется разом

  function connect(b) {
    var s = ses, a = s.cur, A = nodePos(a), B = nodePos(b), crossed = false;
    for (var i = 0; i < s.lines.length; i++) {
      var l = s.lines[i];
      if (l.a === a || l.b === a || l.a === b || l.b === b) continue;
      if (segCross(A, B, nodePos(l.a), nodePos(l.b))) crossed = true;
    }
    s.lines.push({ a: a, b: b, born: now });
    S.lineZap();
    s.offer = [];
    if (crossed) { s.crumble = now + LINE_T; return; }   // осыпается, когда дотянется
    if (b === s.start) { s.done = now + LINE_T; finishLines(); return; }
    if (!s.dir) {
      var N = s.nodes.length, pa = s.poly.indexOf(a), pb = s.poly.indexOf(b);
      s.dir = ((pa + 1) % N === pb) ? 1 : -1;
    }
    s.visited.push(b);
    s.cur = b;
    offerNext();
  }

  function finishLines() {
    var s = ses, bl = s.bl;
    s.offer = [];
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

  /* Нажимать можно и по самому знаку, и по пустоте над ним. */
  function pressLines(x, y) {
    var s = ses;
    if (s.done >= 0) { if (now - s.done > 1.2) endSession(); return; }
    if (s.crumble >= 0) return;
    var lay = blockText(s.bl), hit = -1;
    s.nodes.forEach(function (n, i) {
      var w = lay.words[n.wi];
      if (Math.abs(w.cx - x) < Math.max(w.w / 2, lay.fs) + 6 && Math.abs(w.y - y) < lay.fs + 6) hit = i;
      var visibleVoid = (s.start < 0 && i === s.pending) || s.offer.indexOf(i) >= 0;
      if (visibleVoid && Math.hypot(w.cx - x, w.y - lay.fs * 2.1 - y) < lay.fs + 6) hit = i;
    });
    if (hit < 0) { S.nothing(); return; }
    if (s.start < 0) {
      if (hit !== s.pending) { s.pending = hit; s.offerT = now; S.key(0); return; }
      if (!spendVoid()) return;
      s.start = s.cur = hit; s.visited = [hit];
      var N = s.nodes.length, p = s.poly.indexOf(hit);
      s.offer = [s.poly[(p + 1) % N], s.poly[(p - 1 + N) % N]];
      s.offerT = now;
      S.keyPress(0);
      return;
    }
    if (s.offer.indexOf(hit) >= 0) {
      if (!spendVoid()) return;
      connect(hit);
      return;
    }
    S.nothing();
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
      else if (s.stage === 3) completeWords();
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
    if (!ses || (!ses.drag && !ses.sel)) return;
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
      s.words.forEach(function (w) {
        if (w.heard < 0 || w.done) return;
        var age = now - w.heard, reach = Math.min(w.c.length, 1 + Math.floor(age / WAVE_STEP));
        if (reach > w.rung) { w.rung = reach; S.tick(reach, w.c.length + 2); }
        if (age >= HEAR_T) { w.done = true; w.doneAt = now; S.knock(); }
      });
      if (s.bad && now - s.bad.t > 0.7) s.bad = null;
      show = s.words.every(function (w) { return w.done; });
      rect = rectOf(bl);
    }
    if (s.stage === 4) {
      if (s.crumble >= 0 && now >= s.crumble && !s.crSnd) { s.crSnd = true; S.unravel(); env.shake(0.4); }
      if (s.crumble >= 0 && now - s.crumble > 1.3) {
        s.crumble = -1; s.crSnd = false; s.lines = []; s.start = -1; s.cur = -1; s.dir = 0; s.pending = -1; s.visited = []; s.offer = [];
      }
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
      if (s.stage === 3) {
        var P = env.pointer;
        s.words.forEach(function (w) {
          w.c.forEach(function (k, pos) {
            var m3 = marks.get(cellKey(bl, k));
            if (!m3) return;
            // волна от курсора заглушала бы тихое дыхание слов
            m3.calm = 1;
            if (w.done) { m3.grow = 0.12; m3.lit = 1; return; }
            var age = w.heard >= 0 ? now - w.heard - Math.abs(pos - w.from) * WAVE_STEP : -1;
            // пока не звучит: еле заметное общее дыхание слова
            if (age < 0) { m3.grow = 0.12 + 0.12 * Math.sin(now * w.fr * 2 + w.ph); return; }
            heardMark(m3, w, pos, age, cellXY(bl, k), P);
          });
        });
        if (s.sel) s.sel.cells.forEach(function (k) {
          var ms = marks.get(cellKey(bl, k));
          if (ms) { ms.lit = 1; ms.grow = Math.max(ms.grow || 0, 0.3); }
        });
      }
      if (s.stage === 4) {
        for (var q = 0; q < bl.n; q++) { var m4 = marks.get(cellKey(bl, q)); if (m4) m4.dim = 0.9; }
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
  function drawManyEdges(ctx, bl, groups, col, lw) {
    if (!groups.length) return;
    var o = org(bl);
    ctx.beginPath();
    groups.forEach(function (cs) { edgesPath(ctx, cs, o.x, o.y, F.CELL, true); });
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
        ctx.save();
        ctx.globalAlpha = e.dim ? 0.28 : 1;
        ctx.translate(li.cx + sh, li.cy);
        glowStroke(ctx, 'rgba(255,176,90,0.95)', 10, 1.5);
        G.drawGlyph(ctx, e.g, 40, 1.5);
        ctx.restore();
      }
    });
    ctx.restore();
  }

  /* Разделители предложений: над первым предложением одна тонкая белая
     линия, над вторым две, над третьим три — по строкам, от начала до конца
     предложения. */
  function drawDividers(ctx, bl) {
    var sents = sentences(bl), o = org(bl), c = F.CELL, gap = Math.max(2.5, c * 0.045);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = 'rgba(240,246,255,0.6)';
    ctx.lineWidth = 1;
    sents.forEach(function (cells, si) {
      var runs = [];
      cells.forEach(function (k) {
        var x = k % bl.w, y = (k / bl.w) | 0, last = runs[runs.length - 1];
        if (last && last.y === y && last.x1 === x) last.x1 = x + 1;
        else runs.push({ y: y, x0: x, x1: x + 1 });
      });
      ctx.beginPath();
      runs.forEach(function (r) {
        for (var i = 0; i <= si; i++) {
          var yy = o.y + r.y * c + c * 0.07 + i * gap;
          ctx.moveTo(o.x + r.x0 * c + c * 0.06, yy);
          ctx.lineTo(o.x + r.x1 * c - c * 0.06, yy);
        }
      });
      ctx.stroke();
    });
    ctx.restore();
  }

  /* Текст записи в её рамке. s — идущий четвёртый этап (или null для уже
     прочитанной записи). */
  function drawBlockText(ctx, bl, s) {
    var lay = blockText(bl), r = lay.rect, fs = lay.fs;
    var readyK = !s ? 1 : (s.done >= 0 ? clamp((now - s.done) / 1.4, 0, 1) : 0);
    var nodeOf = {};
    if (s) s.nodes.forEach(function (n, i) { nodeOf[n.wi] = i; });
    var blur = 1 - readyK;

    ctx.save();
    ctx.fillStyle = 'rgba(8,6,3,' + (s ? 0.82 : 0.76) + ')';
    ctx.fillRect(r.x0 + 2, r.y0 + 2, r.x1 - r.x0 - 4, r.y1 - r.y0 - 4);
    ctx.beginPath(); ctx.rect(r.x0, r.y0, r.x1 - r.x0, r.y1 - r.y0); ctx.clip();
    ctx.font = fs.toFixed(1) + 'px Consolas, "Courier New", monospace';
    ctx.textBaseline = 'middle';
    lay.words.forEach(function (w, wi) {
      var isNode = nodeOf[wi] !== undefined;
      if (isNode && readyK < 0.6) return;
      var link = w.text.charAt(0) === '⟨';
      var col = link ? '255,170,90' : (w.key || !s ? '244,238,224' : '255,214,170');
      var alpha = isNode ? clamp((readyK - 0.6) / 0.4, 0, 1) : (link ? 0.75 : 1);
      var jig = (w.key || !s) ? 0 : blur;
      var riseY = 0;
      if (s && w.key && now - s.t0 < 1.2) {
        // собранное слово плавно встаёт на своё место
        var u = clamp((now - s.t0) / 1.2, 0, 1), e = 1 - Math.pow(1 - u, 3);
        riseY = (1 - e) * fs * 1.6; alpha *= e;
      }
      if (w.num !== null) {
        NUM().draw(ctx, w.num, w.cx + Math.sin(now * 17 + wi) * jig * fs * 0.1, w.y + riseY, fs * 1.4, 'rgba(255,220,180,' + alpha + ')');
        return;
      }
      if (w.cmd) {
        // команда пульта записана знаками: её можно набрать
        ctx.save();
        ctx.globalAlpha = alpha;
        ctx.strokeStyle = 'rgba(255,200,130,0.95)';
        w.cmd.forEach(function (g, ci) {
          ctx.save();
          ctx.translate(w.x + fs * 0.62 + ci * fs * 1.25 + Math.sin(now * 13 + ci) * jig * fs * 0.1, w.y + riseY);
          G.drawGlyph(ctx, g, fs * 1.15, Math.max(1, fs * 0.07));
          ctx.restore();
        });
        ctx.restore();
        return;
      }
      var passes = jig > 0.05 ? 3 : 1;
      for (var pass = 0; pass < passes; pass++) {
        ctx.globalAlpha = alpha * (passes > 1 ? 0.35 : 1);
        ctx.fillStyle = 'rgb(' + col + ')';
        var ox = jig * fs * 0.12 * (Math.sin(now * 13 + wi * 3 + pass * 2) * 1.5 + (pass - 1));
        var oy = jig * fs * 0.1 * Math.cos(now * 11 + wi + pass);
        ctx.fillText(w.text, w.x + ox, w.y + oy + riseY);
      }
    });
    ctx.restore();
    if (!s) return;

    // линии, знаки и пустота над ними — поверх текста
    function P(i) { var w = lay.words[s.nodes[i].wi]; return { x: w.cx, y: w.y }; }
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineCap = 'round';
    var crumbleK = s.crumble >= 0 && now >= s.crumble ? (now - s.crumble) / 1.3 : -1;
    s.lines.forEach(function (l) {
      var A = P(l.a), B = P(l.b), grow = clamp((now - l.born) / LINE_T, 0, 1), al = 1, drop = 0;
      if (crumbleK >= 0) {
        al = crumbleK < 0.5 ? (Math.sin(now * 40) > 0 ? 1 : 0.2) : Math.max(0, 1 - (crumbleK - 0.5) / 0.5);
        if (crumbleK > 0.5) drop = (crumbleK - 0.5) * fs * 3;
      }
      if (s.done >= 0 && now > s.done) al = Math.max(0, 1 - readyK * 1.3);
      if (al <= 0) return;
      ctx.globalAlpha = Math.min(1, al);
      glowStroke(ctx, 'rgba(255,150,50,0.95)', s.done >= 0 ? 24 : 12, Math.max(2, fs * (s.done >= 0 ? 0.22 : 0.14)));
      ctx.beginPath();
      ctx.moveTo(A.x, A.y + drop);
      ctx.lineTo(A.x + (B.x - A.x) * grow, A.y + drop + (B.y + drop * 0.3 - A.y) * grow);
      ctx.stroke();
    });
    ctx.globalAlpha = 1;
    ctx.shadowBlur = 0;
    if (readyK < 0.6) {
      var va = clamp((now - s.offerT) / 0.45, 0, 1), vEase = 1 - Math.pow(1 - va, 3);
      s.nodes.forEach(function (n, i) {
        var p = P(i);
        var lit = i === s.pending || s.visited.indexOf(i) >= 0 || s.offer.indexOf(i) >= 0;
        var dimAll = s.start >= 0 || s.pending >= 0;
        ctx.save();
        ctx.translate(p.x, p.y);
        ctx.globalAlpha = (1 - readyK / 0.6) * (lit ? 1 : dimAll ? 0.35 : 0.85);
        glowStroke(ctx, lit ? 'rgba(255,236,200,0.98)' : 'rgba(255,170,90,0.9)', lit ? 14 : 6, Math.max(1.2, fs * 0.08));
        G.drawGlyph(ctx, n.g, fs * (lit ? 2.0 : 1.7), Math.max(1.2, fs * 0.08));
        ctx.restore();
        var showVoid = ((s.start < 0 && i === s.pending) || (s.start >= 0 && s.offer.indexOf(i) >= 0)) && s.crumble < 0;
        if (showVoid) {
          // пустота плавно всплывает над знаком
          var pu = 0.5 + 0.5 * Math.sin(now * 4 + i);
          ctx.save();
          ctx.translate(p.x, p.y - fs * (1.2 + 0.9 * vEase));
          ctx.globalAlpha = vEase;
          glowStroke(ctx, 'rgba(236,244,255,' + (0.5 + pu * 0.5) + ')', 10 + pu * 8, 1.3);
          ctx.beginPath(); ctx.arc(0, 0, fs * 0.8, 0, Math.PI * 2); ctx.stroke();
          G.drawGlyph(ctx, F.VOID_GID, fs * 1.0, 1.2);
          ctx.restore();
        }
      });
    }
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
      // под текстом прочитанной записи сетка фигур и точки уже не нужны
      var textOn = bl.stage >= 5 || (active && ses.stage === 4);
      /* Сетка фигур нужна, пока слов ещё нет. На этапе слов она мешает их
         разглядеть, а после него рамку делят уже слова. */
      var wordsOn = active && ses.stage === 3;
      if (!textOn && !wordsOn && !bl.words) drawManyEdges(ctx, bl, bl.tiles.map(function (tl) { return tl.c; }), 'rgba(236,244,255,0.55)', 1.2);
      if (!textOn && !wordsOn && bl.words) drawManyEdges(ctx, bl, bl.words.map(function (c) { return cellsAbs(bl, c); }), 'rgba(236,244,255,0.5)', 1.2);
      // начатая укладка видна и вне этапа
      if (bl.stage === 1 && bl.draft && !(active && ses.stage === 1)) drawManyEdges(ctx, bl, bl.draft.map(function (d) { return d.c; }), 'rgba(255,190,110,0.6)', 1.6);
      drawTiled(ctx, bl, active);
      ctx.restore();
      Object.keys(bl.restored).forEach(function (kk) {
        var k = +kk;
        if (bl.dots.indexOf(k) >= 0) return;
        var p = cellXY(bl, k);
        drawPurgedAt(ctx, p.x, p.y, F.CELL, bl.cells[k], true);
      });
      if (!textOn) bl.dots.forEach(function (k) { var p = cellXY(bl, k); drawPurgedAt(ctx, p.x, p.y, F.CELL * 0.7, 0, false); });
      if (bl.stage >= 3 && bl.stage < 5 && bl.dots.length && !(active && ses.stage === 4)) drawDividers(ctx, bl);
      // прочитанная запись остаётся текстом прямо в своей рамке на карте
      if (bl.stage >= 5 && !(active && ses.stage === 4)) drawBlockText(ctx, bl, null);
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
        if (s.drag) drawPurgedAt(ctx, s.drag.x, s.drag.y, 52, s.drag.entry.g, true, 0.9);
        // меню появляется, когда время запоминания вышло
        if (now >= s.showUntil) drawMenu(ctx);
      }
      if (s.stage === 3) {
        ctx.save();
        ctx.globalCompositeOperation = 'lighter';
        s.words.forEach(function (w) {
          if (w.done) {
            var a = clamp((now - w.doneAt) / 0.5, 0, 1);
            drawTileEdges(ctx, bl, cellsAbs(bl, w.c), 'rgba(240,246,255,' + (0.35 + 0.55 * a) + ')', 2);
          } else if (w.heard >= 0) {
            var u = clamp((now - w.heard) / HEAR_T, 0, 1);
            drawTileEdges(ctx, bl, cellsAbs(bl, w.c), 'rgba(255,190,110,' + (0.3 + 0.6 * u) + ')', 1.6 + u);
          }
        });
        if (s.sel) drawTileEdges(ctx, bl, cellsAbs(bl, s.sel.cells), 'rgba(255,200,130,0.9)', 2);
        if (s.bad) {
          var ba = 1 - clamp((now - s.bad.t) / 0.7, 0, 1);
          ctx.save();
          ctx.translate(Math.sin(now * 60) * 5 * ba, 0);
          drawTileEdges(ctx, bl, cellsAbs(bl, s.bad.cells), 'rgba(255,70,40,' + ba.toFixed(3) + ')', 2.2);
          ctx.restore();
        }
        if (s.drag) {
          ctx.translate(s.drag.x, s.drag.y);
          glowStroke(ctx, 'rgba(255,176,90,0.95)', 12, 1.6);
          G.drawGlyph(ctx, s.drag.entry.g, F.CELL * 0.7, 1.6);
        }
        ctx.restore();
        drawMenu(ctx);
      }
      if (s.stage === 4) drawBlockText(ctx, bl, s);
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
    debug: function () {
      return {
        errs: errs, file: file.slice(), creature: creatureNo,
        blocks: blocks.map(function (b) { return { id: b.id, stage: b.stage, targets: b.targets, dots: b.dots, restored: Object.keys(b.restored).length, tiles: b.tiles.length }; }),
        ses: ses ? { stage: ses.stage, used: ses.placed ? costOf(ses.placed) : 0, placed: ses.placed && ses.placed.length, crumble: ses.crumble, done: ses.done, visited: ses.visited && ses.visited.length } : null
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
        voidPos: voidPos, nodePos: nodePos, blockText: blockText, removedDone: s.stage === 2 ? removedDone : null
      };
    }
  };
})(window);
