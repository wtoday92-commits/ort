/* ORT — цикл, ввод, выделение.
 *
 * Блок мусора задан двумя якорями: выделение начинается на одном и должно
 * закончиться строго на парном ему. Рамка «вокруг примерно того места» не
 * считается, потому что считаются углы, а не содержимое.
 *
 * Пока идёт выделение, поле замирает. Это и подсказка, что сейчас важен не
 * поиск, а точность, и способ дать рамке вес.
 */
(function (root) {
  'use strict';

  var G = root.Glyphs, F = root.Field, LORE = root.Lore, INV = root.Inventory;

  var dev = /[?&]dev/.test(location.search);
  function qnum(name, def) {
    var m = new RegExp('[?&]' + name + '=([0-9.]+)').exec(location.search);
    return m ? parseFloat(m[1]) : def;
  }
  /* Заставка идёт до конца ПЕРВОГО ПОЛНОГО КРУГА существа: игрок должен
     увидеть весь паттерн, прежде чем получит пульт. На dev круг не ждём,
     если явно не попросить ?intro. */
  var INTRO_FULL = !dev || /[?&]intro/.test(location.search);
  var IDLE_BACK = 14;
  var DRIFT_FIXED = qnum('driftmax', 0);       // для проверок: жёсткий потолок шкалы
  var EJECT_FIRST = qnum('ejectfirst', 60), EJECT_NEXT = qnum('ejectnext', 20);   // длительность сцены выброса, с
  var MOVE_FILL = qnum('fill', 0.05);          // заполненность карты, после которой корабль переезжает
  var NAV_W = 192;
  // перерывы втрое реже, чем были: они не должны дёргать игрока
  var LUNCH_EVERY = qnum('lunch', 45 * 60), LUNCH_DUR = qnum('lunchdur', 30), LUNCH_RETRY = qnum('lunchretry', 9 * 60);
  var SLEEP_EVERY = qnum('sleep', 120 * 60), SLEEP_DUR = qnum('sleepdur', 120), SLEEP_RETRY = qnum('sleepretry', 24 * 60);
  var LORE_IDLE = qnum('loreidle', 180);        // сколько игрок может молчать в лорной вкладке, прежде чем существо вернётся к работе
  var LUNCH_DEATH = 5, SLEEP_DEATH = 3;
  var LIFE = qnum('life', 10 * 3600);          // сколько работает существо, пока его не утилизируют по износу, с
  var TUT_CYCLES = 3;                          // старое существо: столько кругов игрок должен закрыть сам
  var TUT_PLAY = qnum('tutplay', 330), TUT_MIN = qnum('tutmin', 240), TUT_GRACE = 40;
  var SPIN_P = qnum('spin', 0.03);             // как часто край собранного блока занимает крутящийся знак       // столько отказов подряд существо не переживёт
  var TOL = 33;                 // на сколько пикселей можно промахнуться по якорю

  /* Проверка знака стоит ТРЁХ СЕКУНД неподвижности, и до конца выдержки
     не возникает ни звука, ни свечения. Иначе игра вырождается: игрок просто
     водит курсором по экрану и ждёт сигнала, вместо того чтобы искать знак
     глазами. Кольцо выдержки появляется от простого замирания курсора, есть
     под ним якорь или нет, поэтому прощупать им поле нельзя. */
  var DWELL = 3.0;
  var HOLD_SHOW = 0.7;          // когда проступает кольцо выдержки
  var HOLD_SLIP = 11;           // на сколько можно дрогнуть, не сбив выдержку

  var canvas, scene, ctx, post = null, vw = 0, vh = 0, dpr = 1;
  var S = root.Sound;
  var t = 0, last = 0;

  // --- курсор ----------------------------------------------------------------

  var Pointer = { x: 0, y: 0, tx: 0, ty: 0, spd: 0, down: false, dragX: 0, dragY: 0 };
  var hand = null, creature = null;
  var humanAt = -1e9;
  var controlAt = INTRO_FULL ? Infinity : 6;   // с какого момента пульт доступен игроку
  var forced = false;                          // существо само забрало пульт
  function ctrl() { return t >= controlAt; }
  /* В лорной вкладке игрок может думать долго или отвлечься: существо
     возвращается к работе только спустя три минуты тишины. */
  function humanActive() { return ctrl() && !forced && t - humanAt < (panel === 1 ? LORE_IDLE : IDLE_BACK); }

  // --- этапы и папки ---------------------------------------------------------

  /* NONE — свободный режим: ни один этап не выбран, поле можно просто
     рассматривать. Мини-игра, доигранная или брошенная, ВСЕГДА возвращает сюда.
     Иначе приходилось переключаться на чужой этап и обратно, лишь бы запустить
     свой заново. */
  var PHASE = { NONE: -1, COLLECT: 0, ANALYZE: 1, SORT: 2, PURGE: 3 };
  var phase = PHASE.COLLECT;
  var FOLDER_CAP = 9;             // три ряда по три квадрата
  var folders = [0, 0, 0, 0];
  var folderFlare = [0, 0, 0, 0];

  var lastPhase = -1, offStreak = 0, drift = 0, driftFloor = 0;

  /* Очередь единиц работы. Единица рождается на сборе и проходит все четыре
     этапа, неся с собой НАЧЕРТАНИЕ якоря, по которому её собрали, и цепочку
     клеток, найденную на анализе. Материал у каждого этапа один и тот же и
     лежит на поле: игра ничего не подменяет и ничего не выдумывает.
       stage 0 — собрано, ждёт анализа
       stage 1 — проанализировано, ждёт сортировки
       stage 2 — разложено, ждёт утилизации
       stage 3 — утилизировано, уходит из папки */
  var stock = [];
  var mapId = 0;                 // номер карты: после переезда цепочки старой карты недействительны

  function unitsAt(stage) {
    var r = [];
    for (var i = 0; i < stock.length; i++) if (stock[i].stage === stage) r.push(stock[i]);
    return r;
  }

  function syncFolders() {
    for (var i = 0; i < 4; i++) folders[i] = Math.min(FOLDER_CAP, unitsAt(i).length);
  }

  /* Сколько этапов служебного паттерна уже существует. Пока сделаны сбор и
     анализ, круг замыкается на них двоих, и шкала считается по-настоящему:
     ровное чередование её снижает, повторный сбор без анализа поднимает. */
  var CYCLE = 4;

  /* Толчок шкале помимо порядка этапов: за форму собранного и за незакрытую
     работу. Пол шкалы поднимается вместе с ней и обратно не опускается. */
  function nudge(v) {
    if (v <= 0) return;
    drift += v;
    driftFloor = Math.max(driftFloor, drift * 0.45);
  }

  function act(p) {
    var inPattern = (lastPhase < 0) || (p === (lastPhase + 1) % CYCLE);
    if (inPattern) { offStreak = 0; drift = Math.max(driftFloor, drift - 0.9); }
    else { offStreak++; drift += 0.8 * offStreak; driftFloor = Math.max(driftFloor, drift * 0.45); }
    lastPhase = p;
  }

  // --- состояние выделения ---------------------------------------------------

  var SEL = { IDLE: 0, DRAG: 1, CONFIRM: 2, SEND: 3 };
  var sel = SEL.IDLE;
  var startAnchor = null, endAnchor = null;
  var rect = null, button = null;
  var freeze = 0;
  var reject = 0;                // вспышка отказа
  var taken = new Set();         // уже собранные ячейки: из поля они уходят
  var reveals = new Map();       // ячейка -> {ok, age}
  var boost = new Map();
  var holdX = 0, holdY = 0, holdT = 0, holdFired = false;
  var flying = [];
  var pulses = [];               // отклик на захват
  var chains = [];               // цепочки этапа анализа
  var marks = new Map();         // накладка на поле: узлы цепочек
  var errors = 0;                // промахи анализа
  var runErr = [false, false, false, false];   // была ли ошибка в текущем заходе этапа
  var runDots = [0, 0, 0, 0];                   // сколько серых точек заход уже отдал в лор
  var runDone = [[], [], [], []];               // единицы, закончившие этап в этом заходе
  var slips = 0, lastSplits = 0;
  var age = 0, tut = null, lifeFlags = {};      // возраст существа; обучение со старым существом
  var trains = [];               // связки, уходящие в сосуд на нитке
  var CHAIN_MISS = 3;            // столько промахов, и цепочка распускается
  var prevPX = 0, prevPY = 0, cursorSpd = 0, dwellSnd = 0;
  /* Нажатие видно по курсору: он сжимается, пока кнопка зажата, и
     расправляется при отпускании. У нажатий существа сжатие короткое. */
  var squash = 0, pressed = false, tapSquash = 0;
  var pointerIn = true;          // курсор игрока внутри окна игры

  function REAL(a) { return a.role === 1 || a.role === 2; }

  function norm(ax, ay, bx, by) {
    return { x0: Math.min(ax, bx), y0: Math.min(ay, by), x1: Math.max(ax, bx), y1: Math.max(ay, by) };
  }

  function press(x, y) {
    if (sel !== SEL.IDLE) return;
    Pointer.down = true; Pointer.dragX = x; Pointer.dragY = y;
    startAnchor = phase === PHASE.COLLECT ? F.anchorNear(x, y, TOL, REAL) : null;
    pulses.push({ x: x, y: y, age: 0, strong: !!startAnchor });
    S.grip(!!startAnchor);
    sel = SEL.DRAG;
  }

  function release(x, y) {
    if (sel !== SEL.DRAG) return;
    Pointer.down = false;
    var ok = null;
    if (startAnchor) {
      var s = startAnchor.rec;
      ok = F.anchorNear(x, y, TOL, function (a) {
        return a.pid && a.pid === s.pid && a.role !== s.role;
      });
    }
    if (ok) {
      endAnchor = ok;
      rect = norm(startAnchor.x, startAnchor.y, ok.x, ok.y);
      // рамка ложится точно по якорям, с небольшим полем вокруг
      rect.x0 -= 16; rect.y0 -= 16; rect.x1 += 16; rect.y1 += 16;
      // кнопка встаёт рядом с курсором, но всегда за пределами рамки
      var bo = outsidePoint(rect, x, y, 34);
      button = { x: bo.x, y: bo.y, r: 21, hot: 0 };
      sel = SEL.CONFIRM;
    } else {
      reject = 1;
      S.reject();
      rect = null; startAnchor = null;
      sel = SEL.IDLE;
    }
  }

  /* Точка рядом с курсором, но снаружи прямоугольника: у ближайшей к курсору
     кромки. Внутри области кнопку плохо видно из-за знаков. */
  function outsidePoint(rc, x, y, gap) {
    function cl(v, a, b) { return Math.max(a, Math.min(b, v)); }
    var cands = [
      { x: rc.x1 + gap, y: cl(y, rc.y0, rc.y1), d: Math.abs(x - rc.x1) },
      { x: rc.x0 - gap, y: cl(y, rc.y0, rc.y1), d: Math.abs(x - rc.x0) },
      { x: cl(x, rc.x0, rc.x1), y: rc.y1 + gap, d: Math.abs(y - rc.y1) },
      { x: cl(x, rc.x0, rc.x1), y: rc.y0 - gap, d: Math.abs(y - rc.y0) }
    ];
    cands.sort(function (p, q) { return p.d - q.d; });
    for (var i = 0; i < cands.length; i++) {
      var c = cands[i];
      if (c.x > 30 && c.x < vw - 30 && c.y > 96 && c.y < vh - 140) return c;
    }
    return { x: cl(cands[0].x, 30, vw - 30), y: cl(cands[0].y, 96, vh - 140) };
  }

  /* Ошибки улетают в лорную вкладку серыми точками, без нитки. */
  var errDots = [];

  function spawnErrDots(x, y) {
    var tp = panelPos(1);
    for (var i = 0; i < 1; i++) {
      // серая точка отваливается от курсора вниз и только потом улетает в лорную папку
      var sx = x + 3, sy = y + 28;
      errDots.push({
        x0: sx, y0: sy, x1: tp.x + (Math.random() - 0.5) * 8, y1: tp.y + (Math.random() - 0.5) * 6,
        cx: (sx + tp.x) / 2 + (Math.random() - 0.5) * 320, cy: (sy + tp.y) / 2 + (Math.random() - 0.5) * 160,
        d: 0.2, dur: 1.0 + Math.random() * 0.3, t: 0, rung: false
      });
    }
  }

  function stepErrDots(dt) {
    for (var i = errDots.length - 1; i >= 0; i--) {
      var e = errDots[i];
      if (e.d > 0) { e.d -= dt; continue; }
      e.t += dt / e.dur;
      if (e.t >= 1 && !e.rung) { e.rung = true; tabFlare = 1; S.tick(i, 5); }
      if (e.t >= 1.25) errDots.splice(i, 1);
    }
  }

  function drawErrDots() {
    if (!errDots.length) return;
    ctx.save();
    for (var i = 0; i < errDots.length; i++) {
      var e = errDots[i], x, y, a = 1;
      if (e.d > 0) { x = e.x0; y = e.y0 - 28 * Math.min(1, e.d / 0.2); }
      else {
        var u = Math.min(1, e.t), ee = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2, m = 1 - ee;
        x = m * m * e.x0 + 2 * m * ee * e.cx + ee * ee * e.x1;
        y = m * m * e.y0 + 2 * m * ee * e.cy + ee * ee * e.y1;
        if (e.t > 1) a = Math.max(0, 1 - (e.t - 1) / 0.25);
      }
      ctx.fillStyle = 'rgba(90,90,88,' + 0.16 * a + ')';
      ctx.beginPath(); ctx.arc(x, y, 7, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = 'rgba(118,116,110,' + 0.95 * a + ')';
      ctx.beginPath(); ctx.arc(x, y, 3.4, 0, Math.PI * 2); ctx.fill();
    }
    ctx.restore();
  }

  function abort() {
    Pointer.down = false;
    sel = SEL.IDLE; rect = null; button = null;
    startAnchor = null; endAnchor = null;
  }

  /* Отправка: слепок выделенных глифов улетает в папку сбора. */
  function clickButton() {
    if (sel !== SEL.CONFIRM) return;
    var snap = F.snapshot(vw, vh, rect);
    // клетки уникального объекта забирает только сбор самого объекта
    var objId = startAnchor && startAnchor.rec.obj ? startAnchor.rec.obj : 0;
    snap = snap.filter(function (g) { var oi = F.objAt(g.wx, g.wy); return !oi || oi === objId; });
    /* Края блока забираются всегда. Отстающий якорь мог съехать за рамку, и
       тогда на его месте вместо пустоты оставался обычный знак. */
    [startAnchor, endAnchor].forEach(function (an) {
      if (!an) return;
      var ak = F.ckey(an.wx, an.wy);
      for (var si = 0; si < snap.length; si++) if (snap[si].key === ak) return;
      var ap = F.cellCenter(an.wx, an.wy);
      snap.push({ key: ak, wx: an.wx, wy: an.wy, id: F.glyphAt(an.wx, an.wy), x: ap.x, y: ap.y, s: 1 });
    });
    var fp = folderPos(PHASE.COLLECT);
    flying = snap.map(function (g, i) {
      taken.add(g.key);
      return {
        id: g.id, x0: g.x, y0: g.y, s0: g.s,
        x1: fp.x + (Math.random() - 0.5) * 16, y1: fp.y - 2,
        cx: (g.x + fp.x) / 2 + (Math.random() - 0.5) * 220,
        cy: Math.min(g.y, fp.y) - 60 - Math.random() * 140,
        d: i * 0.022 + Math.random() * 0.10, dur: 0.62 + Math.random() * 0.3, t: 0,
        rung: false
      };
    });
    // на освободившемся месте проступят знаки пустоты и очень нескоро зарастут
    F.consume(snap, startAnchor ? startAnchor.rec.pid : 0);
    /* Изредка один край собранного блока занимает не пустота, а случайный
       знак, который так и остаётся крутиться в своей клетке. Это сбой, и
       корабль его хранит наравне с прочими особыми знаками. */
    if (Math.random() < SPIN_P) {
      var edge = Math.random() < 0.5 ? startAnchor : endAnchor;
      if (edge) {
        var sg;
        do { sg = 1 + Math.floor(Math.random() * (G.COUNT - 1)); } while (G.isParasite(sg));
        F.setSpin(F.ckey(edge.wx, edge.wy), sg);
      }
    }
    sel = SEL.SEND;
    button = null;
    // bad[этап] — единица вышла из этого этапа с ошибкой: в папке она серая
    stock.push({ gid: startAnchor ? startAnchor.rec.gid : 0, kind: startAnchor ? startAnchor.rec.kind : 0, stage: 0, chain: null, map: mapId, bad: {} });
    // знаки пустоты, образовавшиеся на сборе, уходят в хранилище числом
    INV.addVoids(humanActive() ? 'p' : 'c', snap.length);
    if (objId) collectObject(objId);
    syncFolders();
    folderFlare[PHASE.COLLECT] = 0.001;   // разгорится, когда глифы дойдут
    act(PHASE.COLLECT);
  }

  /* Собран уникальный объект. Для корабля это не работа, а отклонение: серая
     ячейка сбора и серая точка в лор. Для игрока — новая запись в лорной
     вкладке. */
  function collectObject(id) {
    var ob = F.takeObject(id), u = stock[stock.length - 1];
    if (!ob || !u) return;
    u.bad = u.bad || {};
    u.bad[PHASE.COLLECT] = true;
    u.dotted = { 0: true };
    LORE.credit(1);
    var c = F.cellCenter(ob.cells[0][0], ob.cells[0][1]);
    spawnErrDots(c.x, c.y);
    S.error();
    LORE.addObject({ type: ob.type, onum: ob.onum });
  }

  /* Какой объект появится на новом участке карты. Природные встречаются чаще;
     записи, которые уже прочитаны или потеряны, больше не выпадают. */
  var OBJ = root.LoreText.objects;

  function objSpec(type, onum) {
    var d = OBJ[type];
    return { type: type, cls: d.cls, rows: d.rows, onum: onum || 0 };
  }

  function objPick() {
    var list = [], tot = 0;
    Object.keys(OBJ).forEach(function (k) {
      if (OBJ[k].special || !LORE.objAvailable(k)) return;
      list.push(k); tot += OBJ[k].weight || 1;
    });
    if (!list.length) return null;
    var r = Math.random() * tot;
    for (var i = 0; i < list.length; i++) {
      r -= OBJ[list[i]].weight || 1;
      if (r <= 0) return objSpec(list[i]);
    }
    return objSpec(list[list.length - 1]);
  }

  function randomNatural() {
    var ks = Object.keys(OBJ).filter(function (k) { return OBJ[k].cls === 'nat' && !OBJ[k].special && LORE.objAvailable(k); });
    return ks.length ? ks[Math.floor(Math.random() * ks.length)] : null;
  }

  /* Объект по сценарию: на расстоянии r0..r1 клеток от центра экрана и
     непременно за краем стартового обзора. Капсула — так, чтобы при самом
     сильном отдалении она попадала в поле зрения. */
  function spawnNear(type, r0, r1, onum) {
    var c = F.camCell, cs = 54;
    var cx = c.x + vw / F.CELL / 2, cy = c.y + (vh - 110) / F.CELL / 2;
    var hx = vw / cs / 2 + 3, hy = (vh - 110) / cs / 2 + 2;
    for (var i = 0; i < 30; i++) {
      var ang = Math.random() * Math.PI * 2, r = r0 + Math.random() * (r1 - r0);
      var dx = Math.cos(ang) * r, dy = Math.sin(ang) * r * 0.55;
      if (Math.abs(dx) < hx && Math.abs(dy) < hy) continue;
      var o = objSpec(type, onum);
      o.x = cx + dx; o.y = cy + dy;
      if (F.placeObject(o)) return true;
    }
    return false;
  }

  function stepFlying(dt) {
    if (!flying.length) return;
    var alive = 0;
    for (var i = 0; i < flying.length; i++) {
      var f = flying[i];
      f.d -= dt;
      if (f.d > 0) { alive++; continue; }
      f.t += dt / f.dur;
      if (f.t < 1) alive++;
      else if (!f.rung) {
        f.rung = true;
        var fi = f.fi === undefined ? PHASE.COLLECT : f.fi;
        S.tick(i, flying.length);
        if (folderFlare[fi] < 1) { folderFlare[fi] = 1; S.knock(); }
      }
    }
    if (!alive) {
      flying = [];
      if (sel === SEL.SEND) {
        S.hollow();
        rect = null; startAnchor = null; endAnchor = null;
        sel = SEL.IDLE;
      }
    }
  }

  // --- анализ ----------------------------------------------------------------
  /* Собранные обломки ложатся на поле цепочками. Каждый узел при подходе
     курсора КРЕНИТСЯ и подаётся в сторону следующего: стрелок нет, есть
     наклон. Голова цепочки — единственный узел, который качается сам по себе.
     Кликать надо по порядку.

     Если собрать несколько партий и только потом анализировать, цепочек на
     поле окажется несколько и они перепутаются. Промах в такой мешанине даёт
     не провал, а ОШИБКУ. Ровный паттерн ошибок не даёт никогда. */

  /* Цепочка строится из клеток, которые на поле УЖЕ есть. Первый и последний
     узел — знак того же начертания, что и якорь, по которому этот мусор
     собирали. Между ними обычные клетки по пути. Ничего не подменяется. */
  function chainFor(unit) {
    /* Сначала ищем поблизости: цепочка, растянутая на полкарты, превращает и
       анализ, и следующую за ним утилизацию в долгую дорогу. */
    var cand = F.findGlyph(unit.gid, 0, 30, 20, null);
    if (cand.length < 2) cand = F.findGlyph(unit.gid, 0, 46, 32, null);
    if (cand.length < 2) cand = F.findGlyph(unit.gid, 0, 96, 68, null);
    if (cand.length < 2) return null;
    // первый конец — ближайший к центру экрана, второй — на разумном отдалении
    // от первого, чтобы цепочка не слипалась в точку и не тянулась через карту
    var a = cand[0], b = null;
    for (var ci = 1; ci < cand.length && !b; ci++) {
      var ddx = Math.abs(cand[ci].wx - a.wx), ddy = Math.abs(cand[ci].wy - a.wy);
      ddx = Math.min(ddx, F.W - ddx); ddy = Math.min(ddy, F.H - ddy);
      if (ddx + ddy >= 4 && ddx + ddy <= 16) b = cand[ci];
    }
    if (!b) b = cand[1];
    var avoid = {};
    avoid[F.ckey(a.wx, a.wy)] = 1; avoid[F.ckey(b.wx, b.wy)] = 1;

    var mid = 3 + Math.floor(Math.random() * 2);
    var nodes = [a], k;
    for (k = 1; k <= mid; k++) {
      var u = k / (mid + 1);
      var gx = Math.round(a.wx + (b.wx - a.wx) * u + (Math.random() - 0.5) * 5);
      var gy = Math.round(a.wy + (b.wy - a.wy) * u + (Math.random() - 0.5) * 5);
      var got = null;
      for (var tryN = 0; tryN < 20 && !got; tryN++) {
        var wx = (gx + (tryN ? Math.round((Math.random() - 0.5) * 6) : 0) + F.W) % F.W;
        var wy = (gy + (tryN ? Math.round((Math.random() - 0.5) * 6) : 0) + F.H) % F.H;
        var key = F.ckey(wx, wy);
        if (avoid[key] || F.isSpecial(wx, wy) || F.objAt(wx, wy)) continue;
        avoid[key] = 1;
        got = { wx: wx, wy: wy };
      }
      if (got) nodes.push(got);
    }
    nodes.push(b);
    return nodes.length >= 3 ? nodes : null;
  }

  /* Заход этапа: один анализ, одна доска сортировки, одна доска утилизации.
     Ошибка в заходе — серая ячейка за КАЖДУЮ единицу, которую этот заход
     выпустит, и одна серая точка в лорную вкладку (за сомкнувшиеся группы на
     сортировке — две). Сколько бы ошибок ни было дальше, точка одна. Единица,
     уже отдавшая точку на этом этапе, при повторном заходе даёт серую ячейку,
     но точки больше не даёт. Без ошибок — белая ячейка и ничего больше.
     Для игрока это выглядит как награда за ошибку; для корабля — это работа,
     которая идёт всё хуже. */
  function stageRun(st) { runErr[st] = false; runDots[st] = 0; runDone[st] = []; }
  function stageUnits(st) {
    if (st === PHASE.ANALYZE) return chains.map(function (c) { return c.unit; });
    return st === PHASE.SORT ? sortUnits : st === PHASE.PURGE ? purgeUnits : [];
  }
  function stageDone(st, u) {
    u.bad = u.bad || {};
    u.bad[st] = runErr[st];
    runDone[st].push(u);
  }
  function stageError(st, x, y, dots) {
    if (!runErr[st]) {
      runErr[st] = true;
      runDone[st].forEach(function (u) { u.bad = u.bad || {}; u.bad[st] = true; });
    }
    var give = (dots || 1) - runDots[st];
    if (give <= 0) return;
    var us = stageUnits(st);
    if (us.length && us.every(function (u) { return u.dotted && u.dotted[st]; })) return;
    runDots[st] += give;
    us.forEach(function (u) { u.dotted = u.dotted || {}; u.dotted[st] = true; });
    LORE.credit(give);
    for (var i = 0; i < give; i++) spawnErrDots(x + i * 12, y);
    S.error();
  }

  function buildChains() {
    stageRun(PHASE.ANALYZE);
    slips = 0;
    chains = [];
    var pend = unitsAt(0);
    for (var i = 0; i < Math.min(4, pend.length); i++) {
      var nodes = chainFor(pend[i]);
      if (!nodes) continue;
      pend[i].chain = nodes;
      pend[i].map = mapId;
      chains.push({ nodes: nodes, at: 0, miss: 0, done: false, unit: pend[i] });
    }
  }

  function stepChains() {
    if (phase === PHASE.PURGE && PG.active()) {
      marks.clear();
      PG.marks(marks);
      F.setMarks(marks);
      return;
    }
    if (phase === PHASE.SORT && SZ.active()) {
      marks.clear();
      SZ.marks(marks);
      F.setMarks(marks);
      return;
    }
    if (spinDrag && (inputBlocked() || phase !== PHASE.SORT || panel !== 0)) spinDrag = null;
    if (spinDrag) {
      // взятый крутящийся знак на своём месте не рисуется
      marks.clear();
      marks.set(F.ckey(spinDrag.wx, spinDrag.wy), { hide: 1 });
      F.setMarks(marks);
      return;
    }
    if (phase !== PHASE.ANALYZE || !chains.length) { marks.clear(); F.setMarks(null); return; }
    marks.clear();
    chainMarks(chains, marks);
    F.setMarks(marks);
  }

  function chainMarks(list, out) {
    for (var c = 0; c < list.length; c++) {
      var ch = list[c];
      if (ch.done) continue;
      for (var i = 0; i < ch.nodes.length; i++) {
        var nd = ch.nodes[i];
        var p = F.cellCenter(nd.wx, nd.wy);
        var m = { lean: 0, px: 0, py: 0, lit: i < ch.at ? 1 : 0, head: (i === 0 && ch.at === 0) ? 1 : 0 };
        if (i < ch.nodes.length - 1) {
          var dx = Pointer.x - p.x, dy = Pointer.y - p.y;
          var d = Math.sqrt(dx * dx + dy * dy);
          if (d < 130) {
            var q = F.cellCenter(ch.nodes[i + 1].wx, ch.nodes[i + 1].wy);
            var a = Math.atan2(q.y - p.y, q.x - p.x);
            var k = (1 - d / 130);
            m.lean = Math.cos(a) * 0.42 * k;
            m.px = Math.cos(a) * 11 * k;
            m.py = Math.sin(a) * 11 * k;
          }
        }
        out.set(F.ckey(nd.wx, nd.wy), m);
      }
    }
  }

  /* Нитка между узлами. Дышит, местами истончается до полного исчезновения и
     плывёт за курсором. Взятые куски видны ясно, невзятые — только рядом с
     курсором и урывками: нитка должна намекать на связь, а не выдавать
     порядок целиком, иначе крен узлов теряет смысл. */
  function threadPath(ax, ay, bx, by, sd, pull) {
    var pts = [], N = 16;
    var dx = bx - ax, dy = by - ay;
    var len = Math.sqrt(dx * dx + dy * dy) || 1;
    var nx = -dy / len, ny = dx / len;
    for (var i = 0; i <= N; i++) {
      var u = i / N;
      var x = ax + dx * u, y = ay + dy * u;
      var w = Math.sin(u * 3.1 + t * 0.85 + sd) * 0.62
            + Math.sin(u * 7.7 - t * 1.35 + sd * 2.1) * 0.3;
      var amp = Math.sin(u * Math.PI) * (9 + len * 0.02);
      x += nx * w * amp; y += ny * w * amp;
      if (pull) {
        var px = Pointer.x - x, py = Pointer.y - y;
        var pd = Math.sqrt(px * px + py * py) || 1e-4;
        if (pd < 160) {
          var k = Math.pow(1 - pd / 160, 2) * 30;
          x += px / pd * k; y += py / pd * k;
        }
      }
      pts.push({ x: x, y: y, u: u });
    }
    return pts;
  }

  function strokeThread(pts, base, sd) {
    for (var i = 0; i < pts.length - 1; i++) {
      var u = pts[i].u;
      var n = Math.sin(u * 12.3 + t * 0.7 + sd * 3.3) * 0.5
            + Math.sin(u * 27.1 - t * 1.15 + sd) * 0.5;
      var a = base * Math.max(0, 0.18 + n);
      if (a <= 0.012) continue;
      ctx.strokeStyle = 'rgba(255,206,150,' + Math.min(0.9, a) + ')';
      ctx.lineWidth = 0.55 + a * 1.5;
      ctx.beginPath();
      ctx.moveTo(pts[i].x, pts[i].y);
      ctx.lineTo(pts[i + 1].x, pts[i + 1].y);
      ctx.stroke();
    }
  }

  function drawThreads(list) {
    if (!list) { if (phase !== PHASE.ANALYZE) return; list = chains; }
    if (!list.length) return;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineCap = 'round';
    for (var c = 0; c < list.length; c++) {
      var ch = list[c];
      if (ch.done) continue;
      for (var i = 0; i < ch.nodes.length - 1; i++) {
        var a = F.cellCenter(ch.nodes[i].wx, ch.nodes[i].wy);
        var b = F.cellCenter(ch.nodes[i + 1].wx, ch.nodes[i + 1].wy);
        var taken = i < ch.at - 1;
        var base = 0.5;
        if (!taken) {
          // невзятый кусок виден только около курсора и очень слабо
          var mx = (a.x + b.x) / 2 - Pointer.x, my = (a.y + b.y) / 2 - Pointer.y;
          var md = Math.sqrt(mx * mx + my * my);
          if (md > 330) continue;
          base = 0.26 * (1 - md / 330);
        }
        strokeThread(threadPath(a.x, a.y, b.x, b.y, c * 3.7 + i, !taken), base, c + i * 1.7);
      }
    }
    ctx.restore();
  }

  function analyzeHit(x, y) {
    var best = null, bd = (TOL * 1.35) * (TOL * 1.35);
    for (var c = 0; c < chains.length; c++) {
      var ch = chains[c];
      if (ch.done) continue;
      for (var i = 0; i < ch.nodes.length; i++) {
        var p = F.cellCenter(ch.nodes[i].wx, ch.nodes[i].wy);
        var dx = p.x - x, dy = p.y - y, d2 = dx * dx + dy * dy;
        if (d2 < bd) { bd = d2; best = { ci: c, ni: i, x: p.x, y: p.y }; }
      }
    }
    return best;
  }

  /* Связка уходит в сосуд не россыпью: первой летит голова, а остальных она
     тянет за собой на той же нитке. Нитка резиновая, поэтому хвост идёт
     пружинящей волной и догоняет голову уже у самого сосуда. */
  function launchTrain(cells, fi, onDone, essence) {
    var fp = folderPos(fi);
    var pts = [];
    for (var i = 0; i < cells.length; i++) {
      var p = F.cellCenter(cells[i].wx, cells[i].wy);
      pts.push({ x: p.x, y: p.y, vx: 0, vy: 0, id: F.glyphAt(cells[i].wx, cells[i].wy), rung: false, fade: 1 });
    }
    trains.push({
      pts: pts, fi: fi, t: 0, age: 0, dur: 0.8 + Math.random() * 0.2, rung: false,
      onDone: onDone, essence: !!essence,
      bez: {
        x0: pts[0].x, y0: pts[0].y,
        cx: (pts[0].x + fp.x) / 2 + (Math.random() - 0.5) * 200,
        cy: Math.min(pts[0].y, fp.y) - 90 - Math.random() * 110,
        x1: fp.x, y1: fp.y - 4
      }
    });
  }

  function stepTrains(dt) {
    for (var i = trains.length - 1; i >= 0; i--) {
      var tr = trains[i];
      tr.t = Math.min(1, tr.t + dt / tr.dur);
      var u = tr.t, e = u < 0.5 ? 4 * u * u * u : 1 - Math.pow(-2 * u + 2, 3) / 2;
      var b = tr.bez, m = 1 - e;
      var h = tr.pts[0];
      h.x = m * m * b.x0 + 2 * m * e * b.cx + e * e * b.x1;
      h.y = m * m * b.y0 + 2 * m * e * b.cy + e * e * b.y1;

      /* Пружина почти критическая: нить должна ЧУТЬ отзываться, а не болтаться.
         Первая версия была сильно недодемпфированной, и хвост шёл рывками,
         подолгу догоняя голову. */
      /* После прихода головы длина покоя сходит к нулю, и хвост втягивается
         в сосуд. Раньше он вставал в двадцати четырёх пикселях от цели за
         каждым предыдущим и потому никогда до сосуда не доезжал: связка
         висела столбиком, а потом пропадала разом. */
      var pull = tr.t >= 1 ? Math.max(0, 1 - tr.age / 0.55) : 1;
      var REST = 24 * pull, W0 = 26, Z = 0.92;
      for (var j = 1; j < tr.pts.length; j++) {
        var a = tr.pts[j - 1], q = tr.pts[j];
        var dx = a.x - q.x, dy = a.y - q.y;
        var d = Math.sqrt(dx * dx + dy * dy) || 1e-4;
        var tx = a.x - dx / d * REST, ty = a.y - dy / d * REST;
        q.vx += (W0 * W0 * (tx - q.x) - 2 * Z * W0 * q.vx) * dt;
        q.vy += (W0 * W0 * (ty - q.y) - 2 * Z * W0 * q.vy) * dt;
        q.x += q.vx * dt; q.y += q.vy * dt;
        if (!q.rung && Math.abs(q.x - b.x1) < 30 && Math.abs(q.y - b.y1) < 30) {
          q.rung = true; S.tick(j, tr.pts.length);
        }
      }
      // всё, что дошло до сосуда, плавно в нём растворяется
      if (tr.t >= 1) {
        for (var w = 0; w < tr.pts.length; w++) {
          var pp = tr.pts[w];
          var ddx = pp.x - b.x1, ddy = pp.y - b.y1;
          var close = ddx * ddx + ddy * ddy < 44 * 44;
          if (close || tr.age > 0.5) pp.fade = Math.max(0, pp.fade - dt * 2.3);
        }
      }
      if (!h.rung && tr.t > 0.96) { h.rung = true; S.tick(0, tr.pts.length); }

      if (tr.t >= 1) {
        tr.age += dt;
        var gone = true;
        for (var z = 0; z < tr.pts.length; z++) if (tr.pts[z].fade > 0.02) { gone = false; break; }
        if (gone || tr.age > 1.6) {
          if (!tr.rung) { tr.rung = true; folderFlare[tr.fi] = 1; S.knock(); }
          trains.splice(i, 1);
          if (tr.onDone) tr.onDone();
        }
      }
    }
  }

  function drawTrains() {
    if (!trains.length) return;
    var atlas = F.atlas, box = F.atlasBox;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineCap = 'round';
    for (var i = 0; i < trains.length; i++) {
      var tr = trains[i], pts = tr.pts;
      for (var j = 0; j < pts.length - 1; j++) {
        strokeThread(threadPath(pts[j].x, pts[j].y, pts[j + 1].x, pts[j + 1].y, j + i, false), 0.62, j);
      }
      for (var k = 0; k < pts.length; k++) {
        var pt = pts[k];
        if (pt.fade <= 0.02) continue;
        if (tr.essence) {
          // не знаки, а их данные: белые точки на нитке
          var r = 3.4 * pt.fade * (1 - tr.t * 0.3) + 0.8;
          ctx.globalAlpha = pt.fade;
          ctx.fillStyle = 'rgba(255,246,228,0.95)';
          ctx.beginPath(); ctx.arc(pt.x, pt.y, r, 0, Math.PI * 2); ctx.fill();
          ctx.beginPath(); ctx.arc(pt.x, pt.y, r * 2.6, 0, Math.PI * 2);
          ctx.fillStyle = 'rgba(255,232,190,0.14)'; ctx.fill();
        } else {
          var sc = 1.15 * (1 - tr.t * 0.6);
          var w = box * sc;
          ctx.globalAlpha = Math.max(0, (1 - tr.t * 0.45)) * pt.fade;
          atlas.draw(ctx, pt.id, pt.x - w / 2, pt.y - w / 2, w, w);
        }
      }
    }
    ctx.restore();
  }

  function completeChain(ci) {
    var ch = chains[ci];
    ch.done = true;
    ch.unit.stage = 1;
    stageDone(PHASE.ANALYZE, ch.unit);
    syncFolders();
    /* Знаки с поля не исчезают: они оседают вдвое и блёкнут, потому что из них
       уже всё взято. В папку улетают не они, а ЭССЕНЦИЯ — светящиеся точки на
       той же нитке. Раньше в папку летели сами знаки, и выходило, что анализ
       ничего на поле не меняет. */
    // блёкнут только средние узлы: крайние ещё пойдут в сортировку
    for (var i = 1; i < ch.nodes.length - 1; i++) {
      F.setSpent(F.ckey(ch.nodes[i].wx, ch.nodes[i].wy));
    }
    launchTrain(ch.nodes, PHASE.ANALYZE, null, true);
    // оба конца цепочки — знаки-якоря, прошедшие анализ: в хранилище
    var byMe = humanActive() ? 'p' : 'c';
    INV.add({ k: 'glyph', g: ch.unit.gid, kind: ch.unit.kind, by: byMe });
    INV.add({ k: 'glyph', g: ch.unit.gid, kind: ch.unit.kind, by: byMe });
    act(PHASE.ANALYZE);
    var left = chains.filter(function (q) { return !q.done; });
    if (!left.length) {
      chains = []; marks.clear(); F.setMarks(null);
      phase = PHASE.NONE;              // цепочки кончились, этап отработал
    }
  }

  /* Старое существо на анализе иногда сбивается: тянется к чужому узлу,
     получает ошибку и начинает цепочку заново. Не больше двух раз за анализ.
     В самом первом показе оно ошибается обязательно, один раз: так игрок
     видит, как ошибка улетает серой точкой. */
  function curChain() {
    for (var i = 0; i < chains.length; i++) if (!chains[i].done && chains[i].at < chains[i].nodes.length) return chains[i];
    return null;
  }
  function slipTarget() {
    var c = curChain();
    if (!c || slips >= 2) return null;
    var must = !!(tut && !tut.anaErr && controlAt === Infinity && c.at >= 1);
    if (!must && !(Math.random() < 0.1 * oldness())) return null;
    var wi = c.at + 1 < c.nodes.length ? c.at + 1 : c.at - 1;
    if (wi < 0) return null;
    return { c: c, wx: c.nodes[wi].wx, wy: c.nodes[wi].wy };
  }
  function slipAt(sl) {
    if (!sl || sl.c.done) return;
    slips++;
    if (tut) tut.anaErr = true;
    var p = F.cellCenter(sl.wx, sl.wy);
    analyzePick(p.x, p.y);
    sl.c.at = 0; sl.c.miss = 0;
    S.unravel();
  }

  function analyzePick(x, y) {
    var h = analyzeHit(x, y);
    if (!h) { S.nothing(); return; }
    var ch = chains[h.ci];
    if (h.ni === ch.at) {
      ch.at++;
      pulses.push({ x: h.x, y: h.y, age: 0, strong: true });
      S.chain(ch.at, ch.nodes.length);
      if (ch.at >= ch.nodes.length) completeChain(h.ci);
      return;
    }
    // промах по узлу — ошибка этапа
    errors++;
    S.reject(); reject = 1;
    stageError(PHASE.ANALYZE, x, y, 1);

    /* Перебором цепочку не взять. Три промаха, и она распускается целиком:
       иначе можно было бы просто тыкать во все узлы подряд, пока не попадёшь,
       и крен узлов оказался бы декорацией. */
    ch.miss = (ch.miss || 0) + 1;
    if (ch.miss >= CHAIN_MISS) {
      ch.miss = 0; ch.at = 0;
      S.unravel(); reject = 1;
    }
  }

  // --- сортировка ------------------------------------------------------------
  /* Мини-игра живёт в src/sort.js. Здесь только связь с этапами и папками. */

  var SZ = root.Sort, PG = root.Purge;
  var sortRes = null;
  var sortBtn = { x: 0, y: 0, r: 21, hot: 0 };

  var sortUnits = [], purgeUnits = [];

  /* Блок сортировки — это НАЙДЕННОЕ место на карте, а не новый набор знаков.
     Ищем ближайшую область, где нужное начертание встречается достаточно раз,
     и подгоняем под неё масштаб. Раньше нажатие просто рождало новый блок в
     центре экрана и стирало всё, что там было. */
  function sortBegin() {
    var pend = unitsAt(1);
    sortUnits = [];
    if (!pend.length) return;
    stageRun(PHASE.SORT);

    /* Берём место на карте, где нужное начертание уже есть хоть в каком-то
       числе, а недостающие дубли прилетают из папки. Требовать, чтобы вся
       группа лежала на поле готовой, оказалось неудобно: такие места редки, и
       блок выходил вымученным. */
    var gid = pend[0].gid;
    var gids = [gid];
    sortUnits = [pend[0]];
    for (var i = 1; i < pend.length && gids.length < 3; i++) {
      if (gids.indexOf(pend[i].gid) < 0) { gids.push(pend[i].gid); sortUnits.push(pend[i]); }
    }

    /* Блок растёт по числу групп: под один знак огромная зона не нужна.
       Ставится он ЗДЕСЬ ЖЕ, в пределах видимого поля, и камера никуда не
       прыгает: прыжок читался как телепортация существа на другой конец
       карты. Искать по карте место с готовыми дублями больше не надо —
       недостающие прилетают из папки. */
    var size = [[11, 8], [14, 10], [16, 11]][gids.length - 1];
    var bw = size[0], bh = size[1];
    var zNeed = Math.min(1, (vw - 120) / (bw * 54), (vh - 230) / (bh * 54));
    if (F.zoom > zNeed) F.easeZoom(zNeed);

    var c = F.camCell;
    var fitW = vw / F.CELL, fitH = (vh - 140) / F.CELL;
    /* Место под доской выбирается из нескольких в пределах экрана: там, где
       меньше всего неподвижных знаков. Пустота вечна, и доска, легшая на
       старый сбор, превращалась в лабиринт из стен. */
    var reg = null, bestSp = Infinity;
    for (var tryR = 0; tryR < 14; tryR++) {
      var cand = {
        ox: Math.round(c.x + Math.max(0, fitW - bw) * (0.12 + Math.random() * 0.76)),
        oy: Math.round(c.y + Math.max(0, fitH - bh) * (0.12 + Math.random() * 0.76)),
        w: bw, h: bh, n: 0
      };
      var sp = 0;
      for (var yy = 0; yy < bh; yy++) for (var xx = 0; xx < bw; xx++) {
        var qx = (cand.ox + xx + F.W) % F.W, qy = (cand.oy + yy + F.H) % F.H;
        // пустота на доске подвижна и мешает мало, прочие особые знаки — стены
        if (F.isSpecial(qx, qy)) sp += F.isVoidCell(qx, qy) ? 0.25 : 1;
        if (F.objAt(qx, qy)) sp += 50;
      }
      if (sp < bestSp) { bestSp = sp; reg = cand; }
      if (!sp) break;
    }
    // недособранная раньше группа повторяется ровно на свой остаток
    var wants = sortUnits.map(function (u) { return u.sortWant || rollWant(); });
    SZ.build(F, vw, vh, reg, gids, wants);
    sortBtn.live = false;
    launchInject();
    sortRes = null;
  }

  /* Недостающие знаки вылетают из папки анализа и занимают места в блоке,
     замещая то, что там лежало. */
  var inject = [];

  function launchInject(slot) {
    inject = [];
    var list = SZ.inject || [];
    var fp = folderPos(slot === undefined ? PHASE.ANALYZE : slot);
    for (var k = 0; k < list.length; k++) {
      var p = SZ.cellScreen(list[k].i);
      inject.push({
        i: list[k].i, gid: list[k].gid,
        x0: fp.x, y0: fp.y - 12, x1: p.x, y1: p.y,
        cx: (fp.x + p.x) / 2 + (Math.random() - 0.5) * 280,
        cy: Math.min(fp.y, p.y) - 130 - Math.random() * 110,
        d: k * 0.13, dur: 0.85 + Math.random() * 0.25, t: 0, landed: false
      });
    }
  }

  function stepInject(dt) {
    for (var i = inject.length - 1; i >= 0; i--) {
      var f = inject[i];
      f.d -= dt;
      if (f.d > 0) continue;
      f.t += dt / f.dur;
      if (f.t >= 1 && !f.landed) { f.landed = true; SZ.land(f.i); S.tick(i, inject.length); }
      if (f.t >= 1.3) inject.splice(i, 1);
    }
  }

  function drawInject() {
    if (!inject.length) return;
    var atlas = F.atlas, box = F.atlasBox;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (var i = 0; i < inject.length; i++) {
      var f = inject[i];
      if (f.d > 0) continue;
      var u = Math.min(1.3, f.t);
      var e = Math.min(1, u) , m = 1 - e;
      var x = m * m * f.x0 + 2 * m * e * f.cx + e * e * f.x1;
      var y = m * m * f.y0 + 2 * m * e * f.cy + e * e * f.y1;
      if (u < 0.82) {
        // летит эссенцией, как и всё, что ходит между полем и папками
        var r = 3.6 + Math.sin(u * 9) * 0.6;
        ctx.globalAlpha = 0.95;
        ctx.fillStyle = 'rgba(255,246,228,0.95)';
        ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill();
        ctx.fillStyle = 'rgba(255,232,190,0.16)';
        ctx.beginPath(); ctx.arc(x, y, r * 2.8, 0, Math.PI * 2); ctx.fill();
      } else {
        // у самой клетки разворачивается в знак
        var k = Math.min(1, (u - 0.82) / 0.45);
        var w = box * (0.5 + k * 0.6);
        ctx.globalAlpha = Math.max(0, 1 - Math.max(0, u - 1) / 0.3);
        atlas.draw(ctx, f.gid, x - w / 2, y - w / 2, w, w);
      }
    }
    ctx.restore();
  }

  function sortFinish() {
    if (!SZ.active() || SZ.finishing()) return;
    sortRes = SZ.finish();
    S.sorted(0, 3);
  }

  /* Размер группы: обычно три-четыре знака, изредка пять, совсем редко шесть. */
  function rollWant() {
    var r = Math.random();
    if (r < 0.002) return 6;
    if (r < 0.03) return 5;
    return r < 0.515 ? 3 : 4;
  }

  function sortSettle() {
    var rc = SZ.rect();
    SZ.commit();
    var r = sortRes; sortRes = null;
    phase = PHASE.NONE;                 // этап отработал, возвращаемся в свободный режим
    if (!r) return;

    // собрано не всё или группы сомкнулись — ошибка этапа; сомкнувшиеся дают две точки
    var failed = !!r.glitches || (r.groups || []).some(function (g) { return !g.done; });
    if (failed) stageError(PHASE.SORT, rc ? (rc.x0 + rc.x1) / 2 : vw / 2, rc ? rc.y0 + 20 : vh / 2, r.glitches ? 2 : 1);

    // одна собранная без глюков группа — одна единица, ровно та цепочка,
    // что пришла с анализа
    var got = 0;
    for (var u = 0; u < sortUnits.length; u++) {
      var gr = null;
      for (var q = 0; q < (r.groups || []).length; q++) if (r.groups[q].id === sortUnits[u].gid) gr = r.groups[q];
      if (gr && gr.done) { sortUnits[u].stage = 2; sortUnits[u].sortWant = null; stageDone(PHASE.SORT, sortUnits[u]); got++; }
      // недособранная: запомнить остаток, повтор будет ровно на него
      else if (gr) sortUnits[u].sortWant = Math.max(2, gr.need - gr.got + 1);
    }
    syncFolders();
    if (got > 0) {
      folderFlare[PHASE.SORT] = 1;
      S.knock();
      act(PHASE.SORT);
      /* Форма собранного — главная ловушка этапа. Линия проходит как «без
         ошибки», но для корабля она всё равно неправильная, и шкала чуть
         двинется. У порога есть запас: плотный блок, пусть и не идеальный
         геометрически, не стоит НИЧЕГО. */
      nudge(Math.max(0, 0.82 - r.shape) / 0.82 * 3.4);
    }
    if (got < r.total) { nudge((r.total - got) * 1.4); S.reject(); }
    // соприкоснувшиеся группы дали якоря-глюки: они остались на поле
    if (r.glitches) nudge(r.glitches * 0.9);
  }

  /* Остаток работы на текущей единице: линия в папке анализа ровно такой
     длины, насколько сортировка НЕ закончена. По ходу финальной подсветки
     она тает вместе с загорающимися связками. */
  var analyzeRem = 1;

  function stepSort(dt) {
    if (phase !== PHASE.SORT || !SZ.active()) {
      analyzeRem = 1;
      if (phase !== PHASE.SORT) button = button === sortBtn ? null : button;
      return;
    }
    // кнопка за пределами доски, у ближайшей к курсору кромки, плавно едет за ним
    var tg = outsidePoint(SZ.rect(), Pointer.x, Pointer.y, 36);
    if (!sortBtn.live) { sortBtn.x = tg.x; sortBtn.y = tg.y; sortBtn.live = true; }
    else { var bk = Math.min(1, dt * 5); sortBtn.x += (tg.x - sortBtn.x) * bk; sortBtn.y += (tg.y - sortBtn.y) * bk; }
    sortBtn.r = 21;
    button = SZ.finishing() ? null : sortBtn;

    analyzeRem = 1 - SZ.doneUnits() / Math.max(1, SZ.units);
    if (SZ.finishing()) {
      analyzeRem *= 1 - SZ.finishProgress() * 0.6;
      if (SZ.finishDone()) { sortSettle(); button = null; }
    }
  }

  // --- утилизация ------------------------------------------------------------

  var purgeDrain = 0;

  /* Утилизируем ровно те знаки, что лежали в цепочке между первым и последним.
     Крайние остаются: по ним собиралась группа на сортировке. */
  function purgeBegin() {
    var pend = unitsAt(2);
    purgeUnits = [];
    if (!pend.length) return;
    stageRun(PHASE.PURGE);
    lastSplits = 0;
    // папка утилизации полна: сперва её надо опустошить кнопкой
    if (unitsAt(3).length >= FOLDER_CAP) { S.reject(); reject = 0.6; phase = PHASE.NONE; return; }
    var cells = [];
    for (var i = 0; i < Math.min(3, pend.length); i++) {
      /* После переезда цепочка единицы лежит на старой карте. На новом месте
         она находится заново: утилизировать чужую карту нечем. */
      if (!pend[i].chain || pend[i].map !== mapId) { pend[i].chain = chainFor(pend[i]); pend[i].map = mapId; }
      var ch = pend[i].chain || [];
      for (var k = 1; k < ch.length - 1; k++) if (!F.isGone(ch[k].wx, ch[k].wy)) cells.push(ch[k]);
      purgeUnits.push(pend[i]);
    }
    if (!cells.length) {
      /* Единица без цепочки утилизировать нечем. Раньше она застревала
         навсегда: этап звался снова и снова, доска не строилась, и вся игра
         вставала намертво. Теперь такая единица просто уходит из оборота. */
      for (var q = 0; q < purgeUnits.length; q++) purgeUnits[q].stage = 3;
      purgeUnits = [];
      syncFolders();
      phase = PHASE.NONE;
      return;
    }
    PG.build(F, cells);
  }

  function stepPurge(dt) {
    if (purgeDrain > 0) {
      purgeDrain -= dt;
      if (purgeDrain <= 0) {
        // папка утилизации опустошает себя сама: единица уходит из оборота
        for (var d = 0; d < stock.length; d++) {
          if (stock[d].stage === 3) { stock.splice(d, 1); break; }
        }
        syncFolders();
        folderFlare[PHASE.PURGE] = 1;
        S.dissolve();
        if (folders[PHASE.PURGE] > 0) purgeDrain = 0.45;
      }
    }
    if (phase !== PHASE.PURGE || !PG.built()) return;
    PG.step(dt);
    var prs = PG.progress();
    // передержанный знак расщепился — ошибка этапа
    if ((prs.splits || 0) > lastSplits) { lastSplits = prs.splits; stageError(PHASE.PURGE, Pointer.x, Pointer.y, 1); }
    if (prs.frac < 1) return;

    var r = PG.progress();
    PG.commit();
    for (var u = 0; u < purgeUnits.length; u++) { purgeUnits[u].stage = 3; stageDone(PHASE.PURGE, purgeUnits[u]); }
    purgeUnits = [];
    syncFolders();
    folderFlare[PHASE.PURGE] = 1;
    act(PHASE.PURGE);
    // расщеплённые знаки остались на поле осколками, и корабль это заметил
    if (r.splits) nudge(r.splits * 1.1);
    phase = PHASE.NONE;
  }

  /* Кнопка утилизации. Утилизированное копится в последней папке, пока его не
     сбросят этой кнопкой. Раньше папка опустошала себя сама. */
  var flushFlare = 0;

  function flushPos() {
    var p = folderPos(PHASE.PURGE);
    return { x: p.x + 66, y: p.y - 4, r: 15 };
  }

  function flushHit(x, y) {
    var b = flushPos();
    return Math.hypot(x - b.x, y - b.y) < b.r + 10;
  }

  function flush() {
    if (purgeDrain > 0 || !unitsAt(3).length) { S.nothing(); return false; }
    purgeDrain = 0.3;
    flushFlare = 1;
    S.flush();
    cycleDone();
    /* Круг закончен — сразу включается сбор. Новички после показа не понимали,
       что первый этап надо включить самим, и бродили по карте в свободном
       режиме, ничего не видя. Свободный режим теперь нужен только для пульта
       команд. */
    if (phase !== PHASE.COLLECT && !busyNav()) setPhase(PHASE.COLLECT);
    return true;
  }

  function drawFlush() {
    if (panel !== 0) return;
    var b = flushPos(), n = unitsAt(3).length, drain = purgeDrain > 0;
    var ready = n > 0 && !drain;
    var over = ready && Math.hypot(Pointer.x - b.x, Pointer.y - b.y) < b.r + 10;
    var pulse = 0.5 + 0.5 * Math.sin(t * 2.4);
    var a = ready ? 0.55 + pulse * 0.3 + (over ? 0.2 : 0) : drain ? 0.6 : 0.16;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.translate(b.x, b.y);
    var r = b.r * (1 + flushFlare * 0.18 + (over ? 0.08 : 0));
    ctx.strokeStyle = 'rgba(255,226,180,' + a + ')';
    ctx.lineWidth = 1.4 + flushFlare;
    // та же линза, что у кнопки отправки, но стоящая поперёк
    ctx.beginPath();
    ctx.moveTo(-r, 0);
    ctx.quadraticCurveTo(0, r * 1.15, r, 0);
    ctx.quadraticCurveTo(0, -r * 1.15, -r, 0);
    ctx.stroke();
    // внутри три точки: собраны, пока папка полна, и разлетаются, пока идёт сброс
    var spread = drain ? 0.25 + 0.55 * (0.5 + 0.5 * Math.sin(t * 9)) : 0.18;
    ctx.fillStyle = 'rgba(255,240,215,' + a + ')';
    for (var i = 0; i < 3; i++) {
      var ang = -Math.PI / 2 + i * Math.PI * 2 / 3 + t * (drain ? 3 : 0.4);
      ctx.beginPath();
      ctx.arc(Math.cos(ang) * r * spread, Math.sin(ang) * r * spread * 0.7, 1.6, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.restore();
  }

  // --- переключение этапа ----------------------------------------------------

  /* Какой этап требует работы прямо сейчас. Существо, взяв пульт, идёт именно
     сюда: доделывает брошенное игроком, а не начинает со сбора. Порядок разбора
     обратный служебному, потому что доделывать надо с конца: что дальше всех
     продвинулось, то и ближе к завершению. */
  function needPhase() {
    if (SZ.active()) return PHASE.SORT;
    if (PG.active()) return PHASE.PURGE;
    for (var i = 0; i < chains.length; i++) if (!chains[i].done) return PHASE.ANALYZE;
    if (folders[PHASE.SORT] > 0) return PHASE.PURGE;
    if (folders[PHASE.ANALYZE] > 0) return PHASE.SORT;
    if (folders[PHASE.COLLECT] > 0) return PHASE.ANALYZE;
    return PHASE.COLLECT;
  }

  /* Указатель на материал за краем экрана. Край мягко пульсирует в ту сторону,
     куда надо увести поле. Ни стрелок, ни слов. */
  var guide = null;

  function guideTo(p) {
    if (!p || (p.x > 60 && p.y > 60 && p.x < vw - 60 && p.y < vh - 140)) return;
    guide = p;
  }

  function stepGuide() {
    guide = null;
    if (panel !== 0) return;
    var p = null, i;
    if (phase === PHASE.ANALYZE) {
      for (i = 0; i < chains.length; i++) {
        var ch = chains[i];
        if (ch.done || ch.at >= ch.nodes.length) continue;
        p = F.cellCenter(ch.nodes[ch.at].wx, ch.nodes[ch.at].wy);
        break;
      }
    } else if (phase === PHASE.PURGE && PG.built()) {
      var h = PG.hint();
      if (h) p = { x: h.x, y: h.y };
    }
    if (!p) return;
    if (p.x > 60 && p.y > 60 && p.x < vw - 60 && p.y < vh - 140) return;
    guide = p;
  }

  function drawGuide() {
    if (!guide) return;
    var pulse = 0.5 + 0.5 * Math.sin(t * 2.1);
    var band = 130, a = 0.24 + pulse * 0.30;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    function edge(x, y, w, h, x0, y0, x1, y1) {
      var g = ctx.createLinearGradient(x0, y0, x1, y1);
      g.addColorStop(0, 'rgba(255,206,140,' + a + ')');
      g.addColorStop(0.45, 'rgba(255,190,120,' + a * 0.35 + ')');
      g.addColorStop(1, 'rgba(255,190,120,0)');
      ctx.fillStyle = g;
      ctx.fillRect(x, y, w, h);
    }
    if (guide.x <= 60) edge(0, 0, band, vh, 0, 0, band, 0);
    if (guide.x >= vw - 60) edge(vw - band, 0, band, vh, vw, 0, vw - band, 0);
    if (guide.y <= 60) edge(0, 0, vw, band, 0, 0, 0, band);
    if (guide.y >= vh - 140) edge(0, vh - band, vw, band, 0, vh, 0, vh - band);
    ctx.restore();
  }

  function folderHit(x, y) {
    for (var i = 0; i < 4; i++) {
      var p = folderPos(i);
      if (Math.abs(x - p.x) < 44 && y > p.y - 70 && y < p.y + 34) return i;
    }
    return -1;
  }

  var spinDrag = null;

  function spinTarget(x, y) {
    var c = F.cellNear(x, y);
    if (!c || c.d > TOL || !F.isSorted(c.wx, c.wy) || F.isSpecial(c.wx, c.wy)) return null;
    return c;
  }

  function dropSpin(x, y) {
    var d = spinDrag, c = spinTarget(x, y);
    spinDrag = null;
    if (!c) { S.reject(); reject = 0.4; return; }
    F.moveSpin(F.ckey(d.wx, d.wy), F.ckey(c.wx, c.wy));
    var ol = F.outlineAt(c.wx, c.wy);
    // фигура в хранилище меняется так же: внутри неё теперь крутится этот знак
    var shp = ol ? INV.byId(ol.invId) : null;
    if (shp && INV.setShapeSpin(shp, c.wx, c.wy, d.g)) INV.removeOne('spin', d.g);
    pulses.push({ x: c.x, y: c.y, age: 0, strong: true });
    S.putDown(); S.bloom();
  }

  function drawSpinDrag() {
    if (!spinDrag) return;
    var tg = spinTarget(Pointer.x, Pointer.y), box = F.atlasBox;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    if (tg) {
      ctx.strokeStyle = 'rgba(255,236,200,0.9)';
      ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(tg.x, tg.y, F.CELL * 0.48, 0, Math.PI * 2); ctx.stroke();
    }
    ctx.translate(Pointer.x, Pointer.y);
    ctx.rotate(t * 1.9);
    ctx.globalAlpha = 0.95;
    F.atlas.draw(ctx, spinDrag.g, -box / 2, -box / 2, box, box);
    ctx.restore();
  }

  function setPhase(p) {
    spinDrag = null;
    /* Повторное нажатие по уже выбранному этапу ПЕРЕЗАПУСКАЕТ его, если работы
       там сейчас нет. Без этого существо, оказавшись на пустом этапе, звало
       его снова и снова, получало ранний выход и зацикливалось. Начатую работу
       повторное нажатие не трогает. */
    if (p === phase) {
      if (p === PHASE.ANALYZE && chains.length) return;
      if (p === PHASE.SORT && SZ.active()) return;
      if (p === PHASE.PURGE && PG.built()) return;
    }
    phase = p;
    chains = []; marks.clear(); F.setMarks(null);
    if (SZ.active()) SZ.commit();      // уходим с этапа — знаки остаются как есть
    // нечего анализировать без мусора, нечего сортировать без анализа:
    // этап откроется, но поле останется пустым
    if (PG.built()) PG.commit();
    if (p === PHASE.ANALYZE) buildChains();
    if (p === PHASE.SORT) sortBegin();
    if (p === PHASE.PURGE) purgeBegin();
    S.phase(p);
  }

  /* Нажатие на сосуд уже выбранного этапа снимает этап: игра уходит в
     свободный режим. Только из него и открывается ввод команды. */
  function deactivate(quiet) {
    if (phase === PHASE.NONE) return;
    phase = PHASE.NONE;
    chains = []; marks.clear(); F.setMarks(null);
    if (SZ.active()) SZ.commit();
    if (PG.built()) PG.commit();
    inject = [];
    button = null;
    if (!quiet) S.consoleOff();
  }

  function busyNav() {
    return (phase === PHASE.ANALYZE && chains.length > 0)
        || (phase === PHASE.SORT && SZ.active())
        || (phase === PHASE.PURGE && PG.built());
  }

  // --- круг, передача пульта, выброс ------------------------------------------

  var shake = 0;                       // дёрганье экрана
  var tearPulse = 0, tearFx = 0;       // сила срыва картинки
  var handover = null, cycles = 0;
  var eject = null;

  /* Единица прошла все четыре этапа. Первый такой круг в игре заканчивает
     заставку: пульт с сильными помехами переходит к игроку. */
  function cycleDone() {
    cycles++;
    // обучение: считаются только круги, которые игрок закрыл сам
    if (tut && ctrl() && humanActive()) { tut.cycles++; if (tut.cycles === TUT_CYCLES) tut.t3 = tut.play; }
    if (controlAt === Infinity && !handover && !eject) {
      handover = { t: 0 };
      S.handover();
      LORE.ship('handover');
    }
  }

  function stepHandover(dt) {
    if (!handover) return;
    handover.t += dt;
    var h = handover.t, k;
    if (h < 0.25) k = h / 0.25;
    else if (h < 1.5) k = 0.7 + 0.3 * Math.random();
    else k = Math.max(0, 1 - (h - 1.5) / 0.9);
    tearFx = Math.max(tearFx, k);
    if (h >= 1.1 && controlAt === Infinity) { controlAt = t; scheduleBreaks(); }
    if (h >= 2.4) handover = null;
  }

  /* Потолок скрытой шкалы. Корабль ещё не встречался с таким вмешательством
     и не спешит избавляться от существа: первые три выброса потолок почти не
     меняется, дальше опускается всё заметнее. */
  function driftMax() {
    if (DRIFT_FIXED) return DRIFT_FIXED;
    var d = LORE.ejects();
    return d < 3 ? 320 - d * 10 : Math.max(60, 290 * Math.pow(0.8, d - 2));
  }

  /* Предупреждения. Когда шкала переваливает за половину, корабль начинает
     нервничать: стон металла, помехи по краю экрана, короткие срывы. Чем
     ближе к потолку, тем чаще и сильнее. На трёх порогах — запись в журнал. */
  var edgePulse = 0, warnT = 0, warnFlags = {};

  function stepDefect(dt) {
    if (eject || !ctrl() || tut) return;
    var f = drift / driftMax();
    [[0.6, 'defect_rising'], [0.8, 'defect_high'], [0.95, 'defect_critical']].forEach(function (th) {
      if (f >= th[0] && !warnFlags[th[0]]) { warnFlags[th[0]] = true; LORE.ship(th[1]); }
    });
    if (f < 0.5) { warnT = 0; return; }
    warnT -= dt;
    if (warnT > 0) return;
    var k = Math.min(1, (f - 0.5) * 2);
    warnT = 45 - 38 * k + Math.random() * 6;
    edgePulse = Math.max(edgePulse, 0.25 + 0.55 * k);
    tearPulse = Math.max(tearPulse, 0.08 + 0.3 * k);
    shake = Math.max(shake, 0.1 + 0.4 * k);
    S.defectWarn(f);
  }

  /* Жизнь существа. Каждое существо стареет само: за LIFE (10 часов работы)
     оно изнашивается, и корабль утилизирует его — штатно, как любое другое.
     С 70% жизни существо заметно медленнее и ошибается чаще, с 80% до 90%
     разрушается верхняя панель, после 90% ею пользоваться нельзя. Обычный
     игрок этого не увидит: ошибки копят шкалу изъяна, и существо уходит
     намного раньше. Игрок без ошибок существу жизнь не сокращает.

     Первое подключение — к старому существу, доживающему цикл: оно медленное,
     промахивается, панель разбита. Его утилизируют, когда игрок сам закрыл
     хотя бы три круга и наиграл около пяти с половиной минут; каждый круг
     сверх трёх приближает конец на полминуты, но не раньше четырёх минут, и
     не раньше чем через 40 с после третьего круга. Считается только время,
     когда играет сам игрок: пока он пьёт чай, старик работает сколько угодно. */
  function oldness() { return tut ? 1 : Math.max(0, Math.min(1, (age - 0.7 * LIFE) / (0.3 * LIFE))); }
  function panelDamage() { return tut ? 0.9 : Math.max(0, Math.min(1, (age - 0.8 * LIFE) / (0.1 * LIFE))); }
  function panelLocked() { return !!tut || age >= 0.9 * LIFE; }
  function handSlow() { return tut ? (controlAt === Infinity ? 0.7 : 0.5) : 1 - 0.5 * oldness(); }

  function stepLife(dt) {
    if (eject) return;
    age += dt;
    if (panelLocked() && panel === 1) switchPanel(0, true);
    if (tut) {
      if (humanActive() && panel === 0) tut.play += dt;
      if (tut.cycles >= TUT_CYCLES) {
        var need = Math.max(TUT_MIN, TUT_PLAY - 30 * (tut.cycles - TUT_CYCLES));
        if (tut.play >= need && tut.play >= tut.t3 + TUT_GRACE) endCycle('age');
      }
      return;
    }
    if (age >= 0.8 * LIFE && !lifeFlags.aging) { lifeFlags.aging = true; LORE.ship('aging'); }
    if (age >= LIFE) endCycle('age');
  }

  /* Старое существо видит и слышит хуже. Раз в ~40 с по экрану проходит
     вертикальная помеха, как в старом телевизоре; раз в минуту где-то далеко
     кто-то кашляет, и картинка в такт двоится; весь звук глуше, как через
     подушку. У обычного существа всё это приходит вместе со старостью. */
  var vbar = null, vbarT = 25, cough = null, coughT = 45, muffleSet = -1;

  function stepOldFx(dt) {
    var old = oldness(), m = Math.round(old * 20) / 20;
    if (m !== muffleSet) { muffleSet = m; S.muffle(m); }
    if (vbar) { vbar.t += dt; if (vbar.t >= vbar.dur) vbar = null; }
    if (cough) { cough.t += dt; if (cough.t > cough.end) cough = null; }
    if (old < 0.05 || eject) return;
    vbarT -= dt * old;
    if (vbarT <= 0 && !vbar) {
      vbarT = 32 + Math.random() * 16;
      vbar = { t: 0, dur: 0.8 + Math.random() * 0.5, dir: Math.random() < 0.5 ? 1 : -1, w: 40 + Math.random() * 50 };
      S.crackle(0.6);
    }
    coughT -= dt * old;
    if (coughT <= 0 && !cough) {
      coughT = 50 + Math.random() * 25;
      var pat = [], at = 0, n = 2 + Math.floor(Math.random() * 3);
      for (var i = 0; i < n; i++) {
        var d = 0.22 + Math.random() * 0.18;
        pat.push({ at: at, dur: d, k: 1 - i * 0.12 });
        at += d + 0.08 + Math.random() * 0.28;
      }
      cough = { t: 0, pat: pat, end: at + 0.4 };
      S.cough(pat);
    }
  }

  function coughEnv() {
    if (!cough) return 0;
    var e = 0;
    cough.pat.forEach(function (p) {
      var u = (cough.t - p.at) / p.dur;
      if (u >= 0 && u <= 1) e = Math.max(e, p.k * (u < 0.1 ? u / 0.1 : Math.pow(1 - u, 1.5)));
    });
    return e;
  }

  function drawOldFx() {
    var e = coughEnv();
    if (e > 0.02) {
      // картинка двоится в такт кашлю
      ctx.save();
      ctx.globalAlpha = 0.3 * e;
      ctx.globalCompositeOperation = 'lighter';
      var dx = 4 + 6 * e;
      ctx.drawImage(scene, 0, 0, scene.width, scene.height, dx, dx * 0.3, vw, vh);
      ctx.restore();
    }
    if (!vbar) return;
    var u = vbar.t / vbar.dur, w = vbar.w, span = vw + w * 2;
    var x = vbar.dir > 0 ? -w + u * span : vw + w - u * span, x0 = Math.round(x - w / 2);
    var sx = Math.max(0, Math.min(vw - w, x0));
    ctx.save();
    // кусок кадра под полосой съезжает вниз
    ctx.drawImage(scene, sx * dpr, 0, w * dpr, vh * dpr, x0, 5 + Math.random() * 9, w, vh);
    ctx.globalCompositeOperation = 'lighter';
    var g = ctx.createLinearGradient(x0, 0, x0 + w, 0);
    g.addColorStop(0, 'rgba(255,230,190,0)');
    g.addColorStop(0.5, 'rgba(255,230,190,0.22)');
    g.addColorStop(1, 'rgba(255,230,190,0)');
    ctx.fillStyle = g;
    ctx.fillRect(x0, 0, w, vh);
    ctx.fillStyle = 'rgba(255,240,220,0.32)';
    for (var i = 0; i < 40; i++) ctx.fillRect(x0 + Math.random() * w, Math.random() * vh, 1 + Math.random() * 2, 4 + Math.random() * 44);
    ctx.globalCompositeOperation = 'source-over';
    ctx.fillStyle = 'rgba(0,0,0,0.35)';
    ctx.fillRect(vbar.dir > 0 ? x0 + w : x0 - 3, 0, 3, vh);
    ctx.restore();
  }

  /* Выброс существа. Долгая сцена: минута в первый раз, дальше по двадцать
     секунд.
       1. тревога: помехи по краю экрана, нарастает гул; существо перехватывает
          пульт и суматошно водит курсором по полю;
       2. гул обрывается ударом металлических дверей, и следом вакуум: все
          звуки уходят, остаётся далёкий шум сбрасываемого воздуха;
       3. поле стремительно отдаляется и размывается, веки смыкаются, существо
          пытается их открыть и видит всё хуже, пока не становится темно;
       4. за пульт садится новое существо: глаза открываются, пульт почти сразу
          возвращается игроку. */
  var ejectFx = { scale: 1, blur: 0, lids: 0, edge: 0, dark: 0 };

  function endCycle(reason) {
    if (eject) return;
    if (panel === 1) switchPanel(0, true);
    abort();
    closeConsole(true); conHold = null;
    var D = LORE.firstEject() ? EJECT_FIRST : EJECT_NEXT;
    eject = { t: 0, D: D, reason: reason, door: false, reset: false, panicT: 0, arrival: 0 };
    forced = true;                 // существо перехватывает пульт
    if (reason !== 'drift' && reason !== 'age') S.death();
    S.ejectBegin(D * 0.45);
    /* Первые выбросы для корабля штатны. С пятого — выброс за выбросом — он
       начинает отмечать странность, но причин так и не знает. */
    LORE.ship(reason === 'age' ? 'eject_age'
      : reason === 'drift' ? (LORE.ejects() >= 4 ? 'eject_pattern' : 'eject') : 'death_' + reason);
  }

  function stepEject(dt) {
    if (!eject) return;
    eject.t += dt;
    var e = eject.t, D = eject.D, A = D * 0.45;
    if (!eject.reset) {
      if (e < A) {
        var u = e / A;
        ejectFx.edge = 0.15 + 0.7 * u;
        tearFx = Math.max(tearFx, (Math.random() < 0.06 ? 0.35 : 0.06) * (0.3 + u));
        shake = Math.max(shake, 0.04 + 0.25 * u);
      } else {
        if (!eject.door) {
          eject.door = true;
          S.ejectDoor();
          tearPulse = 1; shake = 1.4;
          F.easeZoom(0.35);
        }
        var v = Math.min(1, (e - A) / (D - A));
        ejectFx.edge = Math.max(0, 0.85 * (1 - v * 4));
        ejectFx.scale = 1 - 0.72 * (1 - Math.pow(1 - v, 2.2));
        ejectFx.blur = Math.min(1, v * 1.4);
        // пытается держать глаза открытыми: веки смыкаются, вздрагивают и снова приоткрываются
        var blink = Math.max(0, Math.sin(e * (0.9 + v * 2.2)));
        ejectFx.lids = Math.min(1, 0.15 + v * 0.8 + blink * 0.3 * v - (1 - v) * 0.15);
        ejectFx.dark = Math.min(1, Math.max(0, (v - 0.55) / 0.45));
      }
      // суматошный курсор: существо мечется по полю
      if (e > D * 0.06) {
        eject.panicT -= dt;
        if (eject.panicT <= 0) {
          eject.panicT = (0.12 + Math.random() * 0.3) * (e < A ? 1 : 1.8);
          hand.to(60 + Math.random() * Math.max(10, vw - 120), 100 + Math.random() * Math.max(10, vh - 260),
                  { speed: 900 + Math.random() * 1000, curve: (Math.random() - 0.5) * 1.8 });
        }
      }
      if (e >= D) {
        eject.reset = true;
        resetCycle();
        S.vacuum(false);
        S.takeover();
      }
      return;
    }
    // новое существо открывает глаза
    eject.arrival += dt;
    var w = Math.min(1, eject.arrival / 3);
    ejectFx.lids = Math.max(0, 1 - w * 1.25);
    ejectFx.dark = Math.max(0, 1 - w * 1.6);
    ejectFx.blur = Math.max(0, 1 - w);
    ejectFx.scale = 0.28 + 0.72 * (1 - Math.pow(1 - w, 3));
    ejectFx.edge = 0;
    tearFx = Math.max(tearFx, 0.35 * (1 - w));
    if (eject.arrival >= 3) {
      ejectFx = { scale: 1, blur: 0, lids: 0, edge: 0, dark: 0 };
      eject = null;
      F.easeZoom(1);
    }
  }

  function resetCycle() {
    abort();
    closeConsole(true); conHold = null;
    deactivate(true);
    stock = []; syncFolders();
    chains = []; trains = []; flying = []; inject = [];
    purgeDrain = 0; purgeUnits = []; sortUnits = [];
    drift = 0; driftFloor = 0; lastPhase = -1; offStreak = 0;
    warnFlags = {}; warnT = 0; edgePulse = 0;
    phase = PHASE.COLLECT;
    lunchDenied = 0; sleepDenied = 0;
    // выброшенное существо уносит с собой всё, что сделало; остаётся только сделанное игроком
    INV.wipe('c');
    var wasTut = !!tut;
    LORE.newCreature(eject ? eject.reason : 'drift');
    tut = null; age = 0; lifeFlags = {};
    /* Капсула только что сменённого существа дрейфует неподалёку. После
       обучения рядом ещё и какой-нибудь астероид, подальше. На четвёртом
       цикле — один раз за игру — заброшенная станция. */
    spawnNear('capsule', 18, 24, LORE.ejected());
    if (wasTut) { var nt = randomNatural(); if (nt) spawnNear(nt, 45, 70); }
    if (LORE.lives() === 4 && !LORE.flag('strange') && spawnNear('station_strange', 28, 40)) LORE.flag('strange', 1);
    forced = false; humanAt = -1e9; handover = null; cycles = 0;
    /* После выброса полная заставка не повторяется: новое существо садится за
       пульт, и почти сразу его можно забрать. Полная заставка — только при
       первом запуске. Раньше пульт ждал, пока новое существо пройдёт целый
       круг, и если оно где-то застревало, игра не отдавала управление. */
    controlAt = t + 2.5;
    scheduleBreaks();
    taken.clear(); reveals.clear();
    hand.x = vw / 2; hand.y = vh / 2; hand.vx = 0; hand.vy = 0;
    Pointer.x = Pointer.tx = hand.x; Pointer.y = Pointer.ty = hand.y;
    creature.rejected = {};
    creature.st = 'resume'; creature.sub = 'go'; creature.timer = 1.5;
  }

  // --- пульт команд ------------------------------------------------------------
  /* В свободном режиме зажатый знак пустоты переводит поле во ввод команды.
     Всё тускнеет, нажатые знаки крупнеют и загораются. Команда — это знаки в
     определённом порядке. Выйти — набрать их задом наперёд и отжать пустоту.

     Команд пока две, и обе нужны существу: обед и сон. Существо уходит само,
     и если игрок выдернет его обратно раньше срока, это отказ. */

  var CMD = root.LoreText.commands;
  var CON_HOLD = 0.9;
  var con = null, conHold = null, conLevel = 0, conIntent = 'lunch';
  var conFx = [];                  // щелчки нажатия и отжатия: уголки вокруг знака
  var lunchDue = Infinity, sleepDue = Infinity, lunchDenied = 0, sleepDenied = 0, breakWait = 0;

  function scheduleBreaks() {
    lunchDue = t + LUNCH_EVERY * (0.9 + Math.random() * 0.2);
    sleepDue = t + SLEEP_EVERY * (0.95 + Math.random() * 0.1);
  }

  function breakDue() {
    // в лорной вкладке существо не прерывает игрока никогда
    if (!ctrl() || con || conHold || eject || move || handover || panel === 1) return null;
    if (t >= sleepDue) return 'sleep';
    if (t >= lunchDue) return 'lunch';
    return null;
  }

  function conPress(v, who) {
    if (con || conHold) return;
    conHold = { wx: v.wx, wy: v.wy, t: 0, who: who };
    S.grip(false);
  }

  function conRelease() {
    if (conHold && !con) S.nothing();
    conHold = null;
  }

  function openConsole(h) {
    con = { wx: h.wx, wy: h.wy, seq: [], rseq: [], dead: [], mode: null, since: 0, dur: 0, revDone: false, age: 0 };
    conHold = null;
    conFx.push({ wx: h.wx, wy: h.wy, age: 0, kind: 'press' });
    S.consoleOn();
    var p = F.cellCenter(h.wx, h.wy);
    pulses.push({ x: p.x, y: p.y, age: 0, strong: true });
  }

  function closeConsole(silent) {
    if (!con) return;
    conFx.push({ wx: con.wx, wy: con.wy, age: 0, kind: 'release' });
    con.seq.forEach(function (k) { if (k.rel === undefined) conFx.push({ wx: k.wx, wy: k.wy, age: 0, kind: 'release' }); });
    con = null; conHold = null;
    marks.clear(); F.setMarks(null);
    if (!silent) S.consoleOff();
  }

  function prefixOf(list, cmd) {
    if (list.length > cmd.length) return false;
    for (var i = 0; i < list.length; i++) if (list[i].gid !== cmd[i]) return false;
    return true;
  }

  function conClick(x, y, who) {
    if (!con) return;
    var c = F.cellNear(x, y);
    if (!c || c.d > TOL * 1.2) { S.nothing(); return; }
    if (c.wx === con.wx && c.wy === con.wy) { conVoid(who); return; }
    if (F.isSpecial(c.wx, c.wy)) { S.nothing(); return; }
    var list = con.mode ? con.rseq : con.seq;
    for (var i = 0; i < list.length; i++) if (list[i].wx === c.wx && list[i].wy === c.wy) { S.nothing(); return; }
    list.push({ wx: c.wx, wy: c.wy, gid: F.glyphAt(c.wx, c.wy), age: 0 });
    if (con.mode) {
      /* Обратный набор ОТЖИМАЕТ знаки прямой команды, с последнего к первому.
         Раньше они так и оставались горящими, хотя по ним уже нажали. */
      var si = con.seq.length - list.length;
      var sk = con.seq[si];
      if (sk && sk.gid === list[list.length - 1].gid) {
        sk.rel = 0;
        conFx.push({ wx: sk.wx, wy: sk.wy, age: 0, kind: 'release' });
        if (sk.wx !== c.wx || sk.wy !== c.wy) conFx.push({ wx: c.wx, wy: c.wy, age: 0, kind: 'press' });
        S.keyRelease(si);
      } else {
        conFx.push({ wx: c.wx, wy: c.wy, age: 0, kind: 'press' });
        S.keyPress(list.length - 1);
      }
    } else {
      conFx.push({ wx: c.wx, wy: c.wy, age: 0, kind: 'press' });
      S.keyPress(list.length - 1);
    }
    if (!con.mode) {
      var hit = null, any = false;
      for (var name in CMD) {
        if (!prefixOf(list, CMD[name])) continue;
        any = true;
        if (list.length === CMD[name].length) hit = name;
      }
      if (!any) { failKeys(list); return; }
      if (hit === 'relocate') { closeConsole(); commandRelocate(); }
      else if (hit) startMode(hit);
    } else {
      var rev = CMD[con.mode].slice().reverse();
      if (!prefixOf(list, rev)) { failKeys(list); return; }
      if (list.length === rev.length) { con.revDone = true; S.keyDone(); }
    }
  }

  function failKeys(list) {
    for (var i = 0; i < list.length; i++) { list[i].age = 0; con.dead.push(list[i]); }
    list.length = 0;
    // сбитый обратный набор снова вдавливает отжатые знаки
    if (con.mode) con.seq.forEach(function (k) { if (k.rel !== undefined) { k.rel = undefined; k.age = 0; } });
    reject = 0.5;
    S.reject();
  }

  function conVoid(who) {
    if (!con.mode) { closeConsole(); return; }
    if (!con.revDone) { S.reject(); reject = 0.4; return; }
    var kind = con.mode, early = t - con.since < con.dur - 0.5;
    closeConsole();
    if (early && who === 'player') deny(kind); else fed(kind);
    forced = false;
    if (creature.st === 'away' || creature.st === 'back') { creature.st = 'resume'; creature.sub = 'go'; creature.timer = 0.5; }
  }

  function startMode(kind) {
    con.mode = kind; con.since = t; con.revDone = false; con.rseq = [];
    con.dur = kind === 'sleep' ? SLEEP_DUR : LUNCH_DUR;
    S.command(kind);
    LORE.ship(kind);
    if (kind === 'lunch') lunchDue = Infinity; else sleepDue = Infinity;
    // кто бы ни набрал команду, существо уходит
    if (creature.st !== 'console') { creature.st = 'away'; creature.sub = 'rest'; }
    forced = false;
    breakWait = 0;
  }

  function fed(kind) {
    if (kind === 'lunch') { lunchDenied = 0; lunchDue = t + LUNCH_EVERY * (0.9 + Math.random() * 0.2); }
    else {
      sleepDenied = 0; sleepDue = t + SLEEP_EVERY;
      if (lunchDue === Infinity) lunchDue = t + LUNCH_EVERY;
      lunchDue = Math.max(lunchDue, t + 90);
    }
  }

  /* Существо выдернули раньше срока. Оно возмущается и садится работать,
     но голод и недосып копятся. */
  function deny(kind) {
    S.indignant();
    LORE.ship(kind + '_denied');
    if (kind === 'lunch') {
      lunchDenied++; lunchDue = t + LUNCH_RETRY;
      if (lunchDenied >= LUNCH_DEATH) endCycle('hunger');
    } else {
      sleepDenied++; sleepDue = t + SLEEP_RETRY;
      if (lunchDue === Infinity) lunchDue = t + LUNCH_RETRY;
      if (sleepDenied >= SLEEP_DEATH) endCycle('sleep');
    }
  }

  /* Нажатый знак сперва проседает, потом выпрыгивает крупнее и оседает. */
  function keyCurve(a) {
    if (a < 0.06) return -0.35 * a / 0.06;
    return 1 + 0.45 * Math.exp(-(a - 0.06) * 10) * Math.cos((a - 0.06) * 24);
  }

  function stepConsole(dt) {
    for (var fx = conFx.length - 1; fx >= 0; fx--) {
      conFx[fx].age += dt;
      if (conFx[fx].age > 0.3) conFx.splice(fx, 1);
    }
    if (conHold && !con) {
      conHold.t += dt;
      if (phase !== PHASE.NONE || sel !== SEL.IDLE) conHold = null;
      else if (conHold.t >= CON_HOLD) openConsole(conHold);
    }
    conLevel += ((con ? 1 : 0) - conLevel) * Math.min(1, dt * (con ? 5 : 2.5));
    F.setConsoleDim(conLevel * 0.74);
    if (!con && !conHold) return;

    if (con) {
      // обед или сон кончился: существо возвращается и забирает пульт
      if (con.mode && creature.st === 'away' && t - con.since >= con.dur) {
        forced = true;
        creature.comeBack();
        tearPulse = Math.max(tearPulse, 0.4);
        S.takeover();
      }
      /* Страховка: если существо так и не смогло отжать пустоту, пульт
         закрывается сам. Зависший ввод команды останавливал бы всю игру. */
      if (con && con.mode && creature.st === 'back' && t - con.since > con.dur + 45) {
        var kind0 = con.mode;
        closeConsole();
        fed(kind0);
        forced = false;
        creature.st = 'resume'; creature.sub = 'go'; creature.timer = 0.5;
        return;
      }
      var all = [con.seq, con.rseq];
      for (var a = 0; a < 2; a++) for (var i = 0; i < all[a].length; i++) {
        all[a][i].age += dt;
        if (all[a][i].rel !== undefined) all[a][i].rel += dt;
      }
      for (var d = con.dead.length - 1; d >= 0; d--) {
        con.dead[d].age += dt;
        if (con.dead[d].age > 0.8) con.dead.splice(d, 1);
      }
    }

    marks.clear();
    var hv = con || conHold;
    var hp = con ? 1 : Math.min(1, conHold.t / CON_HOLD);
    marks.set(F.ckey(hv.wx, hv.wy), { grow: 0.3 + 0.7 * hp + (con && con.mode ? 0.15 * Math.sin(t * 2) : 0) });
    if (con) {
      con.dead.forEach(function (k) {
        marks.set(F.ckey(k.wx, k.wy), { grow: Math.max(0, 1 - k.age / 0.8) * 0.8, dim: Math.min(0.6, k.age / 0.8) });
      });
      con.seq.forEach(function (k) {
        if (k.rel !== undefined) {
          // отжат: проседает и гаснет до обычного
          var r = Math.min(1, k.rel / 0.28);
          if (r < 1) marks.set(F.ckey(k.wx, k.wy), { grow: (1 - r) * 0.8 - Math.sin(r * Math.PI) * 0.3, dim: r * 0.2 });
          return;
        }
        marks.set(F.ckey(k.wx, k.wy), { grow: keyCurve(k.age) * (con.mode ? 0.8 : 1), lit: con.mode ? 1 : 0 });
      });
      con.rseq.forEach(function (k) {
        var key = F.ckey(k.wx, k.wy);
        if (marks.has(key) && !marks.get(key).dim) return;
        // знак обратного набора лишь щёлкает и не остаётся нажатым
        var fade = Math.max(0, 1 - k.age / 0.45);
        if (fade > 0) marks.set(key, { grow: keyCurve(k.age) * fade });
      });
    }
    F.setMarks(marks);
  }

  /* Пора на перерыв, а пультом владеет игрок. Существо даёт доиграть начатое
     и потом само забирает пульт. */
  function stepBreaks(dt) {
    var due = breakDue();
    if (!due || forced) { breakWait = 0; return; }
    if (!humanActive()) return;          // существо уйдёт само на ближайшей развилке
    breakWait += dt;
    var quiet = panel === 0 && sel === SEL.IDLE && !busyNav();
    if ((breakWait > 12 && quiet) || breakWait > 40) {
      forced = true; breakWait = 0;
      tearPulse = Math.max(tearPulse, 0.55);
      S.takeover();
      creature.attach();
    }
  }

  // --- переезд -----------------------------------------------------------------
  /* Карта конечна. Когда она забита следами работы, корабль долго светит одним
     и тем же знаком по всей карте, дожидается паузы в работе и уходит на
     новое место. */

  var move = null;

  function quietNav() {
    return panel === 0 && sel === SEL.IDLE && !busyNav() && !con && !conHold
      && !trains.length && !flying.length && !inject.length && !SZ.finishing();
  }

  /* Команда пульта: корабль уходит с этого места немедленно. Сначала
     раскручиваются двигатели — нарастает вой, дрожит экран, по краю идут
     помехи, — потом тот же прыжок, что и при обычном переезде. */
  function commandRelocate() {
    if ((move && move.st !== 'signal') || eject || panel !== 0) { S.reject(); reject = 0.6; return; }
    // корабль уже сигналил о переезде — команда просто ускоряет его
    move = { st: 'spool', t: 0, gid: -1, ring: 0, cmd: true };
    F.setBeacon(-1);
    deactivate(true);
    S.spool(2.6);
  }

  function stepMove(dt) {
    if (!move) {
      if (panel !== 0 || eject || F.fill() < MOVE_FILL) return;
      var g;
      do { g = 1 + Math.floor(Math.random() * (G.COUNT - 1)); } while (G.isParasite(g));
      move = { st: 'signal', t: 0, gid: g, ring: 0 };
      F.setBeacon(g);
      LORE.ship('relocate_signal');
      return;
    }
    move.t += dt;
    if (move.st === 'spool') {
      var su = Math.min(1, move.t / 2.6);
      shake = Math.max(shake, 0.08 + 0.8 * su * su);
      edgePulse = Math.max(edgePulse, 0.15 + 0.6 * su);
      tearFx = Math.max(tearFx, 0.05 + 0.2 * su + (Math.random() < 0.06 ? 0.3 : 0));
      if (move.t >= 2.6) {
        move.st = 'jump'; move.t = 0; move.swapped = false;
        var sa = Math.random() * Math.PI * 2;
        move.dx = Math.cos(sa); move.dy = Math.sin(sa);
        S.transit();
      }
      return;
    }
    if (move.st === 'signal') {
      move.ring -= dt;
      if (move.ring <= 0 && panel === 0) { S.beacon(); move.ring = 3.2; }
      var can = panel === 0 && !eject && !con && !conHold && !handover;
      if (can && move.t > 20 && (quietNav() || move.t > 110)) {
        if (!quietNav()) { abort(); deactivate(true); }
        move.st = 'jump'; move.t = 0; move.swapped = false;
        var ang = Math.random() * Math.PI * 2;
        move.dx = Math.cos(ang); move.dy = Math.sin(ang);
        S.transit();
      }
      return;
    }
    var T1 = 1.1, T2 = 2.5, u, sp;
    var c = F.camCell;
    if (move.t < T1) {
      u = move.t / T1;
      sp = u * u * 90;
      F.setStreak(u * u, -move.dx, -move.dy);
      F.setFade(1 - Math.max(0, (u - 0.6) / 0.4));
    } else {
      if (!move.swapped) {
        move.swapped = true;
        mapId++;
        F.loadWorld(F.freshWorld({ w: NAV_W, h: NAV_W, seed: (Math.random() * 0xffffff) | 0, zoom: F.zoom }));
        taken.clear(); reveals.clear(); guide = null;
        LORE.ship('relocate');
        LORE.nextSector();
        c = F.camCell;
      }
      u = Math.min(1, (move.t - T1) / (T2 - T1));
      var k = 1 - u;
      sp = k * k * 90;
      F.setStreak(k * k, -move.dx, -move.dy);
      F.setFade(Math.min(1, u * 1.7));
    }
    F.setCam(c.x + move.dx * sp * dt, c.y + move.dy * sp * dt);
    tearFx = Math.max(tearFx, 0.4 * Math.exp(-Math.pow((move.t - T1) / 0.3, 2)));
    if (move.t >= T2) { F.setStreak(0, 0, 0); F.setFade(1); move = null; }
  }


  // --- проверка знака выдержкой ---------------------------------------------
  // Один жест на все случаи: подержал курсор — знак либо раскрывается, либо
  // отшатывается. В покое так проверяется «якорь ли это», в выделении —
  // «тот ли это второй край».

  function stepDwell(dt) {
    // проверять знаки имеет смысл только на сборе
    if (phase !== PHASE.COLLECT) { holdT = 0; holdFired = true; return; }
    // Выдержка считается от НЕПОДВИЖНОСТИ КУРСОРА, а не от наличия якоря под
    // ним. Поэтому кольцо ничего не выдаёт: держать три секунды приходится
    // на каждой догадке, и водить курсором наугад становится бессмысленно.
    var mx = Pointer.x - holdX, my = Pointer.y - holdY;
    if (Math.sqrt(mx * mx + my * my) > HOLD_SLIP) {
      holdX = Pointer.x; holdY = Pointer.y;
      holdT = 0; holdFired = false; dwellSnd = 0;
      return;
    }
    if (holdFired) return;

    holdT += dt;
    if (holdT > HOLD_SHOW) {
      dwellSnd += dt;
      if (dwellSnd > 0.24) {
        dwellSnd = 0;
        S.dwell((holdT - HOLD_SHOW) / (DWELL - HOLD_SHOW));
      }
    }
    if (holdT < DWELL) return;

    holdFired = true;
    var pred = null;
    if (sel === SEL.IDLE) pred = REAL;
    else if (sel === SEL.DRAG && startAnchor) {
      var gid = startAnchor.rec.gid;
      pred = function (a) { return a.gid === gid; };
    }
    var a = pred ? F.anchorNear(Pointer.x, Pointer.y, TOL * 1.15, pred) : null;
    if (!a) { S.nothing(); return; }

    var k = F.ckey(a.wx, a.wy);
    var ok = true;
    if (sel === SEL.DRAG) {
      var st = startAnchor.rec;
      ok = !!(a.rec.pid && a.rec.pid === st.pid && a.rec.role !== st.role);
    }
    reveals.set(k, { ok: ok, age: 0, wx: a.wx, wy: a.wy });
    if (ok) { S.bloom(); S.anchor(a.rec.kind, 1); } else S.flinch();
  }

  function stepPulses(dt) {
    for (var i = pulses.length - 1; i >= 0; i--) {
      pulses[i].age += dt;
      if (pulses[i].age > 0.7) pulses.splice(i, 1);
    }
  }

  function drawPulses() {
    if (!pulses.length) return;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (var i = 0; i < pulses.length; i++) {
      var p = pulses[i], u = p.age / 0.7, a = (1 - u) * (p.strong ? 0.8 : 0.3);
      var r = 10 + u * (p.strong ? 92 : 46);
      ctx.strokeStyle = 'rgba(255,226,180,' + a + ')';
      ctx.lineWidth = (p.strong ? 2.2 : 1.2) * (1 - u) + 0.3;
      ctx.beginPath(); ctx.arc(p.x, p.y, r, 0, Math.PI * 2); ctx.stroke();
    }
    ctx.restore();
  }

  function stepReveals(dt) {
    boost.clear();
    reveals.forEach(function (r, k) {
      r.age += dt;
      if (r.age > 3.4) { reveals.delete(k); return; }
      var e = Math.min(1, r.age / 0.30);
      var fade = Math.max(0, 1 - Math.max(0, r.age - 1.6) / 1.8);
      boost.set(k, (r.ok ? 0.55 : 0.10) * e * fade);
    });
    F.setBoost(boost);
  }

  // --- отрисовка -------------------------------------------------------------

  function folderPos(i) {
    var gap = 100, x0 = vw / 2 - (4 * gap - gap) / 2;
    return { x: x0 + i * gap, y: vh - 64 };
  }

  /* Подложка панели: полоса экрана под ней размывается уменьшением и обратным
     растягиванием, затемняется и отчёркивается тонкой линией. Получается не
     плашка поверх картинки, а расслоение самого экрана. */
  var blurCv = null, bctx = null;

  function backdrop(y0, y1, dir) {
    var h = y1 - y0;
    if (h <= 1 || vw < 4 || scene.width < 4 || scene.height < 4) return;
    var bw = Math.max(8, Math.round(vw / 11)), bh = Math.max(3, Math.round(h / 7));
    if (!blurCv) { blurCv = document.createElement('canvas'); bctx = blurCv.getContext('2d'); }
    if (blurCv.width !== bw || blurCv.height !== bh) { blurCv.width = bw; blurCv.height = bh; }
    bctx.clearRect(0, 0, bw, bh);
    bctx.drawImage(scene,
      0, Math.round(y0 * dpr), Math.round(vw * dpr), Math.round(h * dpr),
      0, 0, bw, bh);

    ctx.save();
    ctx.imageSmoothingEnabled = true;
    ctx.globalAlpha = 0.92;
    ctx.drawImage(blurCv, 0, 0, bw, bh, 0, y0, vw, h);
    ctx.globalAlpha = 1;

    var g = ctx.createLinearGradient(0, y0, 0, y1);
    if (dir > 0) {           // нижняя панель: темнеет книзу
      g.addColorStop(0, 'rgba(7,6,3,0.05)');
      g.addColorStop(0.45, 'rgba(7,6,3,0.5)');
      g.addColorStop(1, 'rgba(7,6,3,0.82)');
    } else {                 // верхняя панель: темнеет кверху
      g.addColorStop(0, 'rgba(7,6,3,0.82)');
      g.addColorStop(0.55, 'rgba(7,6,3,0.5)');
      g.addColorStop(1, 'rgba(7,6,3,0.05)');
    }
    ctx.fillStyle = g;
    ctx.fillRect(0, y0, vw, h);

    // отчерк: ярче в середине, гаснет к краям экрана
    var ly = dir > 0 ? y0 : y1;
    var lg = ctx.createLinearGradient(0, 0, vw, 0);
    lg.addColorStop(0, 'rgba(255,158,58,0)');
    lg.addColorStop(0.5, 'rgba(255,186,110,0.28)');
    lg.addColorStop(1, 'rgba(255,158,58,0)');
    ctx.fillStyle = lg;
    ctx.fillRect(0, ly - 0.5, vw, 1);
    ctx.restore();
  }

  function drawFolders() {
    backdrop(vh - 124, vh, 1);
    var lv = panel === 1 ? LORE.folderView() : null;
    var cap = lv ? lv.cap : FOLDER_CAP, gap = lv ? 5.2 : 3.2;
    for (var i = 0; i < 4; i++) {
      var p = folderPos(i), on = lv ? i === lv.active : i === phase, w = 62;
      ctx.save();
      ctx.translate(p.x, p.y);
      if (on) {
        // активный этап крупнее и отмечен скобками по бокам
        var bp = 0.5 + 0.5 * Math.sin(t * 1.6);
        ctx.save();
        ctx.globalCompositeOperation = 'lighter';
        ctx.strokeStyle = 'rgba(255,196,120,' + (0.20 + bp * 0.14) + ')';
        ctx.lineWidth = 1.3;
        ctx.beginPath();
        ctx.moveTo(-48, -62); ctx.lineTo(-53, -62); ctx.lineTo(-53, 28); ctx.lineTo(-48, 28);
        ctx.moveTo(48, -62); ctx.lineTo(53, -62); ctx.lineTo(53, 28); ctx.lineTo(48, 28);
        ctx.stroke();
        ctx.restore();
        ctx.scale(1.12, 1.12);
      }
      ctx.strokeStyle = on ? 'rgba(255,214,158,1)' : 'rgba(255,150,46,0.3)';
      ctx.lineWidth = on ? 1.7 : 1.3;
      ctx.beginPath();
      ctx.moveTo(-w / 2, -26); ctx.lineTo(-w / 2, 16);
      ctx.quadraticCurveTo(0, 28, w / 2, 16);
      ctx.lineTo(w / 2, -26);
      ctx.stroke();
      var fl = lv ? lv.flare[i] : folderFlare[i];
      if (fl > 0) {
        ctx.save();
        ctx.globalCompositeOperation = 'lighter';
        ctx.strokeStyle = 'rgba(255,232,190,' + fl * 0.9 + ')';
        ctx.lineWidth = 1.4 + fl * 2.2;
        ctx.stroke();
        ctx.restore();
      }
      /* Содержимое папки — квадраты по три в ряд, снизу вверх. Светлый —
         обычная единица, тёмный с контуром — ошибка. Полосы на месте
         квадратов различались плохо, а с ошибками стали бы нечитаемы. */
      var units = lv ? null : unitsAt(i);
      var f = lv ? lv.counts[i] : Math.min(FOLDER_CAP, units.length);
      var SQ = 9, SG = 4, COLS = 3;
      for (var k = 0; k < cap; k++) {
        var col = k % COLS, row = (k / COLS) | 0;
        var sx = (col - 1) * (SQ + SG) - SQ / 2, sy = 7 - row * (SQ + SG) - SQ / 2;
        var full = k < f;
        if (!full) {
          ctx.globalAlpha = 0.10;
          ctx.lineWidth = 1;
          ctx.strokeRect(sx + 0.5, sy + 0.5, SQ - 1, SQ - 1);
          continue;
        }
        var fresh = (k === f - 1) ? fl : 0;
        var dark = lv ? !!(lv.dark && lv.dark[i] && lv.dark[i][k]) : !!(units[k].bad && units[k].bad[i]);
        var sc = 1 + fresh * 0.35;
        if (!lv && i === PHASE.PURGE && purgeDrain > 0 && k === f - 1) sc *= 0.6 + 0.4 * Math.max(0, Math.min(1, purgeDrain / 0.45));
        // последняя единица анализа тает по мере сортировки
        if (!lv && i === PHASE.ANALYZE && k === f - 1) {
          sc *= Math.max(0.2, analyzeRem);
          if (phase === PHASE.SORT) sc *= 0.9 + 0.1 * Math.sin(t * 2.6);
        }
        var s2 = SQ * sc, cx0 = sx + SQ / 2 - s2 / 2, cy0 = sy + SQ / 2 - s2 / 2;
        ctx.globalAlpha = 1;
        if (dark) {
          ctx.fillStyle = 'rgba(46,26,10,0.95)';
          ctx.fillRect(cx0, cy0, s2, s2);
          ctx.strokeStyle = 'rgba(255,150,60,' + (0.75 + fresh * 0.25) + ')';
          ctx.lineWidth = 1.2;
          ctx.strokeRect(cx0 + 0.6, cy0 + 0.6, s2 - 1.2, s2 - 1.2);
        } else {
          ctx.fillStyle = 'rgba(255,' + Math.round(214 + fresh * 30) + ',' + Math.round(160 + fresh * 60) + ',' + (0.88 + fresh * 0.12) + ')';
          ctx.fillRect(cx0, cy0, s2, s2);
        }
        ctx.strokeStyle = on ? 'rgba(255,214,158,1)' : 'rgba(255,150,46,0.3)';
      }
      ctx.globalAlpha = 1;
      ctx.translate(0, -48);
      ctx.strokeStyle = on ? 'rgba(255,232,190,1)' : 'rgba(255,150,46,0.30)';
      G.drawGlyph(ctx, lv ? lv.icons[i] : [7, 58, 121, 196][i], on ? 29 : 25, on ? 1.8 : 1.4);
      ctx.restore();
    }
  }

  /* Кольцо выдержки на пустоте и тихий пульс нажатой пустоты. Пока существа
     нет, вокруг неё медленно тает дуга: сколько ему ещё отсутствовать. */
  function drawConsole() {
    /* Щелчок: четыре уголка сходятся к знаку при нажатии и разлетаются при
       отжатии. */
    if (conFx.length) {
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      for (var q = 0; q < conFx.length; q++) {
        var fx = conFx[q], u = Math.min(1, fx.age / 0.26), e = 1 - Math.pow(1 - u, 3);
        var fp = F.cellCenter(fx.wx, fx.wy);
        var r = fx.kind === 'press' ? F.CELL * (0.95 - 0.4 * e) : F.CELL * (0.55 + 0.5 * e);
        var c = F.CELL * 0.18;
        ctx.strokeStyle = 'rgba(255,232,190,' + (1 - u) * (fx.kind === 'press' ? 0.95 : 0.6) + ')';
        ctx.lineWidth = fx.kind === 'press' ? 1.6 : 1.1;
        ctx.beginPath();
        ctx.moveTo(fp.x - r, fp.y - r + c); ctx.lineTo(fp.x - r, fp.y - r); ctx.lineTo(fp.x - r + c, fp.y - r);
        ctx.moveTo(fp.x + r - c, fp.y - r); ctx.lineTo(fp.x + r, fp.y - r); ctx.lineTo(fp.x + r, fp.y - r + c);
        ctx.moveTo(fp.x - r, fp.y + r - c); ctx.lineTo(fp.x - r, fp.y + r); ctx.lineTo(fp.x - r + c, fp.y + r);
        ctx.moveTo(fp.x + r - c, fp.y + r); ctx.lineTo(fp.x + r, fp.y + r); ctx.lineTo(fp.x + r, fp.y + r - c);
        ctx.stroke();
      }
      ctx.restore();
    }
    var h = con || conHold;
    if (!h) return;
    var p = F.cellCenter(h.wx, h.wy);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    if (!con) {
      var u = Math.min(1, conHold.t / CON_HOLD);
      ctx.strokeStyle = 'rgba(255,228,180,' + (0.3 + u * 0.5) + ')';
      ctx.lineWidth = 1.4 + u;
      ctx.beginPath(); ctx.arc(p.x, p.y, F.CELL * 0.62, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * u); ctx.stroke();
    } else {
      var pu = 0.5 + 0.5 * Math.sin(t * (con.mode ? 1.3 : 3.2));
      ctx.strokeStyle = 'rgba(255,228,180,' + (0.22 + pu * 0.3) + ')';
      ctx.lineWidth = 1.3;
      ctx.beginPath(); ctx.arc(p.x, p.y, F.CELL * (0.58 + pu * 0.08), 0, Math.PI * 2); ctx.stroke();
      if (con.mode) {
        var left = Math.max(0, 1 - (t - con.since) / con.dur);
        ctx.strokeStyle = 'rgba(255,206,150,0.26)';
        ctx.lineWidth = 1;
        ctx.beginPath(); ctx.arc(p.x, p.y, F.CELL * 0.86, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * left); ctx.stroke();
      }
    }
    ctx.restore();
  }

  function drawRect() {
    var r;
    if (sel === SEL.DRAG) r = norm(Pointer.dragX, Pointer.dragY, Pointer.x, Pointer.y);
    else if (rect && (sel === SEL.CONFIRM || sel === SEL.SEND)) r = rect;
    else return;

    var armed = !!startAnchor;
    var pulse = 0.5 + 0.5 * Math.sin(t * 4.2);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineWidth = armed ? 1.5 : 1;
    ctx.strokeStyle = armed
      ? 'rgba(255,214,150,' + (0.55 + pulse * 0.35) + ')'
      : 'rgba(255,140,60,0.34)';
    ctx.strokeRect(r.x0 + 0.5, r.y0 + 0.5, r.x1 - r.x0, r.y1 - r.y0);
    // углы держат смысл: блок задан ими, а не тем, что внутри
    var c = 11;
    ctx.lineWidth = armed ? 2.1 : 1.2;
    ctx.beginPath();
    [[r.x0, r.y0, 1, 1], [r.x1, r.y0, -1, 1], [r.x0, r.y1, 1, -1], [r.x1, r.y1, -1, -1]].forEach(function (p) {
      ctx.moveTo(p[0], p[1] + p[3] * c); ctx.lineTo(p[0], p[1]); ctx.lineTo(p[0] + p[2] * c, p[1]);
    });
    ctx.stroke();
    ctx.restore();
  }

  function drawReveals() {
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    reveals.forEach(function (r) {
      if (taken.has(F.ckey(r.wx, r.wy))) return;
      var p = F.cellCenter(r.wx, r.wy);
      var a = Math.max(0, 1 - r.age / 1.1);
      if (a <= 0) return;
      if (r.ok) {
        // раскрывается: кольцо расходится наружу
        var rr = 12 + (1 - a) * 34;
        ctx.strokeStyle = 'rgba(255,228,180,' + a * 0.8 + ')';
        ctx.lineWidth = 1.6 * a + 0.4;
        ctx.beginPath(); ctx.arc(p.x, p.y, rr, 0, Math.PI * 2); ctx.stroke();
      } else {
        // отшатывается: короткая сжимающаяся дуга и дрожь
        var rr2 = 30 - (1 - a) * 16;
        ctx.strokeStyle = 'rgba(255,120,60,' + a * 0.6 + ')';
        ctx.lineWidth = 1.2;
        var w = Math.sin(r.age * 40) * 2 * a;
        ctx.beginPath(); ctx.arc(p.x + w, p.y, rr2, 0.6, 0.6 + Math.PI * 1.2); ctx.stroke();
      }
    });
    ctx.restore();
  }

  function drawButton() {
    if (!button) return;
    var p = 0.5 + 0.5 * Math.sin(t * 3.1);
    var over = Math.hypot(Pointer.x - button.x, Pointer.y - button.y) < button.r + 10;
    button.hot += ((over ? 1 : 0) - button.hot) * 0.18;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.translate(button.x, button.y);
    ctx.strokeStyle = 'rgba(255,232,190,' + (0.72 + p * 0.24 + button.hot * 0.2) + ')';
    ctx.lineWidth = 1.7 + button.hot * 1.0;
    // не круг и не прямоугольник: две сомкнутые дуги, как линза в письменности
    var r = button.r * (1 + button.hot * 0.12);
    ctx.beginPath();
    ctx.moveTo(0, -r);
    ctx.quadraticCurveTo(r * 1.15, 0, 0, r);
    ctx.quadraticCurveTo(-r * 1.15, 0, 0, -r);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(-r * 0.34, 0); ctx.lineTo(r * 0.34, 0);
    ctx.moveTo(r * 0.1, -r * 0.24); ctx.lineTo(r * 0.34, 0); ctx.lineTo(r * 0.1, r * 0.24);
    ctx.stroke();
    ctx.restore();
  }

  function drawFlying() {
    if (!flying.length) return;
    var atlas = F.atlas, box = F.atlasBox;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (var i = 0; i < flying.length; i++) {
      var f = flying[i];
      if (f.d > 0) {
        ctx.globalAlpha = 0.9;
        var o0 = box * f.s0 / 2;
        atlas.draw(ctx, f.id, f.x0 - o0, f.y0 - o0, box * f.s0, box * f.s0);
        continue;
      }
      var u = Math.min(1, f.t);
      var e = u < 0.5 ? 4 * u * u * u : 1 - Math.pow(-2 * u + 2, 3) / 2;
      var m = 1 - e;
      var x = m * m * f.x0 + 2 * m * e * f.cx + e * e * f.x1;
      var y = m * m * f.y0 + 2 * m * e * f.cy + e * e * f.y1;
      var s = f.s0 * (1 - e * 0.82);
      ctx.globalAlpha = Math.min(1, (1 - e * 0.55) * 1.1);
      var o = box * s / 2;
      atlas.draw(ctx, f.id, x - o, y - o, box * s, box * s);
    }
    ctx.restore();
  }

  function drawReject() {
    if (reject <= 0) return;
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = 'rgba(255,90,40,' + reject * 0.35 + ')';
    ctx.lineWidth = 2;
    ctx.strokeRect(3, 3, vw - 6, vh - 6);
    ctx.restore();
  }

  function drawCursor() {
    var x = Pointer.x, y = Pointer.y;
    var mine = humanActive();
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    // существа нет за пультом: курсор лежит брошенным и почти не виден
    if (!mine && creature.st === 'away') ctx.globalAlpha = 0.16;
    if (eject) ctx.globalAlpha = Math.max(0, 1 - eject.t / 1.6);
    ctx.strokeStyle = mine ? 'rgba(255,232,195,0.92)' : 'rgba(255,158,58,0.6)';
    ctx.lineWidth = 1.2;
    var grip = 1 - 0.38 * squash;
    for (var i = 0; i < 3; i++) {
      var a0 = t * (sel === SEL.DRAG ? 1.5 : 0.6) + i * Math.PI * 2 / 3;
      ctx.beginPath();
      ctx.arc(x, y, (11 + i * 3.5) * grip, a0, a0 + Math.PI * 0.52);
      ctx.stroke();
    }
    // выдержка: дуга замыкается, пока курсор стоит на месте
    if (holdT > HOLD_SHOW && !holdFired) {
      var u = (holdT - HOLD_SHOW) / (DWELL - HOLD_SHOW);
      ctx.strokeStyle = 'rgba(255,228,180,' + (0.35 + u * 0.45) + ')';
      ctx.lineWidth = 1.4 + u * 1.1;
      ctx.beginPath();
      ctx.arc(x, y, 22, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * u);
      ctx.stroke();
    }
    ctx.beginPath(); ctx.arc(x, y, 1.6, 0, Math.PI * 2); ctx.stroke();
    ctx.restore();
  }

  /* Верхняя панель: выбор области данных. Навигационная и лорная выглядят
     одинаково не случайно: для существа это просто две области, обе ему
     понятны. В лорной рядом появляется знак журнала. */
  var panel = 0, tabFlare = 0, navWorld = null, toNav = null;

  function panelPos(i) {
    if (i === 2) return { x: vw / 2 + 132, y: 40 };
    if (i === 3) return { x: vw / 2 + 176, y: 40 };
    return { x: vw / 2 + (i - 0.5) * 104, y: 40 };
  }

  function panelHit(x, y) {
    // разбитая панель не отзывается
    if (!ctrl() || panelLocked()) return -1;
    for (var i = 0; i < 4; i++) {
      if (i >= 2 && panel !== 1) continue;
      var p = panelPos(i);
      if (Math.abs(x - p.x) < (i >= 2 ? 20 : 34) && Math.abs(y - p.y) < 26) return i;
    }
    return -1;
  }

  function drawMenu() {
    // у старого существа панель видна сразу, но разбита
    var pr = tut ? 1 : Math.max(0, Math.min(1, (t - controlAt) / 2.2));
    if (pr <= 0) return;
    var dmg = panelDamage();
    var e = 1 - Math.pow(1 - pr, 3);
    backdrop(0, 78 * e, -1);
    ctx.save();
    ctx.globalAlpha = e;
    for (var i = 0; i < 4; i++) {
      if (i >= 2 && panel !== 1) continue;
      var p = panelPos(i), on = i === panel || (i === 2 && LORE.journalOpen) || (i === 3 && INV.open);
      ctx.save();
      ctx.translate(p.x, -20 + e * (p.y + 20));
      if (dmg > 0) {
        // разрушенная панель: значки дёргаются и пропадают
        var gs = Math.floor(t * 8) * 7 + i * 13;
        ctx.translate((G.rand3(gs, i, 71) - 0.5) * 12 * dmg, (G.rand3(gs, i, 72) - 0.5) * 5 * dmg);
        if (G.rand3(gs, i, 73) < dmg * 0.3) ctx.globalAlpha *= 0.15;
      }
      if (on && i < 2 && dmg < 0.5) {
        var bp = 0.5 + 0.5 * Math.sin(t * 1.6);
        ctx.save();
        ctx.globalCompositeOperation = 'lighter';
        ctx.strokeStyle = 'rgba(255,196,120,' + (0.18 + bp * 0.12) + ')';
        ctx.lineWidth = 1.3;
        ctx.beginPath();
        ctx.moveTo(-30, -19); ctx.lineTo(-35, -19); ctx.lineTo(-35, 19); ctx.lineTo(-30, 19);
        ctx.moveTo(30, -19); ctx.lineTo(35, -19); ctx.lineTo(35, 19); ctx.lineTo(30, 19);
        ctx.stroke();
        ctx.restore();
        ctx.scale(1.2, 1.2);
      }
      // лорная вкладка вспыхивает, когда в неё уходит ошибка
      var fl = i === 1 ? tabFlare : 0;
      var fresh = (i === 2 && LORE.fresh) || (i === 3 && INV.fresh) ? 0.5 + 0.5 * Math.sin(t * 3) : 0;
      ctx.strokeStyle = on ? 'rgba(255,232,190,0.95)'
        : 'rgba(255,' + Math.round(150 + fl * 80 + fresh * 60) + ',' + Math.round(46 + fl * 120 + fresh * 90) + ',' + (0.22 + fl * 0.7 + fresh * 0.4) + ')';
      if (dmg >= 0.5) ctx.strokeStyle = 'rgba(170,132,92,' + (0.75 - 0.25 * dmg).toFixed(2) + ')';
      G.drawGlyph(ctx, [33, 164, 90, 139][i], i >= 2 ? 18 : (on ? 24 : 20), on ? 1.6 : 1.2);
      ctx.restore();
    }
    if (dmg > 0) {
      // рваные полосы помех поперёк панели
      var gb = Math.floor(t * 6);
      ctx.globalAlpha = 1;
      for (var b = 0; b < 4; b++) {
        if (G.rand3(gb, b, 81) > dmg) continue;
        ctx.fillStyle = 'rgba(120,96,70,' + (0.3 * dmg).toFixed(2) + ')';
        ctx.fillRect(vw / 2 - 170 + G.rand3(gb, b, 82) * 240, 22 + G.rand3(gb, b, 83) * 36,
                     40 + G.rand3(gb, b, 84) * 130, 1 + G.rand3(gb, b, 85) * 2);
      }
    }
    ctx.restore();
  }

  /* Переключение вкладки подменяет поле целиком. Начатая навигационная работа
     закрывается: знаки остаются как есть. */
  function switchPanel(p, force) {
    if (p === panel) return;
    if (!force && ((move && move.st === 'jump') || eject)) return;
    abort();
    conHold = null;
    if (panel === 0) {
      // существо на обеде или спит, а игрок ушёл в лор: перерыв засчитан, существо вернулось
      if (con && con.mode) { fed(con.mode); forced = false; creature.st = 'resume'; creature.sub = 'go'; creature.timer = 0.5; }
      closeConsole(true);
      deactivate(true);
      reveals.clear(); boost.clear(); F.setBoost(null);
      navWorld = F.saveWorld();
      panel = 1;
      LORE.enter();
    } else {
      INV.close();
      LORE.leave();
      F.loadWorld(navWorld);
      panel = 0;
    }
    inject = [];
    button = null;
    guide = null;
    tearPulse = Math.max(tearPulse, 0.22);
    S.tab(p);
  }

  /* Пультом никто не владеет, а открыта лорная вкладка: существо идёт к
     навигационной. Лор ему не нужен. */
  function creatureToNav(dt) {
    if (LORE.journalOpen) LORE.toggleJournal();
    INV.close();
    var p = panelPos(0);
    if (!toNav) { toNav = { t: 0 }; hand.to(p.x, p.y, { speed: 320 }); }
    toNav.t += dt;
    hand.retarget(p.x, p.y);
    if (hand.arrived(16) || toNav.t > 5) {
      pulses.push({ x: p.x, y: p.y, age: 0, strong: false });
      toNav = null;
      switchPanel(0, true);
      creature.detach();
    }
  }

  // --- цикл ------------------------------------------------------------------

  function resize() {
    // с постпроходом кадр каждый раз заливается в текстуру, поэтому плотность
    // пикселей ограничена: на 2x загрузка текстуры съедала бы весь бюджет
    dpr = Math.min(post && post.ok ? 1.25 : 2, window.devicePixelRatio || 1);
    vw = canvas.clientWidth; vh = canvas.clientHeight;
    canvas.width = Math.round(vw * dpr);
    canvas.height = Math.round(vh * dpr);
    if (scene !== canvas) { scene.width = canvas.width; scene.height = canvas.height; }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.imageSmoothingQuality = 'high';
  }

  /* Шаг симуляции отделён от отрисовки: так логику можно прогнать без кадров
     и без рендера, что нужно и для проверок, и при скрытой странице. */
  function simulate(dt) {
    t += dt;
    hand.slow = handSlow();
    tearFx = tearPulse;
    tearPulse = Math.max(0, tearPulse - dt * 1.3);
    if (tabFlare > 0) tabFlare = Math.max(0, tabFlare - dt * 0.8);

    /* Вход в лорную вкладку для существа останавливает время: обед и сон
       отодвигаются ровно на столько, сколько игрок провёл в лоре. */
    if (panel === 1) {
      if (isFinite(lunchDue)) lunchDue += dt;
      if (isFinite(sleepDue)) sleepDue += dt;
    }
    var mine = humanActive();
    var jumping = !!((move && move.st === 'jump') || eject);
    if (!mine) {
      if (!jumping) {
        if (panel === 1) creatureToNav(dt);
        else creature.step(dt);
      }
      hand.step(dt);
      // существо не имеет права увести курсор туда, где игрок его не увидит
      hand.x = Math.max(12, Math.min(vw - 12, hand.x));
      hand.y = Math.max(12, Math.min(vh - 12, hand.y));
      Pointer.x = hand.x; Pointer.y = hand.y;
    }
    else {
      // с грузом курсор идёт вязко: знак должен ощущаться тяжёлым
      var k = Math.min(1, dt * (SZ.dragging ? 6 : 18));
      Pointer.x += (Pointer.tx - Pointer.x) * k;
      Pointer.y += (Pointer.ty - Pointer.y) * k;
    }

    /* Повадки выдают знак только там, где он участвует в работе: на сборе и
       только настоящие якоря. */
    F.setHunting(panel === 0 && phase === PHASE.COLLECT ? 1 : 0);

    /* Поле замирает не только под рамкой, но и на всё время работы в блоке,
       в режиме ввода команды и на переезде. */
    var busy = panel === 0 ? busyNav() : LORE.busy();
    var wantFreeze = (sel !== SEL.IDLE || busy || con || jumping) ? 1 : 0;
    freeze += (wantFreeze - freeze) * Math.min(1, dt * (wantFreeze ? 9 : 3.2));
    F.setFreeze(freeze);

    if (panel === 0) stepDwell(dt);
    SZ.step(dt, Pointer);
    if (panel === 0) { stepSort(dt); stepChains(dt); }
    stepPulses(dt);
    stepReveals(dt);
    stepFlying(dt);
    stepTrains(dt);
    if (panel === 0) stepPurge(dt);
    stepInject(dt);
    stepGuide();
    LORE.step(dt);
    INV.step(dt);
    stepErrDots(dt);
    stepSave(dt);
    if (panel === 0) stepConsole(dt);
    stepBreaks(dt);
    stepMove(dt);
    stepHandover(dt);
    stepEject(dt);
    stepDefect(dt);
    if (!tut && drift >= driftMax() && !eject) endCycle('drift');
    stepLife(dt);
    stepOldFx(dt);

    for (var i = 0; i < 4; i++) {
      if (folderFlare[i] > 0) folderFlare[i] = Math.max(0, folderFlare[i] - dt * 1.6);
    }
    if (flushFlare > 0) flushFlare = Math.max(0, flushFlare - dt * 2.5);
    if (shake > 0) shake = Math.max(0, shake - dt * 2.2);
    if (edgePulse > 0) edgePulse = Math.max(0, edgePulse - dt * 0.6);
    if (reject > 0) reject = Math.max(0, reject - dt * 2.2);

    // при ведении гасим слабо: игрок в этот момент ИЩЕТ второй край и поле
    // ему нужно видеть. Сильное гашение — только после отпускания
    if (sel === SEL.DRAG) F.setSel(norm(Pointer.dragX, Pointer.dragY, Pointer.x, Pointer.y), 0.30, 0.11);
    else if (rect && (sel === SEL.CONFIRM || sel === SEL.SEND)) F.setSel(rect, 0.86, 0.05);
    // на сортировке гаснет всё, кроме доски: внимание только на неё
    else if (panel === 0 && phase === PHASE.SORT && SZ.active()) F.setSel(SZ.rect(), 0.8, 0, true);
    else if (panel === 1 && LORE.sortRect()) F.setSel(LORE.sortRect(), 0.8, 0, true);
    else F.setSel(null, 0, 0);

    F.setDt(dt);
    /* Прокрутка нужна не только на сборе: цепочка анализа и знаки утилизации
       могут лежать за краем экрана. Запрещена она на сортировке, где блок
       специально подогнан под экран, во вводе команды и на переезде. */
    /* Открыты хранилище или журнал: поле позади заперто, курсор по нему не
       гуляет и не двигает его. Курсор ушёл из окна — прокрутки краем тоже нет,
       иначе поле уезжало бы бесконечно, пока игрок в другой вкладке. */
    var fieldBlocked = panel === 1 && (INV.open || LORE.journalOpen);
    var allowPan = !jumping && !con && sel === SEL.IDLE
      && !(panel === 0 && phase === PHASE.SORT) && !(panel === 1 && LORE.busy())
      && (mine ? (pointerIn && !fieldBlocked) : (panel === 0 && (creature.st === 'scan'
          // на анализе и утилизации существо уводит поле, только когда цель
          // и правда за краем, а не когда просто работает у кромки экрана
          || ((creature.st === 'chain' || creature.st === 'purge' || creature.st === 'console') && creature.panning))));
    // объекты появляются только на навигационной карте и не у старого существа
    F.setObjSpawn(panel === 0 && !tut);
    F.update(dt, fieldBlocked ? null : Pointer, vw, vh, allowPan);

    var sx = Pointer.x - prevPX, sy = Pointer.y - prevPY;
    cursorSpd = Math.sqrt(sx * sx + sy * sy) / Math.max(1e-4, dt);
    Pointer.spd += (cursorSpd - Pointer.spd) * Math.min(1, dt * 9);
    prevPX = Pointer.x; prevPY = Pointer.y;

    if (tapSquash > 0) tapSquash -= dt;
    var sq = (sel === SEL.DRAG || (mine ? pressed : tapSquash > 0)) ? 1 : 0;
    squash += (sq - squash) * Math.min(1, dt * (sq ? 24 : 12));

    if (t > 120) S.horizon();
    var burst = post ? post.step(dt) : 0;
    if (burst > 0.45 && Math.random() < dt * 6) S.crackle(burst);
    S.frame(dt, cursorSpd, F.hot, freeze);
  }

  function frame(now) {
    var dt = Math.min(0.05, (now - last) / 1000 || 0.016);
    last = now;
    lastSimAt = performance.now();
    simulate(dt);
    render();
    requestAnimationFrame(frame);
  }

  function render() {
    // событие resize иногда не приходит (смена вкладки, перекладка панели),
    // а игра целиком живёт в экранных координатах
    if (canvas.clientWidth !== vw || canvas.clientHeight !== vh) resize();
    // холст может оказаться нулевого размера (панель свёрнута, вкладка ещё не
    // разложена) — рисовать в него нельзя
    if (vw < 4 || vh < 4) return;
    ctx.save();
    if (shake > 0) ctx.translate((Math.random() - 0.5) * shake * 22, (Math.random() - 0.5) * shake * 14);
    ctx.fillStyle = '#070603';
    ctx.fillRect(0, 0, vw, vh);
    F.draw(ctx, vw, vh, (panel === 1 && (INV.open || LORE.journalOpen)) ? null : Pointer);
    if (panel === 0) { drawRect(); drawThreads(); }
    drawPulses();
    if (panel === 0) drawReveals();
    drawFlying();
    drawTrains();
    drawErrDots();
    if (panel === 0) {
      if (phase === PHASE.SORT) { SZ.draw(ctx, t); drawInject(); }
      if (phase === PHASE.PURGE) PG.draw(ctx, t);
      drawConsole();
      drawSpinDrag();
    } else LORE.draw(ctx, t);
    drawFolders();
    drawFlush();
    drawButton();
    drawGuide();
    if (panel === 1) { LORE.drawJournal(ctx, t); INV.draw(ctx, t, vw, vh); }
    drawMenu();
    drawReject();
    drawCursor();
    ctx.restore();
    if (!(post && post.ok) && (ejectFx.dark > 0 || ejectFx.lids > 0)) {
      // без WebGL веки и темнота рисуются просто полосами
      ctx.fillStyle = 'rgba(0,0,0,' + Math.min(1, ejectFx.dark) + ')';
      ctx.fillRect(0, 0, vw, vh);
      var lh = vh * 0.5 * Math.min(1, ejectFx.lids);
      ctx.fillStyle = '#000';
      ctx.fillRect(0, 0, vw, lh); ctx.fillRect(0, vh - lh, vw, lh);
    }
    if (!(post && post.ok) && tearFx > 0.02) drawTearFallback();
    drawOldFx();

    if (post && post.ok) post.render(scene, t, tearFx, { scale: ejectFx.scale, blur: ejectFx.blur, lids: ejectFx.lids, edge: Math.max(ejectFx.edge, edgePulse), dark: ejectFx.dark });
  }

  /* Без WebGL срыв рисуется грубо, полосами прямо в сцене. */
  function drawTearFallback() {
    ctx.save();
    for (var i = 0; i < 9; i++) {
      var y = Math.random() * vh, h = 6 + Math.random() * 40;
      var dx = (Math.random() - 0.5) * 140 * tearFx;
      ctx.globalAlpha = 0.8;
      ctx.drawImage(scene, 0, y * dpr, vw * dpr, h * dpr, dx, y, vw, h);
    }
    ctx.fillStyle = 'rgba(7,6,3,' + tearFx * 0.3 * Math.random() + ')';
    ctx.fillRect(0, 0, vw, vh);
    ctx.restore();
  }

  function bind() {
    /* Мышь, пролетевшая над окном игры, пока игрок работает в другой
       программе, пульт не забирает: только когда окно игры в фокусе. */
    canvas.addEventListener('pointermove', function (e) {
      pointerIn = true;
      if (document.hasFocus()) onMove(e.clientX, e.clientY);
    });
    /* Курсор ушёл из окна: в другую вкладку, другое окно или просто за край.
       Последняя точка остаётся у кромки, и без этого поле прокручивалось бы
       без конца и мешало существу. */
    function pointerOut() { pointerIn = false; pressed = false; }
    window.addEventListener('blur', pointerOut);
    document.addEventListener('mouseleave', pointerOut);
    document.documentElement.addEventListener('pointerleave', pointerOut);
    document.addEventListener('visibilitychange', function () { if (document.hidden) pointerOut(); });
    canvas.addEventListener('pointerdown', function (e) { onDown(e.clientX, e.clientY); });
    window.addEventListener('pointerup', function (e) { onUp(e.clientX, e.clientY); });
    window.addEventListener('keydown', function (e) {
      if (e.key === 'Escape' && panel === 1) { if (INV.open) INV.close(); else if (LORE.journalOpen) LORE.toggleJournal(); }
    });
    window.addEventListener('resize', resize);

    // зум колесом: точка мира под курсором остаётся на месте
    canvas.addEventListener('wheel', function (e) {
      e.preventDefault();
      S.unlock();
      if (inputBlocked()) return;
      humanAt = t;
      if (panel === 1 && INV.open) { INV.wheel(e.deltaY); return; }
      if (panel === 1 && LORE.wheel(e.deltaY, e.clientX, e.clientY)) return;
      var dir = e.deltaY > 0 ? -1 : 1;
      var z = F.zoom * (dir > 0 ? 1.12 : 1 / 1.12);
      if (Math.abs(z - F.zoom) < 1e-4) return;
      F.setZoom(z, e.clientX, e.clientY);
      S.zoom(dir);
    }, { passive: false });

    // браузер не даёт звук до первого действия игрока
    ['pointerdown', 'pointermove', 'keydown'].forEach(function (ev) {
      window.addEventListener(ev, function () { S.unlock(); }, { once: true });
    });
  }

  /* Ввод игрока. Пока идёт заставка, пока существо само забрало пульт, пока
     корабль переезжает или отстреливает кресло, руки игрока ничего не делают. */
  function inputBlocked() {
    return !ctrl() || forced || !!eject || !!(move && (move.st === 'jump' || move.st === 'spool'));
  }

  function onMove(x, y) {
    if (inputBlocked()) return;
    if (!humanActive()) {
      Pointer.tx = Pointer.x = hand.x; Pointer.ty = Pointer.y = hand.y;
      if (creature.st !== 'away') creature.detach();
      toNav = null;
    }
    humanAt = t;
    Pointer.tx = x; Pointer.ty = y;
    if (panel === 1 && INV.open) INV.move(x, y);
    else if (panel === 1) LORE.move(x, y);
  }

  function onDown(x, y) {
    if (inputBlocked()) return;
    if (!humanActive() && creature.st !== 'away') { creature.detach(); toNav = null; }
    humanAt = t;
    Pointer.tx = Pointer.x = x; Pointer.ty = Pointer.y = y;
    pressed = true;

    var ph = panelHit(x, y);
    if (ph === 2) { INV.close(); LORE.toggleJournal(); return; }
    if (ph === 3) { if (LORE.journalOpen) LORE.toggleJournal(); INV.toggle(); S.tab(INV.open ? 1 : 0); return; }
    if (ph >= 0) { switchPanel(ph); return; }

    if (panel === 1) {
      if (INV.open) { INV.press(x, y); return; }
      var lf = LORE.journalOpen ? -1 : folderHit(x, y);
      if (lf >= 0) { LORE.folderClick(lf); return; }
      LORE.press(x, y);
      return;
    }
    if (con) { conClick(x, y, 'player'); return; }
    if (sel === SEL.CONFIRM && button &&
        Math.hypot(x - button.x, y - button.y) < button.r + 12) {
      clickButton();
      return;
    }
    if (sel === SEL.CONFIRM) { abort(); return; }
    if (sel === SEL.IDLE && flushHit(x, y)) {
      pulses.push({ x: flushPos().x, y: flushPos().y, age: 0, strong: false });
      flush();
      return;
    }
    if (sel === SEL.IDLE) {
      var fi = folderHit(x, y);
      if (fi >= 0) { if (fi === phase) deactivate(); else setPhase(fi); return; }
      if (phase === PHASE.PURGE && PG.active()) { PG.press(x, y); return; }
      if (phase === PHASE.SORT && SZ.active()) {
        if (button && Math.hypot(x - button.x, y - button.y) < button.r + 12) {
          sortFinish(); return;
        }
        SZ.pick(x, y);
        return;
      }
      if (phase === PHASE.SORT && !SZ.active()) {
        /* Сортировать нечего — зато можно взять крутящийся знак и перенести
           его в любую разложенную фигуру на карте. */
        var sc = F.cellNear(x, y);
        if (sc && sc.d < TOL && F.spinAt(sc.wx, sc.wy) !== undefined) {
          spinDrag = { wx: sc.wx, wy: sc.wy, g: F.spinAt(sc.wx, sc.wy) };
          S.pickUp();
        } else S.nothing();
        return;
      }
      if (phase === PHASE.ANALYZE) { analyzePick(x, y); return; }
      if (phase === PHASE.NONE) {
        // свободный режим: зажатая пустота открывает ввод команды
        var vd = F.voidNear(x, y, TOL);
        if (vd) conPress(vd, 'player');
        return;
      }
      if (phase !== PHASE.COLLECT) return;
    }
    press(x, y);
  }

  function onUp(x, y) {
    pressed = false;
    if (inputBlocked()) return;
    humanAt = t;
    if (conHold) { conRelease(); return; }
    if (spinDrag) { if (panel === 0) dropSpin(x, y); else spinDrag = null; return; }
    if (panel === 1 && INV.open) { INV.release(); return; }
    if (panel === 1) { LORE.release(x, y); return; }
    if (phase === PHASE.PURGE && PG.active()) { PG.release(); return; }
    if (phase === PHASE.SORT && SZ.dragging) { SZ.drop(); return; }
    if (sel !== SEL.DRAG) return;
    release(x, y);
  }

  /* Новые особые знаки навигационного поля уходят в хранилище данных. */
  function onTrace(ev) {
    if (panel !== 0) return;
    // слева в хранилище то, что сделал игрок, справа — что существо само
    var by = humanActive() ? 'p' : 'c';
    if (ev.type === 'outline') {
      var shp = INV.addShape(ev.cells, ev.W, ev.H, by);
      ev.outline.invId = shp ? shp.id : 0;
    } else if (ev.type === 'purged') {
      INV.add({ k: 'purged', g: ev.id, by: by });
      if (ev.outline && ev.outline.invId) INV.markShape(INV.byId(ev.outline.invId), ev.wx, ev.wy);
    } else INV.add({ k: ev.type, g: ev.id, by: by });
  }

  var saveT = 0, navSaveT = 0;
  function persist() {
    var data = { v: 1, lore: LORE.serialize(), inv: INV.serialize(), life: { age: Math.round(age), tut: tut } };
    // навигационная карта тоже помнится: разложенные группы, пустоты, следы
    var nav = panel === 0 ? F.saveWorld() : navWorld;
    if (nav && ctrl()) data.nav = F.worldToJSON(nav);
    // карта не влезла в хранилище браузера — лор и хранилище важнее, пишем без неё
    if (!root.Save.write(data) && data.nav) { delete data.nav; root.Save.write(data); }
    LORE.clean(); INV.clean();
  }
  function stepSave(dt) {
    saveT += dt; navSaveT += dt;
    if (saveT < 10) return;
    saveT = 0;
    if (LORE.dirty || INV.dirty || navSaveT >= 30) { navSaveT = 0; persist(); }
  }

  function start() {
    canvas = document.getElementById('v');
    post = new root.Post(canvas);
    if (post.ok) {
      scene = document.createElement('canvas');
      ctx = scene.getContext('2d');
    } else {
      // без WebGL игра просто идёт без постобработки, а не падает
      post = null;
      scene = canvas;
      ctx = canvas.getContext('2d');
    }
    resize();
    F.init();
    F.setObjPicker(objPick);
    F.loadWorld(F.freshWorld({ w: NAV_W, h: NAV_W, seed: 0x5f3a71, zoom: 1 }));
    if (controlAt !== Infinity) scheduleBreaks();
    // память между запусками: лор и хранилище данных
    var saved = root.Save.load();
    if (saved) { if (saved.lore) LORE.load(saved.lore); if (saved.inv) INV.load(saved.inv); }
    // первое подключение — к старому существу, доживающему свой цикл
    if (saved && saved.life) { age = +saved.life.age || 0; tut = saved.life.tut || null; }
    else if ((!saved && INTRO_FULL) || /[?&]tut\b/.test(location.search)) tut = { play: 0, cycles: 0, t3: 0, anaErr: false };
    if (saved && saved.nav) {
      try { F.loadWorld(F.worldFromJSON(saved.nav)); }
      catch (e) { F.loadWorld(F.freshWorld({ w: NAV_W, h: NAV_W, seed: 0x5f3a71, zoom: 1 })); }
    }
    /* Полная заставка — только при самом первом запуске. Если сохранение уже
       есть, игрок это видел, и пульт отдаётся через несколько секунд: иначе
       после перезагрузки игрок снова ждал бы, пока существо пройдёт круг. */
    if (saved && controlAt === Infinity) { controlAt = 6; }
    F.onTrace(onTrace);
    window.addEventListener('beforeunload', persist);
    LORE.init({
      active: function () { return panel === 1; },
      view: function () { return { w: vw, h: vh }; },
      pointer: Pointer,
      folderPos: folderPos,
      pulse: function (x, y, s) { pulses.push({ x: x, y: y, age: 0, strong: !!s }); },
      outside: function (rc, x, y) { return outsidePoint(rc, x, y, 36); },
      train: function (cells, slot, essence, onDone) { launchTrain(cells, slot, onDone, essence); },
      inject: function (slot) { launchInject(slot); },
      drawInject: drawInject,
      setButton: function (b) { button = b; },
      chainMarks: chainMarks,
      drawThreads: drawThreads,
      guide: guideTo,
      reject: function (k) { reject = k; },
      shake: function (k) { shake = Math.max(shake, k); tearPulse = Math.max(tearPulse, k * 0.25); },
      time: function () { return t; }
    });
    Pointer.x = Pointer.tx = vw / 2;
    Pointer.y = Pointer.ty = vh / 2;
    hand = new root.Hand(vw / 2, vh / 2);
    creature = new root.Creature({
      hand: hand,
      view: function () { return { w: vw, h: vh }; },
      cursor: function () { return Pointer; },
      anchors: function (pred, margin) { return F.anchorsOnScreen(vw, vh, pred, margin); },
      screenOf: function (wx, wy) { return F.cellCenter(wx, wy); },
      armed: function () { return !!startAnchor; },
      press: press, release: release, abort: abort,
      /* Видимый жест нажатия: без него смена этапа выглядела самопроизвольной. */
      tap: function (x, y) { pulses.push({ x: x, y: y, age: 0, strong: false }); tapSquash = 0.14; },
      button: function () { return button; },
      clickButton: clickButton,
      phase: function () { return phase; },
      needPhase: needPhase,
      zoomBy: function (dir) {
        var z = F.zoom * (dir > 0 ? 1.18 : 1 / 1.18);
        /* Существо не отдаляет поле дальше 0.6: на сильном отдалении на экране
           в шесть раз больше знаков, и кадр становится в разы тяжелее. Игроку
           колесо по-прежнему даёт весь диапазон. */
        if (dir < 0 && z < 0.6) return;
        F.setZoom(z, vw / 2, vh / 2);
        S.zoom(dir);
      },
      zoom: function () { return F.zoom; },
      setPhase: setPhase,
      folderPos: folderPos,
      /* Существо знает работу, поэтому следующий узел цепочки ему известен.
         Но дойти до него и нажать оно всё равно должно руками. */
      chainNext: function () {
        for (var c = 0; c < chains.length; c++) {
          var ch = chains[c];
          if (!ch.done && ch.at < ch.nodes.length) return ch.nodes[ch.at];
        }
        return null;
      },
      analyzePick: analyzePick,
      sortActive: function () { return phase === PHASE.SORT && SZ.active() && !SZ.finishing(); },
      sortHint: SZ.hint,
      sortHeldLit: SZ.heldLit,
      sortPick: SZ.pick,
      sortDrop: SZ.drop,
      sortHeld: function () { var bb = SZ.board(); return bb ? bb.drag : -1; },
      cell: function () { return F.CELL; },
      oldness: oldness,
      slipTarget: slipTarget,
      slipAt: slipAt,
      sortFinish: sortFinish,
      sortBusy: function () { return SZ.finishing() || SZ.active(); },
      sortButton: function () { return button === sortBtn ? sortBtn : null; },
      purgeHint: function () { return phase === PHASE.PURGE ? PG.hint() : null; },
      purgeReady: PG.readyToLeave,
      purgePress: PG.press,
      purgeRelease: PG.release,
      view2: function () { return { w: vw, h: vh }; },

      // пульт команд
      breakDue: function () { return panel === 0 ? breakDue() : null; },
      deactivate: function () { deactivate(); },
      voidsOnScreen: function () { return F.voidsOnScreen(vw, vh); },
      conPress: function (x, y) {
        var v = F.voidNear(x, y, TOL);
        if (!v || phase !== PHASE.NONE || sel !== SEL.IDLE) return;
        conIntent = breakDue() || 'lunch';
        conPress(v, 'creature');
        pulses.push({ x: x, y: y, age: 0, strong: false });
      },
      conHolding: function () { return !!conHold || !!con; },
      conRelease: function () { if (!con) conRelease(); },
      conOpen: function () { return !!con; },
      conKeys: function () { return CMD[con && con.mode ? con.mode : conIntent]; },
      conClick: function (x, y) { conClick(x, y, 'creature'); },
      wear: function () {
        var c = F.camCell, n = 0, k = 0;
        var nx = Math.ceil(vw / F.CELL), ny = Math.ceil((vh - 130) / F.CELL);
        for (var j = 1; j < ny; j += 2) for (var i = 1; i < nx; i += 2) {
          k++;
          if (F.isWorked((Math.floor(c.x) + i + F.W) % F.W, (Math.floor(c.y) + j + F.H) % F.H)) n++;
        }
        return k ? n / k : 0;
      },
      pairWear: function (ax, ay, bx, by) {
        var dx = bx - ax, dy = by - ay;
        if (dx > F.W / 2) dx -= F.W; else if (dx < -F.W / 2) dx += F.W;
        if (dy > F.H / 2) dy -= F.H; else if (dy < -F.H / 2) dy += F.H;
        var x0 = Math.min(0, dx), y0 = Math.min(0, dy), n = 0, k = 0;
        for (var j = 0; j <= Math.abs(dy); j++) for (var i = 0; i <= Math.abs(dx); i++) {
          k++;
          if (F.isWorked((ax + x0 + i + F.W) % F.W, (ay + y0 + j + F.H) % F.H)) n++;
        }
        return k ? n / k : 0;
      },
      conMode: function () { return con ? con.mode : null; },
      conVoid: function () { return con ? F.cellCenter(con.wx, con.wy) : null; },
      flushNeeded: function () { return panel === 0 && purgeDrain <= 0 && unitsAt(3).length > 0; },
      flushPos: flushPos,
      flush: flush,
      revealAt: function (wx, wy) { return reveals.get(F.ckey(wx, wy)) || null; },
      teaching: function () { return !ctrl(); },
      time: function () { return t; },
      mapId: function () { return mapId; },
      mapSize: function () { return { w: F.W, h: F.H }; },
      home: function () { return { x: F.W / 2, y: F.H / 2 }; },
      viewCell: function () { var c = F.camCell; return { x: c.x + vw / 2 / F.CELL, y: c.y + (vh - 110) / 2 / F.CELL }; },
      conProgress: function () { return con ? (con.mode ? con.rseq.length : con.seq.length) : 0; },
      findKey: function (gid, hx, hy) {
        /* Обратную команду набирают по тем же знакам, что горят с прямой.
           Раньше они исключались из поиска, и если нужный знак на экране был
           один, существо не могло вернуться с обеда и зависало навсегда. */
        if (con && con.mode) {
          for (var s = 0; s < con.seq.length; s++) {
            var sk = con.seq[s];
            if (sk.gid !== gid || F.isSpecial(sk.wx, sk.wy)) continue;
            var sp = F.cellCenter(sk.wx, sk.wy);
            if (sp.x > 20 && sp.y > 90 && sp.x < vw - 20 && sp.y < vh - 130) return { wx: sk.wx, wy: sk.wy };
          }
        }
        var used = {};
        if (con) (con.mode ? con.rseq : con.seq).forEach(function (k) { used[F.ckey(k.wx, k.wy)] = 1; });
        var hits = F.findGlyph(gid, 0, Math.ceil(vw / F.CELL) + 2, Math.ceil(vh / F.CELL) + 2, used);
        var best = null, bd = Infinity;
        for (var i = 0; i < hits.length; i++) {
          var p = F.cellCenter(hits[i].wx, hits[i].wy);
          if (p.x < 50 || p.y < 100 || p.x > vw - 50 || p.y > vh - 150) continue;
          var d = Math.hypot(p.x - hx, p.y - hy);
          if (d < bd) { bd = d; best = { wx: hits[i].wx, wy: hits[i].wy }; }
        }
        return best;
      }
    });
    bind();
    if (dev) {
      root.ORT = {
        creature: creature,
        hand: hand,
        tick: function (dt, n) {
          for (var i = 0; i < (n || 1); i++) simulate(dt || 1 / 60);
        },
        draw: render,
        onMove: onMove, onDown: onDown, onUp: onUp,
        switchPanel: switchPanel,
        inv: INV, persist: persist,
        stock: function () { return stock; },
        chains: function () { return chains; },
        sizes: function () {
          return { field: F.sizes(), stock: stock.length, taken: taken.size, reveals: reveals.size, trains: trains.length,
                   flying: flying.length, pulses: pulses.length, errDots: errDots.length, inject: inject.length, marks: marks.size,
                   inv: INV.count, heapMB: performance.memory ? Math.round(performance.memory.usedJSHeapSize / 1048576) : null };
        },
        errDots: spawnErrDots,
        sortButton: function () { return button === sortBtn ? sortBtn : null; },
        setPhase: setPhase,
        breakNow: function (kind) { if (kind === 'sleep') sleepDue = t; else lunchDue = t; },
        relocateNow: function () { MOVE_FILL = 0; },
        endNow: function (r) { endCycle(r || 'drift'); },
        setDrift: function (v) { drift = v; },
        setAge: function (v) { age = v; },
        oldFx: function () { vbarT = 0; coughT = 0; },
        spawnObj: function (type, r0, r1, onum) { return spawnNear(type, r0 || 4, r1 || 6, onum); },
        objects: function () { return F.objects(); },
        button: function () { return button; },
        oldFxHold: function (k) {
          if (vbar) vbar.dur *= k;
          if (cough) { cough.pat.forEach(function (p) { p.at *= k; p.dur *= k; }); cough.end *= k; }
        },
        oldFxState: function () { return { vbar: !!vbar, cough: cough ? cough.pat.length : 0, env: coughEnv() }; },
        tut: function () { return tut; },
        driftMax: function () { return driftMax(); },
        ejectFx: function () { return ejectFx; },
        state: function () {
          return {
            t: Math.round(t), panel: panel, controlAt: controlAt, forced: forced, handover: !!handover,
            con: con ? { mode: con.mode, seq: con.seq.length, rseq: con.rseq.length, revDone: con.revDone } : null,
            conHold: !!conHold, lunchDue: Math.round(lunchDue - t), sleepDue: Math.round(sleepDue - t),
            lunchDenied: lunchDenied, sleepDenied: sleepDenied,
            move: move ? move.st : null, eject: eject ? eject.reason : null,
            fill: Math.round(F.fill() * 10000) / 10000, mapId: mapId, cycles: cycles, age: Math.round(age), drift: Math.round(drift * 10) / 10,
            creature: creature.st + '/' + creature.sub
          };
        },
        runTo: function (want, maxSec) {
          var n = Math.round((maxSec || 60) * 60);
          for (var i = 0; i < n; i++) {
            simulate(1 / 60);
            if (['idle', 'drag', 'confirm', 'send'][sel] === want) return Math.round(i / 60 * 10) / 10;
          }
          return null;
        },
        peek: function () {
          return {
            sel: ['idle', 'drag', 'confirm', 'send'][sel],
            creature: creature.st + '/' + creature.sub,
            startAnchor: startAnchor ? startAnchor.rec.kind : null,
            pool: creature.pool.length,
            phase: ['none', 'collect', 'analyze', 'sort', 'purge'][phase + 1],
            folder0: folders[0],
            folder1: folders[1],
            chains: chains.filter(function (c) { return !c.done; }).length,
            sortFrac: Math.round((SZ.active() ? SZ.progress().frac : 0) * 100) / 100,
            purge: PG.active() ? PG.progress() : null,
            folder3: folders[3],
            sortShape: SZ.active() ? Math.round(SZ.shape() * 100) / 100 : null,
            folder2: folders[2],
            trains: trains.length,
            errors: errors,
            reveals: reveals.size,
            taken: taken.size,
            anchorsOnScreen: F.anchorsOnScreen(vw, vh, REAL).length,
            decoysOnScreen: F.anchorsOnScreen(vw, vh, function (a) { return !a.role; }).length,
            sameGid: startAnchor
              ? F.anchorsOnScreen(vw, vh, function (a) { return a.gid === startAnchor.rec.gid; }).length
              : null,
            drift: Math.round(drift * 10) / 10
          };
        }
      };
    }
    last = performance.now();
    startBackground();
    requestAnimationFrame(frame);
  }

  /* В фоновой вкладке (и в окне, закрытом другими) браузер не зовёт
     requestAnimationFrame, и мир вставал: звук играл, а существо часами
     сидело без дела. Поэтому время подгоняет ещё и таймер в отдельном
     потоке — его браузер почти не душит. Если кадры идут, таймер молчит;
     если кадров нет дольше 0.4 с, он сам досчитывает прошедшее время.
     Рисовать в скрытой вкладке незачем, считается только работа. */
  var lastSimAt = 0;
  function backgroundTick() {
    var nowMs = performance.now();
    if (nowMs - lastSimAt < 400) return;
    var el = Math.min(300, (nowMs - lastSimAt) / 1000);
    lastSimAt = nowMs;
    while (el > 0) { var d = Math.min(0.05, el); simulate(d); el -= d; }
  }
  function startBackground() {
    // вкладка могла открыться сразу в фоне, без единого кадра
    lastSimAt = performance.now();
    try {
      var code = 'setInterval(function () { postMessage(0); }, 250);';
      var w = new Worker(URL.createObjectURL(new Blob([code], { type: 'text/javascript' })));
      w.onmessage = backgroundTick;
    } catch (e) {
      setInterval(backgroundTick, 250);
    }
  }

  root.addEventListener('load', start);
})(window);
