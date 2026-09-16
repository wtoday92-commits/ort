/* ORT — сортировка.
 *
 * На поле выделяется большой блок. Внутри него стоят неподвижные ЯКОРЯ —
 * ровно те знаки, что пришли с анализа. Их трогать нельзя. Всё остальное в
 * блоке можно брать и перетаскивать.
 *
 * Задача: собрать возле каждого якоря все знаки того же начертания так, чтобы
 * они смыкались с ним по вертикали или горизонтали. Сомкнувшийся знак
 * загорается. Когда берёшь знак и ведёшь его на новое место, остальные вдоль
 * пути аккуратно сдвигаются на одну клетку и занимают освободившееся место.
 *
 * Закончить можно в любой момент кнопкой у края блока. Если собрано не всё,
 * этап не закрыт: в папке останется остаток, и его придётся доделывать, а
 * корабль всё это время будет копить шкалу дефекта.
 *
 * Форма собранного тоже важна, и это главная ловушка этапа. Линия проходит
 * как «без ошибки», но для корабля она всё равно неправильная, и шкала чуть
 * двинется. Правильны плотные блоки, и именно их показывает существо.
 *
 * После окончания знаки остаются на поле там, где их оставил игрок, навсегда.
 */
(function (root) {
  'use strict';

  var G = root.Glyphs, S = root.Sound;

  var BW = 13, BH = 9;        // размер текущего блока, приходит с областью
  var ANCH = 3;               // сколько групп разбираем разом

  var F = null;
  var b = null;               // текущая доска

  function idx(cx, cy) { return cy * BW + cx; }
  function inside(cx, cy) { return cx >= 0 && cy >= 0 && cx < BW && cy < BH; }

  /* Объём сортировки задаёт АНАЛИЗ: сколько цепочек игрок оттуда прислал,
     столько якорей и будет. Прислал одну — ищешь дубли одного знака в
     небольшом блоке. Накопил три — разбираешь три группы разом в большом.
     Существо работает по одной цепочке за круг, поэтому у него всегда один
     якорь, и сортировка у него короткая. */
  /* Доска — это НАЙДЕННЫЙ кусок карты, а не новый набор знаков. Приходит
     готовая область и список начертаний, которые в ней надо сгрести. Особые
     знаки внутри области неподвижны наравне с якорями: поле их не отдаёт. */
  function build(field, vw, vh, reg, gids, want) {
    F = field;
    BW = reg.w; BH = reg.h;
    var cells = new Array(BW * BH), occ = {}, x, y, i;

    for (y = 0; y < BH; y++) {
      for (x = 0; x < BW; x++) {
        var wx = (reg.ox + x + F.W) % F.W, wy = (reg.oy + y + F.H) % F.H;
        var id = F.glyphAt(wx, wy);
        /* Пустота на доске подвижна: её сдвигает протаскиваемый знак, как и
           любой другой. Остальные особые знаки неподвижны. Вне сортировки
           пустота по-прежнему не двигается никогда. */
        var vd = F.isVoidCell(wx, wy);
        // разложенные раньше группы неприкосновенны: их не вытолкнуть и не заместить
        var sp = !vd && (F.isSpecial(wx, wy) || F.isSorted(wx, wy));
        cells[idx(x, y)] = { id: vd ? F.VOID_GID : id, anchor: false, fixed: sp, isVoid: vd, px: 0, py: 0, set: false };
        if (!sp && !vd && gids.indexOf(id) >= 0) (occ[id] = occ[id] || []).push(idx(x, y));
      }
    }

    /* Чего в области не хватает, то ПРИЛЕТАЕТ ИЗ ПАПКИ и замещает собой
       обычные знаки внутри блока. Брать только то, что уже лежит на карте,
       оказалось неудобно: одного начертания из двухсот шестнадцати в случайном
       месте почти не бывает, и блоки выходили вымученными. */
    var inject = [];
    for (var g = 0; g < gids.length; g++) {
      var list = occ[gids[g]] || (occ[gids[g]] = []);
      // размер группы задаётся на каждое начертание отдельно
      var wantG = Array.isArray(want) ? (want[g] || 4) : (want || 4);
      var miss = Math.max(0, wantG - list.length);
      if (!miss) continue;
      var free = [];
      for (i = 0; i < cells.length; i++) {
        if (cells[i].fixed || cells[i].isVoid || gids.indexOf(cells[i].id) >= 0) continue;
        free.push(i);
      }
      for (var m = 0; m < miss && free.length; m++) {
        var pick = free.splice(Math.floor(Math.random() * free.length), 1)[0];
        cells[pick].id = gids[g];
        cells[pick].pending = true;      // пока летит, в клетке пусто
        list.push(pick);
        inject.push({ i: pick, gid: gids[g] });
      }
    }

    var anchors = [], total = 0;
    for (g = 0; g < gids.length; g++) {
      var lst = occ[gids[g]] || [];
      if (lst.length < 2) continue;
      // якорем становится тот, что уже лежал на карте
      var ai = lst[0];
      cells[ai].anchor = true;
      cells[ai].pending = false;
      anchors.push({ cx: ai % BW, cy: (ai / BW) | 0, id: gids[g], need: lst.length - 1 });
      total += lst.length - 1;
    }

    b = {
      ox: reg.ox, oy: reg.oy, ids: gids, anchors: anchors, cells: cells,
      drag: -1, stepT: 0, lit: [], total: total, units: anchors.length, fin: null,
      inject: inject
    };
    relight();
    return b;
  }

  /* Прилетевший знак занимает своё место. */
  function land(i) {
    if (!b || !b.cells[i]) return;
    b.cells[i].pending = false;
    relight();
  }

  function cellScreen2(i) { return cellScreen(i % BW, (i / BW) | 0); }

  function cellKey(cx, cy) {
    return F.ckey((b.ox + cx + F.W) % F.W, (b.oy + cy + F.H) % F.H);
  }

  function cellScreen(cx, cy) {
    return F.cellCenter((b.ox + cx + F.W) % F.W, (b.oy + cy + F.H) % F.H);
  }

  /* Что смыкается с якорем через клетки того же начертания — то и горит. */
  function relight() {
    var i;
    b.lit = new Array(BW * BH);
    for (i = 0; i < b.anchors.length; i++) {
      var a = b.anchors[i], stack = [[a.cx, a.cy]], seen = {};
      while (stack.length) {
        var p = stack.pop(), key = p[0] + ',' + p[1];
        if (seen[key]) continue;
        seen[key] = 1;
        var cell = b.cells[idx(p[0], p[1])];
        if (!cell || cell.pending || cell.id !== a.id) continue;
        b.lit[idx(p[0], p[1])] = 1;
        var nb = [[p[0] + 1, p[1]], [p[0] - 1, p[1]], [p[0], p[1] + 1], [p[0], p[1] - 1]];
        for (var q = 0; q < 4; q++) if (inside(nb[q][0], nb[q][1])) stack.push(nb[q]);
      }
    }
  }

  /* Смыкание двух РАЗНЫХ групп. Это же сортировка: разное лежать вместе не
     должно. Такие клетки становятся якорями-глюками и остаются на поле. */
  function touching(i) {
    if (!b.lit[i]) return false;
    var x = i % BW, y = (i / BW) | 0, id = b.cells[i].id;
    for (var d = 0; d < 4; d++) {
      var nx = x + DIRS[d][0], ny = y + DIRS[d][1];
      if (!inside(nx, ny)) continue;
      var ni = idx(nx, ny);
      if (b.lit[ni] && b.cells[ni].id !== id) return true;
    }
    return false;
  }

  /* Сколько групп собрано ПОЛНОСТЬЮ и без глюков. Каждая такая группа — одна
     единица, ровно та цепочка, что пришла с анализа. */
  function doneUnits() {
    var n = 0;
    for (var a = 0; a < b.anchors.length; a++) {
      var an = b.anchors[a], ok = true, cnt = 0;
      for (var i = 0; i < b.cells.length && ok; i++) {
        if (b.cells[i].id !== an.id) continue;
        if (touching(i)) ok = false;
        else if (b.lit[i]) cnt++;
      }
      if (ok && cnt >= an.need + 1) n++;
    }
    return n;
  }

  function progress() {
    var lit = 0, i;
    for (i = 0; i < b.cells.length; i++) {
      if (b.cells[i].anchor) continue;
      if (b.ids.indexOf(b.cells[i].id) >= 0 && b.lit[i]) lit++;
    }
    return { lit: lit, total: b.total, frac: b.total ? lit / b.total : 1 };
  }

  /* Насколько собранное похоже на плотный блок, а не на линию или россыпь.
     Считаем смычки внутри каждой связки и делим на предел для такого числа
     клеток. У линии смычек вдвое меньше, чем у квадрата, и корабль это
     заметит, даже если формально сортировка сошлась. */
  function shape() {
    var adj = 0, best = 0;
    for (var a = 0; a < b.anchors.length; a++) {
      var cnt = 0, an = b.anchors[a];
      for (var y = 0; y < BH; y++) {
        for (var x = 0; x < BW; x++) {
          var i = idx(x, y);
          if (!b.lit[i] || b.cells[i].id !== an.id) continue;
          cnt++;
          if (inside(x + 1, y) && b.lit[idx(x + 1, y)] && b.cells[idx(x + 1, y)].id === an.id) adj++;
          if (inside(x, y + 1) && b.lit[idx(x, y + 1)] && b.cells[idx(x, y + 1)].id === an.id) adj++;
        }
      }
      if (cnt > 1) best += 2 * cnt - 2 * Math.ceil(Math.sqrt(cnt));
    }
    return best > 0 ? Math.max(0, Math.min(1, adj / best)) : 1;
  }

  // --- перетаскивание --------------------------------------------------------

  function cellAt(x, y) {
    var best = -1, bd = 1e9;
    for (var y2 = 0; y2 < BH; y2++) {
      for (var x2 = 0; x2 < BW; x2++) {
        var p = cellScreen(x2, y2);
        var dx = p.x - x, dy = p.y - y, d = dx * dx + dy * dy;
        if (d < bd) { bd = d; best = idx(x2, y2); }
      }
    }
    return bd < (F.CELL * 0.85) * (F.CELL * 0.85) ? best : -1;
  }

  function pick(x, y) {
    if (!b || b.fin) return false;
    var i = cellAt(x, y);
    // пустоту саму не берут: она только уступает дорогу
    if (i < 0 || b.cells[i].anchor || b.cells[i].fixed || b.cells[i].pending || b.cells[i].isVoid) return false;
    b.drag = i;
    b.stepT = 0;
    if (S) S.pickUp();
    return true;
  }

  /* Взятый знак не летает поверх доски: он ПРОТАЛКИВАЕТСЯ сквозь неё. Клетка,
     в которой он сейчас, шагает по одной за курсором, и сосед, через которого
     он проходит, занимает освободившееся место. Дальше тот же сосед освободит
     место следующему, и сетка перетекает сама собой.

     Раньше сдвиг считался разом в момент отпускания: знак плыл поверх чужих
     клеток, а потом целая строка резко переставлялась. */
  function dragStep(cursor) {
    var from = b.drag;
    var fx = from % BW, fy = (from / BW) | 0;
    var to = cellAt(cursor.x, cursor.y);
    if (to < 0 || to === from) return false;

    /* Шаг считается по КРАТЧАЙШЕМУ пути, а не жадно. Жадный обход застревал в
       тупиках: каждый соседний проход уводил дальше от цели, груз вставал, и
       почти каждый ход оказывался впустую.

       Якоря и уже сомкнувшиеся знаки с места не сдвинуть: иначе, протаскивая
       груз сквозь собранную связку, её же и разваливаешь. Эти клетки подсвечены
       сильнее прочих, так что правило читается. */
    var next = firstStep(from, to, false);
    // обычного пути нет: только тогда груз перескакивает неподвижные знаки
    if (next < 0) next = firstStep(from, to, true);
    if (next < 0) return false;

    var tmp = b.cells[next];
    b.cells[next] = b.cells[from];
    b.cells[from] = tmp;
    b.drag = next;
    return true;
  }

  var DIRS = [[1, 0], [-1, 0], [0, 1], [0, -1]];

  function passable(i) { return !b.cells[i].anchor && !b.cells[i].fixed && !b.cells[i].pending && !b.lit[i]; }

  /* Первый шаг кратчайшего пути от клетки груза к клетке под курсором.

     Пустота на доске подвижна и дорогу не перекрывает. Остальные неподвижные
     знаки (утилизированное, осколки, глюки) груз перескакивает, но только
     если обходного пути нет вовсе: перескок выглядит странно. */
  function firstStep(from, to, skip) {
    if (from === to) return -1;
    var prev = new Int16Array(BW * BH).fill(-1);
    var seen = new Uint8Array(BW * BH);
    var q = [from], head = 0;
    seen[from] = 1;
    while (head < q.length) {
      var cur = q[head++];
      var cx = cur % BW, cy = (cur / BW) | 0;
      for (var d = 0; d < 4; d++) {
        var nx = cx + DIRS[d][0], ny = cy + DIRS[d][1];
        while (skip && inside(nx, ny) && b.cells[idx(nx, ny)].fixed) { nx += DIRS[d][0]; ny += DIRS[d][1]; }
        if (!inside(nx, ny)) continue;
        var ni = idx(nx, ny);
        if (seen[ni] || !passable(ni)) continue;
        seen[ni] = 1; prev[ni] = cur;
        if (ni === to) {
          var walk = ni;
          while (prev[walk] !== from) walk = prev[walk];
          return walk;
        }
        q.push(ni);
      }
    }
    return -1;
  }

  function drop() {
    if (!b || b.drag < 0) return false;
    b.drag = -1;
    relight();
    if (S) S.putDown();
    return true;
  }

  // --- кадр ------------------------------------------------------------------

  function step(dt, cursor) {
    if (!b) return;

    if (b.drag >= 0 && cursor) {
      b.stepT -= dt;
      var moved = 0;
      // до трёх шагов за кадр, иначе на быстром ведении доска отстаёт
      while (b.stepT <= 0 && moved < 3) {
        if (!dragStep(cursor)) break;
        moved++;
        b.stepT += 0.045;
      }
      if (b.stepT < 0) b.stepT = 0;
      // каждый шаг груза сквозь доску слышен: знаки шуршат, уступая место
      if (moved) { relight(); if (S) S.slide(moved); }
    } else if (cursor && !b.fin) {
      // курсор над доской тихо щёлкает на каждой новой клетке
      var hv = cellAt(cursor.x, cursor.y);
      if (hv >= 0 && hv !== b.hover && S) S.hover();
      b.hover = hv;
    }

    var k = Math.min(1, dt * 13);
    for (var y = 0; y < BH; y++) {
      for (var x = 0; x < BW; x++) {
        var i = idx(x, y), c = b.cells[i];
        var p = cellScreen(x, y);
        var tx = p.x, ty = p.y;
        if (i === b.drag && cursor) { tx = cursor.x; ty = cursor.y; }
        if (!c.set) { c.px = tx; c.py = ty; c.set = true; }
        else { c.px += (tx - c.px) * (i === b.drag ? Math.min(1, dt * 26) : k); c.py += (ty - c.py) * k; }
      }
    }
    if (b.fin) {
      b.fin.t += dt;
      // звук идёт вместе с подсветкой, знак за знаком
      var ph = finPhase(), lit = Math.floor((b.fin.t - ph.tB) / 0.17);
      if (lit > b.fin.rang && lit >= 0 && lit < b.fin.order.length) {
        b.fin.rang = lit;
        if (S) {
          if (b.fin.bad.indexOf(b.fin.order[lit]) >= 0) S.glitch();
          else S.settle(lit, b.fin.order.length);
        }
      }
      if (!b.fin.warned && b.fin.missed.length && b.fin.t > ph.tC) {
        b.fin.warned = true;
        if (S) S.forgot();
      }
    }
  }

  /* Накладка на поле: блок целиком подменяет собой то, что в нём было. */
  /* Якоря и уже сомкнувшиеся знаки светятся ВСЕГДА, а не только пока знак в
     руке. Наполнитель блока при этом приглушён. Раньше подсветка включалась
     лишь на перетаскивании, а фон блока и так стоял почти в насыщении, так
     что контраста не оставалось вовсе: цели было не видно. */
  function marks(out) {
    if (!b) return;
    var held = b.drag >= 0;
    for (var y = 0; y < BH; y++) {
      for (var x = 0; x < BW; x++) {
        var i = idx(x, y), c = b.cells[i];
        var p = cellScreen(x, y);
        var m = {
          id: c.id, head: c.anchor ? 1 : 0, still: 1, lean: 0,
          px: c.px - p.x, py: c.py - p.y, lit: 0, grow: 0, dim: 0, grab: 0, scale: 0
        };
        if (c.pending) { m.hide = 1; out.set(cellKey(x, y), m); continue; }
        if (b.fin) finMark(m, i);
        else {
          m.lit = b.lit[i] ? 1 : 0;
          var important = m.lit || c.anchor;
          m.grab = i === b.drag ? 1 : 0;
          m.grow = important ? (held ? 0.55 : 0.3) : 0;
          m.dim = important || i === b.drag ? 0 : (held ? 0.62 : 0.44);
        }
        out.set(cellKey(x, y), m);
      }
    }
  }

  /* Концовка идёт ступенями и НЕ ТОРОПИТСЯ:
       1. весь блок садится в размере и гаснет;
       2. собранное загорается по одному, неспешно;
       3. если что-то не собрано, забытые знаки мелко дрожат: вот их и
          проглядели;
       4. остальным плавно возвращается размер и цвет, рамка тает. */
  function finPhase() {
    var f = b.fin;
    var tB = 1.1;
    var tC = tB + f.order.length * 0.17;
    var tD = tC + (f.missed.length ? 1.6 : 0.7);
    return { tB: tB, tC: tC, tD: tD, tEnd: tD + 1.1 };
  }

  function finMark(m, i) {
    var f = b.fin, ph = finPhase(), T = f.t;
    var sink = Math.min(1, T / ph.tB);
    var back = T > ph.tD ? Math.min(1, (T - ph.tD) / 1.1) : 0;
    var k = sink * (1 - back);

    var pos = f.order.indexOf(i);
    if (pos >= 0) {
      var at = ph.tB + pos * 0.17;
      if (T >= at) {
        if (f.bad.indexOf(i) >= 0) {
          /* Соприкоснувшиеся группы: подсветка дошла и вместо ровного света
             дала сбой. Знак дрожит вразнобой и мерцает не в такт ничему. */
          m.px += Math.sin(T * 44 + i * 2.3) * 4.2;
          m.py += Math.cos(T * 39 + i) * 2.8;
          m.scale = 0.9 + 0.2 * Math.sin(T * 27 + i);
          m.grow = Math.sin(T * 19 + i) > 0 ? 0.7 : 0;
          m.dim = 0.35;
          return;
        }
        m.lit = 1;
        var pop = Math.max(0, 1 - (T - at) / 0.45);
        m.scale = 1 + pop * 0.22;
        m.grow = 0.3 + pop * 0.5;
        return;
      }
    }
    if (f.missed.indexOf(i) >= 0 && T > ph.tC && T < ph.tD) {
      // забытое дрожит: так видно, чего именно не хватило
      m.px += Math.sin(T * 38 + i) * 3.4;
      m.grow = 0.3 * (0.5 + 0.5 * Math.sin(T * 17 + i));
      m.dim = 0.2;
      return;
    }
    m.scale = 1 - 0.3 * k;
    m.dim = 0.72 * k;
  }

  function frame() {
    var a = cellScreen(0, 0), z = cellScreen(BW - 1, BH - 1);
    var h = F.CELL * 0.62;
    return { x0: a.x - h, y0: a.y - h, x1: z.x + h, y1: z.y + h };
  }

  function button() {
    var f = frame();
    return { x: f.x1 + 34, y: f.y1 - 12, r: 21, hot: 0 };
  }

  function draw(ctx, t) {
    if (!b) return;
    var f = frame();
    var fade = 1;
    if (b.fin) {
      var ph = finPhase();
      fade = b.fin.t > ph.tD ? Math.max(0, 1 - (b.fin.t - ph.tD) / 1.1) : 1;
    }
    if (fade <= 0.01) return;
    ctx.save();
    ctx.globalAlpha = fade;
    ctx.globalCompositeOperation = 'lighter';
    var pr = progress();
    ctx.strokeStyle = 'rgba(255,196,124,' + (0.30 + pr.frac * 0.30) + ')';
    ctx.lineWidth = 1.1;
    ctx.strokeRect(f.x0 + 0.5, f.y0 + 0.5, f.x1 - f.x0, f.y1 - f.y0);
    var c = 16;
    ctx.lineWidth = 1.9;
    ctx.beginPath();
    [[f.x0, f.y0, 1, 1], [f.x1, f.y0, -1, 1], [f.x0, f.y1, 1, -1], [f.x1, f.y1, -1, -1]].forEach(function (p) {
      ctx.moveTo(p[0], p[1] + p[3] * c); ctx.lineTo(p[0], p[1]); ctx.lineTo(p[0] + p[2] * c, p[1]);
    });
    ctx.stroke();
    ctx.restore();
  }

  /* Итог по каждой группе: сколько надо было и сколько собрано. По нему
     недособранная группа повторяется ровно с тем же знаком и ровно на
     недостающее число. */
  function groupsState() {
    return b.anchors.map(function (an) {
      var ok = true, cnt = 0;
      for (var i = 0; i < b.cells.length; i++) {
        if (b.cells[i].id !== an.id) continue;
        if (touching(i)) ok = false;
        else if (b.lit[i]) cnt++;
      }
      return { id: an.id, need: an.need, got: Math.max(0, cnt - 1), done: ok && cnt >= an.need + 1 };
    });
  }

  function finish() {
    if (!b || b.fin) return null;
    var pr = progress(), sh = shape();
    var order = [], missed = [], bad = [], i;
    for (i = 0; i < b.cells.length; i++) {
      if (b.lit[i]) { order.push(i); if (touching(i)) bad.push(i); }
      else if (!b.cells[i].anchor && b.ids.indexOf(b.cells[i].id) >= 0) missed.push(i);
    }
    order.sort(function (p, q) { return p - q; });
    b.fin = { t: 0, order: order, missed: missed, bad: bad, rang: -1, warned: false };
    return {
      frac: pr.frac, shape: sh, steps: order.length,
      missed: missed.length, glitches: bad.length,
      units: doneUnits(), total: b.units, groups: groupsState()
    };
  }

  function finishing() { return !!(b && b.fin); }

  function finishProgress() {
    if (!b || !b.fin || !b.fin.order.length) return 1;
    var ph = finPhase();
    return Math.max(0, Math.min(1, (b.fin.t - ph.tB) / (ph.tC - ph.tB)));
  }

  function finishDone() {
    return !!(b && b.fin && b.fin.t >= finPhase().tEnd);
  }

  /* Знаки остаются на поле ровно там, где их оставил игрок. Навсегда. */
  function commit() {
    if (!b) return;
    for (var y = 0; y < BH; y++) {
      for (var x = 0; x < BW; x++) {
        var ck = cellKey(x, y), cl = b.cells[idx(x, y)];
        F.setOverride(ck, cl.id);
        // пустота остаётся пустотой там, куда её сдвинули
        if (!cl.fixed) F.setVoidAt(ck, !!cl.isVoid);
      }
    }
    /* Обводим контуром каждую собранную без глюков группу: разложенное должно
       быть видно на поле и потом, а не теряться среди прочего письма. */
    for (var a = 0; a < b.anchors.length; a++) {
      var an = b.anchors[a], cells = [], bad = false;
      for (var i = 0; i < b.cells.length && !bad; i++) {
        if (b.cells[i].id !== an.id) continue;
        if (touching(i)) bad = true;
        else if (b.lit[i]) cells.push({ wx: (b.ox + (i % BW) + F.W) % F.W, wy: (b.oy + ((i / BW) | 0) + F.H) % F.H });
      }
      if (!bad && cells.length >= an.need + 1) F.addOutline(cells);
    }

    // якоря-глюки остаются на поле навсегда и никуда не уходят
    if (b.fin) {
      for (var g = 0; g < b.fin.bad.length; g++) {
        var i = b.fin.bad[g];
        F.setGlitch(cellKey(i % BW, (i / BW) | 0));
      }
    }
    b = null;
  }

  function active() { return !!b; }

  /* Сомкнулся ли знак, который сейчас в руке. Существо по этому и понимает,
     что груз встал на место, и отпускает. */
  function heldLit() { return !!(b && b.drag >= 0 && b.lit[b.drag]); }

  /* Подсказка существу. Оно знает работу и собирает ПЛОТНЫЕ блоки: выбирает
     место, у которого больше всего смычек с уже собранным. */
  function hint() {
    if (!b || b.fin) return null;
    for (var a = 0; a < b.anchors.length; a++) {
      var an = b.anchors[a];
      var need = 0, i;
      for (i = 0; i < b.cells.length; i++) {
        if (!b.cells[i].anchor && !b.cells[i].fixed && b.cells[i].id === an.id && !b.lit[i]) need++;
      }
      if (!need) continue;

      // габарит уже собранного, чтобы мерить раздувание
      var bx0 = 1e9, by0 = 1e9, bx1 = -1e9, by1 = -1e9;
      for (i = 0; i < b.cells.length; i++) {
        if (!b.lit[i] || b.cells[i].id !== an.id) continue;
        var lx = i % BW, ly = (i / BW) | 0;
        bx0 = Math.min(bx0, lx); bx1 = Math.max(bx1, lx);
        by0 = Math.min(by0, ly); by1 = Math.max(by1, ly);
      }

      var bestCell = -1, bestScore = -1e9;
      for (var y = 0; y < BH; y++) {
        for (var x = 0; x < BW; x++) {
          var j = idx(x, y);
          if (b.cells[j].anchor || b.cells[j].fixed || (b.lit[j] && b.cells[j].id === an.id)) continue;
          var touch = 0;
          [[1, 0], [-1, 0], [0, 1], [0, -1]].forEach(function (d) {
            var nx = x + d[0], ny = y + d[1];
            if (inside(nx, ny) && b.lit[idx(nx, ny)] && b.cells[idx(nx, ny)].id === an.id) touch++;
          });
          if (!touch) continue;
          /* В клетку надо ещё суметь войти. Якоря и сомкнувшиеся знаки не
             сдвигаются, поэтому цель, окружённая ими со всех сторон, это
             карман: груз туда не протолкнуть. Раньше существо выбирало такой
             карман и намертво вставало на последнем знаке. */
          var open = 0;
          [[1, 0], [-1, 0], [0, 1], [0, -1]].forEach(function (d) {
            var ex = x + d[0], ey = y + d[1];
            if (!inside(ex, ey)) return;
            var ei = idx(ex, ey);
            if (!b.cells[ei].anchor && !b.cells[ei].fixed && !b.lit[ei]) open++;
          });
          if (!open) continue;

          // к чужой группе не прислоняемся: это дало бы якорь-глюк
          var clash = false;
          for (var dd = 0; dd < 4; dd++) {
            var qx = x + DIRS[dd][0], qy = y + DIRS[dd][1];
            if (!inside(qx, qy)) continue;
            var qi = idx(qx, qy);
            if (b.lit[qi] && b.cells[qi].id !== an.id) { clash = true; break; }
          }
          if (clash) continue;

          // плотность: сильнее всего ценим клетку, которая не раздувает
          // габарит уже собранного. Без этого связка расползалась лентой
          var grow = 0;
          if (bx0 <= bx1) {
            grow = (Math.max(bx1, x) - Math.min(bx0, x)) - (bx1 - bx0)
                 + (Math.max(by1, y) - Math.min(by0, y)) - (by1 - by0);
          }
          var score = touch * 12 - grow * 7 + open
                    - (Math.abs(x - an.cx) + Math.abs(y - an.cy)) * 0.5;
          if (score > bestScore) { bestScore = score; bestCell = j; }
        }
      }
      if (bestCell < 0) continue;

      var src = -1, sd = 1e9;
      var bx = bestCell % BW, by = (bestCell / BW) | 0;
      for (i = 0; i < b.cells.length; i++) {
        if (b.cells[i].anchor || b.cells[i].fixed || b.cells[i].id !== an.id || b.lit[i]) continue;
        var d = Math.abs((i % BW) - bx) + Math.abs(((i / BW) | 0) - by);
        if (d < sd) { sd = d; src = i; }
      }
      if (src < 0) continue;
      return { src: src, from: cellScreen(src % BW, (src / BW) | 0), to: cellScreen(bx, by) };
    }
    return null;
  }

  root.Sort = {
    build: build, step: step, marks: marks, draw: draw,
    pick: pick, drop: drop, frame: frame, button: button,
    progress: progress, shape: shape, finish: finish,
    finishing: finishing, finishProgress: finishProgress, finishDone: finishDone, commit: commit,
    active: active, hint: hint, heldLit: heldLit, doneUnits: doneUnits,
    land: land, cellScreen: cellScreen2, rect: frame,
    board: function () { return b; },
    get inject() { return b ? b.inject : []; },
    get units() { return b ? b.units : 0; },
    get dragging() { return !!(b && b.drag >= 0); }
  };
})(window);
