/* ORT — хранилище данных.
 *
 * Всё, что выработано на навигационном поле, остаётся здесь и переживает и
 * выброс, и новый запуск игры. Хранилище поделено надвое: слева то, что
 * сделал игрок, справа то, что существо сделало само.
 *   — знаки пустоты, образовавшиеся на сборе: только их число;
 *   — знаки-якоря, прошедшие анализ (за одну цепочку всегда два одинаковых);
 *   — утилизированные знаки: белые, в круге;
 *   — расщеплённые знаки;
 *   — якоря-глюки сортировки;
 *   — крутящиеся знаки, занявшие край собранного блока;
 *   — фигуры разложенных групп. Без знаков внутри, только контур, в том же
 *     положении, в каком группа легла на поле. Если потом клетку этой группы
 *     утилизировали, в фигуре на том же месте появляется белый круг.
 *
 * Лорные этапы берут отсюда материал и тратят его: взятое пропадает.
 *
 * Числа в игре пишутся точками, как на игральной кости: единицы — точки,
 * десятки — кружки побольше на тех же местах, сотни — ещё крупнее.
 */
(function (root) {
  'use strict';

  var G = root.Glyphs;
  var ORDER = ['glyph', 'purged', 'shard', 'glitch', 'spin', 'shape'];

  var items = [];            // { k, g, by } или { k: 'shape', c, w, h, p, by }
  var voids = { p: 0, c: 0 };
  var open = false, k = 0, zoom = 1, scroll = 0, maxScroll = 0;
  var drag = null, dirty = false, fresh = 0;
  var nextId = 1;            // номера фигур: по ним карта находит свою фигуру

  function wrapS(v, n) { var r = ((v % n) + n) % n; return r > n / 2 ? r - n : r; }

  // --- числа точками ---------------------------------------------------------

  var PAT = {
    1: [4], 2: [0, 8], 3: [0, 4, 8], 4: [0, 2, 6, 8], 5: [0, 2, 4, 6, 8],
    6: [0, 2, 3, 5, 6, 8], 7: [0, 2, 3, 4, 5, 6, 8], 8: [0, 1, 2, 3, 5, 6, 7, 8], 9: [0, 1, 2, 3, 4, 5, 6, 7, 8]
  };

  function drawNumeral(ctx, n, cx, cy, size, color) {
    n = Math.max(0, Math.floor(n || 0));
    var d = size * 0.3, digits = [], m = n;
    do { digits.push(m % 10); m = Math.floor(m / 10); } while (m > 0);
    ctx.save();
    ctx.strokeStyle = color; ctx.fillStyle = color;
    for (var lvl = digits.length - 1; lvl >= 0; lvl--) {
      var dg = digits[lvl];
      if (!dg) continue;
      var pos = PAT[dg];
      for (var i = 0; i < pos.length; i++) {
        var px = cx + (pos[i] % 3 - 1) * d, py = cy + (((pos[i] / 3) | 0) - 1) * d;
        ctx.beginPath();
        if (lvl === 0) { ctx.arc(px, py, Math.max(1.2, size * 0.045), 0, Math.PI * 2); ctx.fill(); }
        else {
          ctx.lineWidth = Math.max(0.8, size * 0.022);
          ctx.arc(px, py, size * (0.06 + lvl * 0.045), 0, Math.PI * 2);
          ctx.stroke();
        }
      }
    }
    ctx.restore();
  }

  /* Счёт предметов пишется как степень: мелко, справа над предметом.
     right/top — правый верхний угол самого предмета. */
  function drawSup(ctx, n, right, top, size, color) {
    drawNumeral(ctx, n, right + size * 0.42, top + size * 0.05, size, color);
  }

  /* Одинаковые фигуры: тот же контур, те же круги и крутящиеся знаки,
     тот же владелец. Такие лежат в хранилище одной стопкой со счётом. */
  var sigMemo = typeof WeakMap === 'function' ? new WeakMap() : null;
  function shapeSig(it, withMarks) {
    var sn = (it.s ? it.s.length : 0) + '/' + (it.p ? it.p.length : 0);
    var m = sigMemo && sigMemo.get(it);
    if (!m || m.sn !== sn) {
      var cells = it.c.map(function (q) { return q[0] + ',' + q[1]; }).sort().join(';');
      var spins = (it.s || []).map(function (e) { return e.i + ':' + e.g; }).sort().join(',');
      var marks = (it.p || []).slice().sort(function (a, b) { return a - b; }).join(',');
      m = { sn: sn, base: (it.by || 'c') + '|' + cells + '|' + spins, full: '' };
      m.full = m.base + '|' + marks;
      if (sigMemo) sigMemo.set(it, m);
    }
    return withMarks ? m.full : m.base;
  }
  // список фигур -> стопки { item, n } в порядке первого появления
  function stackShapes(list, withMarks) {
    var groups = {}, out = [];
    list.forEach(function (it) {
      var key = shapeSig(it, withMarks), g = groups[key];
      if (!g) { g = groups[key] = { item: it, n: 0 }; out.push(g); }
      g.n++;
    });
    return out;
  }

  root.Numeral = { draw: drawNumeral, sup: drawSup };

  // --- содержимое --------------------------------------------------------------

  /* Хранилище не бесконечно: у каждого владельца не больше CAP предметов.
     Существо работает сутками в фоновой вкладке, и без предела хранилище
     разрасталось до тысяч предметов — сохранение и отрисовка тяжелели.
     Уходит самое старое, фигуры — в последнюю очередь. */
  var CAP = 700;
  function add(it) {
    if (!it.by) it.by = 'c';
    items.push(it);
    var mine = 0, oldest = -1, oldestAny = -1;
    for (var i = 0; i < items.length; i++) {
      if ((items[i].by || 'c') !== it.by) continue;
      mine++;
      if (oldestAny < 0) oldestAny = i;
      if (oldest < 0 && items[i].k !== 'shape') oldest = i;
    }
    if (mine > CAP) items.splice(oldest >= 0 ? oldest : oldestAny, 1);
    dirty = true; fresh = 1;
    return it;
  }

  function remove(it) {
    var i = items.indexOf(it);
    if (i >= 0) { items.splice(i, 1); dirty = true; }
  }

  /* Фигура группы: клетки переводятся в свои координаты от левого верхнего
     угла. Поворот не меняется: вертикальная палка остаётся вертикальной. */
  function addShape(cells, W, H, by) {
    if (!cells.length) return null;
    var bx = cells[0].wx, by0 = cells[0].wy, rel = [], minX = 0, minY = 0, maxX = 0, maxY = 0, i;
    for (i = 0; i < cells.length; i++) {
      var x = wrapS(cells[i].wx - bx, W), y = wrapS(cells[i].wy - by0, H);
      rel.push([x, y]);
      minX = Math.min(minX, x); minY = Math.min(minY, y);
      maxX = Math.max(maxX, x); maxY = Math.max(maxY, y);
    }
    for (i = 0; i < rel.length; i++) { rel[i][0] -= minX; rel[i][1] -= minY; }
    var it = add({ k: 'shape', id: nextId++, c: rel, w: maxX - minX + 1, h: maxY - minY + 1, p: [], by: by });
    /* Где фигура лежит на карте. Сохраняется вместе с номером: разложенная
       группа на карте помнит номер фигуры, и связь переживает перезапуск. */
    it.o = { x: bx + minX, y: by0 + minY, W: W, H: H };
    return it;
  }

  function markShape(it, wx, wy) {
    if (!it || !it.o || items.indexOf(it) < 0) return;
    var o = it.o;
    var x = ((wx - o.x) % o.W + o.W) % o.W, y = ((wy - o.y) % o.H + o.H) % o.H;
    for (var i = 0; i < it.c.length; i++) {
      if (it.c[i][0] === x && it.c[i][1] === y) {
        if (it.p.indexOf(i) < 0) { it.p.push(i); dirty = true; fresh = 1; }
        return;
      }
    }
  }

  // --- отрисовка ---------------------------------------------------------------

  function glow(ctx, color, blur) { ctx.shadowColor = color; ctx.shadowBlur = blur; }

  /* Каждый знак хранилища рисуется со свечением один раз в отдельную
     картинку, дальше выводится готовой. Размытие на сотнях знаков каждый кадр
     вешало вкладку, стоило хранилищу разрастись. */
  var sheet = null;

  function spriteFor(it, S, sz) {
    if (!sheet) sheet = new G.SpriteSheet(2048);
    var key = it.k + '|' + it.g + '|' + Math.round(S) + (it.k === 'shape' ? '|' + JSON.stringify(it.c) + '|' + it.p.join(',') : '');
    var pad = Math.ceil(S * 0.35);
    return sheet.get(key, sz.w + pad * 2, sz.h + pad * 2, function (c) { drawItem(c, it, 0, 0, 0, S, 0, true); });
  }

  function drawCached(ctx, it, n, cx, cy, S, t, sz) {
    var sp = spriteFor(it, S, sz);
    if (it.k === 'spin' || it.k === 'glitch') {
      ctx.save();
      ctx.translate(cx, cy);
      if (it.k === 'spin') ctx.rotate(t * 1.9 + n);
      else {
        ctx.translate(Math.sin(t * 41 + n) * S * 0.04, Math.cos(t * 37 + n * 1.7) * S * 0.03);
        ctx.globalAlpha *= Math.sin(t * 23 + n) > 0.2 ? 1 : 0.35;
      }
      sheet.draw(ctx, sp, -sp.w / 2, -sp.h / 2);
      ctx.restore();
    } else sheet.draw(ctx, sp, Math.round(cx - sp.w / 2), Math.round(cy - sp.h / 2));
    if (it.k === 'shape' && it.s && it.s.length) {
      // крутящиеся знаки внутри фигуры рисуются поверх готовой картинки
      var u = S * 0.42, ox = cx - it.w * u / 2, oy = cy - it.h * u / 2;
      it.s.forEach(function (e) {
        var q = it.c[e.i];
        if (!q) return;
        ctx.save();
        ctx.translate(ox + (q[0] + 0.5) * u, oy + (q[1] + 0.5) * u);
        ctx.rotate(t * 1.9 + e.i);
        ctx.strokeStyle = 'rgba(255,200,130,0.95)';
        G.drawGlyph(ctx, e.g, u * 0.8, Math.max(1, S * 0.03));
        ctx.restore();
      });
    }
  }

  function drawItem(ctx, it, n, cx, cy, S, t, still) {
    var lw = Math.max(1.1, S * 0.034);
    ctx.save();
    ctx.translate(cx, cy);
    switch (it.k) {
      case 'glyph':
        glow(ctx, 'rgba(255,150,50,0.9)', S * 0.18);
        ctx.strokeStyle = 'rgba(255,176,90,0.95)';
        G.drawGlyph(ctx, it.g, S * 0.74, lw);
        break;
      case 'purged':
        glow(ctx, 'rgba(214,232,255,0.95)', S * 0.22);
        ctx.strokeStyle = 'rgba(238,246,255,0.95)';
        ctx.lineWidth = lw;
        ctx.beginPath(); ctx.arc(0, 0, S * 0.4, 0, Math.PI * 2); ctx.stroke();
        G.drawGlyph(ctx, it.g, S * 0.5, lw * 0.85);
        break;
      case 'shard':
        ctx.strokeStyle = 'rgba(178,178,184,0.9)';
        var ink = S * 0.66, rh = ink / 3;
        for (var r = 0; r < 3; r++) {
          ctx.save();
          ctx.translate((G.rand3(it.g, r, 62) - 0.5) * S * 0.24, (r - 1) * rh + (G.rand3(it.g, r, 63) - 0.5) * S * 0.16);
          ctx.rotate((G.rand3(it.g, r, 64) - 0.5) * 0.9);
          G.drawRegister(ctx, it.g, r, ink, lw * 0.8);
          ctx.restore();
        }
        break;
      case 'glitch':
        if (!still) {
          ctx.translate(Math.sin(t * 41 + n) * S * 0.04, Math.cos(t * 37 + n * 1.7) * S * 0.03);
          ctx.globalAlpha *= Math.sin(t * 23 + n) > 0.2 ? 1 : 0.35;
        }
        glow(ctx, 'rgba(255,120,50,0.9)', S * 0.16);
        ctx.strokeStyle = 'rgba(255,150,80,0.95)';
        G.drawGlyph(ctx, it.g, S * 0.7, lw);
        break;
      case 'spin':
        if (!still) ctx.rotate(t * 1.9 + n);
        glow(ctx, 'rgba(255,150,50,0.9)', S * 0.18);
        ctx.strokeStyle = 'rgba(255,190,110,0.95)';
        G.drawGlyph(ctx, it.g, S * 0.7, lw);
        break;
      case 'shape':
        var u = S * 0.42, ox = -it.w * u / 2, oy = -it.h * u / 2, set = {}, i;
        for (i = 0; i < it.c.length; i++) set[it.c[i][0] + ',' + it.c[i][1]] = 1;
        glow(ctx, 'rgba(255,150,50,0.9)', S * 0.16);
        ctx.strokeStyle = 'rgba(255,176,90,0.95)';
        ctx.lineWidth = lw;
        ctx.lineCap = 'round';
        ctx.beginPath();
        for (i = 0; i < it.c.length; i++) {
          var x = it.c[i][0], y = it.c[i][1];
          var x0 = ox + x * u, y0 = oy + y * u, x1 = x0 + u, y1 = y0 + u;
          if (!set[x + ',' + (y - 1)]) { ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); }
          if (!set[x + ',' + (y + 1)]) { ctx.moveTo(x0, y1); ctx.lineTo(x1, y1); }
          if (!set[(x - 1) + ',' + y]) { ctx.moveTo(x0, y0); ctx.lineTo(x0, y1); }
          if (!set[(x + 1) + ',' + y]) { ctx.moveTo(x1, y0); ctx.lineTo(x1, y1); }
        }
        ctx.stroke();
        if (it.p.length) {
          glow(ctx, 'rgba(214,232,255,0.95)', S * 0.16);
          ctx.strokeStyle = 'rgba(238,246,255,0.95)';
          for (i = 0; i < it.p.length; i++) {
            var pc = it.c[it.p[i]];
            if (!pc) continue;
            ctx.beginPath();
            ctx.arc(ox + (pc[0] + 0.5) * u, oy + (pc[1] + 0.5) * u, u * 0.3, 0, Math.PI * 2);
            ctx.stroke();
          }
        }
        break;
    }
    ctx.restore();
  }

  function itemSize(it, S) {
    if (it.k !== 'shape') return { w: S, h: S };
    var u = S * 0.42;
    return { w: Math.max(S, it.w * u + S * 0.2), h: Math.max(S, it.h * u + S * 0.2) };
  }

  /* Одна колонка хранилища: число пустоты сверху, дальше по видам. */
  function drawColumn(ctx, by, x0, colW, yStart, S, t, vh) {
    var gap = S * 0.3, y = yStart;
    // пустота: сам знак и рядом его число точками
    ctx.save();
    ctx.translate(x0 + S / 2, y + S / 2);
    glow(ctx, 'rgba(255,150,50,0.7)', S * 0.12);
    ctx.strokeStyle = 'rgba(255,170,90,0.75)';
    G.drawGlyph(ctx, 0, S * 0.7, Math.max(1.1, S * 0.034));
    ctx.restore();
    ctx.save();
    glow(ctx, 'rgba(255,200,140,0.8)', S * 0.1);
    drawSup(ctx, voids[by], x0 + S * 0.72, y + S * 0.2, S * 0.5, 'rgba(255,214,170,0.95)');
    ctx.restore();
    y += S + gap * 1.4;

    for (var c = 0; c < ORDER.length; c++) {
      var kind = ORDER[c], rowH = 0, x = x0, started = false;
      var list = [];
      for (var q = 0; q < items.length; q++) {
        if (items[q].k === kind && (items[q].by || 'c') === by) list.push(kind === 'shape' ? items[q] : { item: items[q], n: 1, at: q });
      }
      if (kind === 'shape') list = stackShapes(list, true);
      for (var n = 0; n < list.length; n++) {
        var it = list[n].item, cnt = list[n].n;
        if (!started) {
          started = true;
          var lg = ctx.createLinearGradient(x0, 0, x0 + colW, 0);
          lg.addColorStop(0, 'rgba(255,158,58,0)');
          lg.addColorStop(0.5, 'rgba(255,186,110,0.2)');
          lg.addColorStop(1, 'rgba(255,158,58,0)');
          ctx.fillStyle = lg;
          ctx.fillRect(x0, y, colW, 1);
          y += gap * 1.4;
        }
        var sz = itemSize(it, S), supW = cnt > 1 ? S * 0.55 : 0;
        if (x + sz.w + supW > x0 + colW && x > x0) { x = x0; y += rowH + gap; rowH = 0; }
        var top = y + (cnt > 1 ? S * 0.25 : 0);
        if (top + sz.h > 84 && y < vh) {
          drawCached(ctx, it, list[n].at === undefined ? n : list[n].at, x + sz.w / 2, top + sz.h / 2, S, t, sz);
          if (cnt > 1) {
            var u = S * 0.42;
            ctx.save();
            glow(ctx, 'rgba(255,200,140,0.8)', S * 0.08);
            drawSup(ctx, cnt, x + sz.w / 2 + it.w * u / 2, top + sz.h / 2 - it.h * u / 2, S * 0.42, 'rgba(255,214,170,0.95)');
            ctx.restore();
          }
        }
        x += sz.w + supW + gap;
        rowH = Math.max(rowH, sz.h + (top - y));
      }
      if (started) y += rowH + gap;
    }
    return y;
  }

  function draw(ctx, t, vw, vh) {
    if (k < 0.01) return;
    ctx.save();
    ctx.globalAlpha = k;
    ctx.fillStyle = 'rgba(7,6,3,0.92)';
    ctx.fillRect(0, 0, vw, vh);
    ctx.beginPath(); ctx.rect(0, 84, vw, vh - 84); ctx.clip();
    ctx.globalCompositeOperation = 'lighter';

    var S = 40 * zoom, total = Math.min(1240, vw - 60), half = (total - 50) / 2, x0 = (vw - total) / 2;
    var y0 = 118 - scroll;
    var yl = drawColumn(ctx, 'p', x0, half, y0, S, t, vh);
    var yr = drawColumn(ctx, 'c', x0 + half + 50, half, y0, S, t, vh);
    // разделитель: слева игрок, справа существо
    ctx.fillStyle = 'rgba(255,186,110,0.18)';
    ctx.fillRect(x0 + half + 25, 100, 1, vh - 120);
    maxScroll = Math.max(0, Math.max(yl, yr) + scroll - vh + 40);
    if (scroll > maxScroll) scroll = maxScroll;
    ctx.restore();
  }

  root.Inventory = {
    add: add, remove: remove, addShape: addShape, stackShapes: stackShapes, markShape: markShape, draw: draw,
    /* Выброшенное существо уносит с собой всё, что сделало. */
    wipe: function (by) {
      items = items.filter(function (it) { return (it.by || 'c') !== by; });
      voids[by] = 0;
      dirty = true;
    },
    /* Внутри фигуры теперь крутится знак. */
    setShapeSpin: function (it, wx, wy, g) {
      if (!it || !it.o || items.indexOf(it) < 0) return false;
      var o = it.o;
      var x = ((wx - o.x) % o.W + o.W) % o.W, y = ((wy - o.y) % o.H + o.H) % o.H;
      for (var i = 0; i < it.c.length; i++) {
        if (it.c[i][0] !== x || it.c[i][1] !== y) continue;
        it.s = (it.s || []).filter(function (e) { return e.i !== i; });
        it.s.push({ i: i, g: g });
        dirty = true; fresh = 1;
        return true;
      }
      return false;
    },
    removeOne: function (k, g) {
      for (var i = items.length - 1; i >= 0; i--) {
        if (items[i].k === k && items[i].g === g) { items.splice(i, 1); dirty = true; return true; }
      }
      return false;
    },
    addVoids: function (by, n) { if (n > 0) { voids[by === 'p' ? 'p' : 'c'] += n; dirty = true; } },
    voids: function (by) { return voids[by]; },
    /* Потратить один знак пустоты: сперва из той части, что названа первой. */
    spendVoid: function (order) {
      order = order || ['c', 'p'];
      for (var i = 0; i < order.length; i++) {
        if (voids[order[i]] > 0) { voids[order[i]]--; dirty = true; return true; }
      }
      return false;
    },
    step: function (dt) { k += ((open ? 1 : 0) - k) * Math.min(1, dt * 7); },
    toggle: function () { open = !open; if (open) fresh = 0; drag = null; },
    close: function () { open = false; drag = null; },
    press: function (x, y) { drag = { y: y, s: scroll }; },
    move: function (x, y) { if (drag) scroll = Math.max(0, Math.min(maxScroll, drag.s - (y - drag.y))); },
    release: function () { drag = null; },
    wheel: function (dy) {
      var z = Math.max(0.4, Math.min(3, zoom * (dy > 0 ? 1 / 1.12 : 1.12)));
      scroll *= z / zoom;
      zoom = z;
    },
    get open() { return open; },
    get fresh() { return fresh; },
    get dirty() { return dirty; },
    get count() { return items.length; },
    items: function () { return items; },
    byId: function (id) {
      if (!id) return null;
      for (var i = 0; i < items.length; i++) if (items[i].id === id) return items[i];
      return null;
    },
    clean: function () { dirty = false; },
    serialize: function () { return { items: items, voids: voids, zoom: zoom }; },
    load: function (d) {
      if (!d || !Array.isArray(d.items)) return;
      items = d.items.filter(function (it) { return it && ORDER.indexOf(it.k) >= 0; });
      items.forEach(function (it) { if (!it.by) it.by = 'c'; });
      nextId = 1;
      items.forEach(function (it) { if (it.id >= nextId) nextId = it.id + 1; });
      items.forEach(function (it) { if (it.k === 'shape' && !it.id) it.id = nextId++; });
      if (d.voids) voids = { p: d.voids.p | 0, c: d.voids.c | 0 };
      if (d.zoom) zoom = Math.max(0.4, Math.min(3, d.zoom));
    }
  };
})(window);
