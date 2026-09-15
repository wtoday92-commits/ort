/* ORT — утилизация.
 *
 * Курсор замирает над знаком, и знак начинает распадаться. Пока держишь,
 * нарастают помехи и дрожь. Потом наступает провал в тишину — вот это и есть
 * окно. Увёл курсор в окне — знак распался. Увёл рано — восстановился.
 * Передержал — расщепился надвое, и осколок остаётся на поле навсегда.
 *
 * Окно у каждого знака своё и зависит от его массы, то есть от числа
 * замкнутых форм в начертании. Тяжёлый распадается дольше. Игроку этого никто
 * не говорит: он нащупывает связь сам, и с какого-то момента начинает
 * узнавать срок по виду знака.
 *
 * Главный канал здесь звук. Помехи растут, а окно слышно как провал.
 */
(function (root) {
  'use strict';

  var G = root.Glyphs, S = root.Sound;

  var LATE = 0.45;           // сколько можно передержать до расщепления

  var F = null, b = null;

  /* Утилизируем ровно те клетки, что пришли из цепочки анализа. Ни искать, ни
     выдумывать ничего не надо: материал уже определён и лежит на поле. */
  function build(field, cells) {
    F = field;
    var items = [];
    for (var i = 0; i < cells.length; i++) {
      var id = F.glyphAt(cells[i].wx, cells[i].wy);
      var mass = G.massOf(id);
      items.push({
        wx: cells[i].wx, wy: cells[i].wy, id: id,
        w0: 0.75 + mass * 0.28,        // окно тем позже, чем тяжелее знак
        w1: 0.75 + mass * 0.28 + 0.55,
        hold: 0, done: 0, split: 0
      });
    }
    b = { items: items, splits: 0, at: -1, held: 0 };
    return b;
  }

  function live() {
    var n = 0;
    for (var i = 0; i < b.items.length; i++) if (!b.items[i].done) n++;
    return n;
  }

  function progress() {
    var done = 0;
    for (var i = 0; i < b.items.length; i++) if (b.items[i].done) done++;
    return { done: done, total: b.items.length, splits: b.splits,
             frac: b.items.length ? done / b.items.length : 1 };
  }

  /* Знак берут зажатием и отпускают в нужный миг. Ровно в окне — распад,
     раньше — восстановление, позже — знак ломается и остаётся осколками. */
  function settle(it) {
    var key = F.ckey(it.wx, it.wy);
    if (it.hold >= it.w0 && it.hold <= it.w1) {
      it.done = 1;
      F.setPurged(key, it.id);          // на месте знака остаётся белая метка
      if (S) S.dissolve();
    } else if (it.hold > it.w1) {
      it.split = 1; it.done = 1; b.splits++;
      F.setShards(key, it.id);          // ломается именно этот знак
      if (S) S.shatter();
    } else if (it.hold > 0.1) {
      if (S) S.restore();
    }
    it.hold = 0;
  }

  function press(x, y) {
    if (!b) return false;
    var tol = F.CELL * 0.85, bd = tol * tol, near = -1;
    for (var i = 0; i < b.items.length; i++) {
      var it = b.items[i];
      if (it.done) continue;
      var p = F.cellCenter(it.wx, it.wy);
      var dx = p.x - x, dy = p.y - y, d = dx * dx + dy * dy;
      if (d < bd) { bd = d; near = i; }
    }
    if (near < 0) return false;
    b.at = near;
    b.items[near].hold = 0;
    b.held = 1;
    return true;
  }

  function release() {
    if (!b || !b.held) return false;
    b.held = 0;
    if (b.at >= 0 && !b.items[b.at].done) settle(b.items[b.at]);
    b.at = -1;
    return true;
  }

  function step(dt) {
    if (!b || !b.held || b.at < 0) return;
    var it = b.items[b.at];
    if (it.done) { b.held = 0; b.at = -1; return; }
    it.hold += dt;
    // передержал совсем — ломается сам, без отпускания
    if (it.hold > it.w1 + LATE) { settle(it); b.held = 0; b.at = -1; }
  }

  function marks(out) {
    if (!b) return;
    for (var i = 0; i < b.items.length; i++) {
      var it = b.items[i];
      if (it.done) continue;
      var h = (b.held && i === b.at) ? it.hold : 0;
      var m = { id: it.id, still: 1, lean: 0, px: 0, py: 0, lit: 0, grow: 0, dim: 0, scale: 1 };

      if (h <= 0) { m.grow = 0.75; m.scale = 1.18; }
      else if (h < it.w0) {
        // помехи растут: дрожь и ступенчатое угасание
        var u = h / it.w0;
        var q = Math.floor(u * 4) / 4;
        m.px = Math.sin(h * 46 + i) * 4.5 * u;
        m.py = Math.cos(h * 51 + i * 1.3) * 3.0 * u;
        m.dim = q * 0.6;
        m.scale = 1 - q * 0.18;
      } else if (h <= it.w1) {
        // провал в тишину: дрожь пропадает, знак почти прозрачен
        m.dim = 0.74;
        m.scale = 0.8;
        m.grow = 0.2 * (0.5 + 0.5 * Math.sin(h * 7));
      } else {
        // передержал: знак раздваивается на глазах
        var v = Math.min(1, (h - it.w1) / LATE);
        m.px = Math.sin(h * 60) * 9 * v;
        m.dim = 0.5 - v * 0.5;
        m.scale = 0.82 + v * 0.3;
      }
      out.set(F.ckey(it.wx, it.wy), m);
    }
  }

  function draw(ctx, t) {
    if (!b) return;
    /* Кольцо вокруг каждого знака, который ещё предстоит утилизировать. Без
       него их приходилось искать вслепую: на огромном поле пять подсвеченных
       знаков теряются. */
    var pulse = 0.5 + 0.5 * Math.sin(t * 1.9);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = 'rgba(255,206,150,' + (0.18 + pulse * 0.18) + ')';
    ctx.lineWidth = 1.2;
    for (var i = 0; i < b.items.length; i++) {
      if (b.items[i].done || (b.held && i === b.at)) continue;
      var q = F.cellCenter(b.items[i].wx, b.items[i].wy);
      ctx.beginPath();
      ctx.arc(q.x, q.y, F.CELL * 0.52 + pulse * 3, 0, Math.PI * 2);
      ctx.stroke();
    }
    ctx.restore();

    if (b.at < 0 || !b.held) return;
    var it = b.items[b.at];
    if (!it || it.done || it.hold <= 0.05) return;
    var p = F.cellCenter(it.wx, it.wy);
    // кольцо распада: сжимается, пока держишь. В окне оно почти сомкнуто
    var u = Math.min(1.25, it.hold / it.w1);
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = 'rgba(255,190,120,' + (0.2 + 0.3 * (1 - Math.abs(1 - u))) + ')';
    ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.arc(p.x, p.y, 34 - u * 16, 0, Math.PI * 2);
    ctx.stroke();
    ctx.restore();
  }

  /* Существо знает срок распада и уводит курсор точно в окне. */
  function hint() {
    if (!b) return null;
    for (var i = 0; i < b.items.length; i++) {
      if (!b.items[i].done) {
        var p = F.cellCenter(b.items[i].wx, b.items[i].wy);
        return { x: p.x, y: p.y, i: i };
      }
    }
    return null;
  }

  /* Существо уводит руку в самом начале окна, а не в середине: пока рука
     разгоняется и выходит из радиуса, знак продолжает распадаться. Ждало до
     середины — и расщепляло четыре знака из пяти. */
  function readyToLeave() {
    if (!b || b.at < 0) return false;
    var it = b.items[b.at];
    return !!it && !it.done && it.hold >= it.w0 + 0.02;
  }

  /* active — есть ли ещё что утилизировать. built — существует ли доска вообще.
     Различать обязательно: когда распался последний знак, active уже ложно, а
     доска ещё цела, и именно в этот момент надо передать работу в папку. */
  function active() { return !!(b && live() > 0); }
  function built() { return !!b; }
  function commit() { b = null; }

  root.Purge = {
    build: build, step: step, marks: marks, draw: draw,
    press: press, release: release,
    progress: progress, hint: hint, readyToLeave: readyToLeave,
    active: active, built: built, commit: commit,
    debug: function () { return b ? { at: b.at, held: b.held, splits: b.splits, items: b.items.map(function (i) { return { hold: Math.round(i.hold * 100) / 100, w0: Math.round(i.w0 * 100) / 100, w1: Math.round(i.w1 * 100) / 100, done: i.done, split: i.split }; }) } : null; },
    get units() { return b ? b.items.length : 0; }
  };
})(window);
