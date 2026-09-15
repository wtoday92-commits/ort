/* ORT — письменность.
 *
 * Глиф = три вертикальных регистра, в каждом один из шести примитивов.
 * 6^3 = 216 глифов. Ни один примитив не повторяет человеческий знак:
 * ни замкнутых овалов с хвостом, ни диагональных перекладин, ни точек над
 * основанием. Всё строится из дуг, линз, гребёнок и стеблей.
 *
 * Из состава глифа выводятся четыре скрытых свойства. Каждое кормит свой этап.
 */
(function (root) {
  'use strict';

  var REG = 3;          // регистров в глифе
  var MARKS = 6;        // примитивов на регистр
  var COUNT = 216;      // MARKS^REG

  // --- детерминированный хэш -------------------------------------------------

  function hash3(x, y, s) {
    var n = (Math.imul(x | 0, 374761393) + Math.imul(y | 0, 668265263) + Math.imul(s | 0, 1274126177)) | 0;
    n = (n ^ (n >>> 13)) | 0;
    n = Math.imul(n, 1274126177) | 0;
    return (n ^ (n >>> 16)) >>> 0;
  }

  function rand3(x, y, s) {
    return hash3(x, y, s) / 4294967296;
  }

  // --- свойства глифа --------------------------------------------------------

  // Какие примитивы считаются замкнутыми (дают массу).
  var CLOSED = [false, false, false, true, false, true]; // линза и кольцо
  // Сколько штрихов примитива пересекает базовую линию регистра.
  var CROSSINGS = [0, 1, 1, 0, 2, 2];

  function regs(id) {
    return [id % MARKS, ((id / MARKS) | 0) % MARKS, ((id / (MARKS * MARKS)) | 0) % MARKS];
  }

  /* масса: число замкнутых регистров, 0..3.
     Работает в СБОРЕ (тяжёлое отстаёт от дрейфа) и задаёт окно распада в УТИЛИЗАЦИИ. */
  function massOf(id) {
    var r = regs(id), m = 0;
    for (var i = 0; i < REG; i++) if (CLOSED[r[i]]) m++;
    return m;
  }

  /* наклон: направление на следующий якорь в АНАЛИЗЕ, 0..5 (шестой круг). */
  function leanOf(id) {
    var r = regs(id);
    return ((r[0] - r[2]) % MARKS + MARKS) % MARKS;
  }

  /* класс: суммарное число пересечений базовой линии, 0..6.
     Глифы одного класса синхронно всплывают на волне в СОРТИРОВКЕ. */
  function classOf(id) {
    var r = regs(id), c = 0;
    for (var i = 0; i < REG; i++) c += CROSSINGS[r[i]];
    return c;
  }

  /* паразит: верхний и нижний регистры совпали, средний пуст.
     Мусор, нужный кораблю и мешающий игроку. Вычищается в лорной УТИЛИЗАЦИИ. */
  function isParasite(id) {
    var r = regs(id);
    return r[0] === r[2] && r[1] === 0;
  }

  // --- отрисовка примитивов --------------------------------------------------
  // Каждый рисуется в прямоугольник (-w/2, -h/2) .. (w/2, h/2) вокруг нуля.

  /* Ни один примитив не должен читаться как наша цифра или буква.
     Поэтому здесь нет ни ровного круга, ни одиночной вертикальной палки,
     ни точки над основанием: только асимметричные дуги, вилки и гребёнки. */
  function mark(ctx, t, w, h) {
    var hw = w / 2, hh = h / 2;
    ctx.beginPath();
    switch (t) {
      case 0: // гребёнка: планка с тремя зубьями разной длины
        ctx.moveTo(-hw, -hh * 0.35);
        ctx.lineTo(hw * 0.85, -hh * 0.35);
        ctx.moveTo(-hw * 0.6, -hh * 0.35); ctx.lineTo(-hw * 0.6, hh * 0.5);
        ctx.moveTo(0, -hh * 0.35); ctx.lineTo(0, hh * 0.85);
        ctx.moveTo(hw * 0.6, -hh * 0.35); ctx.lineTo(hw * 0.6, hh * 0.3);
        break;
      case 1: // дуга, открытая влево, с прижатым внутрь отростком
        ctx.arc(-hw * 0.3, 0, hw * 0.8, -Math.PI * 0.62, Math.PI * 0.52);
        ctx.moveTo(-hw * 0.3, -hh * 0.1);
        ctx.lineTo(-hw * 1.0, hh * 0.35);
        break;
      case 2: // дуга, открытая вправо, с отростком в другую сторону
        ctx.arc(hw * 0.3, 0, hw * 0.8, Math.PI * 0.48, Math.PI * 1.62);
        ctx.moveTo(hw * 0.3, hh * 0.1);
        ctx.lineTo(hw * 1.0, -hh * 0.35);
        break;
      case 3: // линза: две дуги, сомкнутые остриями. Замкнута, но не круг
        ctx.moveTo(hw * 0.1, -hh * 0.9);
        ctx.quadraticCurveTo(hw * 1.1, hh * 0.15, -hw * 0.1, hh * 0.9);
        ctx.quadraticCurveTo(-hw * 1.1, -hh * 0.15, hw * 0.1, -hh * 0.9);
        break;
      case 4: // вилка: стебель, расщеплённый надвое, и боковая засечка
        ctx.moveTo(hw * 0.15, -hh * 0.85);
        ctx.lineTo(hw * 0.15, hh * 0.05);
        ctx.lineTo(-hw * 0.6, hh * 0.8);
        ctx.moveTo(hw * 0.15, hh * 0.05);
        ctx.lineTo(hw * 0.85, hh * 0.7);
        ctx.moveTo(hw * 0.15, -hh * 0.35);
        ctx.lineTo(-hw * 0.7, -hh * 0.55);
        break;
      case 5: // крюк: почти замкнутый виток с вылетающим наружу хвостом
        ctx.arc(0, 0, hw * 0.62, -Math.PI * 0.15, Math.PI * 1.55);
        ctx.lineTo(hw * 1.05, hh * 0.85);
        break;
    }
    ctx.stroke();
  }

  /* Рисует глиф в текущем трансформе, вписывая в квадрат size.
     Регистры сдвинуты по горизонтали в зависимости от примитива: без этого
     стебли выстраиваются в сплошные вертикали и поле читается как водопад. */
  function drawGlyph(ctx, id, size, lineWidth) {
    var r = regs(id);
    var rh = size / REG;
    ctx.lineWidth = lineWidth;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    for (var i = 0; i < REG; i++) {
      var shift = ((r[i] % 3) - 1) * size * 0.085;
      var tilt = (((r[i] * 7 + i * 5) % 5) - 2) * 0.055;
      ctx.save();
      ctx.translate(shift, (i - 1) * rh);
      ctx.rotate(tilt);
      mark(ctx, r[i], size * 0.60, rh * 0.80);
      ctx.restore();
    }
  }

  // --- атлас -----------------------------------------------------------------
  // 216 глифов пререндерятся в offscreen-канвасы с запечённым свечением.
  // Дальше рисуем через drawImage: дёшево и держит тысячи глифов в кадре.

  /* Один регистр глифа отдельно. Нужен осколкам: разломанный знак должен
     остаться узнаваемым, а не превратиться в горсть случайных палок. */
  function drawRegister(ctx, id, i, size, lineWidth) {
    var r = regs(id);
    var rh = size / REG;
    ctx.lineWidth = lineWidth;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    var shift = ((r[i] % 3) - 1) * size * 0.085;
    var tilt = (((r[i] * 7 + i * 5) % 5) - 2) * 0.055;
    ctx.save();
    ctx.translate(shift, 0);
    ctx.rotate(tilt);
    mark(ctx, r[i], size * 0.60, rh * 0.80);
    ctx.restore();
  }

  /* Глиф занимает заметно меньше ячейки: воздух между знаками — половина
     ощущения. fill — доля ячейки, которую занимает сам знак.
     ss — надсэмплинг: атлас печётся крупнее и уменьшается при выводе, иначе
     знак мылится, особенно под волной, где он растянут вдвое.
     Печём два прохода: мягкий подсвет и поверх него резкое ядро. Один
     размытый проход даёт кашу, ядро возвращает чёткость. */
  function buildAtlas(cell, color, glow, fill, ss) {
    fill = fill || 0.64;
    ss = ss || 2;
    var box = Math.round(cell * 1.44);      // логический размер клетки атласа
    var px = Math.round(box * ss);
    var ink = cell * fill * ss;
    var lw = Math.max(1.05 * ss, ink * 0.055);
    /* Все знаки лежат на ОДНОМ большом холсте. Раньше у каждого знака был
       свой маленький холст, а маленькие холсты браузер держит в обычной
       памяти и при каждом выводе заново переносит в видеокарту: на сильном
       отдалении это тысячи переносов в кадр. Между клетками поле в пару
       пикселей, чтобы соседние знаки не подмешивались при сглаживании. */
    var G2 = 2, slot = px + G2 * 2, cols = 15, rows = Math.ceil(COUNT / cols);
    var sheet = document.createElement('canvas');
    sheet.width = cols * slot;
    sheet.height = rows * slot;
    var x = sheet.getContext('2d');
    for (var id = 0; id < COUNT; id++) {
      var ox = (id % cols) * slot, oy = ((id / cols) | 0) * slot;
      x.save();
      x.beginPath(); x.rect(ox, oy, slot, slot); x.clip();
      x.translate(ox + slot / 2, oy + slot / 2);
      if (glow > 0) {
        x.save();
        x.strokeStyle = color;
        x.globalAlpha = 0.42;
        x.shadowColor = color;
        x.shadowBlur = glow * ss;
        drawGlyph(x, id, ink, lw * 0.9);
        x.restore();
      }
      x.strokeStyle = color;
      drawGlyph(x, id, ink, lw);
      x.restore();
    }
    return {
      canvas: sheet, box: box, cell: cell, ss: ss,
      draw: function (ctx, gid, dx, dy, dw, dh) {
        ctx.drawImage(sheet, (gid % cols) * slot + G2, ((gid / cols) | 0) * slot + G2, px, px, dx, dy, dw, dh);
      }
    };
  }

  /* Лист готовых картинок: всё, что рисуется со свечением один раз и потом
     выводится много раз, складывается на один большой холст полками. Когда
     лист заполнен, он очищается и заполняется заново. */
  function SpriteSheet(side) {
    this.side = side || 2048;
    this.cv = document.createElement('canvas');
    this.cv.width = this.cv.height = this.side;
    this.c = this.cv.getContext('2d');
    this.map = new Map();
    this.x = 0; this.y = 0; this.row = 0;
  }
  SpriteSheet.prototype.get = function (key, w, h, drawFn) {
    var e = this.map.get(key);
    if (e) return e;
    w = Math.ceil(w); h = Math.ceil(h);
    if (this.x + w > this.side) { this.x = 0; this.y += this.row; this.row = 0; }
    if (this.y + h > this.side) {
      this.c.clearRect(0, 0, this.side, this.side);
      this.map.clear();
      this.x = 0; this.y = 0; this.row = 0;
    }
    var c = this.c;
    c.save();
    c.beginPath(); c.rect(this.x, this.y, w, h); c.clip();
    c.translate(this.x + w / 2, this.y + h / 2);
    drawFn(c, w, h);
    c.restore();
    e = { sx: this.x, sy: this.y, w: w, h: h };
    this.map.set(key, e);
    this.x += w + 2;
    this.row = Math.max(this.row, h + 2);
    return e;
  };
  SpriteSheet.prototype.draw = function (ctx, e, dx, dy, dw, dh) {
    ctx.drawImage(this.cv, e.sx, e.sy, e.w, e.h, dx, dy, dw === undefined ? e.w : dw, dh === undefined ? e.h : dh);
  };

  root.Glyphs = {
    COUNT: COUNT,
    REG: REG,
    MARKS: MARKS,
    hash3: hash3,
    rand3: rand3,
    regs: regs,
    massOf: massOf,
    leanOf: leanOf,
    classOf: classOf,
    isParasite: isParasite,
    drawGlyph: drawGlyph,
    drawRegister: drawRegister,
    buildAtlas: buildAtlas,
    SpriteSheet: SpriteSheet
  };
})(window);
