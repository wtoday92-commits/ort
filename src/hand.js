/* ORT — рука.
 *
 * Модель ведения курсора живым существом. За пультом сидит не программа,
 * поэтому здесь нет ни прямых линий, ни постоянной скорости, ни одинаковых пауз.
 *
 * Что даёт ощущение живого:
 *   - разгон и торможение через предел ускорения, а не через заданную скорость;
 *   - кривизна траектории: сильная в начале хода, исчезает у цели;
 *   - рыскание перпендикулярно ходу тремя несоизмеримыми частотами;
 *   - плавающая скорость внутри одного хода;
 *   - микропаузы в случайные моменты;
 *   - режим осмотра: курсор мелко ходит около точки, «проверяя» знак.
 */
(function (root) {
  'use strict';

  function rnd(a, b) { return a + Math.random() * (b - a); }

  function Hand(x, y) {
    this.x = x || 0; this.y = y || 0;
    this.vx = 0; this.vy = 0;
    this.gx = this.x; this.gy = this.y;
    this.speed = 420;
    this.curve = 0;
    this.d0 = 1;
    this.t = rnd(0, 100);
    this.hold = 0;
    this.holdIn = rnd(0.8, 2.2);
    this.ph = [rnd(0, 9), rnd(0, 9), rnd(0, 9)];
    this.fr = [rnd(0.6, 1.2), rnd(1.6, 2.5), rnd(3.0, 4.3)];
    this.look = null;              // цель осмотра
    this.la = rnd(0, 6.28);
    this.lspd = 1;
    this.lr = 20;
    this.slow = 1;                 // старое существо водит курсор медленнее
  }

  /* Новый ход к точке. Кривизна и скорость выбираются заново каждый раз,
     поэтому два хода к одной точке никогда не совпадают. */
  Hand.prototype.to = function (x, y, opt) {
    opt = opt || {};
    this.look = null;
    this.gx = x; this.gy = y;
    var d = Math.sqrt((x - this.x) * (x - this.x) + (y - this.y) * (y - this.y));
    this.d0 = Math.max(60, d);
    this.speed = opt.speed || rnd(260, 640);
    this.curve = opt.curve !== undefined ? opt.curve : rnd(-0.62, 0.62);
    this.holdIn = rnd(0.4, 1.7);
    this.ph[0] = rnd(0, 9);
  };

  /* Осмотр: курсор ходит около знака неровными петлями, как будто существо
     вглядывается. Радиус дышит, направление обхода случайное. */
  Hand.prototype.inspect = function (x, y, r) {
    this.look = { x: x, y: y };
    this.lr = r || 22;
    this.lspd = rnd(0.45, 1.15) * (Math.random() < 0.5 ? -1 : 1);
  };

  /* Подправить цель, не сбрасывая манеру хода. Нужно, когда знак уплывает
     вместе с полем: существо ведёт курсор к знаку, а не к точке экрана. */
  Hand.prototype.retarget = function (x, y) {
    this.gx = x; this.gy = y;
  };

  Hand.prototype.relook = function (x, y) {
    if (this.look) { this.look.x = x; this.look.y = y; }
  };

  Hand.prototype.dist = function (x, y) {
    return Math.sqrt((this.x - x) * (this.x - x) + (this.y - y) * (this.y - y));
  };

  Hand.prototype.arrived = function (tol) {
    return this.dist(this.gx, this.gy) < (tol || 14);
  };

  Hand.prototype.step = function (dt) {
    this.t += dt;
    var tx, ty, spd, wobAmp, curAmt;

    if (this.look) {
      this.la += this.lspd * dt;
      var rr = this.lr * (0.5 + 0.5 * Math.sin(this.t * 1.6 + this.ph[1]));
      tx = this.look.x + Math.cos(this.la) * rr;
      ty = this.look.y + Math.sin(this.la) * rr * 0.78;
      spd = 130 * this.slow; wobAmp = 8; curAmt = 0;
    } else {
      tx = this.gx; ty = this.gy;
      this.holdIn -= dt;
      if (this.hold > 0) this.hold -= dt;
      else if (this.holdIn <= 0) { this.hold = rnd(0.08, 0.34); this.holdIn = rnd(0.7, 2.6); }
      // скорость плавает внутри хода: ровное ведение выдаёт машину
      spd = this.speed * this.slow * (1 + 0.32 * Math.sin(this.t * 0.85 + this.ph[2]));
      if (this.hold > 0) spd *= 0.05;
      wobAmp = 62; curAmt = 1;
    }

    var dx = tx - this.x, dy = ty - this.y;
    var d = Math.sqrt(dx * dx + dy * dy) || 1e-6;
    var ux = dx / d, uy = dy / d;

    // подход к цели гасится, старт мягкий за счёт предела ускорения ниже
    var env = Math.min(1, 0.12 + d / 80);

    if (curAmt) {
      var cur = this.curve * Math.min(1, d / this.d0);
      var cs = Math.cos(cur), sn = Math.sin(cur);
      var rx = ux * cs - uy * sn, ry = ux * sn + uy * cs;
      ux = rx; uy = ry;
    }

    var wob = Math.sin(this.t * this.fr[0] + this.ph[0]) * 0.58
            + Math.sin(this.t * this.fr[1] + this.ph[1]) * 0.30
            + Math.sin(this.t * this.fr[2] + this.ph[2]) * 0.13;
    var amp = Math.min(1, d / 150) * wobAmp;

    var dvx = ux * spd * env - uy * wob * amp;
    var dvy = uy * spd * env + ux * wob * amp;

    var k = Math.min(1, dt * 7.2);
    this.vx += (dvx - this.vx) * k;
    this.vy += (dvy - this.vy) * k;
    this.x += this.vx * dt;
    this.y += this.vy * dt;
  };

  root.Hand = Hand;
})(window);
