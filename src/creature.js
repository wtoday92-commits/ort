/* ORT — существо за пультом.
 *
 * Оно знает работу, но не является программой. Поэтому оно ищет глазами,
 * проверяет найденное, иногда проверяет не то, иногда не замечает близкий
 * знак и тянется к далёкому, а иногда замечает более близкий уже на ходу
 * и резко меняет курс.
 *
 * Существо дёргает ровно тот же интерфейс, что и игрок: нажать, вести,
 * отпустить, нажать кнопку. В состояние игры в обход правил оно не лезет,
 * иначе показанный на экране паттерн был бы враньём.
 *
 * Цель всегда хранится в координатах МИРА и переводится в экранные каждый
 * кадр. Поле уплывает, и существо ведёт курсор к знаку, а не к точке экрана.
 */
(function (root) {
  'use strict';

  function rnd(a, b) { return a + Math.random() * (b - a); }
  function chance(p) { return Math.random() < p; }
  function REAL(a) { return a.role === 1 || a.role === 2; }
  function key(o) { return o.wx + '|' + o.wy; }

  function Creature(api) {
    this.api = api;
    this.hand = api.hand;
    this.st = 'scan';
    this.sub = 'move';
    this.timer = 0;
    this.target = null;
    this.start = null;
    this.cand = null;
    this.pool = [];
    this.want = 0;
    this.tried = {};
    this.rejected = {};
    this.reroll = 0;
    this.tgt = null;
  }

  /* Живая экранная позиция цели. Для пустого места она не меняется. */
  Creature.prototype.live = function (o) {
    if (!o) return null;
    if (o.blank) return { x: o.x, y: o.y };
    return this.api.screenOf(o.wx, o.wy);
  };

  Creature.prototype.onScreen = function (p) {
    var v = this.api.view();
    return p && p.x > 8 && p.y > 8 && p.x < v.w - 8 && p.y < v.h - 8;
  };

  /* Замечание знака падает с расстоянием, но не до нуля: далёкий знак тоже
     может броситься в глаза. Отсюда разброс в поведении. */
  Creature.prototype.pick = function (list, farBias) {
    if (!list.length) return null;
    var h = this.hand, tot = 0, i, w = [];
    for (i = 0; i < list.length; i++) {
      var dx = list[i].x - h.x, dy = list[i].y - h.y;
      var ww = Math.exp(-Math.sqrt(dx * dx + dy * dy) / 430) + 0.06;
      if (farBias) ww = 1 / (ww + 0.02);
      w.push(ww); tot += ww;
    }
    var r = Math.random() * tot;
    for (i = 0; i < list.length; i++) { r -= w[i]; if (r <= 0) return list[i]; }
    return list[list.length - 1];
  };

  /* Если цель за краем экрана, рука идёт к этому краю: прокрутка от края
     уведёт поле в нужную сторону. Так существо доезжает до материала, а не
     упирается в кромку. */
  Creature.prototype.steer = function (p) {
    var v = this.api.view(), h = this.hand;
    var x = p.x, y = p.y, out = false;
    if (x < 40) { x = 24; out = true; } else if (x > v.w - 40) { x = v.w - 24; out = true; }
    // цель внизу уходит под панель, но рука для прокрутки встаёт так же
    // глубоко у кромки, как и вверху: иначе вниз поле почти не ехало
    if (y < 40) { y = 24; out = true; } else if (y > v.h - 130) { y = v.h - 24; out = true; }
    h.retarget(x, y);
    this.panning = out;
    return out;
  };

  Creature.prototype.enter = function (w) {
    var h = this.hand;
    if (w === 1) { this.st = 'chain'; this.sub = 'weigh'; this.timer = rnd(0.6, 1.6); h.inspect(h.x, h.y, rnd(12, 26)); }
    else if (w === 2) { this.st = 'sort'; this.sub = 'weigh'; this.timer = rnd(0.7, 1.9); h.inspect(h.x, h.y, rnd(12, 26)); }
    else if (w === 3) { this.st = 'purge'; this.sub = 'go'; this.timer = rnd(0.4, 1.1); }
    else {
      this.st = 'scan'; this.sub = 'move'; this.timer = rnd(0.3, 0.9);
      h.to(h.x + rnd(-180, 180), h.y + rnd(-140, 60));
    }
  };

  Creature.prototype.giveUp = function () {
    this.api.abort();
    this.cand = null; this.start = null; this.target = null;
    this.st = 'scan'; this.sub = 'move'; this.timer = 0;
  };

  /* Какому этапу отвечает каждое состояние. Нужно, чтобы поймать рассинхрон:
     игрок мог бросить работу на чужом этапе или вовсе выйти в свободный режим,
     и тогда существо обязано пересобраться, а не продолжать по инерции. */
  var PHASE_OF = {
    scan: 0, inspect: 0, begin: 0, hunt: 0, verify: 0, send: 0,
    chain: 1, sort: 2, purge: 3
  };

  Creature.prototype.step = function (dt) {
    var api = this.api, h = this.hand, v = api.view(), self = this;
    // старое существо думает медленнее: все его паузы и поиски тянутся дольше
    this.timer -= dt * (1 - 0.4 * api.oldness());
    /* Между нажатиями по кнопкам и сосудам всегда есть пауза. Без неё
       существо, попав на этап без работы, щёлкало по сосудам без остановки. */
    this.tapCd = Math.max(0, (this.tapCd || 0) - dt);
    this.zoomCd = Math.max(0, (this.zoomCd || 0) - dt);
    this.panning = false;          // выставит steer, если цель за краем

    if (this.st !== 'toPhase' && this.st !== 'resume') {
      var own = PHASE_OF[this.st];
      if (own !== undefined && own !== api.phase()) {
        this.st = 'resume'; this.sub = 'go'; this.timer = 0;
        this.cand = null; this.start = null; this.tgt = null;
      }
    }

    /* Пора на обед или спать. Уходит существо только на развилке, между
       этапами, а не посреди начатой работы: так уходил бы и живой работник. */
    if ((this.st === 'resume' || this.st === 'scan' || this.st === 'toPhase') && !api.armed() && api.breakDue()) {
      this.st = 'console'; this.sub = 'free'; this.timer = rnd(0.4, 1.0);
      this.moving = false; this.cand = null; this.start = null; this.tgt = null;
    }

    switch (this.st) {

      /* --- пульт команд: снять этап, зажать пустоту, набрать команду ------- */
      case 'console': {
        if (this.sub === 'free') {
          if (api.phase() === -1) { this.sub = 'seek'; this.timer = rnd(0.3, 0.8); return; }
          var ff = api.folderPos(api.phase());
          if (!this.moving) { h.to(ff.x, ff.y - 30, { speed: rnd(220, 400) }); this.moving = true; this.timer = rnd(2.5, 4); return; }
          h.retarget(ff.x, ff.y - 30);
          if ((h.arrived(20) || this.timer <= 0) && this.tapCd <= 0) {
            this.tapCd = rnd(1.1, 2.0);
            api.tap(ff.x, ff.y - 30);
            api.deactivate();
            this.moving = false;
            h.inspect(h.x, h.y, rnd(10, 20));
            this.sub = 'seek'; this.timer = rnd(0.6, 1.4);
          }
          return;
        }
        if (this.sub === 'seek') {
          if (this.timer > 0) return;
          var vs = api.voidsOnScreen().filter(function (p) {
            return p.x > 60 && p.y > 100 && p.x < v.w - 60 && p.y < v.h - 150;
          });
          if (!vs.length) {
            this.dry = (this.dry || 0) + 1;
            if (this.dry > 2 && api.zoom() > 0.5) { this.dry = 0; api.zoomBy(-1); this.timer = rnd(0.8, 1.4); return; }
            h.to(chance(0.5) ? rnd(20, 60) : v.w - rnd(20, 60), rnd(v.h * 0.25, v.h * 0.65), { speed: rnd(260, 420) });
            this.sub = 'pan'; this.timer = rnd(1.4, 2.6);
            return;
          }
          this.dry = 0;
          this.voidCell = this.pick(vs, false);
          var pv0 = this.live(this.voidCell);
          h.to(pv0.x, pv0.y, { speed: rnd(240, 460) });
          this.sub = 'goVoid'; this.timer = rnd(2.2, 4.2);
          return;
        }
        if (this.sub === 'pan') {
          this.panning = true;
          if (this.timer <= 0) { this.sub = 'seek'; this.timer = 0; }
          return;
        }
        if (this.sub === 'goVoid') {
          var pv = this.live(this.voidCell);
          if (!this.onScreen(pv)) { this.sub = 'seek'; return; }
          h.retarget(pv.x, pv.y);
          if (h.arrived(10) || this.timer <= 0) {
            api.conPress(pv.x, pv.y);
            if (!api.conHolding()) { this.sub = 'seek'; this.timer = rnd(0.3, 0.8); return; }
            this.sub = 'hold'; this.timer = rnd(1.1, 1.6);
          }
          return;
        }
        if (this.sub === 'hold') {
          var ph = this.live(this.voidCell);
          if (ph) h.relook(ph.x, ph.y);
          if (this.timer > 0) return;
          if (!api.conOpen()) { if (!api.conHolding()) this.sub = 'seek'; return; }
          api.conRelease();
          this.keys = api.conKeys().slice(); this.ki = 0;
          h.inspect(h.x, h.y, rnd(10, 22));
          this.sub = 'pickKey'; this.timer = rnd(0.7, 1.5);
          return;
        }
        this.typeKeys('leave');
        return;
      }

      // --- кнопка утилизации: опустошить последнюю папку ------------------
      case 'flush': {
        if (!api.flushNeeded()) { this.st = 'resume'; this.sub = 'go'; this.timer = 0; return; }
        var fb = api.flushPos();
        if (this.sub === 'go') { h.to(fb.x, fb.y, { speed: rnd(220, 380) }); this.sub = 'reach'; this.timer = rnd(2.5, 4); return; }
        h.retarget(fb.x, fb.y);
        if (!h.arrived(8)) { if (this.timer <= 0) { h.to(fb.x, fb.y, { speed: 200 }); this.timer = 2; } return; }
        if (this.tapCd > 0) return;
        this.tapCd = rnd(1.1, 2.0);
        api.tap(fb.x, fb.y);
        api.flush();
        h.inspect(h.x, h.y, rnd(8, 16));
        this.st = 'resume'; this.sub = 'go'; this.timer = 0;
        return;
      }

      // --- его нет: обедает или спит. Курсор лежит там, где его бросили ----
      case 'away':
        return;

      // --- вернулось: обратная команда и отжатая пустота --------------------
      case 'back':
        this.typeKeys('release');
        return;

      /* Взяв пульт, существо идёт туда, где работа брошена. Не доделана
         сортировка — доделывает сортировку, сколько бы там ни осталось, потом
         утилизацию, и только потом возвращается к ровному кругу. Раньше оно
         всегда начинало со сбора и, если этап был не выбран, просто бесцельно
         водило курсором по полю. */
      case 'resume': {
        // папка утилизации не пуста: сперва опустошить её кнопкой
        if (api.flushNeeded()) { this.st = 'flush'; this.sub = 'go'; this.timer = 0; return; }
        var w = api.needPhase();
        if (api.phase() === w) { this.enter(w); return; }
        this.want = w;
        this.st = 'toPhase'; this.sub = 'go'; this.timer = rnd(2.6, 4.4);
        var fr = api.folderPos(w);
        h.to(fr.x, fr.y - 30, { speed: rnd(220, 400) });
        return;
      }

      // --- поиск: водит курсором по полю и ЗАМЕЧАЕТ якоря ------------------
      /* Существо не знает, где якоря. Оно ведёт курсор по полю и видит то же,
         что видит игрок:
           — дёрганых, отстающих и окаменевших видно глазом. Далёкий замечается
             редко, близкий к курсору — быстро;
           — тяжёлый и пугливый себя глазом не выдают. Их находит волна: курсор
             прошёл рядом, знак отозвался, и существо это увидело.
         Заметив, курсор замирает на секунду-другую: существо присматривается.
         Совсем редко оно обознаётся, смотрит и идёт искать дальше. */
      case 'scan': {
        if (this.sub === 'travel') { this.stepTravel(); return; }

        if (this.sub === 'notice') {
          var pn = this.live(this.target);
          if (!pn || !this.onScreen(pn)) { this.sub = 'move'; this.timer = 0; return; }
          if (this.timer > 0) return;
          if (this.target.falseSeen) {
            // показалось
            this.sub = 'move'; this.timer = 0;
            return;
          }
          // в обучении существо проверяет выдержкой всегда, потом — иногда
          this.check = api.teaching() || chance(0.35);
          h.to(pn.x, pn.y, { speed: rnd(200, 420) });
          this.st = 'inspect'; this.sub = 'move'; this.timer = rnd(2.8, 4.5);
          return;
        }

        if (this.sub === 'pause') {
          if (this.timer <= 0) { this.sub = 'move'; this.timer = 0; }
          return;
        }

        var seen = this.perceive(dt);
        if (seen) {
          this.target = seen;
          h.inspect(h.x, h.y, rnd(2, 5));          // курсор замирает: присматривается
          this.sub = 'notice'; this.timer = rnd(0.9, 2.1);
          this.sweeps = 0;
          return;
        }
        if (!h.arrived(30) && this.timer > 0) return;

        /* Место изработано: здесь уже собрано несколько блоков, экран забит
           пустотой и разложенным, или обход раз за разом ничего не даёт.
           Существо переходит к следующему участку своей спирали. */
        var fresh = this.eligible();
        this.sweeps = (this.sweeps || 0) + 1;
        if ((this.areaWork || 0) >= 3 || api.wear() > 0.3
            || this.sweeps > 9 || (this.sweeps > 4 && !fresh.length)) {
          this.travel();
          return;
        }
        if (chance(0.1)) {                          // просто задумалось
          h.inspect(h.x, h.y, rnd(6, 16));
          this.sub = 'pause'; this.timer = rnd(0.7, 1.8);
          return;
        }
        // следующий отрезок обхода: ведёт через экран, продолжая прежний ход
        this.sweepAng = (this.sweepAng === undefined ? rnd(0, 6.28) : this.sweepAng) + rnd(-1.3, 1.3);
        var len = rnd(260, 560);
        var sx = h.x + Math.cos(this.sweepAng) * len, sy = h.y + Math.sin(this.sweepAng) * len;
        if (sx < 90 || sx > v.w - 90) { this.sweepAng = Math.PI - this.sweepAng; sx = Math.max(90, Math.min(v.w - 90, sx)); }
        if (sy < 120 || sy > v.h - 170) { this.sweepAng = -this.sweepAng; sy = Math.max(120, Math.min(v.h - 170, sy)); }
        h.to(sx, sy, { speed: rnd(190, 360) });
        this.sub = 'move'; this.timer = rnd(2.5, 4.5);
        break;
      }

      // --- подход к замеченному якорю, проверка выдержкой, нажатие ---------
      case 'inspect': {
        var p = this.live(this.target);
        if (!this.onScreen(p)) { this.giveUp(); return; }
        if (this.sub === 'move') {
          h.retarget(p.x, p.y);
          if (h.arrived(7)) {
            if (this.check) {
              // держит курсор неподвижно, пока знак не отзовётся звуком
              h.retarget(h.x, h.y);
              this.sub = 'dwell'; this.timer = 4.6;
            } else {
              h.inspect(p.x, p.y, rnd(3, 7));
              this.sub = 'look'; this.timer = rnd(0.4, 1.1);
            }
          } else if (this.timer <= 0) { h.to(p.x, p.y, { speed: rnd(160, 260) }); this.timer = 2; }
          return;
        }
        if (this.sub === 'dwell') {
          var rv = api.revealAt(this.target.wx, this.target.wy);
          if (!rv && this.timer > 0) return;
          this.sub = 'aimWait'; this.timer = rnd(0.35, 0.8);
          return;
        }
        if (this.sub === 'look') {
          h.relook(p.x, p.y);
          if (this.timer > 0) return;
          this.sub = 'aimWait'; this.timer = 0;
          return;
        }
        if (this.sub === 'aimWait') {
          if (this.timer > 0) return;
          h.to(p.x, p.y, { speed: 160 });
          this.sub = 'aim'; this.timer = 1.6;
          return;
        }
        // нажимаем только когда курсор действительно на знаке
        h.retarget(p.x, p.y);
        if (!h.arrived(6)) { if (this.timer <= 0) { h.to(p.x, p.y, { speed: 160 }); this.timer = 1.6; } return; }
        api.press(h.x, h.y);
        if (!api.armed()) { this.rejected[key(this.target)] = 1; this.giveUp(); return; }
        this.start = this.target;
        this.st = 'begin'; this.sub = 'look'; this.timer = rnd(1.2, 2.8);
        this.slow = false;
        break;
      }

      // --- начало блока: держит нажатым и ищет глазами второй край --------
      case 'begin': {
        // замирает или очень медленно ведёт курсор: ищет второй край
        if (!this.slow) {
          this.slow = true;
          if (chance(0.5)) h.to(h.x + rnd(-70, 70), h.y + rnd(-50, 50), { speed: rnd(22, 50), curve: rnd(-0.3, 0.3) });
          else h.retarget(h.x, h.y);
        }
        if (this.timer > 0) return;
        this.slow = false;
        var s0 = this.start.rec, gid = s0.gid, sk = key(this.start);
        var pool = api.anchors(function (a) { return a.gid === gid; })
          .filter(function (a) { return key(a) !== sk; });
        var mate = null, decoys = [];
        for (var pi = 0; pi < pool.length; pi++) {
          var pr = pool[pi].rec;
          if (pr.pid && pr.pid === s0.pid && pr.role !== s0.role) mate = pool[pi];
          else decoys.push(pool[pi]);
        }
        if (!mate) {
          // второго края на экране нет: блок брошен, как бросил бы и живой игрок
          api.release(h.x, h.y);
          this.cand = null; this.start = null;
          this.st = 'scan'; this.sub = 'move'; this.timer = 0;
          return;
        }
        /* Примерно в четверти случаев существо сперва принимает за второй край
           похожий знак, проверяет его выдержкой, не получает отклика и только
           потом идёт к настоящему. */
        this.plan = [];
        if (decoys.length && chance(0.25 + 0.35 * api.oldness())) this.plan.push(this.pick(decoys, false));
        this.plan.push(mate);
        this.st = 'hunt'; this.sub = 'next'; this.timer = 0;
        break;
      }

      // --- второй край: подвести, проверить выдержкой, отпустить -----------
      case 'hunt': {
        if (this.sub === 'next') {
          this.cand = this.plan.shift();
          if (!this.cand) {
            api.release(h.x, h.y);
            this.cand = null; this.start = null;
            this.st = 'scan'; this.sub = 'move'; this.timer = 0;
            return;
          }
          var pc0 = this.live(this.cand);
          h.to(pc0.x, pc0.y, { speed: rnd(140, 300) });
          this.sub = 'move'; this.timer = rnd(2.5, 4.5);
          return;
        }
        var pc = this.live(this.cand);
        if (this.sub === 'move') {
          h.retarget(pc.x, pc.y);
          if (h.arrived(6)) { h.retarget(h.x, h.y); this.sub = 'dwell'; this.timer = 4.6; }
          else if (this.timer <= 0) { h.to(pc.x, pc.y, { speed: 160 }); this.timer = 2; }
          return;
        }
        if (this.sub === 'dwell') {
          var rv2 = api.revealAt(this.cand.wx, this.cand.wy);
          if (!rv2 && this.timer > 0) return;
          var cr = this.cand.rec, sr = this.start.rec;
          var ok = rv2 ? rv2.ok : !!(cr.pid && cr.pid === sr.pid && cr.role !== sr.role);
          if (ok) { this.sub = 'release'; this.timer = rnd(0.3, 0.7); }
          else { h.inspect(h.x, h.y, rnd(4, 9)); this.sub = 'doubt'; this.timer = rnd(0.6, 1.3); }
          return;
        }
        if (this.sub === 'doubt') {
          if (this.timer <= 0) this.sub = 'next';
          return;
        }
        if (this.timer > 0) return;
        h.retarget(pc.x, pc.y);
        if (!h.arrived(8)) return;
        api.release(h.x, h.y);
        if (!api.button()) { this.cand = null; this.start = null; this.st = 'scan'; this.sub = 'move'; this.timer = 0; return; }
        h.inspect(h.x, h.y, rnd(6, 14));
        this.st = 'send'; this.sub = 'wait'; this.timer = rnd(0.45, 1.1);
        break;
      }

      // --- сортировка: таскает знаки к якорям, собирая плотные блоки -------
      case 'sort': {
        if (!api.sortActive()) {
          if (api.sortBusy()) { h.relook(h.x, h.y); return; }   // идёт подсветка
          this.want = api.needPhase();
          this.st = 'toPhase'; this.sub = 'go'; this.timer = rnd(2.6, 4.4);
          var f3 = api.folderPos(this.want);
          h.to(f3.x, f3.y - 30, { speed: rnd(220, 400) });
          return;
        }

        /* Пока груз в руке, решение уже принято: доводим и отпускаем. Подсказку
           в этот момент не спрашиваем вовсе. Раньше спрашивали, и когда груз
           по дороге случайно смыкался, подсказка обнулялась, существо уходило
           к кнопке НЕ ОТПУСТИВ знак и продолжало таскать им всю доску. */
        if (this.sub === 'carry') {
          if (api.sortHeld() < 0) { this.tgt = null; this.sub = 'weigh'; this.timer = rnd(0.2, 0.5); return; }
          if (!this.tgt) {
            api.sortDrop();
            this.sub = 'weigh'; this.timer = rnd(0.2, 0.6);
            return;
          }
          h.retarget(this.tgt.x, this.tgt.y);
          // отпускаем, как только груз встал на место: доводить до точной
          // клетки не обязательно
          /* Ждём именно смыкания, а не прихода руки: клетка груза тащится
             за курсором и может отставать, а бросать его на полдороге значит
             потратить ход впустую. */
          if (api.sortHeldLit() || this.timer <= 0) {
            api.sortDrop();
            this.tgt = null;
            h.inspect(h.x, h.y, rnd(9, 18));
            this.sub = 'weigh'; this.timer = rnd(0.12, 0.45);
          }
          return;
        }

        var hn = api.sortHint();
        if (!hn) {
          // разложено всё: существо закрывает этап кнопкой
          var bt = api.sortButton();
          if (!bt) { h.relook(h.x, h.y); return; }
          if (this.sub !== 'end') {
            h.to(bt.x, bt.y, { speed: rnd(240, 420) });
            this.sub = 'end'; this.timer = rnd(1.4, 3.0);
            return;
          }
          h.retarget(bt.x, bt.y);
          if (h.arrived(12) && this.tapCd <= 0) {
            this.tapCd = rnd(1.1, 2.0);
            api.tap(bt.x, bt.y);
            api.sortFinish();
            this.sub = 'wait'; this.timer = rnd(0.5, 1.2);
          } else if (this.timer <= 0) { h.to(bt.x, bt.y, { speed: 220 }); this.timer = 2; }
          return;
        }

        if (this.sub === 'go') {
          var ax = hn.from.x + (this.aimOff ? this.aimOff.x : 0), ay = hn.from.y + (this.aimOff ? this.aimOff.y : 0);
          h.retarget(ax, ay);
          /* Берёт только когда рука и правда стоит на знаке. Раньше по
             истечении времени хватало то, что под курсором, и на мелкой
             клетке это часто был сосед. */
          var tol = Math.max(4, Math.min(15, api.cell() * 0.28));
          if (!h.arrived(tol)) {
            if (this.timer <= 0) { h.to(ax, ay, { speed: rnd(200, 320) }); this.timer = rnd(1.0, 1.8); }
            return;
          }
          // взяли не тот знак — сразу кладём обратно и смотрим заново
          if (!api.sortPick(ax, ay) || api.sortHeld() !== hn.src) {
            this.aimOff = null;
            if (api.sortHeld() >= 0) api.sortDrop();
            this.sub = 'weigh'; this.timer = rnd(0.3, 0.7);
            return;
          }
          // цель запоминается в момент захвата: доска перетекает под грузом,
          // и пересчитывать её на ходу нельзя
          this.tgt = { x: hn.to.x, y: hn.to.y };
          h.to(this.tgt.x, this.tgt.y, { speed: rnd(200, 330) });
          this.sub = 'carry'; this.timer = rnd(2.4, 4.2);
          return;
        }

        h.relook(h.x, h.y);
        if (this.timer <= 0) {
          // старое существо иногда целится мимо и хватает соседа
          var cc = api.cell();
          this.aimOff = chance(0.35 * api.oldness()) ? { x: rnd(-1, 1) * cc * 0.9, y: rnd(-1, 1) * cc * 0.9 } : null;
          h.to(hn.from.x, hn.from.y, { speed: rnd(300, 560) });
          this.sub = 'go'; this.timer = rnd(1.0, 2.4);
        }
        break;
      }

      // --- утилизация: держит курсор на знаке и уводит точно в окне --------
      case 'purge': {
        var pt = api.purgeHint();
        if (!pt) { this.st = 'resume'; this.sub = 'go'; this.timer = 0; return; }

        /* После ухода рука должна ДОЙТИ до конца. Раньше она в тот же кадр
           разворачивалась обратно к тому же знаку, тот додерживался и
           расщеплялся: четыре знака из пяти уходили в брак. */
        if (this.sub === 'leave') {
          if (this.timer <= 0) { this.sub = 'go'; this.timer = 0; }
          return;
        }
        if (this.sub === 'go') {
          h.to(pt.x, pt.y, { speed: rnd(260, 460) });
          this.sub = 'reach'; this.timer = rnd(1.4, 3.0);
          return;
        }
        if (this.sub === 'reach') {
          if (this.steer(pt)) { this.timer = Math.max(this.timer, 1.2); return; }
          if (!h.arrived(8)) { if (this.timer <= 0) { h.to(pt.x, pt.y, { speed: 200 }); this.timer = 2; } return; }
          {
            api.purgePress(h.x, h.y);        // жмём ровно там, где курсор
            this.sub = 'hold'; this.timer = rnd(3.5, 5.0);
          }
          return;
        }
        // ждём провала в тишину и отпускаем ровно там
        h.retarget(pt.x, pt.y);
        if (api.purgeReady() || this.timer <= 0) {
          api.purgeRelease();
          h.to(pt.x + rnd(-190, 190), pt.y + rnd(-150, 150), { speed: rnd(360, 580) });
          this.sub = 'leave'; this.timer = rnd(0.35, 0.7);
        }
        break;
      }

      // --- проверка второго края -------------------------------------------
      case 'verify': {
        var pv = this.live(this.cand);
        h.relook(pv.x, pv.y);
        if (this.timer > 0) return;
        var s = this.start.rec, c = this.cand.rec;
        if (c.pid && c.pid === s.pid && c.role !== s.role) {
          api.release(pv.x, pv.y);
          h.inspect(pv.x, pv.y, rnd(10, 20));
          this.st = 'send'; this.sub = 'wait'; this.timer = rnd(0.45, 1.1);
        } else {
          this.tried[key(this.cand)] = 1;
          this.cand = null;
          this.st = 'hunt'; this.sub = 'weigh'; this.timer = rnd(0.4, 1.5);
        }
        break;
      }

      // --- отправка: доводит курсор до кнопки и нажимает --------------------
      case 'send': {
        var b = api.button();
        if (!b) { this.cand = null; this.start = null; this.st = 'scan'; this.sub = 'move'; this.timer = 0; return; }
        if (this.timer > 0) return;
        if (this.sub === 'wait') {
          h.to(b.x, b.y, { speed: rnd(240, 420) });
          this.sub = 'reach'; this.timer = rnd(1.6, 3.2);
          return;
        }
        h.retarget(b.x, b.y);
        if (!h.arrived(12)) { if (this.timer <= 0) { h.to(b.x, b.y, { speed: 220 }); this.timer = 2; } return; }
        {
          api.clickButton();
          this.cand = null; this.start = null;
          this.rejected = {};
          this.areaWork = (this.areaWork || 0) + 1;
          // служебный паттерн: за сбором идёт анализ, а не следующий сбор
          this.want = api.needPhase();
          this.st = 'toPhase'; this.sub = 'go'; this.timer = rnd(2.6, 4.4);
          var fa = api.folderPos(this.want);
          h.to(fa.x, fa.y - 30, { speed: rnd(220, 400) });
        }
        break;
      }

      // --- переход на другой этап: доводит курсор до сосуда и нажимает -----
      case 'toPhase': {
        var fp = api.folderPos(this.want);
        h.retarget(fp.x, fp.y - 30);
        /* Перед точной работой — анализом, сортировкой, утилизацией —
           существо приближает карту колесом, как сделал бы игрок. На
           отдалённом поле клетки мелкие, и рука хватала не те знаки.
           Приближать надо ДО входа в этап: доска сортировки ложится в
           пределах видимого поля. */
        if (this.want >= 1 && api.zoom() < 0.9) {
          if (this.zoomCd <= 0) { api.zoomBy(1); this.zoomCd = rnd(0.22, 0.4); }
          return;
        }
        // Этап переключается ТОЛЬКО по приходу к сосуду. Раньше срабатывал и
        // таймер, а он был коротким, поэтому этапы менялись сами собой,
        // где-то на полпути, и жеста нажатия было не видно.
        if (!h.arrived(18) && this.timer > 0) return;
        if (!h.arrived(26)) { this.timer = rnd(1.2, 2.2); return; }
        if (this.tapCd > 0) return;
        this.tapCd = rnd(1.1, 2.0);
        api.tap(fp.x, fp.y - 30);
        api.setPhase(this.want);
        this.enter(this.want);
        break;
      }

      // --- цепочка анализа: узел за узлом по наклону ------------------------
      case 'chain': {
        var nd = api.chainNext();
        if (!nd) {                       // цепочек больше нет, возвращаемся к сбору
          this.slip = null;
          // цепочек больше нет: идём туда, где работа ждёт
          this.want = api.needPhase();
          this.st = 'toPhase'; this.sub = 'go'; this.timer = rnd(2.6, 4.4);
          var f2 = api.folderPos(this.want);
          h.to(f2.x, f2.y - 30, { speed: rnd(220, 400) });
          return;
        }
        var np = api.screenOf(nd.wx, nd.wy);

        if (this.sub === 'weigh') {
          h.relook(h.x, h.y);
          if (this.timer <= 0) {
            // старое существо сбивается: тянется не к тому узлу
            this.slip = api.slipTarget();
            if (this.slip) np = api.screenOf(this.slip.wx, this.slip.wy);
            h.to(np.x, np.y, { speed: rnd(200, 470) });
            this.sub = 'move'; this.timer = rnd(1.8, 4.2);
          }
          return;
        }
        if (this.slip) np = api.screenOf(this.slip.wx, this.slip.wy);
        if (this.sub === 'move') {
          if (this.steer(np)) { this.timer = Math.max(this.timer, 1.2); return; }
          h.retarget(np.x, np.y);
          if (h.arrived(14)) {
            h.inspect(np.x, np.y, rnd(4, 9));
            this.sub = 'look'; this.timer = rnd(0.3, 0.9);
          } else if (this.timer <= 0) { h.to(np.x, np.y, { speed: rnd(200, 300) }); this.timer = 2; }
          return;
        }
        if (this.sub === 'look') {
          h.relook(np.x, np.y);
          if (this.timer > 0) return;
          h.to(np.x, np.y, { speed: 160 });
          this.sub = 'aim'; this.timer = 1.5;
          return;
        }
        /* Раньше узел нажимался по его координатам, где бы ни был курсор, и
           существо «тыкало» знак раньше, чем до него доезжало. */
        h.retarget(np.x, np.y);
        if (!h.arrived(6)) { if (this.timer <= 0) { h.to(np.x, np.y, { speed: 160 }); this.timer = 1.5; } return; }
        {
          if (this.slip) {
            // нажало не тот узел: ошибка, и цепочку приходится начинать заново
            api.slipAt(this.slip);
            this.slip = null;
            h.inspect(h.x, h.y, rnd(10, 20));
            this.sub = 'weigh'; this.timer = rnd(1.4, 2.6);
            break;
          }
          api.analyzePick(h.x, h.y);
          // внутри цепочки существо идёт увереннее: путь ему уже показан
          this.sub = 'weigh'; this.timer = rnd(0.15, 0.6);
        }
        break;
      }
    }
  };

  /* --- восприятие ---------------------------------------------------------- */

  /* Годные якоря на экране: второй край виден, блок не лежит на изработанном. */
  Creature.prototype.eligible = function () {
    var api = this.api, v = api.view(), self = this;
    if (this.eligT !== undefined && api.time() - this.eligT < 0.2) return this.eligCache;
    this.eligT = api.time();
    this.eligCache = api.anchors(REAL).filter(function (a) {
      if (self.rejected[key(a)]) return false;
      var m = a.rec.mate;
      if (!m) return false;
      var q = api.screenOf(m.x, m.y);
      if (!(q.x > 80 && q.y > 100 && q.x < v.w - 80 && q.y < v.h - 150)) return false;
      if (a.x < 60 || a.y < 90 || a.x > v.w - 60 || a.y > v.h - 150) return false;
      return api.pairWear(a.wx, a.wy, m.x, m.y) < 0.4;
    });
    return this.eligCache;
  };

  var VISUAL = { 1: 1, 3: 1 };      // отстающий и сбойный видны глазом; затаившийся, тяжёлый и пугливый — на волне

  /* Что существо заметило за этот миг. Проверяется пять раз в секунду. */
  Creature.prototype.perceive = function (dt) {
    this.pAcc = (this.pAcc || 0) + dt;
    if (this.pAcc < 0.2) return null;
    var stepT = this.pAcc; this.pAcc = 0;
    var api = this.api, h = this.hand, v = api.view(), now = api.time();
    var spd = Math.sqrt(h.vx * h.vx + h.vy * h.vy);
    var reach = 150 * Math.min(1.3, Math.max(0.6, api.zoom()));
    this.waved = this.waved || {};
    var list = this.eligible(), best = null;
    for (var i = 0; i < list.length; i++) {
      var a = list[i], d = Math.sqrt((a.x - h.x) * (a.x - h.x) + (a.y - h.y) * (a.y - h.y));
      var kind = a.rec.kind, rate = 0, k = key(a);
      if (VISUAL[kind]) {
        // далёкий бросается в глаза редко, у самого курсора — почти сразу
        rate = kind === 0 ? 0.025 + 0.9 * Math.exp(-d / 140) : 0.05 + 1.5 * Math.exp(-d / 160);
      } else {
        // тяжёлый отзывается на любой проход волны, пугливый — только на быстрый
        // тяжёлый и затаившийся выдают себя на любом проходе волны, пугливый — только на быстром
        if (d < reach && (kind === 2 || kind === 0 || spd > 150)) this.waved[k] = now;
        var w = this.waved[k];
        if (w !== undefined && now - w > 0.25 && now - w < 1.8) rate = 2.4;
      }
      rate *= 1 - 0.55 * api.oldness();             // старое существо замечает хуже
      if (rate && Math.random() < 1 - Math.exp(-rate * stepT)) {
        if (!best || d < best.d) best = { a: a, d: d };
      }
    }
    if (best) return best.a;
    // совсем редко обознаётся: что-то почудилось
    if (Math.random() < 0.012 * (1 + 3 * api.oldness()) * stepT) {
      return { blank: true, falseSeen: true,
               x: Math.max(80, Math.min(v.w - 80, h.x + rnd(-280, 280))),
               y: Math.max(110, Math.min(v.h - 160, h.y + rnd(-200, 200))) };
    }
    return null;
  };

  /* --- обход карты по спирали ---------------------------------------------- */
  /* Работа начинается в середине карты и расходится от неё прямоугольной
     спиралью. Шаг — примерно экран. Спираль нарочно неровная: каждая точка
     чуть сдвинута. Изработанный участок существо просто проезжает. */

  var SX = 22, SY = 12;

  function Spiral() { this.x = 0; this.y = 0; this.dir = 0; this.leg = 1; this.left = 1; this.turns = 0; this.first = true; }
  Spiral.prototype.next = function () {
    if (this.first) { this.first = false; return { x: 0, y: 0 }; }
    var D = [[1, 0], [0, 1], [-1, 0], [0, -1]];
    this.x += D[this.dir][0]; this.y += D[this.dir][1];
    if (--this.left === 0) {
      this.dir = (this.dir + 1) % 4; this.turns++;
      if (this.turns % 2 === 0) this.leg++;
      this.left = this.leg;
    }
    return { x: this.x, y: this.y };
  };

  function wrapS(v, n) { var r = ((v % n) + n) % n; return r > n / 2 ? r - n : r; }

  Creature.prototype.travel = function () {
    var api = this.api, h = this.hand;
    if (!this.spiral || this.spiralMap !== api.mapId()) {
      this.spiralMap = api.mapId();
      this.spiral = new Spiral();
      this.home = api.home();
    }
    var W = api.mapSize(), wp = null;
    for (var guard = 0; guard < 200 && !wp; guard++) {
      var n = this.spiral.next();
      if (Math.abs(n.y) * SY > W.h / 2) { this.spiral = new Spiral(); continue; }   // карта пройдена — сначала
      if (Math.abs(n.x) * SX > W.w / 2) continue;
      wp = n;
    }
    if (!wp) wp = { x: 0, y: 0 };
    this.wp = { x: this.home.x + wp.x * SX + rnd(-3, 3), y: this.home.y + wp.y * SY + rnd(-2, 2) };
    this.sub = 'travel'; this.timer = 22; this.travelGo = false;
    this.areaWork = 0; this.sweeps = 0; this.rejected = {}; this.waved = {};
    if (api.zoom() < 0.99) api.zoomBy(1);
  };

  /* Рука стоит у края в сторону точки. Чем ближе точка, тем мельче рука
     заходит в полосу прокрутки: поле тормозит, а не проскакивает. */
  Creature.prototype.stepTravel = function () {
    var api = this.api, h = this.hand, v = api.view(), W = api.mapSize();
    var c = api.viewCell();
    var dx = wrapS(this.wp.x - c.x, W.w), dy = wrapS(this.wp.y - c.y, W.h);
    var dist = Math.sqrt(dx * dx + dy * dy);
    if (dist < 2.5 || this.timer <= 0) {
      this.sub = 'move'; this.timer = 0;
      h.to(v.w / 2 + rnd(-220, 220), v.h / 2 + rnd(-140, 60), { speed: rnd(240, 400) });
      return;
    }
    var ux = dx / dist, uy = dy / dist;
    var inset = 22 + (1 - Math.min(1, dist / 12)) * 85;
    var cx = v.w / 2, cy = v.h / 2;
    var k = Math.min((v.w / 2 - inset) / Math.max(1e-3, Math.abs(ux)), (v.h / 2 - inset) / Math.max(1e-3, Math.abs(uy)));
    var ex = cx + ux * k, ey = cy + uy * k;
    if (!this.travelGo) { h.to(ex, ey, { speed: rnd(320, 480) }); this.travelGo = true; }
    else h.retarget(ex, ey);
    this.panning = true;
  };

  /* Набор знаков команды по одному. Знак ищется глазами на экране, как и всё
     остальное; нет нужного — существо отдаляет поле, а если и так нет, бросает
     команду и отжимает пустоту. */
  Creature.prototype.typeKeys = function (then) {
    var api = this.api, h = this.hand, v = api.view();
    if (!api.conOpen()) { this.st = 'resume'; this.sub = 'go'; this.timer = rnd(0.4, 1); this.moving = false; return; }

    if (this.sub === 'pickKey') {
      h.relook(h.x, h.y);
      if (this.timer > 0) return;
      // сколько знаков уже принято, берём у пульта: промах или сброс не собьют счёт
      // прямая команда уже принята — дальше набирать нечего
      this.ki = (then === 'leave' && api.conMode()) ? this.keys.length : api.conProgress();
      if (this.ki >= this.keys.length) { this.sub = then; this.timer = rnd(0.5, 1.2); this.moving = false; return; }
      var c = api.findKey(this.keys[this.ki], h.x, h.y);
      if (!c) {
        if (api.zoom() > 0.42) { api.zoomBy(-1); this.timer = rnd(0.8, 1.4); return; }
        this.sub = 'release'; this.moving = false; this.timer = 0;
        return;
      }
      this.keyCell = c;
      var p = this.live(c);
      h.to(p.x, p.y, { speed: rnd(220, 420) });
      this.sub = 'goKey'; this.timer = rnd(1.8, 3.6);
      return;
    }
    if (this.sub === 'goKey') {
      var pk = this.live(this.keyCell);
      h.retarget(pk.x, pk.y);
      if (h.arrived(9) || this.timer <= 0) {
        h.inspect(pk.x, pk.y, rnd(3, 7));
        this.sub = 'press'; this.timer = rnd(0.25, 0.7);
      }
      return;
    }
    if (this.sub === 'press') {
      var pp = this.live(this.keyCell);
      h.relook(pp.x, pp.y);
      if (this.timer > 0) return;
      api.conClick(pp.x, pp.y);
      this.ki++;
      this.sub = 'pickKey'; this.timer = rnd(0.35, 1.0);
      return;
    }
    if (this.sub === 'leave') {
      if (this.timer > 0) return;
      if (api.conMode()) {
        // команда принята: рука отъезжает в сторону и замирает
        h.to(v.w * rnd(0.62, 0.86), v.h - rnd(170, 240), { speed: rnd(150, 240) });
        this.st = 'away'; this.sub = 'rest';
        return;
      }
      this.sub = 'release'; this.moving = false;
      return;
    }
    if (this.sub === 'release') {
      var cv = api.conVoid();
      if (!cv) { this.st = 'resume'; this.sub = 'go'; this.timer = 0; return; }
      if (!this.moving) { h.to(cv.x, cv.y, { speed: rnd(220, 380) }); this.moving = true; this.timer = rnd(2, 3.4); return; }
      h.retarget(cv.x, cv.y);
      if (h.arrived(9) || this.timer <= 0) {
        this.moving = false;
        api.conClick(cv.x, cv.y);
        if (!api.conOpen()) { this.st = 'resume'; this.sub = 'go'; this.timer = rnd(0.6, 1.2); }
        // пустота не отжалась: обратная команда не добрана, возвращаемся к знакам
        else if (api.conMode()) { this.sub = 'pickKey'; this.timer = rnd(0.6, 1.2); }
        else { this.timer = rnd(0.5, 1); }
      }
    }
  };

  /* Обед или сон кончился: существо садится обратно и набирает команду задом
     наперёд. */
  Creature.prototype.comeBack = function () {
    this.st = 'back'; this.sub = 'pickKey'; this.timer = rnd(0.9, 1.8);
    this.keys = this.api.conKeys().slice().reverse(); this.ki = 0;
    this.moving = false;
  };

  /* Существо отпускает пульт: всё брошенное надо вернуть в исходное. */
  Creature.prototype.detach = function () {
    if (this.st !== 'scan') this.api.abort();
    this.st = 'resume'; this.sub = 'go'; this.timer = 0;
    this.cand = null; this.start = null; this.target = null;
    this.rejected = {};
  };

  Creature.prototype.attach = function () {
    var c = this.api.cursor();
    this.hand.x = c.x; this.hand.y = c.y;
    this.hand.vx = 0; this.hand.vy = 0;
    // подключаясь, существо сначала разбирается, где игрок остановился
    this.st = 'resume'; this.sub = 'go'; this.timer = 0;
  };

  root.Creature = Creature;
})(window);
