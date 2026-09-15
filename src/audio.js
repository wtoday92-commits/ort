/* ORT — звук.
 *
 * Всё синтезируется на месте, файлов нет. Интервалы взяты негармоничные
 * (1, 1.37, 1.78, 2.41), поэтому созвучия не складываются ни в аккорд, ни в
 * лад: это не музыка, а работа прибора.
 *
 * Звук здесь не украшение. На нём висит второй канал подсказки: у якоря под
 * курсором свой тон на каждую повадку, выдержка слышна нарастанием, а
 * подтверждение и отказ различаются на слух раньше, чем глазом.
 *
 * Браузер не даёт звук до первого касания, поэтому заставка сначала идёт
 * тихой и оживает, как только игрок шевельнётся.
 */
(function (root) {
  'use strict';

  var RATIO = [1, 1.37, 1.78, 2.41, 3.11];   // пять повадок якоря
  var BASE = 196;

  var ctx = null, master = null, noiseBuf = null;
  var bed = null, sweep = null, room = null, far = null, farOn = false;
  var ready = false, muted = false;
  var farFilter = null, farOsc = [], radioBus = null;
  var lab = null, labOn = false, roomMul = 1, pendingRoom = null;
  var labChain = 0, frameAcc = 0, lastParam = {};
  var compNode = null, airBus = null, airSrc = null, humNodes = null, vacuumOn = false;

  function now() { return ctx ? ctx.currentTime : 0; }

  function makeNoise() {
    var n = ctx.sampleRate * 2;
    var b = ctx.createBuffer(1, n, ctx.sampleRate);
    var d = b.getChannelData(0);
    var last = 0;
    for (var i = 0; i < n; i++) {
      var w = Math.random() * 2 - 1;
      last = (last + 0.02 * w) / 1.02;    // коричневый: белый слишком колкий
      d[i] = last * 3.5;
    }
    return b;
  }

  function noiseSource(loop) {
    var s = ctx.createBufferSource();
    s.buffer = noiseBuf;
    s.loop = !!loop;
    return s;
  }

  function init() {
    var AC = root.AudioContext || root.webkitAudioContext;
    if (!AC) return false;
    ctx = new AC();
    noiseBuf = makeNoise();

    master = ctx.createGain();
    master.gain.value = 0.0001;
    var comp = ctx.createDynamicsCompressor();
    comp.threshold.value = -18;
    comp.ratio.value = 6;
    master.connect(comp);
    comp.connect(ctx.destination);
    compNode = comp;

    // общий фильтр помещения: при заморозке поля он закрывается, и комната
    // как будто задерживает дыхание
    room = ctx.createBiquadFilter();
    room.type = 'lowpass';
    room.frequency.value = 1800;
    room.Q.value = 0.4;
    room.connect(master);

    // подложка: два расстроенных низа плюс глухой шум
    bed = ctx.createGain();
    bed.gain.value = 0.16;
    bed.connect(room);
    [44, 44.7, 66.3].forEach(function (f, i) {
      var o = ctx.createOscillator();
      o.type = i === 2 ? 'sine' : 'triangle';
      o.frequency.value = f;
      var g = ctx.createGain();
      g.gain.value = i === 2 ? 0.12 : 0.3;
      o.connect(g); g.connect(bed);
      o.start();
      // медленное биение, чтобы подложка не стояла на месте
      var lfo = ctx.createOscillator();
      lfo.frequency.value = 0.031 + i * 0.017;
      var lg = ctx.createGain();
      lg.gain.value = 0.10;
      lfo.connect(lg); lg.connect(g.gain);
      lfo.start();
    });
    var bn = noiseSource(true);
    var bf = ctx.createBiquadFilter();
    bf.type = 'lowpass'; bf.frequency.value = 140;
    var bg = ctx.createGain(); bg.gain.value = 0.30;
    bn.connect(bf); bf.connect(bg); bg.connect(bed);
    bn.start();

    // шелест поля под курсором: полосовой шум, громкость ведётся снаружи
    var sn = noiseSource(true);
    var sf = ctx.createBiquadFilter();
    sf.type = 'bandpass'; sf.frequency.value = 2400; sf.Q.value = 1.1;
    sweep = ctx.createGain(); sweep.gain.value = 0;
    sn.connect(sf); sf.connect(sweep); sweep.connect(room);
    sn.start();

    /* Очень далёкий эмбиент. Включается не сразу, а спустя пару минут, и
       наплывает больше минуты. Он должен не начаться, а оказаться: игрок не
       ловит момент включения, а через какое-то время замечает, что фон уже
       есть. Монотонный нарочно: это не музыка, а то, что снаружи. */
    far = ctx.createGain();
    far.gain.value = 0.0001;
    var fl = farFilter = ctx.createBiquadFilter();
    fl.type = 'lowpass'; fl.frequency.value = 420; fl.Q.value = 0.7;
    far.connect(fl); fl.connect(master);
    [58.2, 87.1, 116.9, 174.3].forEach(function (f, i) {
      var o = ctx.createOscillator();
      o.type = 'sine';
      o.frequency.value = f;
      o.detune.value = (i % 2 ? 7 : -7);
      var g = ctx.createGain();
      g.gain.value = [0.5, 0.3, 0.2, 0.1][i];
      o.connect(g); g.connect(far);
      o.start();
      farOsc.push({ o: o, g: g, base: f, gain: [0.5, 0.3, 0.2, 0.1][i] });
      // очень медленное дыхание, периоды несоизмеримы между собой
      var lfo = ctx.createOscillator();
      lfo.frequency.value = 0.0121 + i * 0.0073;
      var lg = ctx.createGain(); lg.gain.value = 0.42;
      lfo.connect(lg); lg.connect(g.gain);
      lfo.start();
    });
    var fn = noiseSource(true);
    var ff = ctx.createBiquadFilter();
    ff.type = 'bandpass'; ff.frequency.value = 190; ff.Q.value = 0.5;
    var fg = ctx.createGain(); fg.gain.value = 0.22;
    fn.connect(ff); ff.connect(fg); fg.connect(far);
    fn.start();

    ready = true;
    return true;
  }

  /* --- голос космоса ------------------------------------------------------- */
  /* Дальний фон не стоит на месте: раз в полминуты-минуту он медленно
     перестраивается — сдвигаются тоны, открывается и закрывается фильтр,
     меняется вес голосов. Перестройка идёт десятками секунд, её не слышно как
     событие, только как то, что фон стал другим. */
  function farDrift() {
    if (!ready || !farOn) return;
    var t = now();
    farFilter.frequency.setTargetAtTime(240 + Math.random() * 520, t, 14);
    farOsc.forEach(function (v) {
      v.o.detune.setTargetAtTime((Math.random() - 0.5) * 60, t, 18);
      v.g.gain.setTargetAtTime(v.gain * (0.35 + Math.random() * 1.1), t, 16);
    });
    // иногда один голос уходит на чужой интервал и возвращается
    if (Math.random() < 0.35) {
      var v = farOsc[Math.floor(Math.random() * farOsc.length)];
      var m = [1.37, 0.73, 1.19, 0.84][Math.floor(Math.random() * 4)];
      v.o.frequency.setTargetAtTime(v.base * m, t, 20);
      setTimeout(function () { if (ready) v.o.frequency.setTargetAtTime(v.base, now(), 24); }, 40000 + Math.random() * 30000);
    }
    setTimeout(farDrift, 28000 + Math.random() * 40000);
  }

  /* Очень далёкое радио. Изредка фон ловит обрывок чужой передачи: шипение
     полосы, свист несущей, ползущий по частоте, морзянку или бормотание,
     похожее на голос. Всё глухо, с эхом, сбоку и на самой грани слышимости. */
  function radioBusInit() {
    radioBus = ctx.createGain();
    radioBus.gain.value = 1;
    var hp = ctx.createBiquadFilter(); hp.type = 'highpass'; hp.frequency.value = 350;
    var lp = ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 2600;
    var dl = ctx.createDelay(1); dl.delayTime.value = 0.27;
    var fb = ctx.createGain(); fb.gain.value = 0.32;
    radioBus.connect(hp); hp.connect(lp); lp.connect(master);
    lp.connect(dl); dl.connect(fb); fb.connect(dl); dl.connect(master);
  }

  function radio() {
    if (!ready || !farOn) return;
    if (!muted && !labOn) {
      if (!radioBus) radioBusInit();
      var t = now(), dur = 2.5 + Math.random() * 5.5, vol = 0.018 + Math.random() * 0.022;
      var out = ctx.createGain();
      out.gain.setValueAtTime(0.0001, t);
      out.gain.exponentialRampToValueAtTime(vol, t + dur * 0.3);
      out.gain.setValueAtTime(vol, t + dur * 0.7);
      out.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      // замирания: сигнал то пропадает, то возвращается
      var fade = ctx.createGain(); fade.gain.value = 0.6;
      var lfo = ctx.createOscillator(); lfo.frequency.value = 0.4 + Math.random() * 1.6;
      var lg = ctx.createGain(); lg.gain.value = 0.4;
      lfo.connect(lg); lg.connect(fade.gain); lfo.start(t); lfo.stop(t + dur + 0.1);
      var node = out;
      if (ctx.createStereoPanner) {
        var pan = ctx.createStereoPanner(); pan.pan.value = (Math.random() - 0.5) * 1.6;
        out.connect(pan); node = pan;
      }
      fade.connect(out);
      node.connect(radioBus);

      // шипение полосы есть всегда
      var n = noiseSource(false); n.playbackRate.value = 1.8;
      var bp = ctx.createBiquadFilter(); bp.type = 'bandpass'; bp.Q.value = 1.4;
      bp.frequency.value = 1100 + Math.random() * 1400;
      var ng = ctx.createGain(); ng.gain.value = 0.7;
      n.connect(bp); bp.connect(ng); ng.connect(fade);
      n.start(t); n.stop(t + dur + 0.1);

      var kind = Math.floor(Math.random() * 3);
      if (kind === 0) {
        // свист несущей, ползущий по частоте
        var o = ctx.createOscillator(); o.type = 'sine';
        var f0 = 700 + Math.random() * 900;
        o.frequency.setValueAtTime(f0, t);
        o.frequency.exponentialRampToValueAtTime(f0 * (0.6 + Math.random() * 0.9), t + dur);
        var og = ctx.createGain(); og.gain.value = 0.35;
        o.connect(og); og.connect(fade); o.start(t); o.stop(t + dur + 0.1);
      } else if (kind === 1) {
        // морзянка
        var mo = ctx.createOscillator(); mo.type = 'sine'; mo.frequency.value = 600 + Math.random() * 300;
        var mg = ctx.createGain(); mg.gain.value = 0;
        mo.connect(mg); mg.connect(fade); mo.start(t); mo.stop(t + dur + 0.1);
        var at = t + 0.3;
        while (at < t + dur - 0.3) {
          var len = Math.random() < 0.5 ? 0.07 : 0.21;
          mg.gain.setValueAtTime(0.5, at); mg.gain.setValueAtTime(0, at + len);
          at += len + (Math.random() < 0.25 ? 0.35 : 0.08);
        }
      } else {
        // бормотание: пила через плавающие форманты, рваными слогами
        var vo = ctx.createOscillator(); vo.type = 'sawtooth';
        vo.frequency.value = 110 + Math.random() * 70;
        var fm = ctx.createBiquadFilter(); fm.type = 'bandpass'; fm.Q.value = 5;
        var vg = ctx.createGain(); vg.gain.value = 0;
        vo.connect(fm); fm.connect(vg); vg.connect(fade);
        vo.start(t); vo.stop(t + dur + 0.1);
        var st = t + 0.2;
        while (st < t + dur - 0.2) {
          var sl = 0.08 + Math.random() * 0.22;
          fm.frequency.setValueAtTime(500 + Math.random() * 1400, st);
          vo.frequency.setValueAtTime(100 + Math.random() * 90, st);
          vg.gain.setValueAtTime(0.9, st); vg.gain.setTargetAtTime(0, st + sl * 0.6, 0.03);
          st += sl + Math.random() * 0.18;
        }
      }
    }
    setTimeout(radio, 45000 + Math.random() * 100000);
  }

  /* --- компьютерный фон лорной вкладки -------------------------------------
     Журнал корабля звучит не космосом, а машиной: гул вентилятора, сетевой
     фон, редкие щелчки реле, короткие писки и очереди данных. */
  function setParam(key, param, v, tau) {
    var last = lastParam[key];
    if (last !== undefined && Math.abs(last - v) <= Math.max(0.0005, Math.abs(v) * 0.03)) return;
    lastParam[key] = v;
    var t = now();
    if (param.cancelAndHoldAtTime) param.cancelAndHoldAtTime(t); else param.cancelScheduledValues(t);
    param.setTargetAtTime(v, t, tau);
  }

  /* Металлический удар: негармоничный звонкий тон мимо фильтра комнаты. */
  function metal(freq, dur, vol) {
    var t = now(), o = ctx.createOscillator(), o2 = ctx.createOscillator(), g = ctx.createGain();
    o.type = 'square'; o.frequency.value = freq;
    o2.type = 'triangle'; o2.frequency.value = freq * 2.76;
    g.gain.setValueAtTime(vol, t);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    var bp = ctx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = freq * 1.5; bp.Q.value = 2.5;
    o.connect(bp); o2.connect(bp); bp.connect(g); g.connect(master);
    o.start(t); o2.start(t); o.stop(t + dur + 0.05); o2.stop(t + dur + 0.05);
  }

  function labInit() {
    lab = ctx.createGain();
    lab.gain.value = 0.0001;
    lab.connect(master);
    /* Серверная: ровный мягкий поток вентиляторов, под ним едва слышный гул
       питания. Без писков и высоких тонов: звук должен не раздражать часами,
       а просто стоять в комнате. */
    var n = noiseSource(true);
    var lp = ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 480; lp.Q.value = 0.3;
    var lp2 = ctx.createBiquadFilter(); lp2.type = 'lowpass'; lp2.frequency.value = 900;
    var ng = ctx.createGain(); ng.gain.value = 0.42;
    n.connect(lp); lp.connect(lp2); lp2.connect(ng); ng.connect(lab);
    n.start();
    // воздух из решёток: очень тихий широкий шелест повыше
    var n2 = noiseSource(true);
    var bp = ctx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 1500; bp.Q.value = 0.35;
    var ag = ctx.createGain(); ag.gain.value = 0.035;
    n2.playbackRate.value = 0.83;
    n2.connect(bp); bp.connect(ag); ag.connect(lab);
    n2.start();
    // гул питания и лопасти двух вентиляторов, чуть расстроенных между собой
    [[50, 0.018], [100, 0.006], [117, 0.004], [117.6, 0.004]].forEach(function (p) {
      var o = ctx.createOscillator(); o.type = 'sine'; o.frequency.value = p[0];
      var g = ctx.createGain(); g.gain.value = p[1];
      o.connect(g); g.connect(lab); o.start();
    });
    // поток медленно дышит
    var lfo = ctx.createOscillator(); lfo.frequency.value = 0.045;
    var lg = ctx.createGain(); lg.gain.value = 70;
    lfo.connect(lg); lg.connect(lp.frequency); lfo.start();
  }

  /* Короткий тихий щелчок прямо в шину серверной: реле, головка диска. */
  function labClick(freq, vol, dur) {
    var t = now(), s = noiseSource(false), f = ctx.createBiquadFilter(), g = ctx.createGain();
    s.playbackRate.value = 0.8 + Math.random() * 0.4;
    f.type = 'bandpass'; f.frequency.value = freq; f.Q.value = 2.2;
    g.gain.setValueAtTime(vol, t);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    s.connect(f); f.connect(g); g.connect(lab);
    s.start(t); s.stop(t + dur + 0.03);
  }

  function labPing(freq, dur, vol, type) {
    var t = now(), o = ctx.createOscillator(), g = ctx.createGain();
    o.type = type || 'square'; o.frequency.value = freq;
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(vol, t + 0.004);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(lab);
    o.start(t); o.stop(t + dur + 0.02);
  }

  function labChirps(id) {
    // у писков одна цепочка: при частом переключении вкладок они больше не размножаются
    if (!ready || !labOn || id !== labChain) return;
    // изредка: щелчок реле, пара тихих тиков диска или двойной мягкий стук
    if (!muted) {
      var r = Math.random();
      if (r < 0.45) labClick(1800 + Math.random() * 1400, 0.05, 0.02);
      else if (r < 0.8) {
        var cnt = 2 + Math.floor(Math.random() * 3), base = 2600 + Math.random() * 1200;
        for (var i = 0; i < cnt; i++) (function (k) {
          setTimeout(function () { if (labOn) labClick(base, 0.025, 0.012); }, k * (55 + Math.random() * 40));
        })(i);
      } else {
        labClick(900, 0.06, 0.04);
        setTimeout(function () { if (labOn) labClick(1100, 0.04, 0.035); }, 110);
      }
    }
    setTimeout(function () { labChirps(id); }, 3000 + Math.random() * 7000);
  }

  /* Звук включается только после первого действия игрока. */
  function unlock() {
    if (!ready && !init()) return;
    if (ctx.state === 'suspended') ctx.resume();
    if (!muted && !vacuumOn) master.gain.setTargetAtTime(0.5, now(), 1.2);
    if (pendingRoom) { var pr = pendingRoom; pendingRoom = null; API.room(pr); }
  }

  function ping(freq, dur, vol, type, detune) {
    if (!ready || muted) return;
    var t = now();
    var o = ctx.createOscillator();
    o.type = type || 'sine';
    o.frequency.value = freq;
    if (detune) o.detune.value = detune;
    var g = ctx.createGain();
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(vol, t + Math.min(0.03, dur * 0.2));
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(room);
    o.start(t); o.stop(t + dur + 0.05);
  }

  function hit(dur, vol, lo, hi, sweepTo) {
    if (!ready || muted) return;
    var t = now();
    var s = noiseSource(false);
    s.playbackRate.value = 0.7 + Math.random() * 0.6;
    var f = ctx.createBiquadFilter();
    f.type = 'bandpass';
    f.frequency.setValueAtTime(hi, t);
    if (sweepTo) f.frequency.exponentialRampToValueAtTime(sweepTo, t + dur);
    f.Q.value = 1.4;
    var hp = ctx.createBiquadFilter();
    hp.type = 'highpass'; hp.frequency.value = lo;
    var g = ctx.createGain();
    g.gain.setValueAtTime(vol, t);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    s.connect(f); f.connect(hp); hp.connect(g); g.connect(room);
    s.start(t); s.stop(t + dur + 0.05);
  }

  /* Тон с изгибом высоты: для возмущения, смерти и срыва. */
  function bend(f0, f1, dur, vol, type) {
    if (!ready || muted) return;
    var t = now();
    var o = ctx.createOscillator();
    o.type = type || 'sine';
    o.frequency.setValueAtTime(f0, t);
    o.frequency.exponentialRampToValueAtTime(f1, t + dur);
    var g = ctx.createGain();
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(vol, t + Math.min(0.04, dur * 0.2));
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(master);
    o.start(t); o.stop(t + dur + 0.05);
  }

  /* Длинный шум с огибающей: срывы и переезд. Идёт мимо фильтра комнаты,
     потому что это не звук поля, а звук самого прибора. */
  function wash(dur, vol, f0, f1, q) {
    if (!ready || muted) return;
    var t = now();
    var s = noiseSource(true);
    var f = ctx.createBiquadFilter();
    f.type = 'bandpass'; f.Q.value = q || 0.8;
    f.frequency.setValueAtTime(f0, t);
    f.frequency.exponentialRampToValueAtTime(f1, t + dur);
    var g = ctx.createGain();
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + dur * 0.35);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    s.connect(f); f.connect(g); g.connect(master);
    s.start(t); s.stop(t + dur + 0.05);
  }

  var API = {
    unlock: unlock,
    get ready() { return ready && ctx && ctx.state === 'running'; },

    toggle: function () {
      muted = !muted;
      if (ready) master.gain.setTargetAtTime(muted ? 0.0001 : 0.5, now(), 0.2);
      return muted;
    },

    /* Дальний фон наплывает спустя пару минут игры и очень медленно. */
    horizon: function () {
      if (!ready || muted || farOn) return;
      farOn = true;
      far.gain.setTargetAtTime(labOn ? 0.0001 : 0.30, now(), 26);
      setTimeout(farDrift, 40000 + Math.random() * 20000);
      setTimeout(radio, 70000 + Math.random() * 60000);
    },

    /* Каждый кадр: шелест поля и закрытие комнаты при заморозке. */
    /* Десять раз в секунду и только при заметном изменении. Раньше каждый
       кадр ставил три новых события автоматизации, и за часы игры они
       копились в звуковом движке браузера. */
    frame: function (dt, speed, waveHot, freeze) {
      if (!ready || muted) return;
      frameAcc += dt;
      if (frameAcc < 0.1) return;
      frameAcc = 0;
      var want = Math.min(0.055, speed * 0.00006 + waveHot * 0.012);
      setParam('sweep', sweep.gain, want * roomMul, 0.08);
      setParam('room', room.frequency, 1800 - freeze * 1150, 0.25);
      setParam('bed', bed.gain, (0.16 - freeze * 0.055) * roomMul, 0.4);
    },

    /* Якорь под курсором: свой тон на каждую повадку. Второй канал подсказки. */
    anchor: function (kind, closeness) {
      if (!ready || muted) return;
      ping(BASE * RATIO[kind] * 0.5, 0.16, 0.02 + closeness * 0.05, 'sine');
    },

    /* Выдержка проверки: тон ползёт вверх, пока держишь. */
    dwell: function (p) {
      if (!ready || muted) return;
      ping(BASE * (0.62 + p * 0.5), 0.1, 0.012 + p * 0.02, 'triangle');
    },

    bloom: function () {
      ping(BASE * 1.37, 0.5, 0.10, 'sine');
      ping(BASE * 1.37 * 1.78, 0.42, 0.05, 'sine', 6);
      hit(0.3, 0.05, 900, 3200, 1400);
    },

    flinch: function () {
      hit(0.18, 0.11, 200, 1400, 260);
      ping(BASE * 0.53, 0.16, 0.05, 'square');
    },

    grip: function (strong) {
      hit(0.13, strong ? 0.16 : 0.07, 90, strong ? 1800 : 900, 220);
      if (strong) ping(BASE * 0.5, 0.24, 0.06, 'triangle');
    },

    /* Знак улетел в сосуд. Тон падает по ходу пачки: слышно, что она кончается. */
    tick: function (i, n) {
      ping(BASE * (2.41 - 1.2 * (i / Math.max(1, n))), 0.075, 0.035, 'sine');
    },

    knock: function () {
      ping(BASE * 0.37, 0.55, 0.16, 'triangle');
      hit(0.22, 0.10, 60, 500, 90);
    },

    reject: function () {
      hit(0.32, 0.12, 120, 700, 170);
      ping(BASE * 0.51, 0.3, 0.05, 'sawtooth');
      ping(BASE * 0.51 * 1.06, 0.3, 0.05, 'sawtooth');
    },

    /* Полосы помех слышны тем же, чем видны. */
    crackle: function (v) {
      if (v < 0.35) return;
      hit(0.1 + v * 0.16, 0.02 + v * 0.05, 700, 5200, 2000);
    },

    /* Пустота проступила на месте собранного знака. */
    hollow: function () {
      ping(BASE * 0.74, 0.7, 0.018, 'sine');
    },

    /* Ничего не нашлось: выдержка кончилась впустую. Очень тихо, чтобы этот
       звук не превратился в детектор «здесь пусто». */
    nothing: function () {
      hit(0.12, 0.018, 300, 900, 400);
    },

    /* Узел цепочки взят. Тон поднимается по ходу цепочки. */
    chain: function (i, n) {
      ping(BASE * (1 + 1.41 * (i / Math.max(1, n))), 0.16, 0.07, 'sine');
      hit(0.09, 0.03, 600, 2600, 1200);
    },

    /* Ошибка анализа. Не провал, а сбой: для корабля это порча, для игрока
       сырьё для расшифровки, поэтому звук двойственный, а не штрафной. */
    error: function () {
      ping(BASE * 1.78, 0.26, 0.06, 'triangle');
      ping(BASE * 1.78 * 1.03, 0.26, 0.06, 'triangle');
      hit(0.2, 0.05, 400, 2200, 700);
    },

    phase: function (p) {
      ping(BASE * RATIO[p % 4] * 0.75, 0.2, 0.05, 'triangle');
      hit(0.14, 0.04, 150, 1200, 300);
    },

    /* Цепочка сбилась: слишком много промахов подряд, всё сначала. */
    unravel: function () {
      ping(BASE * 1.41, 0.45, 0.09, 'triangle');
      ping(BASE * 1.41 * 0.67, 0.5, 0.07, 'triangle');
      hit(0.45, 0.09, 150, 1800, 200);
    },

    /* Группа разложена по классу. */
    sorted: function (i, n) {
      ping(BASE * (1.37 + 0.7 * (i / Math.max(1, n))), 0.32, 0.09, 'sine');
      ping(BASE * 2.41, 0.2, 0.04, 'sine', 9);
    },

    /* Пульс класса при сортировке: у каждого класса свой период. */
    beat: function (cls) {
      ping(BASE * [0.83, 1.19, 1.61][cls % 3], 0.11, 0.022, 'sine');
    },

    /* Знак лёг на место при финальной подсветке сортировки. */
    settle: function (i, n) {
      ping(BASE * (0.9 + 0.9 * (i / Math.max(1, n))), 0.24, 0.06, 'sine');
      hit(0.07, 0.022, 700, 2400, 1100);
    },

    /* Забытые знаки дрожат: короткий неуютный отклик. */
    forgot: function () {
      ping(BASE * 0.61, 0.5, 0.06, 'triangle');
      ping(BASE * 0.61 * 1.04, 0.5, 0.06, 'triangle');
      hit(0.4, 0.05, 200, 1100, 300);
    },

    /* Якорь-глюк: сорванный, ни на что не похожий звук. */
    glitch: function () {
      ping(BASE * 3.11, 0.1, 0.08, 'square');
      ping(BASE * 3.11 * 0.503, 0.16, 0.06, 'sawtooth');
      hit(0.18, 0.09, 900, 6000, 5200);
    },

    /* Утилизация: распад, восстановление, расщепление. */
    dissolve: function () {
      hit(0.42, 0.07, 90, 1800, 110);
      ping(BASE * 0.5, 0.5, 0.05, 'sine');
    },

    restore: function () {
      ping(BASE * 0.83, 0.2, 0.04, 'triangle');
    },

    /* Знак разломился. Сухой треск и расходящаяся вниз пара тонов: не похоже
       ни на глюк сортировки, ни на отказ. */
    shatter: function () {
      hit(0.09, 0.16, 1200, 7000, 3000);
      hit(0.5, 0.07, 200, 2600, 260);
      ping(BASE * 2.41, 0.09, 0.07, 'square');
      ping(BASE * 0.71, 0.6, 0.05, 'triangle');
      ping(BASE * 0.71 * 0.94, 0.6, 0.04, 'triangle');
    },

    splitOff: function () {
      ping(BASE * 1.03, 0.3, 0.07, 'sawtooth');
      ping(BASE * 1.49, 0.3, 0.07, 'sawtooth');
      hit(0.3, 0.08, 300, 3000, 600);
    },

    zoom: function (dir) {
      ping(BASE * (dir > 0 ? 1.78 : 1.37), 0.09, 0.022, 'triangle');
    },

    /* Пульт переходит к игроку. Громко и грязно: связь рвётся и
       пересобирается на другом конце. */
    handover: function () {
      wash(2.4, 0.5, 5200, 180, 0.6);
      hit(0.5, 0.3, 60, 900, 70);
      bend(BASE * 2.41, BASE * 0.37, 1.8, 0.09, 'sawtooth');
      bend(BASE * 2.48, BASE * 0.35, 1.9, 0.08, 'sawtooth');
      for (var i = 0; i < 7; i++) {
        (function (k) { setTimeout(function () { hit(0.06 + Math.random() * 0.1, 0.14, 900, 7000, 2400); }, k * 170 + Math.random() * 90); })(i);
      }
    },

    /* Существо само забирает пульт: коротко, но с тем же срывом. */
    takeover: function () {
      wash(0.7, 0.22, 3600, 300, 0.7);
      bend(BASE * 1.78, BASE * 0.74, 0.5, 0.05, 'sawtooth');
    },

    /* Режим ввода команды: пустота нажата. */
    consoleOn: function () {
      ping(BASE * 0.5, 1.1, 0.10, 'sine');
      ping(BASE * 0.5 * 1.37, 0.9, 0.05, 'sine', 5);
      hit(0.3, 0.05, 80, 700, 120);
    },
    consoleOff: function () {
      ping(BASE * 0.5 * 1.37, 0.4, 0.06, 'sine');
      ping(BASE * 0.5, 0.7, 0.06, 'sine');
    },
    key: function (i) {
      ping(BASE * (1.37 + i * 0.41), 0.14, 0.07, 'triangle');
      hit(0.05, 0.05, 1200, 4200, 2000);
    },
    /* Команда принята: три нисходящих тона. */
    command: function (kind) {
      var r = kind === 'sleep' ? [2.41, 1.37, 0.74, 0.5] : [2.41, 1.78, 1.0];
      r.forEach(function (m, i) { setTimeout(function () { ping(BASE * m, 0.5, 0.08, 'sine'); }, i * 140); });
    },
    /* Нажатие знака в пульте: сухой щелчок вниз, короткий тон. Отжатие —
       щелчок вверх и тот же тон ниже. */
    keyPress: function (i) {
      hit(0.03, 0.26, 1800, 6500, 3200);
      ping(BASE * 0.62, 0.07, 0.10, 'square');
      setTimeout(function () {
        hit(0.025, 0.10, 900, 4200, 2200);
        ping(BASE * (1.37 + i * 0.41), 0.26, 0.08, 'triangle');
      }, 40);
    },
    keyRelease: function (i) {
      hit(0.025, 0.16, 1500, 5200, 2600);
      ping(BASE * (1.37 + i * 0.41) * 0.74, 0.2, 0.07, 'triangle');
      setTimeout(function () { ping(BASE * 0.5, 0.06, 0.06, 'square'); }, 35);
    },
    keyDone: function () {
      ping(BASE * 1.0, 0.3, 0.06, 'sine');
      ping(BASE * 1.78, 0.3, 0.05, 'sine');
    },

    /* Возмущение: существо выдернули с обеда или со сна. Короткий носовой
       всхлип вверх и обиженный спад. */
    indignant: function () {
      bend(BASE * 1.2, BASE * 2.1, 0.12, 0.11, 'sawtooth');
      setTimeout(function () { bend(BASE * 2.0, BASE * 0.9, 0.34, 0.10, 'sawtooth'); }, 130);
      setTimeout(function () { bend(BASE * 1.9, BASE * 1.1, 0.22, 0.07, 'square'); }, 330);
    },

    /* Существо умерло. Долгий провал вниз. */
    death: function () {
      bend(BASE * 1.37, BASE * 0.12, 3.2, 0.14, 'triangle');
      bend(BASE * 1.41, BASE * 0.11, 3.4, 0.10, 'sawtooth');
      wash(3.0, 0.16, 900, 60, 0.5);
    },

    /* Выброс: корабль отстреливает кресло. */
    eject: function () {
      hit(0.8, 0.4, 40, 500, 50);
      wash(3.2, 0.45, 300, 6000, 0.5);
      bend(BASE * 0.25, BASE * 3.1, 2.6, 0.08, 'sawtooth');
    },

    /* Маяк переезда: низкий колокол, повторяется, пока корабль ждёт. */
    beacon: function () {
      ping(BASE * 0.37, 2.2, 0.12, 'sine');
      ping(BASE * 0.37 * 2.41, 1.6, 0.04, 'sine', 4);
      ping(BASE * 0.37 * 3.11, 1.1, 0.02, 'sine', -6);
    },

    /* Переезд: разгон шума вверх, удар, торможение вниз. */
    transit: function () {
      wash(1.2, 0.5, 120, 7000, 1.2);
      bend(BASE * 0.3, BASE * 4, 1.1, 0.07, 'sawtooth');
      setTimeout(function () {
        hit(0.5, 0.35, 40, 400, 45);
        wash(1.3, 0.4, 6000, 90, 1.0);
      }, 1100);
    },

    /* Сброс папки утилизации: глухой выдох вниз. */
    flush: function () {
      wash(0.9, 0.18, 1600, 120, 0.9);
      ping(BASE * 0.74, 0.6, 0.08, 'sine');
      ping(BASE * 0.5, 0.9, 0.07, 'triangle');
    },
    /* для проверок */
    _radio: function () { var was = farOn; farOn = true; radio(); farOn = was; },
    _drift: function () { var was = farOn; farOn = true; farDrift(); farOn = was; },

    /* Смена комнаты: навигация звучит космосом, лорная вкладка — машиной. */
    room: function (kind) {
      if (!ready) { pendingRoom = kind; return; }
      if (!lab) labInit();
      var t = now(), lore = kind === 'lore';
      if (lore && !labOn) { labOn = true; var id = ++labChain; setTimeout(function () { labChirps(id); }, 500); }
      if (!lore) labOn = false;
      roomMul = lore ? 0.18 : 1;
      lastParam = {};
      lab.gain.setTargetAtTime(lore ? 0.4 : 0.0001, t, lore ? 1.4 : 0.5);
      far.gain.setTargetAtTime(lore ? 0.0001 : (farOn ? 0.3 : 0.0001), t, lore ? 0.6 : 3);
    },

    /* Рамка записи проступает. */
    frameOn: function () {
      bend(BASE * 0.5, BASE * 2.41, 1.4, 0.07, 'triangle');
      wash(1.5, 0.14, 250, 3200, 0.8);
      ping(BASE * 3.11, 1.2, 0.04, 'sine');
    },

    /* Линия между знаками. */
    lineZap: function () {
      bend(BASE * 3.11, BASE * 1.37, 0.16, 0.07, 'sawtooth');
      hit(0.06, 0.08, 1500, 6000, 3000);
      ping(BASE * 1.78, 0.3, 0.05, 'sine');
    },

    /* --- выброс существа ------------------------------------------------- */

    /* Гул нарастает всё время тревоги. */
    ejectBegin: function (dur) {
      if (!ready || muted) return;
      var t = now();
      var g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(0.5, t + dur);
      var lp = ctx.createBiquadFilter(); lp.type = 'lowpass';
      lp.frequency.setValueAtTime(110, t);
      lp.frequency.exponentialRampToValueAtTime(1100, t + dur);
      lp.connect(g); g.connect(master);
      var nodes = [];
      [38, 38.7, 57.2, 76.1].forEach(function (f, i) {
        var o = ctx.createOscillator();
        o.type = i < 2 ? 'sawtooth' : 'triangle';
        o.frequency.setValueAtTime(f, t);
        o.frequency.exponentialRampToValueAtTime(f * 1.4, t + dur);
        o.connect(lp); o.start(t); nodes.push(o);
      });
      var n = noiseSource(true), nf = ctx.createBiquadFilter();
      nf.type = 'bandpass'; nf.frequency.value = 190; nf.Q.value = 0.7;
      n.connect(nf); nf.connect(lp); n.start(t); nodes.push(n);
      humNodes = { g: g, nodes: nodes };
    },

    /* Гул обрывается резким ударом металлических дверей, и следом — вакуум. */
    ejectDoor: function () {
      if (!ready) return;
      var t = now();
      if (humNodes) {
        humNodes.g.gain.cancelScheduledValues(t);
        humNodes.g.gain.setValueAtTime(0.4, t);
        humNodes.g.gain.linearRampToValueAtTime(0.0001, t + 0.04);
        humNodes.nodes.forEach(function (o) { o.stop(t + 0.1); });
        humNodes = null;
      }
      if (!muted) {
        [131, 187.3, 262.9, 349.6, 511.8, 733.4].forEach(function (f, i) { metal(f, 0.6 + Math.random() * 1.0, 0.11 - i * 0.012); });
        hit(0.4, 0.5, 40, 900, 55);
        hit(0.14, 0.3, 1500, 6500, 2600);
        setTimeout(function () { if (ready) { hit(0.25, 0.25, 50, 700, 60); metal(97, 1.2, 0.06); } }, 140);
      }
      API.vacuum(true);
    },

    /* Вакуум: все звуки уходят, остаётся только далёкий шум сбрасываемого
       воздуха, и тот медленно слабеет. */
    vacuum: function (on) {
      if (!ready) return;
      var t = now();
      vacuumOn = on;
      if (on) {
        master.gain.cancelScheduledValues(t);
        master.gain.setTargetAtTime(0.0001, t + 0.35, 0.12);
        if (!airBus) { airBus = ctx.createGain(); airBus.gain.value = 0.0001; airBus.connect(compNode); }
        if (airSrc) { airSrc.stop(t); airSrc = null; }
        var s = noiseSource(true);
        var hp = ctx.createBiquadFilter(); hp.type = 'highpass'; hp.frequency.value = 650;
        var lp = ctx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 2400;
        var fl = ctx.createGain(); fl.gain.value = 0.7;
        var lfo = ctx.createOscillator(); lfo.frequency.value = 0.27;
        var lg = ctx.createGain(); lg.gain.value = 0.3;
        lfo.connect(lg); lg.connect(fl.gain); lfo.start(t);
        s.connect(hp); hp.connect(lp); lp.connect(fl); fl.connect(airBus);
        s.start(t);
        airSrc = { stop: function (at) { s.stop(at); lfo.stop(at); } };
        airBus.gain.cancelScheduledValues(t);
        airBus.gain.setValueAtTime(0.0001, t);
        airBus.gain.exponentialRampToValueAtTime(muted ? 0.0001 : 0.13, t + 0.7);
        airBus.gain.setTargetAtTime(muted ? 0.0001 : 0.02, t + 1.5, 9);
      } else {
        master.gain.cancelScheduledValues(t);
        master.gain.setTargetAtTime(muted ? 0.0001 : 0.5, t, 0.9);
        if (airBus) { airBus.gain.cancelScheduledValues(t); airBus.gain.setTargetAtTime(0.0001, t, 0.6); }
        if (airSrc) { airSrc.stop(t + 3); airSrc = null; }
      }
    },

    /* Корабль нервничает: стон металла и глухой удар. Чем выше шкала, тем громче. */
    defectWarn: function (f) {
      if (!ready || muted) return;
      var k = Math.max(0, Math.min(1, (f - 0.5) * 2));
      bend(BASE * 0.26, BASE * 0.19, 1.4, 0.04 + 0.08 * k, 'sawtooth');
      hit(0.7, 0.03 + 0.07 * k, 50, 500, 70);
      ping(BASE * (1.07 + Math.random() * 0.2), 0.4, 0.015 + 0.03 * k, 'triangle', 23);
    },

    /* Слог встал в предложение: тихий щипок струны. */
    pluck: function (i) {
      var f = BASE * [1.37, 1.78, 2.41][(i || 0) % 3] * 1.5;
      bend(f * 1.012, f, 0.7, 0.04, 'triangle');
      ping(f * 2.01, 0.25, 0.012, 'sine');
    },

    /* Сортировка: курсор над доской, взятие, шаг груза, отпускание. */
    hover: function () {
      ping(BASE * 3.11 * (0.92 + Math.random() * 0.16), 0.04, 0.02, 'sine');
    },
    pickUp: function () {
      hit(0.08, 0.07, 300, 2000, 600);
      ping(BASE * 1.19, 0.14, 0.035, 'triangle');
    },
    slide: function (n) {
      hit(0.05 + 0.02 * (n || 1), 0.03 + 0.012 * (n || 1), 700, 2600, 1200);
      ping(BASE * (0.8 + Math.random() * 0.1), 0.06, 0.03, 'triangle');
    },
    putDown: function () {
      ping(BASE * 0.74, 0.22, 0.05, 'sine');
      hit(0.05, 0.05, 200, 1200, 300);
    },

    /* Команда переезда: двигатели раскручиваются, нарастает вой. */
    spool: function (dur) {
      if (!ready || muted) return;
      var t = now(), g = ctx.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(0.35, t + dur);
      g.gain.linearRampToValueAtTime(0.0001, t + dur + 0.15);
      var lp = ctx.createBiquadFilter(); lp.type = 'lowpass';
      lp.frequency.setValueAtTime(200, t); lp.frequency.exponentialRampToValueAtTime(4000, t + dur);
      lp.connect(g); g.connect(master);
      [55, 82.5, 110.7].forEach(function (f, i) {
        var o = ctx.createOscillator(); o.type = i ? 'sawtooth' : 'triangle';
        o.frequency.setValueAtTime(f, t); o.frequency.exponentialRampToValueAtTime(f * 7, t + dur);
        o.connect(lp); o.start(t); o.stop(t + dur + 0.2);
      });
      var n = noiseSource(false), nf = ctx.createBiquadFilter();
      nf.type = 'bandpass'; nf.frequency.setValueAtTime(300, t); nf.frequency.exponentialRampToValueAtTime(3000, t + dur); nf.Q.value = 0.8;
      n.connect(nf); nf.connect(lp); n.start(t); n.stop(t + dur + 0.2);
      metal(98, 0.9, 0.05);
    },

    tab: function (p) {
      ping(BASE * (p ? 1.19 : 0.83), 0.3, 0.06, 'sine');
      hit(0.12, 0.04, 400, 2200, 800);
    },

    /* Слово прочитано: стеклянный звон. */
    decode: function () {
      ping(BASE * 3.11, 0.9, 0.06, 'sine');
      ping(BASE * 2.41, 1.1, 0.05, 'sine', 7);
      ping(BASE * 1.37, 1.3, 0.05, 'sine', -5);
    }
  };

  root.Sound = API;
})(window);
