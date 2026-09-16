/* ORT — постобработка.
 *
 * Сцена рисуется в canvas 2D, а на экран попадает через один проход WebGL:
 * лёгкая бочка, хроматическая аберрация к краям, зерно, редкие полосы помех,
 * развёртка и виньетка.
 *
 * Всё это должно быть НА ГРАНИ ЗАМЕТНОСТИ. Задача не в эффекте, а в том,
 * чтобы стекло читалось стеклом, а картинка имела толщину. Если постобработку
 * видно как постобработку, значения задраны.
 *
 * Если WebGL недоступен, модуль честно отключается и сцена выводится как есть.
 */
(function (root) {
  'use strict';

  var VERT = [
    'attribute vec2 p;',
    'varying vec2 uv;',
    'void main(){ uv = p * 0.5 + 0.5; gl_Position = vec4(p, 0.0, 1.0); }'
  ].join('\n');

  var FRAG = [
    'precision mediump float;',
    'varying vec2 uv;',
    'uniform sampler2D tex;',
    'uniform vec2 res;',
    'uniform float time;',
    'uniform float burst;',      // сила помех прямо сейчас
    'uniform float bulge;',
    'uniform float chroma;',
    'uniform float tear;',
    'uniform float scaleOut;',   // картинка уходит вдаль: 1 — как есть, меньше — поле отдаляется
    'uniform float blurAmt;',    // размытие: существо видит всё хуже
    'uniform float lids;',       // веки: 0 — глаза открыты, 1 — закрыты
    'uniform float edge;',       // помехи по краю экрана
    'uniform float dark;', 'vec2 mirror(vec2 u) { return 1.0 - abs(mod(u, 2.0) - 1.0); }',       // сильный срыв картинки: передача управления, переезд, выброс

    'float hash(vec2 v){ return fract(sin(dot(v, vec2(12.9898, 78.233))) * 43758.5453); }',

    'void main(){',
    '  vec2 p = uv * 2.0 - 1.0;',
    '  float r2 = dot(p, p);',

    // бочка: середина чуть ближе к глазу, края уходят назад
    '  vec2 q = p * (1.0 - bulge * r2);',

    /* Срыв. Картинку рвёт на горизонтальные ленты, каждая уезжает вбок
       целиком; вся развёртка подпрыгивает. В покое tear равен нулю, и этот
       кусок не делает ничего. */
    '  if (tear > 0.001) {',
    '    float tb = floor(uv.y * 34.0 + floor(time * 13.0) * 3.7);',
    '    float tn = hash(vec2(tb, floor(time * 21.0)));',
    '    q.x += (tn - 0.5) * tear * 0.34 * step(0.62 - tear * 0.3, tn);',
    '    q.y += (hash(vec2(floor(time * 9.0), 5.0)) - 0.5) * tear * 0.05;',
    '  }',

    /* Полосы помех. Сдвиг внутри ленты СВЯЗНЫЙ: вся лента едет вбок целиком,
       а не каждая строка сама по себе. Построчная дрожь читалась как повадка
       знака и давала ложные срабатывания: игрок видел дёргающийся символ и
       шёл его проверять, хотя якорем тот не был. */
    '  float bandY = fract(time * 0.083 + hash(vec2(floor(time * 0.7), 3.0)));',
    '  float band = exp(-pow((uv.y - bandY) * 62.0, 2.0));',
    '  float slide = (hash(vec2(floor(time * 9.0), 7.0)) - 0.5);',
    '  q.x += slide * band * (0.0022 + burst * 0.006);',

    // хроматическая аберрация: в центре нулевая, к краям расходится
    '  q = q / max(0.05, scaleOut);',
    '  vec2 ca = q * (chroma + tear * 0.045) * (r2 + tear * 0.7);',
    '  vec2 uR = (q + ca) * 0.5 + 0.5;',
    '  vec2 uG = q * 0.5 + 0.5;',
    '  vec2 uB = (q - ca) * 0.5 + 0.5;',
    // картинка уходит вдаль, но не кончается: вокруг неё зеркальные копии поля
    '  if (scaleOut < 0.999) { uR = mirror(uR); uG = mirror(uG); uB = mirror(uB); }',

    '  vec3 c = vec3(0.0);',
    '  if (uG.x > 0.0 && uG.x < 1.0 && uG.y > 0.0 && uG.y < 1.0) {',
    '    if (blurAmt < 0.001) {',
    '      c.r = texture2D(tex, clamp(uR, 0.0, 1.0)).r;',
    '      c.g = texture2D(tex, uG).g;',
    '      c.b = texture2D(tex, clamp(uB, 0.0, 1.0)).b;',
    '    } else {',
    '      for (int i = 0; i < 16; i++) {',
    '        float fi = float(i);',
    '        float ang = fi * 2.39996;',
    '        vec2 o = vec2(cos(ang), sin(ang)) * sqrt(fi + 0.5) * 0.25 * blurAmt * 0.04;',
    '        c.r += texture2D(tex, clamp(uR + o, 0.0, 1.0)).r;',
    '        c.g += texture2D(tex, clamp(uG + o, 0.0, 1.0)).g;',
    '        c.b += texture2D(tex, clamp(uB + o, 0.0, 1.0)).b;',
    '      }',
    '      c /= 16.0;',
    '    }',
    '  }',

    // зерно: слабое, но живое, иначе чёрный фон выглядит мёртвой заливкой
    '  float g = hash(uv * res + vec2(time * 61.0, time * 37.0)) - 0.5;',
    '  c += g * (0.022 + burst * 0.05 + tear * 0.42);',
    '  c *= 1.0 - tear * 0.75 * step(0.78, hash(vec2(floor(time * 17.0), 11.0)));',
    // помехи по краю экрана
    '  float edgeMask = smoothstep(0.5, 1.0, max(abs(p.x), abs(p.y)));',
    '  c += (hash(uv * res * 0.5 + vec2(time * 97.0, time * 53.0)) - 0.5) * edge * edgeMask * 0.9;',
    '  c *= 1.0 - edge * edgeMask * 0.45 * step(0.72, hash(vec2(floor(uv.y * 60.0), floor(time * 18.0))));',
    // веки смыкаются сверху и снизу, края чуть скруглены
    '  float lidEdge = 1.0 - lids * 1.2;',
    '  float lid = smoothstep(lidEdge, lidEdge - 0.2, abs(p.y) + 0.25 * p.x * p.x * lids);',
    '  c *= mix(1.0, lid, step(0.001, lids));',
    '  c *= 1.0 - dark;',
    '  c += tear * 0.30 * exp(-pow((uv.y - fract(time * 1.9)) * 24.0, 2.0)) * vec3(1.0, 0.8, 0.55);',

    // развёртка и виньетка уже после бочки, поэтому они гнутся вместе с полем
    '  c *= 0.90 + 0.10 * sin(uv.y * res.y * 1.05);',
    '  c *= 1.0 - 0.52 * pow(max(0.0, r2 - 0.30), 1.35);',

    '  gl_FragColor = vec4(max(c, vec3(0.0)), 1.0);',
    '}'
  ].join('\n');

  function compile(gl, type, src) {
    var s = gl.createShader(type);
    gl.shaderSource(s, src);
    gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
      console.warn('ORT post:', gl.getShaderInfoLog(s));
      return null;
    }
    return s;
  }

  function Post(canvas) {
    var gl = null;
    try {
      gl = canvas.getContext('webgl', { alpha: false, antialias: false, depth: false })
        || canvas.getContext('experimental-webgl', { alpha: false, depth: false });
    } catch (e) { gl = null; }
    if (!gl) { this.ok = false; return; }

    var vs = compile(gl, gl.VERTEX_SHADER, VERT);
    var fs = compile(gl, gl.FRAGMENT_SHADER, FRAG);
    if (!vs || !fs) { this.ok = false; return; }

    var prog = gl.createProgram();
    gl.attachShader(prog, vs); gl.attachShader(prog, fs);
    gl.bindAttribLocation(prog, 0, 'p');
    gl.linkProgram(prog);
    if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) { this.ok = false; return; }

    var buf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, buf);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 3, -1, -1, 3]), gl.STATIC_DRAW);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);

    var texture = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, texture);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);

    this.ok = true;
    this.gl = gl;
    this.prog = prog;
    this.tex = texture;
    this.u = {
      tex: gl.getUniformLocation(prog, 'tex'),
      res: gl.getUniformLocation(prog, 'res'),
      time: gl.getUniformLocation(prog, 'time'),
      burst: gl.getUniformLocation(prog, 'burst'),
      bulge: gl.getUniformLocation(prog, 'bulge'),
      chroma: gl.getUniformLocation(prog, 'chroma'),
      tear: gl.getUniformLocation(prog, 'tear'),
      scaleOut: gl.getUniformLocation(prog, 'scaleOut'),
      blurAmt: gl.getUniformLocation(prog, 'blurAmt'),
      lids: gl.getUniformLocation(prog, 'lids'),
      edge: gl.getUniformLocation(prog, 'edge'),
      dark: gl.getUniformLocation(prog, 'dark')
    };
    // помехи приходят редкими короткими вспышками, а не ровным шумом
    this.burst = 0;
    this.nextBurst = 3 + Math.random() * 9;
  }

  /* Возвращает силу вспышки помех: её же слышно в звуке. */
  Post.prototype.step = function (dt) {
    if (!this.ok) return 0;
    this.nextBurst -= dt;
    if (this.nextBurst <= 0) {
      this.burst = 0.5 + Math.random() * 0.5;
      this.nextBurst = 4 + Math.random() * 14;
    }
    this.burst = Math.max(0, this.burst - dt * 2.6);
    return this.burst;
  };

  Post.prototype.render = function (scene, time, tear, fx) {
    fx = fx || {};
    if (!this.ok) return;
    var gl = this.gl;
    gl.viewport(0, 0, gl.drawingBufferWidth, gl.drawingBufferHeight);
    gl.useProgram(this.prog);
    gl.bindTexture(gl.TEXTURE_2D, this.tex);
    /* Память под текстуру выделяется только при смене размера. Раньше она
       заново выделялась каждый кадр, и за долгую игру видеопамять и память
       браузера разбухали. */
    if (this.tw !== scene.width || this.th !== scene.height) {
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, scene);
      this.tw = scene.width; this.th = scene.height;
    } else {
      gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, gl.RGBA, gl.UNSIGNED_BYTE, scene);
    }
    gl.uniform1i(this.u.tex, 0);
    gl.uniform2f(this.u.res, gl.drawingBufferWidth, gl.drawingBufferHeight);
    gl.uniform1f(this.u.time, time);
    gl.uniform1f(this.u.burst, this.burst);
    gl.uniform1f(this.u.bulge, 0.034);
    gl.uniform1f(this.u.chroma, 0.0058);
    gl.uniform1f(this.u.tear, Math.max(0, Math.min(1, tear || 0)));
    gl.uniform1f(this.u.scaleOut, fx.scale === undefined ? 1 : fx.scale);
    gl.uniform1f(this.u.blurAmt, fx.blur || 0);
    gl.uniform1f(this.u.lids, fx.lids || 0);
    gl.uniform1f(this.u.edge, fx.edge || 0);
    gl.uniform1f(this.u.dark, fx.dark || 0);
    gl.drawArrays(gl.TRIANGLES, 0, 3);
  };

  root.Post = Post;
})(window);
