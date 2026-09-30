"""Снимок как сигнал с датчика корабля, а не как картинка.

Генератор всегда тянет к красивому кадру: объект по центру, свет как в кино,
чистое изображение. Датчику всё это не нужно. Здесь снимок проходит путь,
который прошёл бы на борту: кадр обрезан как попало (камера наведена по
расчёту, а не по вкусу), разрешение датчика низкое, экспозиция выставлена
автоматически и мимо, уровней яркости мало, шум, сдвинутые строки развёртки.
Результат — только чёрный и оттенки оранжевого.
"""
import random, sys
import numpy as np
from PIL import Image, ImageFilter

RAMP = np.array([
    [0, 0, 0], [26, 6, 0], [70, 22, 2], [130, 48, 6], [190, 88, 16], [236, 138, 48], [255, 196, 120]
], dtype=np.float32)

def ramp(v):
    # v 0..1 -> цвет по оранжевой шкале
    x = np.clip(v, 0, 1) * (len(RAMP) - 1)
    i = np.floor(x).astype(int); f = (x - i)[..., None]
    j = np.clip(i + 1, 0, len(RAMP) - 1)
    return RAMP[i] * (1 - f) + RAMP[j] * f

def sensor(src, dst, seed, far=False):
    rnd = random.Random(seed); nr = np.random.default_rng(seed)
    im = Image.open(src).convert('L')
    W = im.width
    # 1. кадр наведён по расчёту: обрезка 62–85% в случайном месте
    if not far:
        c = rnd.uniform(0.62, 0.85)
        cw = int(W * c)
        x0 = rnd.randint(0, W - cw); y0 = rnd.randint(0, W - cw)
        im = im.crop((x0, y0, x0 + cw, y0 + cw))
    # 2. низкое разрешение датчика. У дальнего снимка объект — несколько
    #    светлых точек, и простое уменьшение их стирает: сначала точки
    #    раздуваются, чтобы пережить уменьшение
    res = rnd.choice([96, 112, 128, 144])
    if far:
        k = max(3, (im.width // res) | 1)
        im = im.filter(ImageFilter.MaxFilter(min(k, 9)))
    im = im.resize((res, res), Image.BILINEAR)
    a = np.asarray(im, dtype=np.float32) / 255.0
    # 3. автоэкспозиция: сперва по самому светлому участку, потом мимо —
    #    иногда пересвет, иногда недосвет, но не до пустого кадра
    # усиление не больше чем втрое: почти пустой кадр должен остаться тёмным
    a = a / max(0.33, float(np.percentile(a, 99.7)))
    gain = rnd.choice([rnd.uniform(1.3, 1.9), rnd.uniform(0.7, 0.88), rnd.uniform(0.9, 1.15)])
    a = np.clip((a - rnd.uniform(0.02, 0.1)) * gain, 0, 1) ** rnd.uniform(0.9, 1.4)
    # 4. мало уровней яркости
    lv = rnd.choice([5, 6, 7, 8])
    a = np.round(a * lv) / lv
    # 5. шум: сильнее в тенях, плюс неравномерность столбцов
    a = a + nr.normal(0, 0.06, a.shape) * (1.2 - a)
    a = a + nr.normal(0, 0.025, (1, res))
    # 6. развёртка: несколько строк сдвинуты, пара битых
    for _ in range(rnd.randint(2, 6)):
        y = rnd.randrange(res); h = rnd.randint(1, 4); s = rnd.randint(-12, 12)
        a[y:y + h] = np.roll(a[y:y + h], s, axis=1)
    for _ in range(rnd.randint(0, 2)):
        y = rnd.randrange(res); a[y] = rnd.choice([0.0, 0.85])
    # горячие пиксели
    for _ in range(rnd.randint(3, 10)):
        a[rnd.randrange(res), rnd.randrange(res)] = 1.0
    a = np.clip(a, 0, 1)
    # 7. обратно в 640 без сглаживания лишнего: видно, что датчик грубый
    rgb = ramp(a).astype(np.uint8)
    out = Image.fromarray(rgb, 'RGB').resize((640, 640), Image.BILINEAR)
    out = out.filter(ImageFilter.GaussianBlur(0.6))
    out.save(dst, 'WEBP', quality=84)

if __name__ == '__main__':
    sensor(sys.argv[1], sys.argv[2], int(sys.argv[3]), len(sys.argv) > 4)
