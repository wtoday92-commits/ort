/* ORT — память между запусками.
 *
 * Карта при каждом запуске новая. Сохраняется только то, что принадлежит
 * игроку: прочитанный лор, записи журнала, лорные папки и хранилище данных.
 * Всё лежит в localStorage этого браузера.
 *
 * Для проверок: ?nosave — ничего не читать и не писать; ?savekey=имя —
 * отдельная ячейка сохранения.
 */
(function (root) {
  'use strict';

  var m = /[?&]savekey=([\w-]+)/.exec(location.search);
  /* Номер версии в ключе: при несовместимой переделке сохранения его
     поднимают, и игра начинается заново. v2 — полный сброс после новой
     лорной части. */
  var KEY = 'ort.save.v2' + (m ? '.' + m[1] : '');
  // ?reset — стереть сохранение и начать с нуля
  if (/[?&]reset/.test(location.search)) { try { root.localStorage.removeItem(KEY); } catch (e) {} }
  // старое сохранение прежней версии больше не читается и просто убирается
  try { root.localStorage.removeItem('ort.save.v1'); } catch (e) {}
  var off = /[?&]nosave/.test(location.search);

  root.Save = {
    key: KEY,
    load: function () {
      if (off) return null;
      try {
        var s = root.localStorage.getItem(KEY);
        return s ? JSON.parse(s) : null;
      } catch (e) { return null; }
    },
    write: function (data) {
      if (off) return false;
      try { root.localStorage.setItem(KEY, JSON.stringify(data)); return true; }
      catch (e) { return false; }
    },
    clear: function () {
      try { root.localStorage.removeItem(KEY); } catch (e) {}
    }
  };
})(window);
