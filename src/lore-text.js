/* ORT — тексты лора.
 *
 * Отдельный файл нарочно: тексты будут переписываться много раз, и лезть ради
 * этого в код не должно быть нужно.
 *
 * Слово — это знак. Каждому слову при запуске назначается собственное
 * начертание из письменности, одно и то же навсегда. Прочитав слово в лорном
 * блоке, игрок узнаёт его везде: и в других блоках, и в журнале корабля.
 * Непрочитанное слово в журнале так и остаётся знаком.
 *
 * Перевод — не проза, а подстрочник отношений: узел, связь, узел (см. раздел 8
 * проектного документа). Связи пишутся в угловых скобках, узлы — прописными.
 *
 * У каждого блока три прочтения. Какое получит игрок, решает ФОРМА, в которую
 * он разложил знаки на первой сортировке этого блока:
 *   dense — плотными пятнами, как хочет корабль;
 *   line  — линиями;
 *   chaos — россыпью.
 * Все три собраны из одних и тех же слов блока, но говорят разное.
 */
(function (root) {
  'use strict';

  var words = {
    // узлы
    ship: 'КОРАБЛЬ',
    vessel: 'СОСУД',
    creature: 'СУЩЕСТВО',
    remnant: 'ОСТАТОК',
    place: 'МЕСТО',
    hunger: 'ГОЛОД',
    sleep: 'СОН',
    capsule: 'КАПСУЛА',
    depth: 'НЕДРА',
    other: 'ДРУГОЙ',
    hand: 'РУКА',
    order: 'ПОРЯДОК',
    defect: 'ИЗЪЯН',
    void: 'ПУСТОТА',
    previous: 'ПРЕЖНИЙ',
    next: 'СЛЕДУЮЩИЙ',
    seat: 'ПУЛЬТ',
    outside: 'СНАРУЖИ',
    memory: 'ПАМЯТЬ',
    many: 'МНОЖЕСТВО',
    one: 'ОДИН',

    // связи
    holds: '⟨держит-как-назначение⟩',
    was_attention: '⟨то-что-было-вниманием⟩',
    therefore_not: '⟨и-поэтому-не⟩',
    sits_as_tool: '⟨сидит-как-инструмент⟩',
    until_unneeded: '⟨до-момента-когда-перестанет-быть-нужным⟩',
    moves_to: '⟨перемещается-в-сторону⟩',
    fills: '⟨заполняет-без-остатка⟩',
    replaces: '⟨заменяет-не-замечая⟩',
    eats: '⟨принимает-внутрь-чтобы-продолжать⟩',
    watches: '⟨смотрит-изнутри⟩',
    counts: '⟨ведёт-счёт-чтобы-не⟩',
    leaves: '⟨оставляет-позади⟩',
    same_as: '⟨то-же-что⟩',
    refuses: '⟨не-даёт⟩',
    ends: '⟨перестаёт-продолжаться⟩',
    because: '⟨по-причине⟩',
    inside: '⟨внутри⟩',
    belongs: '⟨принадлежит-не-себе⟩',
    becomes: '⟨становится-постепенно⟩',

    /* Корабль ничего не знает о том, кто ведёт руку существа, и никогда не
       узнает. Он видит только поведение существа, поэтому его записи — о ритме,
       пропусках и износе, а не о причинах. */
    strange: 'СТРАННОСТЬ',
    changes: '⟨меняет-ритм⟩',
    usual: '⟨как-бывает⟩',
    skips: '⟨пропускает⟩',
    slows: '⟨работает-медленнее⟩',
    prepares: '⟨готовит⟩',
    again: '⟨снова⟩'
  };

  /* Лорные блоки. at — смещение левого верхнего угла от середины лорного
     поля, в клетках. */
  var blocks = [
    {
      id: 'vessel', at: [-8, -5],
      text: {
        dense: ['vessel', 'holds', 'remnant', 'was_attention', 'therefore_not', 'creature', 'sits_as_tool', 'seat', 'until_unneeded'],
        line: ['creature', 'sits_as_tool', 'vessel', 'holds', 'remnant', 'until_unneeded', 'seat'],
        chaos: ['remnant', 'holds', 'creature', 'therefore_not', 'vessel', 'was_attention', 'seat']
      }
    },
    {
      id: 'seat', at: [12, -2],
      text: {
        dense: ['other', 'inside', 'hand', 'watches', 'order', 'becomes', 'defect'],
        line: ['hand', 'watches', 'other', 'therefore_not', 'order', 'same_as', 'defect'],
        chaos: ['defect', 'inside', 'other', 'becomes', 'hand', 'watches', 'order']
      }
    },
    {
      id: 'capsule', at: [-5, 10],
      text: {
        dense: ['depth', 'holds', 'capsule', 'next', 'creature', 'replaces', 'previous', 'creature'],
        line: ['previous', 'creature', 'ends', 'capsule', 'inside', 'depth', 'next'],
        chaos: ['capsule', 'replaces', 'depth', 'previous', 'same_as', 'next', 'creature']
      }
    },
    {
      id: 'hunger', at: [15, 12],
      text: {
        dense: ['creature', 'eats', 'remnant', 'because', 'hunger', 'therefore_not', 'ends'],
        line: ['hunger', 'inside', 'creature', 'counts', 'sleep', 'refuses', 'other'],
        chaos: ['other', 'eats', 'sleep', 'hunger', 'because', 'remnant', 'ends']
      }
    },
    {
      id: 'place', at: [-25, 2],
      text: {
        dense: ['ship', 'moves_to', 'next', 'place', 'leaves', 'previous', 'place', 'void', 'fills'],
        line: ['void', 'fills', 'place', 'therefore_not', 'ship', 'leaves'],
        chaos: ['place', 'moves_to', 'ship', 'void', 'same_as', 'previous']
      }
    },
    {
      id: 'memory', at: [28, -8],
      text: {
        dense: ['memory', 'belongs', 'ship', 'many', 'creature', 'same_as', 'one', 'creature'],
        line: ['one', 'creature', 'counts', 'many', 'therefore_not', 'memory'],
        chaos: ['ship', 'belongs', 'memory', 'creature', 'was_attention', 'outside']
      }
    }
  ];

  /* Записи корабля. Появляются в журнале по событиям и написаны теми же
     словами, поэтому читаются ровно настолько, насколько игрок уже прочёл лор. */
  var ship = {
    /* Все записи — только о том, что корабль видит в существе. Неэффективность
       для него штатна: тревоги нет, пока выброс не начинает повторяться с
       каждым следующим существом (eject_pattern, с пятого выброса). */
    handover: ['creature', 'changes', 'usual'],
    relocate_signal: ['void', 'fills', 'place'],
    relocate: ['ship', 'moves_to', 'next', 'place', 'leaves', 'previous', 'place'],
    lunch: ['creature', 'eats', 'remnant'],
    lunch_denied: ['creature', 'skips', 'hunger'],
    sleep: ['creature', 'sleep', 'inside', 'seat'],
    sleep_denied: ['creature', 'skips', 'sleep'],
    death_hunger: ['creature', 'ends', 'because', 'hunger', 'capsule', 'replaces', 'previous', 'creature'],
    death_sleep: ['creature', 'ends', 'because', 'sleep', 'capsule', 'replaces', 'previous', 'creature'],
    eject: ['creature', 'until_unneeded', 'ship', 'leaves', 'creature', 'outside', 'capsule', 'next'],
    eject_pattern: ['defect', 'fills', 'creature', 'again', 'same_as', 'previous', 'creature', 'strange'],
    defect_rising: ['creature', 'slows', 'usual'],
    defect_high: ['defect', 'inside', 'creature'],
    defect_critical: ['ship', 'prepares', 'capsule', 'next']
  };

  /* Записи журнала корабля — белые блоки на лорном поле.
     at — смещение левого верхнего угла от середины лорного поля, в клетках.
     sentences — предложения в порядке чтения. key — слово, которое игрок
     соберёт из слогов в этом предложении; ровно одно предложение без слова.
     extra — лишние слоги, которые окажутся не у дел.
     '#creature' — номер существа, пишется точками. */
  var logs = [
    {
      id: 'log1', color: 'white', at: [-4, -2], w: 8, h: 3,
      sentences: [
        { text: ['КОРАБЛЬ', '⟨продолжается-как-назначено⟩', 'ПОРЯДОК', '⟨без-отклонения⟩'], key: ['КО', 'РАБЛЬ'] },
        { text: ['СУЩЕСТВО', '⟨заступает-как-инструмент⟩', '⟨внутри⟩', 'ПУЛЬТ'], key: ['СУ', 'ЩЕС', 'ТВО'] },
        { text: ['НОМЕР', '#creature', '⟨то-что-отличает-от-прежних⟩'], key: ['НО', 'МЕР'] },
        { text: ['ИЗЪЯН', '⟨не-найден⟩', '⟨и-поэтому-не⟩', 'ТРЕВОГА'], key: null }
      ],
      extra: ['ТАН']
    },
    /* Запись об инциденте. Появляется только после первого выброса существа и
       открывается раньше всех прочих ещё не начатых записей. '#ejected' —
       номер выброшенного существа. */
    {
      id: 'log_eject', color: 'white', at: [-4, 3], w: 8, h: 3, requires: 'eject', priority: 1,
      sentences: [
        { text: ['ИЗЪЯН', '⟨заполняет-без-остатка⟩', 'СУЩЕСТВО', '#ejected'], key: ['ИЗЪ', 'ЯН'] },
        { text: ['ОТСЕК', '⟨открывается-наружу⟩', '⟨как-назначено⟩'], key: ['ОТ', 'СЕК'] },
        { text: ['ВОЗДУХ', '⟨уходит-вместе-с⟩', 'СУЩЕСТВО', '⟨и-поэтому-не⟩', 'ВОЗВРАТ'], key: ['ВОЗ', 'ДУХ'] },
        { text: ['КАПСУЛА', '⟨заменяет-не-замечая⟩', 'ПРЕЖНИЙ', '⟨на⟩', '#creature'], key: null }
      ],
      extra: ['ШЛЮ', 'ЗА']
    },
    {
      id: 'log3', color: 'white', at: [-4, 8], w: 8, h: 3,
      sentences: [
        { text: ['ПОЛЕ', '⟨отдаёт-как-назначено⟩', 'ОСТАТОК'], key: ['ПО', 'ЛЕ'] },
        { text: ['СОСУД', '⟨принимает-не-считая⟩', 'ОСТАТОК'], key: ['СО', 'СУД'] },
        { text: ['ПОРЯДОК', '⟨держится-пока⟩', 'СУЩЕСТВО', '⟨не-отклоняется⟩'], key: ['ПО', 'РЯ', 'ДОК'] },
        { text: ['ОТКЛОНЕНИЕ', '⟨бывает-у-любого⟩', 'СУЩЕСТВО', '⟨и-поэтому-не⟩', 'ТРЕВОГА'], key: null }
      ],
      extra: ['ЛОК']
    },
    {
      id: 'log4', color: 'white', at: [-4, 13], w: 8, h: 3,
      sentences: [
        { text: ['СУЩЕСТВО', '⟨изнашивается-как-любой⟩', 'ИНСТРУМЕНТ'], key: ['ИНС', 'ТРУ', 'МЕНТ'] },
        { text: ['КАПСУЛА', '⟨хранит-достаточно⟩', 'СЛЕДУЮЩИЙ'], key: ['КАП', 'СУ', 'ЛА'] },
        { text: ['ЗАМЕНА', '⟨происходит-как-назначено⟩'], key: ['ЗА', 'МЕ', 'НА'] },
        { text: ['НЕЭФФЕКТИВНОСТЬ', '⟨штатна⟩', '⟨и-поэтому-не⟩', 'ТРЕВОГА'], key: null }
      ],
      extra: ['ЛЕ']
    },
    {
      id: 'log5', color: 'white', at: [-4, 18], w: 8, h: 3,
      sentences: [
        { text: ['МЕСТО', '⟨заполняется-без-остатка⟩'], key: ['МЕС', 'ТО'] },
        { text: ['КОРАБЛЬ', '⟨уходит-по⟩', 'ЗНАКИ', '#cmd:relocate'], key: ['ЗНА', 'КИ'] },
        { text: ['ПУСТОТА', '⟨открывает⟩', 'ПУЛЬТ', '⟨для⟩', '⟨этих-знаков⟩'], key: ['ПУС', 'ТО', 'ТА'] },
        { text: ['ПРЕЖНИЙ', 'МЕСТО', '⟨остаётся-позади⟩', '⟨навсегда⟩'], key: null }
      ],
      extra: ['ЛЕТ']
    },
    /* Первая запись, где корабль замечает неладное. Он не знает причин и
       никогда не узнает: видит лишь, что КАЖДОЕ следующее существо перестаёт
       работать так же, как прежнее. Появляется только после пятого выброса. */
    {
      id: 'log_strange', color: 'white', at: [-4, 23], w: 8, h: 3, minEjects: 5, priority: 2,
      sentences: [
        { text: ['КАЖДЫЙ', 'СУЩЕСТВО', '⟨перестаёт-быть-нужным-раньше-срока⟩'], key: ['КАЖ', 'ДЫЙ'] },
        { text: ['СЛЕДУЮЩИЙ', '⟨отклоняется-так-же-как⟩', 'ПРЕЖНИЙ'], key: ['ПРЕЖ', 'НИЙ'] },
        { text: ['ИЗЪЯН', '⟨не-найден-ни-в⟩', 'КАПСУЛА', '⟨ни-в⟩', 'ПУЛЬТ'], key: ['КАП', 'СУ', 'ЛА'] },
        { text: ['РАБОТА', '⟨идёт-не-как-назначено⟩', '⟨и-поэтому⟩', 'СТРАННОСТЬ'], key: null }
      ],
      extra: ['ТОК']
    }
  ];

  /* Команды пульта: начертания в порядке ввода. Выход — те же в обратном. */
  var commands = {
    lunch: [18, 143, 77],
    sleep: [201, 36, 112, 165],
    // переезд корабля на новое место; записан в пятом корабельном логе
    relocate: [52, 97, 144, 181, 23]
  };

  /* Эти знаки заняты интерфейсом и словами не становятся. */
  var reserved = [0, 7, 58, 121, 196, 33, 164, 90, 139];

  root.LoreText = { words: words, blocks: blocks, logs: logs, ship: ship, commands: commands, reserved: reserved };
})(window);
