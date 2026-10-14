# DeepSeek Harness

Поддерживается официальный [DeepSeek Harness](https://github.com/deepseek-ai/deepseek-harness)
(`dsh`). Адаптер закреплён на **0.2.1-alpha.2**; контракт сверён с upstream
`d743267388641bc76f17c45ce8b4c231aed1d32c`. Другие версии нужно проверять отдельно:
Harness пока меняет интерфейсы между версиями.

## Запуск

Нужны Node.js **22.19+ в ветке 22 или 24+**, npm, Python 3.11+, `uv`, `elan/lake`,
Git; для статьи — `pdflatex`. Запускайте команды из папки созданного проекта.

```sh
python tools/host/harness.py prepare
python tools/host/harness.py run web
```

`prepare` работает без сети и ключей. `run` сначала обновляет производные файлы,
затем запускает закреплённый пакет через npm; первый запуск скачивает Harness.
Команда работает в Windows и Linux/macOS и передаёт аргументы без командной оболочки.
Выберите в интерфейсе Harness папку этого проекта, preset **Standard** и настройте
провайдера/модель. Ключ задаётся в настройках Harness, в проект его не записывают.

Для запуска сервера без открытия браузера:

```sh
python tools/host/harness.py run web -- --no-open
```

Для одной задачи (провайдер и модель уже настроены в Harness):

```sh
python tools/host/harness.py run headless -- "Прочитай AGENTS.md, LAYOUT.md и FACETS.md и проверь состояние проекта"
```

Эквивалентный прямой запуск после `prepare`:

```sh
npx --yes @deepseek-ai/dsh@0.2.1-alpha.2 web --patch ./output/harness/cordis.patch.yml
```

`--patch` обязателен: `.mcp.json` и `.claude/settings.json` сами по себе не подключают
инструменты в Harness. Один запущенный экземпляр с этим patch привязан к одному
проекту: MCP имеет абсолютный `cwd`. Для другого проекта запустите отдельный экземпляр.
После переноса папки повторите `prepare`. Профили Minimal/PTC и произвольные пользовательские
профили этим адаптером не проверяются; используйте Web/Standard или Headless.

## Что доступно

Harness получает то же, что Claude Code: адаптер читает состав из `.claude/` и
`.mcp.json` при каждой подготовке. Текущий список печатает команда

```sh
python tools/host/harness.py list
```

Команды помечены в нём косой чертой, навыки с пометкой «только по вызову пользователя»
модель сама не загружает. Выбирайте skill в меню `/`, затем дописывайте аргумент; если
клиент не показывает меню, попросите выполнить skill по имени. `uv` запускает
MCP-серверы в корне проекта; вызов MCP может занимать до десяти минут, например сборка Lean.

Роли запускаются нативным `spawn` с пустой историей. Критик, рецензент и сверяющие
получают только материал проверки. Модель наследуется от родительской сессии;
названия моделей Claude Code в API DeepSeek не отправляются. Глубина 2 допускает вызов
одной роли из другой. Возврат id агента ещё не означает завершение: вызывающий ждёт
отчёт, сверяет файл и только затем меняет статус.

## Как переносится воркфлоу Claude Code

Новая команда, роль, навык или MCP-сервер попадают в Harness после `prepare` (его
вызывает `run`). В `tools/host/harness.py`, тестах и этом файле их
имён нет, править там нечего.

| В Claude Code | В Harness |
| --- | --- |
| `.claude/commands/NAME.md` | skill `NAME` в `.dsh/skills/`; в начало добавлены правила вызова ролей, таблица «Классы и пути (LAYOUT.md)», список ролей с описаниями и имена MCP |
| `.claude/skills/NAME/` | skill `NAME` вместе со справочниками и скриптами |
| `disable-model-invocation: true` у навыка | поле сохраняется; такой навык получает то же начало, что команда |
| `description` у навыка | строка каталога навыков: модель выбирает навык по имени и первым 500 знакам описания; на более длинном описании навыка, доступного модели, `prepare` останавливается |
| `when_to_use` у навыка | дописывается к `description`; то же условие лежит в поле `whenToUse`, которое Harness модели не показывает |
| `paths` у навыка | слова «При работе с файлами МАСКА.» дописываются к `description` после условия из `when_to_use`; сам фильтр в Harness не действует, команды получают строку «перед правкой таких файлов загрузи эти skills» |
| `$ARGUMENTS` | слова «аргументы вызова из сообщения пользователя» |
| `.claude/agents/NAME.md` | инструмент `research_NAME` с подчёркиваниями вместо дефисов; имя роли в обратных кавычках заменяется именем инструмента во всех текстах |
| `tools` у роли | строка с набором инструментов и MCP роли; при `Agent` роль получает правила вызова и список остальных ролей, иначе запрет вызывать роли |
| `omitClaudeMd: true` у роли | роль не получает указания читать `AGENTS.md`, `LAYOUT.md` и `FACETS.md` |
| `model` у роли, `argument-hint` | не переносятся: модель наследуется от сессии |
| имена инструментов Claude Code в тексте (`Read`, `Bash`, `WebSearch`, …) и моделей (`opus`, …) | текст не меняется; перед ним ставится пояснение с аналогами для встреченных имён |
| сервер из `.mcp.json` | запись `dsh-mcp-client` с абсолютным `cwd` проекта |

Раскладка классов и путей живёт в `LAYOUT.md` (раздел «Первичное»), состояние единиц —
в шапках `claims/` по правилам `FACETS.md`. Адаптер вставляет таблицу классов только
в шапку workflow-навыков: роли получают указание прочитать `LAYOUT.md` и `FACETS.md`.

Правка адаптера нужна в трёх случаях. Первый — поле шапки, для которого нет правила:
`prepare` и `check` печатают «Не перенесено в Harness» с именем файла и поля, а
`tools/tests/test_harness.py` проверяет, что таких полей у исходных инструкций нет;
правило добавляется в `SKILL_HANDLED` или `AGENT_HANDLED`. Второй — новый встроенный
инструмент Claude Code, которого нет в словаре `CLAUDE_TOOLS`. Третий — смена версии
Harness: `DSH_VERSION` и `UPSTREAM_REVISION` в `tools/host/harness.py`, затем проверка
схемами из раздела «Проверка».

Для транскрипции PDF и проверки карточек нужна модель с поддержкой изображений.
При текстовой модели остальные процессы доступны, но нельзя считать PDF прочитанным
или источник сверенным. Настройте подходящую модель в Harness для этих задач.

## Источники и обновление

Существующие `.claude/agents`, `.claude/commands`, `.claude/skills` остаются единым
источником инструкций. `tools/host/harness.py` преобразует их в `.dsh/skills/` и
`output/harness/cordis.patch.yml`. Справочные материалы копируются с сохранением
относительных путей. Неподдерживаемая YAML-шапка вызывает ошибку, а не потерю инструкций.
При удалении исходной команды её неизменённые производные файлы убираются по манифесту;
чужие файлы не удаляются, ручные изменения устаревших производных требуют переноса.

Проект создан до шаблона `research-template`, и `create.py --update` к нему не применим.
`tools/host/harness.py`, `tools/tests/test_harness.py` и `tools/tests/harness_runtime.mjs` — копии файлов
шаблона; новую версию адаптера переносят копированием этих трёх файлов в `tools/host/` и
`tools/tests/`. После изменения исходных инструкций или `.mcp.json` повторите `prepare`;
`run` делает это автоматически. Для работающего Harness после пересборки patch
перезапустите процесс. Производные файлы не редактируйте вручную и не коммитьте.

Дополнительные настройки Harness передавайте отдельным локальным patch после
сгенерированного: `python tools/host/harness.py run web -- --patch /path/to/local.yml`.
Адаптер не переносит разрешения Claude и не меняет глобальные настройки Harness.
Права задаются в Harness; ограничения мест записи в ролях являются инструкциями.
Поле `env` stdio-сервера копируется в patch, который лежит в `output/` вне Git; ключи в
`.mcp.json` не храните. HTTP-сервер с `headers` настраивается отдельным Cordis patch:
отметьте запись в `.mcp.json` как `disabled: true` и включите её локальным patch. Поддерживаются stdio и HTTP; SSE не конвертируется.

## Проверка

```sh
python tools/host/harness.py check
python tools/host/harness.py list
python -m unittest discover tools/tests
```

`harness.py check` проверяет свежесть файлов, не запускает модель и ничего не пишет.
Структуру итоговой конфигурации можно проверить самим Harness без запроса к модели:

```sh
python tools/host/harness.py run web -- --dump-config
```

Проверка настоящими схемами и загрузчиком skills Harness (установка только в `output/`):

```sh
npm install --prefix output/harness/runtime @deepseek-ai/dsh@0.2.1-alpha.2
node tools/tests/harness_runtime.mjs output/harness/runtime/node_modules
node tools/tests/harness_runtime.mjs output/harness/runtime/node_modules --mcp
```

Последняя команда проверяет handshake и список инструментов каждого MCP-сервера:
у `lean-lsp` — наличие `lean_goal` (сборка Lean не запускается), у `lit` — вызов
`lit.papers`. `uv` может скачать зависимости;
вызовов модели и внешнего поиска в этом тесте нет. Общий `--dump-config-schema` в
0.2.1-alpha.2 может завершаться ошибкой на встроенных Web presets; тест выше проверяет
все записи patch непосредственно валидаторами их плагинов.

Модульные тесты адаптера печатает `python -m unittest discover tools/tests`; они не
требуют сети, Node.js и MCP-серверов.

При первом реальном запуске проверьте наличие `mcp__lit__papers`
и инструментов `lean-lsp`, затем выполните `/day` на своей постановке. Ошибка запуска
MCP отражается в диагностике Harness; видимый интерфейс ещё не подтверждает работу серверов.

Контракты upstream: [MCP](https://github.com/deepseek-ai/deepseek-harness/blob/d743267388641bc76f17c45ce8b4c231aed1d32c/packages/mcp/mcp-client/README.md),
[skills](https://github.com/deepseek-ai/deepseek-harness/blob/d743267388641bc76f17c45ce8b4c231aed1d32c/packages/skill/skill-filesystem/README.md),
[роли](https://github.com/deepseek-ai/deepseek-harness/blob/d743267388641bc76f17c45ce8b4c231aed1d32c/packages/subagent/tool-subagent/README.md),
[CLI](https://github.com/deepseek-ai/deepseek-harness/blob/d743267388641bc76f17c45ce8b4c231aed1d32c/apps/cli/README.md).
