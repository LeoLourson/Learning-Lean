# Раскладка классов

Единственный носитель соответствия «класс → путь» в проекте. Другие файлы
ссылаются на классы по имени (`` `record` ``, `` `card` ``, `` `paper` ``) и не
повторяют пути. Инструкции читают эту таблицу; адаптер
(`tools/host/harness.py`) вставляет её в шапку workflow-навыков Harness.

Правила раскладки:

1. Файл принадлежит ровно одному классу. Классов вне таблицы не бывает.
2. Смысловые классы — по природе объекта; служебное — только в `output/`.
3. Первичное не смешивается с производным: производное несут баннер
   `<!-- generated; do not edit -->` и проверку свежести.
4. Ссылки внутри текстов — по идентификатору (`C7`, `I22`, `S4`), не по
   `файл:строка`.
5. Тела инструкций пишутся нейтрально к хосту: классы, роли, проверки. Имена
   инструментов Claude Code (`Agent`, `Task`, `Bash`), моделей (`opus`,
   `sonnet`, `haiku`) и настройки (`paths`, `model`, `tools`) допустимы только в
   шапках `.claude/**` и в `settings.json`.

Разбор таблиц машинный: строка класса начинается с `| \`` (обратная кавычка во
второй позиции), первый столбец — имя класса, второй — путь или маска.

## Первичное

| Класс | Путь | Кто пишет | Что это |
| --- | --- | --- | --- |
| `rules` | `AGENTS.md`, `README.md`, `CLAUDE.md`, `WORKFLOW.md`, `.gitignore` | человек | устав проекта, вход, точка входа Claude Code, схема работы |
| `layout` | `LAYOUT.md`, `FACETS.md` | человек | эта таблица и шапки единиц |
| `instruction` | `.claude/**` | человек | контракт Claude Code: команды, роли, навыки, настройки |
| `mcp` | `.mcp.json` | человек | состав MCP-серверов |
| `build` | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | человек | закреплённая сборка; версии не меняются |
| `probe` | `Scratch.lean`, `Search.lean`, `Target.lean` | человек | прогоны, адресуемые Lake по имени |
| `statement` | `claims/question.md` | человек | постановка задачи (одна) |
| `record` | `claims/C*.md` | человек | запись результата: один файл — одно утверждение |
| `idea` | `claims/I*.md` | человек | идея по открытому узлу |
| `card` | `claims/S*.md` | человек | карточка чужого результата |
| `paper` | `paper/*.tex` | человек | изложение: `paper/review.tex`, `paper/exposition.tex` |
| `collection` | `sources/registry.json`, `sources/README.md` | человек | опись коллекции источников |
| `library` | `Involution/<Слой>/*.lean`, `Involution.lean` | человек | Lean: слои теории |
| `tool` | `tools/**` | человек | скрипты процесса |
| `task` | `tasks/**` | человек | обмен с внешним исполнителем |
| `experiment` | `experiments/**` | человек | вычислительный опыт |
| `hostmisc` | `.vscode/**`, `.github/**` | человек | служебное хост-окружения |

Слои библиотеки: `Setup`, `Folding`, `Model`, `Estimates`, `Theorems`,
`Examples`. Модуль слоя *k* не импортирует слой выше *k*; модуль, нарушающий это,
переносится в более высокий слой (правило ближайшего рода).

## Производное

| Класс | Путь | Кто создаёт | Проверка свежести |
| --- | --- | --- | --- |
| `index` | `index.md` | `tools/state/build_index.py` | `python tools/state/build_index.py --check` |
| `plan` | `blueprint.md` | `tools/state/build_index.py` | там же |
| `catalog` | `sources/catalog.md` | `tools/sources/lit.py catalog` | `sources/registry.json` |
| `statusfrag` | `paper/generated/status.tex` | `tools/state/gen_status.py` | `python tools/state/gen_status.py --check` |
| `ledger` | `output/generated/Axioms.lean` | `tools/state/gen_ledger.py` | `tools/check/check.ps1` |
| `skills` | `.dsh/skills/**` | `tools/host/harness.py prepare` | `python tools/host/harness.py check` |
| `patch` | `output/harness/**` | там же | там же |
| `snapshot` | `output/snapshot/**` | `tools/host/prepare-input.ps1` | тот же скрипт, повторный прогон |
| `buildout` | `output/build/**`, `output/review.pdf`, `output/literature/**` | сборка и `lit.py` | — |
| `migration` | `output/migration/**` | разовая реорганизация | — |

`output/` — цех: внутри допустима любая служебная раскладка. В Git не входит.

## Откуда что пришло

Запись переноса из старого дерева — `output/migration/README.md` (история, не
правило; её можно удалить, когда ссылки на старое дерево не нужны). Оригинал
проекта остаётся на месте и не меняется: новая папка — его копия с новой
организацией.
