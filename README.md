# Спектральная задача с отражением аргумента

Оператор $L_a y=-y''(x)-a(x)y''(-x)$ на $(-1,1)$ с условиями Дирихле,
$L_a y\in L_2(-1,1;\mathbb C)$, при вещественном $a$. Проект идёт по маршруту лекции 2
курса «Алгебра · ИИ · Lean» (А. Перепечко, осень 2026): постановка, контекст,
миниобзор, карта лемм, формализация в Lean 4 с Mathlib.

Вопрос: при каких условиях на $a$ корневые функции $L_a$ образуют базис Рисса, а при
каких — только базис Рисса со скобками. Постановка, условия и контрольные случаи —
`claims/question.md`.

## Раскладка

| Класс | Где лежит |
| --- | --- |
| правила и вход | `AGENTS.md`, `README.md`, `CLAUDE.md` |
| постановка | `claims/question.md` |
| записи, идеи, карточки | `claims/C*.md`, `claims/I*.md`, `claims/S*.md` |
| изложение | `paper/review.tex`, `paper/exposition.tex` |
| источники | `sources/registry.json`, `sources/README.md`, `sources/catalog.md` |
| библиотека Lean | `Involution/<Слой>/*.lean`, `Involution.lean` |
| инструменты | `tools/**` |
| обмен с Aristotle | `tasks/A*/**` |
| опыты | `experiments/E*/**` |
| производное и цех | `index.md`, `blueprint.md`, `paper/generated/`, `output/` |

Это краткая выжимка; полное соответствие «класс → путь», слои библиотеки и правила
раскладки — в [LAYOUT.md](LAYOUT.md), шапки единиц и статусы — в
[FACETS.md](FACETS.md). Рукописного списка файлов и таблицы результатов здесь нет:
они производны и устаревают.

## Где смотреть результаты

- [index.md](index.md) — сводка единиц по классам и статусам; производная.
- [blueprint.md](blueprint.md) — план: узлы и зависимости, модули Lean, задачи
  Aristotle; производный.
- `output/generated/Axioms.lean` — реестр аксиом итоговых теорем; производный.
- Первичное — шапки самих единиц в `claims/`: состояние живёт только там.

Сводки собирают инструменты `tools/state/` из шапок, поэтому расхождение статусов
между документами невозможно; вручную их не правят.

## Как проверить

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File tools\check\check.ps1
```

Скрипт проверяет обязательные файлы, сборку `lake build` и отсутствие `sorry` в
`Target.lean`, `Scratch.lean`, `Search.lean`. Дополнительно перед завершением работы
выполняй `git diff --check`.

Версии закреплены в `lean-toolchain`, `lakefile.toml` и `lake-manifest.json`:
Lean `v4.35.0-rc4`, Mathlib `v4.35.0-rc4`. Если `lake` не найден, добавь
`$env:USERPROFILE\.elan\bin` в `PATH`; на новом компьютере сначала `lake exe cache get`.
В библиотеке нет `sorry` и `axiom`; список проверок аксиом — в `Scratch.lean`.
Заготовка `tasks/A4/package/` содержит один `sorry` и в сборку не входит.

## Как собрать статьи

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File tools\docs\build-review.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File tools\docs\build-exposition.ps1
```

Скрипты запускают из корня проекта, готовые PDF — в `output/build`; они дважды
запускают `pdflatex` и печатают предупреждения (неразрешённые ссылки, `Overfull`).
Оформление ведут скиллы из `.claude/skills/` (см. раздел «Оформление текста» в
[AGENTS.md](AGENTS.md)).

## Источники

Реестр — `sources/registry.json`, правит его `python tools/sources/lit.py` (`add`,
`add-file`, `attach`, `fetch`, `pdf`); каталог `sources/catalog.md` пересобирает
`catalog`. Опись коллекции и внешние исходные файлы — `sources/README.md`.
