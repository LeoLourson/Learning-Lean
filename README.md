# Спектральная задача с отражением аргумента

В пространстве $L_2(-1,1;\mathbb C)$ изучаем оператор

$$
L_a y=-y''(x)-a(x)\,y''(-x),\qquad y(-1)=y(1)=0,
$$

с вещественным коэффициентом $a$, для которого $\lvert a(x)a(-x)\rvert\le\kappa<1$ почти всюду.
Вопрос: при каких условиях на $a$ корневые функции $L_a$ образуют базис Рисса, а при
каких — только базис Рисса со скобками. Проект идёт по маршруту лекции 2 курса
«Алгебра · ИИ · Lean» (А. Перепечко, осень 2026): постановка, контекст, миниобзор,
карта лемм, формализация в Lean 4 с Mathlib.

## Результаты

| Условие на $a$ | Вывод | Теорема Lean |
| --- | --- | --- |
| $a\in L_\infty$, $a(-x)=a(x)$ | базис Рисса из собственных функций; присоединённых функций нет | `rieszBasis_of_even` |
| $a\in W^2_\infty$, $0<m\le\lvert a\rvert\le M$ | базис Рисса со скобками из конечномерных инвариантных блоков | `bracketBasis_of_signDefinite` |
| то же и $\bigl\lvert a'(x)/a(x)+a'(-x)/a(-x)\bigr\rvert\le\eta$, $160(1+\sqrt\kappa)\eta<\pi(1-\sqrt\kappa)$ | тот же вывод; доказательство без контурных интегралов | `bracketBasis_of_nearlyEven` |
| $a\in L_\infty$ | компактный обратный, альтернатива Фредгольма; базисность не следует | `productBound_compact_inverse`, `productBound_fredholm` |
| $a\in L_\infty$, $a(-x)=-a(x)$ | $L_a$ унитарно эквивалентен $(1+ia)(-D^2)$; базисность не доказана | `oddCoefficient_unitary_multiplication` |
| $a\in L_\infty$, $\lvert a(x)+a(-x)\rvert\le2\alpha$, $\alpha<1$, $\lvert a(x)-a(-x)\rvert\le2\beta$ | собственные значения в секторе $(1-\alpha)\lvert\operatorname{Im}\lambda\rvert\le\beta\operatorname{Re}\lambda$; $\lVert(L_a+s)^{-1}\rVert\le C/s$ при $s>0$; полнота корневых функций по теореме из S3, в Lean не формализована | `eigenvalue_sector`, `resolvent_ray_estimate` |
| $a$ непрерывна на $[-1,1]$, $\lvert a(x)a(-x)\rvert<1$; в частности весь класс постановки | $\lVert(L_a+s)^{-1}\rVert\le C/s$ при $s\ge s_0$ и полнота корневых функций (C19). В Lean доказана оценка в калибровочных данных $r,w,b$; выбор фазы $\psi$ и теорема о полноте из S3 не формализованы | `gauge_resolvent_ray_estimate` |
| $a=4$ на $(0,1)$, $a=0$ на $(-1,0)$ | собственных значений нет | `oneSided_no_eigenfunction`, `oneSided_no_bracket_basis` |
| $a(x)=\max(x,0)$ | нет базиса Рисса из собственных функций | `ramp_no_riesz_eigenbasis` |
| $a(x)=x/2$ | нет базиса Рисса из собственных функций | `halfSlope_no_riesz_eigenbasis` |

Доказательства, источники и границы каждого утверждения записаны в
[context.md](context.md). Теоремы Lean сформулированы на слабой области Дирихле: две
слабые производные в $L_2$ и нулевые значения непрерывного представителя на концах. Она
равна $H^2\cap H_0^1$, где $H_0^1$ — замыкание гладких функций с компактным носителем
(`memDirichletH2_iff_h2_and_h01`). Размер скобок не оценён; обычный базис Рисса для
знакопостоянного $a$, не являющегося чётным, не установлен. В строке с сектором оценка
$\lvert a(x)a(-x)\rvert\le\kappa<1$ не используется.

## Файлы

| Файл или папка | Содержание |
| --- | --- |
| [question.md](question.md) | объект, условия, вопрос, первая цель формализации, три контрольных случая |
| [context.md](context.md) | записи C1–C19: условия, утверждение, доказательство, теоремы Lean, границы |
| [review.tex](review.tex) | миниобзор: четыре раздела и библиография |
| [exposition.tex](exposition.tex) | связное изложение результатов с основными шагами доказательств |
| [blueprint.md](blueprint.md) | узлы и зависимости, модули Lean, задачи Aristotle |
| [ideas.md](ideas.md) | журнал идей по открытым узлам: формулировка, набросок, статус, следующий шаг |
| [.claude/commands/](.claude/commands/) | команды: `/day` — ежедневный цикл, `/sources` — поиск и загрузка источников, `/transcribe` — PDF источника в LaTeX |
| [.claude/skills/](.claude/skills/) | оформление текста: `exposition` (команда `/exposition`), `shkalikov-style`, `paper-canvas`, `paper-de-ai` |
| [.claude/agents/](.claude/agents/) | агенты: идеи, критика, опыты, рецензия, формализация, соответствие формализации, поиск по Mathlib и литературе, транскрипция, сверка карточек |
| [sources/](sources/README.md) | реестр источников, каталог, карточки проверенных теорем |
| `.mcp.json` | MCP-серверы проекта: `lean-lsp` (цели и диагностика Lean) и `lit` (источники) |
| [AGENTS.md](AGENTS.md) | правила работы агента |
| [DEEPSEEK.md](DEEPSEEK.md) | работа в DeepSeek Harness: `python scripts/harness.py run web`; команды, роли и навыки собираются из `.claude/` |
| `tests/` | проверки адаптера Harness: `python -m unittest discover tests` |
| `Involution/`, `Involution.lean` | библиотека Lean |
| `Target.lean` | первая цель: редукция системы $2\times2$ |
| `Scratch.lean`, `Search.lean` | проверка имён Mathlib и аксиом; пример `exact?` |
| `input/`, `input-lean/` | пакеты для Aristotle |
| `scripts/` | `lit.py` — источники: загрузка, транскрипции, поиск по полным текстам; сборка обзора, проверки, подготовка пакетов |
| `output/` | PDF обзора, статьи, архивы ответов Aristotle; в Git не входит |

## Сборка Lean

Версии закреплены в `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`:
Lean `v4.35.0-rc4`, Mathlib `1f414401f69059aa7eead47b53ee40bd38455eeb`.

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"   # если lake не найден
lake exe cache get                                    # на новом компьютере
lake build
lake env lean Target.lean
lake env lean Scratch.lean
```

Проверка обязательных файлов, сборки, `Target`, `Scratch`, `Search` и исключения
`output/` из Git:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check.ps1
```

В библиотеке нет `sorry` и `axiom`. `#print axioms` для итоговых теорем показывает
`propext`, `Classical.choice`, `Quot.sound`; список проверок — в `Scratch.lean`.
Упражнение `input-lean/Target.lean` содержит один `sorry` и в сборку не входит.

## Сборка миниобзора

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/build-review.ps1
```

Скрипт дважды запускает `pdflatex`, пишет `output/review.pdf` и выводит предупреждения
из `output/review.log`. При рабочем Perl годится `latexmk -pdf -outdir=output review.tex`.

## Aristotle

Корневые заметки первичны; `input/` — их снимок вместе со статьями, `input-lean/` —
отдельный пакет с одной целью. Снимок обновляет скрипт, он ничего не отправляет:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/prepare-input.ps1
aristotle submit "Выполни prompt.md" --project-dir input --wait --destination output/review-result.tar.gz
aristotle submit "Заполни sorry в Target.lean, сохрани формулировку" --project-dir input-lean --wait --destination output/lean-result.tar.gz
```

Ключ передаётся через `ARISTOTLE_API_KEY` и в файлах проекта не хранится. Сервис ведёт
один проект за раз; состояние показывает `aristotle tasks <project-id>`. Ответ
распаковывают в `output/`, сверяют формулировки с отправленными, переносят доказательство
и повторяют локальную сборку и `#print axioms`. Задачи и принятые из них модули
перечислены в [blueprint.md](blueprint.md).
