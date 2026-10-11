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
| $a=4$ на $(0,1)$, $a=0$ на $(-1,0)$ | собственных значений нет | `oneSided_no_eigenfunction`, `oneSided_no_bracket_basis` |
| $a(x)=\max(x,0)$ | нет базиса Рисса из собственных функций | `ramp_no_riesz_eigenbasis` |

Доказательства, источники и границы каждого утверждения записаны в
[context.md](context.md). Теоремы Lean сформулированы на слабой области Дирихле: две
слабые производные в $L_2$ и нулевые значения непрерывного представителя на концах. Её
равенство с $H^2\cap H_0^1$, где $H_0^1$ — замыкание гладких функций с компактным
носителем, в Lean не доказано. Размер скобок не оценён; обычный базис Рисса для
нечётного $a$ не установлен.

## Файлы

| Файл или папка | Содержание |
| --- | --- |
| [question.md](question.md) | объект, условия, вопрос, первая цель формализации, три контрольных случая |
| [context.md](context.md) | записи C1–C16: условия, утверждение, доказательство, теоремы Lean, границы |
| [review.tex](review.tex) | миниобзор: четыре раздела и библиография |
| [exposition.tex](exposition.tex) | связное изложение результатов с основными шагами доказательств |
| [blueprint.md](blueprint.md) | узлы и зависимости, модули Lean, задачи Aristotle |
| [ideas.md](ideas.md) | журнал идей по открытым узлам: формулировка, набросок, статус, следующий шаг |
| [.claude/commands/day.md](.claude/commands/day.md) | ежедневный цикл, команда `/day` |
| [.claude/commands/exposition.md](.claude/commands/exposition.md) | обновление `exposition.tex`, команда `/exposition` |
| [.claude/style/shkalikov.md](.claude/style/shkalikov.md) | выжимка стиля А. А. Шкаликова для `exposition.tex` |
| [sources/](sources/README.md) | реестр источников и карточки проверенных теорем |
| [AGENTS.md](AGENTS.md) | правила работы агента |
| `Involution/`, `Involution.lean` | библиотека Lean |
| `Target.lean` | первая цель: редукция системы $2\times2$ |
| `Scratch.lean`, `Search.lean` | проверка имён Mathlib и аксиом; пример `exact?` |
| `input/`, `input-lean/` | пакеты для Aristotle |
| `scripts/` | сборка обзора, проверки, подготовка пакетов, загрузка статей |
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
