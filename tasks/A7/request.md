---
id: A7
title: Теорема Маркуса–Мацаева при p = 1/2 (диагональная форма)
status: accepted
goal: C16
date: 2026-10-10
archive: [output/aristotle-markus-result.tar.gz, output/aristotle-markus-result2.tar.gz]
---

# A7. Теорема Маркуса–Мацаева при $p=1/2$ (диагональная форма)

Строка 6 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`c4fdbf81-6fdc-48c0-b18a-995935371d25`; задачи: `63224d6a-5993-4188-aa64-9beefd477ff0`
(первая, исчерпала лимит времени) и `ecce65e9-e25e-4af0-8613-29225712bd50`
(продолжение, `COMPLETE`).

## Что отправлено

Единственный `sorry` — теорема `exists_bracket_basis_of_subordinate_general` в
заготовке `MarkusMatsaev`: $G=\operatorname{diag}(\lambda_i)$, $\lambda_i>0$,
счётная функция $N(t)=\#\{i:\lambda_i\le t^2\}\le c_2t+C_0$, возмущение $S$
подчинено $G$ с показателем $1/2$; вывод — конечномерные инвариантные подпространства,
образующие базис Рисса подпространств. Это теорема 6.1 работы Wyss
(arXiv:0906.2631v1, источник `S4`) в частном случае: самосопряжённый положительный
диагональный $G$, один луч, $p=1/2$. Формулировку менять нельзя, разрешены новые
файлы и леммы.

- Пакет: `output/aristotle-markus` (весь проект, закреплённые версии, `prompt.md` и
  текст статьи Wyss в `paper/`).
- Дата отправки: 2026-10-10.

## Что вернулось

- Первый прогон закончился по лимиту времени с одной недоказанной леммой
  `MMData.exists_cuts`; команда `aristotle continue` её закрыла (второй архив).
- Итог: `#print axioms Involution.exists_bracket_basis_of_subordinate_general` —
  `[propext, Classical.choice, Quot.sound]`; добавлены `MMWindowCut` (окно, формула
  Вудбери, лемма о минимуме модуля) и `MMGoodCut` (`finite_of_count`,
  `exists_sparse_window`, `exists_cuts`); в `MMWindow` исправлены два сломанных шага
  доказательства `inv_one_sub_K_eq` без изменения формулировок.
- Архивы: `output/aristotle-markus-result.tar.gz` (первый прогон, сводка «достигнут
  лимит времени») и `output/aristotle-markus-result2.tar.gz` (итог); выписка —
  `answer/note.md`.

## Сверка

- Заголовки объявлений: по квитанции формулировка цели не менялась, файлы проекта,
  существовавшие до отправки, не изменены; по `blueprint.md` формулировки сверены с
  отправленной заготовкой.
- `sorry` и `axiom`: нет; в проекте ответа не осталось ни одного `sorry`.
- Локальная сборка: пройдена. После переноса локально правился стиль: устаревшие имена
  лемм, длинные строки, неиспользуемый аргумент `simp`, три вызова `simp` заменены на
  `simp only` (`blueprint.md`); квитанция добавляет отключение стилевых линтеров
  (длинные строки в 7 модулях, несколько целей в 1, гибкая тактика в 3 объявлениях).
  Формулировки не менялись.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.

## Источники сведений

`blueprint.md` (строка 6 и абзац о задаче 6), `output/aristotle-markus-receipt.json`,
`output/aristotle-markus/prompt.md`,
`output/aristotle-markus-result2/output-final_aristotle/ARISTOTLE_SUMMARY.md`,
запись `C16` (в её абзаце «Lean» названы `MarkusMatsaev` и модули `MM*`).
Перенос — `report.md`.
