---
id: A3
title: Диагональные операторы и мультипликаторы Шура
status: accepted
goal: C13
date: 2026-10-10
archive: output/aristotle-schur-result.tar.gz
---

# A3. Диагональные операторы и мультипликаторы Шура

Строка 3 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`d1c6ea68-aea5-4e0f-ae40-fd4a5cf66d60`, задача: `d935ef55-2174-4951-8b66-53c07d12bf28`.

## Что отправлено

Задача — заполнить все `sorry` в заготовке `SchurMultiplier` (20 утверждений).
Заголовки и определения менять нельзя, разрешены вспомогательные леммы и импорты
Mathlib. Содержание запроса: `opEntry` и экстенсиональность (`opEntry_ext`,
`clm_ext_basis`), `exists_diagOp` и его API (`inner_basis_diagOp`,
`diagOp_apply_basis`, `diagOp_norm_le`, `opEntry_diagOp_comp`, `opEntry_comp_diagOp`,
`diagOp_comp`, `diagOp_one`, `inner_diagOp_left`), `SchurBound` и его случаи
(`product`, `of_hasSum`, `blockSum`), оценки разделённых мультипликаторов
`schurBound_separated_upper`/`lower`, `exists_weighted_extension`. Квитанция требует
`#print axioms` для шести объявлений и запрещает молча менять формулировки.

- Пакет: `output/aristotle-schur` (весь проект с закреплёнными версиями и `prompt.md`).
- Дата отправки: 2026-10-10.

## Что вернулось

- Заполнены все 20 `sorry`; по сводке сервиса сравнение с исходным коммитом
  показывает, что удалены только строки `sorry`, определения и формулировки не
  менялись, `lake build` проходит, ложных утверждений нет.
- Архив: `output/aristotle-schur-result.tar.gz`; выписка — `answer/note.md`.
- Добавлены вспомогательные леммы `norm_le_of_coord_sum_le`, `exists_of_coord`,
  `sum_norm_sq_proj_le`, `hasSum_geom_uv`.

## Сверка

- Заголовки объявлений: по квитанции «all statements and definitions unchanged»;
  по `blueprint.md` формулировки сверены с отправленной заготовкой.
- `sorry` и `axiom`: нет (сводка сервиса).
- Локальная сборка: пройдена; после переноса локально правился только стиль —
  `show` заменён на `change`, убран неиспользуемый `CompleteSpace`, переименован
  неиспользуемый биндер (квитанция).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — для
  `SchurBound.blockSum`, `SchurBound.of_hasSum`, `schurBound_separated_upper`,
  `schurBound_separated_lower`, `exists_weighted_extension`, `diagOp_norm_le`.

## Источники сведений

`blueprint.md` (строка 3), `output/aristotle-schur-receipt.json`,
`output/aristotle-schur/prompt.md`, `output/aristotle-schur-result/aristotle-schur_aristotle/ARISTOTLE_SUMMARY.md`,
запись `C13` (в её абзаце «Lean» названы `SchurMultiplier` и `SparseCuts`).
Перенос — `report.md`.
