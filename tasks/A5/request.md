---
id: A5
title: Три леммы метода подобных операторов
status: accepted
goal: C13
date: 2026-10-10
archive: output/aristotle-cuts-result.tar.gz
---

# A5. Три леммы метода подобных операторов

Строка 4 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`62ba5391-5d03-4a3d-b1e5-9949583b2639`, задача: `767bf9da-85af-4038-8f31-f7a5bd6edf47`.

## Что отправлено

Задача — заполнить все `sorry` заготовки `SparseCuts`: `exists_similarity_fixedPoint`
(неподвижная точка сжимающего отображения на замкнутом шаре),
`exists_sparse_cuts` (окна с зазором из оценки счётной функции) и
`card_le_of_finiteRank_approx` (конечномерность спектрального множества).
Формулировки менять нельзя, разрешены вспомогательные леммы; требовался
`#print axioms` трёх теорем.

- Пакет: `output/aristotle-cuts` (весь проект с закреплёнными версиями и `prompt.md`).
- Дата отправки: 2026-10-10.

## Что вернулось

- Все три `sorry` заполнены; добавлена вспомогательная лемма `exists_gap_point`
  (оконное утверждение из наброска). Три утверждения истинны, контрпримера нет.
- Архив: `output/aristotle-cuts-result.tar.gz`; выписка — `answer/note.md`.
- Замечание сервиса: в `exists_sparse_cuts` не используются гипотезы `hω`
  (положительность $\omega$) и `hC₀` ($0\le C_0$) — теорема верна и без них; по
  требованию запроса формулировки оставлены без изменений.

## Сверка

- Заголовки объявлений: по квитанции «statements unchanged, module adopted»; по
  `blueprint.md` формулировки сверены с отправленной заготовкой; сервис подтвердил,
  что формулировки не менялись.
- `sorry` и `axiom`: нет.
- Локальная сборка: пройдена; после переноса переименованы два неиспользуемых
  биндера (квитанция).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — для
  `exists_similarity_fixedPoint`, `exists_sparse_cuts`, `card_le_of_finiteRank_approx`.

## Источники сведений

`blueprint.md` (строка 4), `output/aristotle-cuts-receipt.json`,
`output/aristotle-cuts/prompt.md`,
`output/aristotle-cuts-result/aristotle-cuts_aristotle/ARISTOTLE_SUMMARY.md`,
запись `C13`. Перенос — `report.md`.
