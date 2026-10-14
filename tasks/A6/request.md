---
id: A6
title: Калибровочные данные близкого к чётному коэффициента
status: accepted
goal: C15
date: 2026-10-10
archive: output/aristotle-nearly-even-result.tar.gz
---

# A6. Калибровочные данные близкого к чётному коэффициента

Строка 5 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`7f253d14-9ab7-4b6c-a64c-d8814d2e70f6`, задача: `90829830-813c-4646-be5b-2b7725a92d22`.

## Что отправлено

Единственный `sorry` проекта — теорема `nearlyEven_gauge_data` в заготовке
`NearlyEvenBrackets` (запись `C15`). Формулировку менять нельзя, другие определения и
утверждения тоже; файл должен продолжать собираться вместе с `nearlyEven_bracket_basis`
ниже теоремы. В запросе выписаны калибровка $r=(\lvert a(x)\rvert/\lvert a(-x)\rvert)^{1/4}$,
$b=\sigma\sqrt{\lvert a(x)a(-x)\rvert}$ и тождество
$r'/r=\tfrac14\bigl(a'/a+a'(-x)/a(-x)\bigr)$.

- Пакет: `output/aristotle-nearly-even` (весь проект с закреплёнными версиями и
  `prompt.md`).
- Дата отправки: 2026-10-10.

## Что вернулось

- Теорема доказана; по сводке сервиса формулировки и определения не менялись, удалена
  только строка `sorry`, `lake build` проходит, `sorry`, `admit`, `axiom` и
  `@[implemented_by]` в проекте нет.
- Архив: `output/aristotle-nearly-even-result.tar.gz`; выписка — `answer/note.md`.
- Добавлены леммы `uIoc_neg_disjoint`, `absolutelyContinuousOnInterval_comp_neg`,
  `reflectCoefficient`, `reflectCoefficient_ae`, `HasACMultiplierDerivative.reflect`,
  `HasACMultiplierDerivative.coeff_add`, `nearlyEven_gauge_real_identity`,
  `nearlyEven_log_bound`.

## Сверка

- Заголовки объявлений: по квитанции изменился только `Involution/Estimates/NearlyEvenBrackets.lean`,
  формулировка леммы с `sorry` и итоговой теоремы не менялись; по `blueprint.md`
  формулировки сверены с отправленной заготовкой.
- `sorry` и `axiom`: нет.
- Локальная сборка: пройдена; после переноса локально добавлены импорт
  `BracketCorollaries`, следствие `nearlyEven_bracket_rootVectors` и перенесена одна
  строка (квитанция).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — для
  `nearlyEven_gauge_data` и `nearlyEven_bracket_basis`.

## Источники сведений

`blueprint.md` (строка 5), `output/aristotle-nearly-even-receipt.json`,
`output/aristotle-nearly-even/prompt.md`,
`output/aristotle-nearly-even-result/aristotle-nearly-even_aristotle/ARISTOTLE_SUMMARY.md`,
запись `C15`. Перенос — `report.md`.
