---
id: A2
title: Ортонормированность и полнота модельной системы
status: accepted
goal: C3
date: 2026-10-10
archive: output/aristotle-model-result.tar.gz
---

# A2. Ортонормированность и полнота модельной системы

Строка 2 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`94d172f6-5648-4b7e-859a-b69130301e10`, задача: `d20adaf7-99a5-49b0-b530-05e1ac020d7a`.

## Что отправлено

Задача — создать модуль `ModelBasis` с определением `constantModelVector` и двумя
целями (запись `C3`):

```lean
def constantModelVector : ℕ ⊕ ℕ → IntervalL2 :=
  Sum.elim
    (fun n => cosineWaveL2 (((n : ℝ) + 1 / 2) * Real.pi))
    (fun n => sineWaveL2 (((n : ℝ) + 1) * Real.pi))

theorem constantModel_orthonormal : Orthonormal ℂ constantModelVector

theorem constantModel_dense_span :
    (Submodule.span ℂ (Set.range constantModelVector)).topologicalClosure = ⊤
```

Сверх целей запрос требовал построить `constantModelHilbertBasis` через
`HilbertBasis.mk` и получить обычный `RieszBasis` переносом, а также вернуть
`#print axioms` четырёх результатов; мера `intervalMeasure` ненормированная, поэтому
моды имеют квадрат нормы $1$.

- Пакет: `output/aristotle-model-completeness` (весь проект с закреплёнными
  версиями и `prompt.md`); текст запроса сохранён как
  `output/aristotle-model-completeness-prompt.md`.
- Дата отправки: 2026-10-10.

## Что вернулось

- Статус `COMPLETE`, 100 % (`output/aristotle-model-status.json`): создан
  `Involution/ModelBasis.lean`, в `Involution.lean` добавлен импорт; по сводке
  сервиса проект собирается без `sorry`, без новых аксиом и без предупреждений,
  определения не менялись.
- Архив: `output/aristotle-model-result.tar.gz`; выписка — `answer/note.md`.
- Доказательство полноты: нечётное продолжение относительно $x=1$ на $(-1,3]$,
  равенство Парсеваля `tsum_sq_fourierCoeffOn` для периода $4$; базис
  `AddCircle.fourierBasis` напрямую не использован из-за нормированной меры Хаара.

## Сверка

- Заголовки объявлений: по квитанции выборочное принятие, «all revisions matched»;
  по `blueprint.md` формулировки сверены с отправленной заготовкой.
- `sorry` и `axiom`: нет.
- Локальная сборка: проект собран локально в закреплённых версиях; отдельная
  проверка самостоятельного файла и аудит аксиом пройдены (квитанция).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — один и тот же
  список для `constantModel_orthonormal`, `constantModel_dense_span`,
  `constantModelHilbertBasis_coe`, `constantModelRieszBasis_vector`
  (`answer/note.md`).

## Источники сведений

`blueprint.md` (строка 2), `output/aristotle-model-completeness-receipt.json`,
`output/aristotle-model-status.json`, `output/aristotle-model-completeness-prompt.md`,
запись `C3`. Перенос — `report.md`.
