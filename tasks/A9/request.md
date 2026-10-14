---
id: A9
title: При a = x/2 нет базиса Рисса из собственных функций (узел S-GENERAL)
status: accepted
goal: C18
date: 2026-10-11
archive: output/aristotle-halfslope-result.tar.gz
---

# A9. При $a(x)=x/2$ нет базиса Рисса из собственных функций

Строка 8 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`55948b6e-fdd9-40a9-a773-134c314d2281`; задача прогона:
`51364e1d-4dad-4e2e-84a5-a22b83d74a36` (заголовок `ARISTOTLE_SUMMARY.md` ответа).

## Что отправлено

Три `sorry` заготовки `HalfSlope`; цель — последняя теорема, формулировку которой
менять нельзя, две промежуточные разрешено переформулировать:

```lean
theorem Involution.halfSlope_no_riesz_eigenbasis :
    ¬ ∃ (ι : Type) (b : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemDirichletH2 (b.vector i), ∃ lam : ℂ,
        variableSobolevOperator halfSlopeClass (b.vector i) hf.1 = lam • b.vector i
```

Промежуточные: `halfSlope_quasimodes` и `rieszEigenbasis_count`. Бумажный набросок —
идея `I7`; численное подтверждение — опыт `E`-класса по квазимодам.

- Пакет: `output/aristotle-halfslope` (весь проект с закреплёнными версиями и
  `prompt.md`).
- Дата отправки: 2026-10-11.

## Что вернулось

- Статус `COMPLETE`. По `blueprint.md` определения и заголовки трёх теорем совпадают с
  заготовкой, `sorry` и `axiom` нет; добавлены модули `Involution/Estimates/HalfSlopeProfile.lean` и
  `Involution/Estimates/RieszEigenCount.lean`, два импорта и шесть вспомогательных объявлений в
  `Involution/Estimates/HalfSlope.lean`. Файл `Target.lean`, добавленный сервисом, не перенесён. Три модуля
  перенесены без правок.
- Ответ сервиса: `#print axioms Involution.halfSlope_no_riesz_eigenbasis` —
  `[propext, Classical.choice, Quot.sound]`; ветви записаны как $\exp(\log s/4)$ и
  $\exp(\log s/2)$; срезка построена из `Real.smoothTransition`.
- Архив: `output/aristotle-halfslope-result.tar.gz`; выписка — `answer/note.md`.

## Сверка

- Заголовки объявлений: совпадают с отправленной заготовкой; сервис подтвердил, что
  формулировки не менялись (кроме разрешённых промежуточных, которые тоже сохранены).
- `sorry` и `axiom`: нет.
- Локальная сборка: пройдена; три модуля перенесены без правок.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` (запись `C18` и
  выписка сервиса).

## Источники сведений

`blueprint.md` (строка 8 и абзац о задаче 8), `output/aristotle-halfslope-receipt.json`
(написан при отправке, говорит «ответа ещё нет»),
`output/aristotle-halfslope/prompt.md`,
`output/aristotle-halfslope-result/aristotle-halfslope_aristotle/ARISTOTLE_SUMMARY.md`,
запись `C18`, идея `I7`. Перенос — `report.md`.
