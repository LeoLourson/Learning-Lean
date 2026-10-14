---
id: A8
title: Слабая область Дирихле равна H² ∩ H₀¹ (узел S-DOMAIN)
status: accepted
goal: Q
date: 2026-10-10
archive: output/aristotle-domain-result.tar.gz
---

# A8. Слабая область Дирихле равна $H^2\cap H_0^1$ (узел S-DOMAIN)

Строка 7 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`18ff2d66-76b1-4b36-9808-c9e2df6825f5`; задача прогона:
`3529d8a9-d25a-4861-a1b2-188b3716e768` (заголовок `ARISTOTLE_SUMMARY.md` ответа).

## Что отправлено

Два `sorry` заготовки `SobolevClosure` вместе с определениями `IsTestPair` и
`MemIntervalH01`:

```lean
theorem Involution.memIntervalH01_iff_trace (f : IntervalL2) :
    MemIntervalH01 f ↔ (∃ g : IntervalL2, HasL2WeakDeriv f g) ∧ HasDirichletTrace f

theorem Involution.memDirichletH2_iff_h2_and_h01 (f : IntervalL2) :
    MemDirichletH2 f ↔ MemIntervalH2 f ∧ MemIntervalH01 f
```

$H_0^1(-1,1)$ в заготовке — замыкание гладких функций с носителем в $(-1,1)$ по норме
$H^1$. Формулировки и определения менять нельзя; в `prompt.md` был набросок с
равномерной сходимостью и коррекцией среднего.

- Пакет: `output/aristotle-open-nodes` — весь проект (99 файлов) с закреплёнными
  версиями и `prompt.md`.
- Дата отправки: 2026-10-10.

## Что вернулось

- Обе теоремы доказаны; по `blueprint.md` из 99 отправленных файлов изменён один,
  `SobolevClosure`: определения и заголовки двух теорем совпадают с заготовкой,
  добавлены импорт `Involution.ComplexAC` и десять вспомогательных объявлений.
  Доказательство идёт через $K^{\perp\perp}=\overline K$ для подпространства пробных
  пар, а не по наброску из `prompt.md`; теорема о плотности гладких финитных функций
  в $L_2$ не понадобилась.
- Ответ `COMPLETE`, `lake build` проходит, `sorry` и `axiom` под `Involution/` нет;
  выписка `#print axioms`: обе теоремы дают
  `[propext, Classical.choice, Quot.sound]`.
- Архив: `output/aristotle-domain-result.tar.gz`; выписка — `answer/note.md`.
- Определения `IsTestPair` и `MemIntervalH01` приняты 11.10.2026: пользователь оставил
  решение за циклом, определение совпадает со стандартным замыканием
  $C_c^\infty(-1,1)$ по норме $H^1$ (идея `I1`).

## Сверка

- Заголовки объявлений: совпадают с отправленной заготовкой (`blueprint.md`); сервис
  подтверждает, что существующие формулировки и определения не менялись.
- `sorry` и `axiom`: нет.
- Локальная сборка: модуль собран с закреплёнными версиями (`blueprint.md`).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` (выписка сервиса).

## Источники сведений

`blueprint.md` (строка 7 и абзац о задаче 7), `output/aristotle-open-nodes-receipt.json`
(написан при отправке, поэтому говорит «ответа ещё нет»),
`output/aristotle-open-nodes/prompt.md`,
`output/aristotle-domain-result/aristotle-open-nodes_aristotle/ARISTOTLE_SUMMARY.md`,
идея `I1`, раздел «Область определения» постановки `Q`. Перенос — `report.md`.
Отдельной записи `C` у этого узла нет, поэтому цель задачи указана как `Q`.
