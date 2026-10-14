---
id: A1
title: Постоянство при нулевой слабой производной
status: accepted
goal: C1
date: 2026-10-10
archive: output/aristotle-weak-result.tar.gz
---

# A1. Постоянство при нулевой слабой производной

Строка 1 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`94018f4e-bbff-42ca-b92b-d4529070e91a`, задача: `73290ec5-bda0-409d-94a9-38b54c15c57a`.

## Что отправлено

Цель — одно объявление, модуль `WeakConstant`:

```lean
theorem HasWeakDerivOn.ae_eq_const_of_zero
    {l r : ℝ} (hlr : l < r) {f : ℝ → ℂ}
    (hf : HasWeakDerivOn (Set.Ioo l r) f 0) :
    ∃ c : ℂ, f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo l r)] (fun _ => c)
```

- Пакет: `output/aristotle-weak-regularity` — весь проект с закреплёнными Lean
  `v4.35.0-rc4` и ревизией Mathlib из `lake-manifest.json` и текст запроса
  `prompt.md`; текст сохранён отдельно как `output/aristotle-weak-regularity-prompt.md`.
- Требования запроса: сохранить определения `HasWeakDerivOn` и `IsSmoothTestOn`, не
  добавлять аксиом, не заменять равенство почти всюду поточечным, вернуть исходник,
  команды проверки и `#print axioms`.
- Дата отправки: 2026-10-10.

## Что вернулось

- Статус сервиса `COMPLETE`, 100 % (`output/aristotle-weak-status.json`). Создан
  модуль `Involution/WeakConstant.lean`; в `Involution.lean` добавлен один импорт;
  сервис предпочитает Lean `v4.28.0` (поле `service_preferred_lean` квитанции).
- Архив: `output/aristotle-weak-result.tar.gz`; выписка — `answer/note.md`.
- Доказательство: нормированная гладкая bump-функция $\eta$, вычитание
  $(\int\varphi)\eta$ из произвольной пробной $\varphi$ и теорема Mathlib
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`; вывод — равенство почти
  всюду, непрерывность $f$ не предполагается.

## Сверка

- Заголовки объявлений: по квитанции принятие выборочное («selective adoption»), по
  `blueprint.md` формулировки сверены с отправленной заготовкой; формулировка
  перенесённого объявления совпадает с отправленной.
- `sorry` и `axiom`: нет (сводка сервиса).
- Локальная сборка: модуль собран в закреплённых версиях, `lake build` и
  `lake env lean` (`blueprint.md`, квитанция).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` (квитанция и
  `answer/note.md`).

## Источники сведений

`blueprint.md` (раздел «Задачи Aristotle», строка 1), `output/aristotle-weak-regularity-receipt.json`,
`output/aristotle-weak-status.json`, `output/aristotle-weak-regularity-prompt.md`,
запись `C1` (объявление названо в её абзаце «Lean»). Перенос описан в `report.md`.
