---
id: A10
title: Обратимость T_a и оценка резольвенты (утверждение 2 записи C17)
status: accepted
goal: C17
date: 2026-10-12
archive: output/aristotle-resolvent-result.tar.gz
---

# A10. Обратимость $T_a$ и оценка резольвенты $L_a+s$

Строка 9 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`4fa6750a-179c-4643-a25c-4fd9f13cfe54`, задача: `94d2c2e1-2336-496c-90ef-d1768192ed06`.

## Что отправлено

Три `sorry` заготовки `ResolventBound` — утверждение 2 записи `C17`:

```lean
theorem Involution.reflectedMultiplier_re_inner_bound (A : IntervalLInfinity) (α : ℝ)
    (hα : ∀ᵐ x ∂intervalMeasure, ‖A x + A (-x)‖ ≤ 2 * α) (W : IntervalL2) :
    |(inner ℂ W (reflectedMultiplier A W)).re| ≤ α * ‖W‖ ^ 2

theorem Involution.principalOperator_boundedInverse (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α) :
    ∃ Tinv : IntervalL2 →L[ℂ] IntervalL2,
      Tinv.comp (principalOperator (realIntervalCoefficient a ha)) = 1 ∧
      (principalOperator (realIntervalCoefficient a ha)).comp Tinv = 1 ∧
      ‖Tinv‖ ≤ (1 - α)⁻¹

theorem Involution.resolvent_estimate (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α)
    (s : ℝ) (hs : 0 < s) (h : IntervalL2) : …
```

Формулировки менять нельзя, в библиотеку заготовка не входит. Заготовка была собрана
локально в закреплённых версиях перед отправкой (три предупреждения
`declaration uses sorry`). Задача отправлена по прямому запросу пользователя;
параллельная локальная формализация остановлена, потому что шла слишком долго.

- Пакет: `output/aristotle-resolvent` (весь проект с закреплёнными версиями,
  `prompt.md` и собранный `.lake`).
- Дата отправки: 2026-10-12.

## Что вернулось

- Статус `COMPLETE_WITH_ERRORS`. Доказана `principalOperator_boundedInverse`
  (через `exists_inverse_of_coercive`). Две другие формулировки заготовки ложны, и
  сервис доказал их отрицания в `ResolventCounter.lean`: в
  `reflectedMultiplier_re_inner_bound` пропущена вещественность коэффициента
  (контрпример $A=i\operatorname{sign}x$, $\alpha=0$), а оценка
  $\lVert G\rVert/(s+1-\alpha)$ в `resolvent_estimate` неверна уже при $a=0$
  ($\lambda_1=\pi^2/4>1$).
- `Involution/Estimates/ResolventAux.lean` содержит исправленные результаты:
  `reflectedMultiplier_re_inner_bound_of_real`, `resolvent_estimate_corrected`
  (однозначная разрешимость при $s\ge0$ и оценка $\lVert f\rVert\le\lVert G\rVert\lVert h\rVert/(1-\alpha)$)
  и `exists_inverse_of_coercive`.
- Архив: `output/aristotle-resolvent-result.tar.gz`; выписка — `answer/note.md`.

## Сверка

- Заголовки объявлений: формулировки заготовки не менялись; заголовок
  `principalOperator_boundedInverse` совпадает с отправленным.
- `sorry` и `axiom`: в перенесённых модулях нет; версия `Involution/Estimates/ResolventBound.lean` с двумя
  `sorry` осталась в архиве, `ResolventCounter.lean` в библиотеку не входит.
- Локальная сборка: пройдена; в библиотеке вторая оценка (3) доказана локально теоремой
  `resolvent_ray_estimate`, ошибка записи `C17` исправлена 12.10.2026.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — для
  `principalOperator_boundedInverse`, `resolvent_estimate_corrected`,
  `resolvent_ray_estimate` (запись `C17`, выписка сервиса для доказанной теоремы).

## Источники сведений

`blueprint.md` (строка 9 и абзацы о задаче 9), `output/aristotle-resolvent-receipt.json`
(написан при отправке), `output/aristotle-resolvent/prompt.md`,
`output/aristotle-resolvent-result/aristotle-resolvent_aristotle/ARISTOTLE_SUMMARY.md`,
запись `C17` (абзацы «Граница точности», «Lean», «Соответствие формализации»).
Перенос — `report.md`.
