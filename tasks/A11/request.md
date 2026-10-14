---
id: A11
title: Выбор гладкой нечётной фазы (утверждение 3 записи C19)
status: accepted
goal: C19
date: 2026-10-13
archive: output/aristotle-phase-result.tar.gz
---

# A11. Выбор гладкой нечётной фазы $\psi$

Строка 10 таблицы «Задачи Aristotle» исходного `blueprint.md`. Проект Aristotle:
`b3851f6d-14d1-4885-bfd0-5a52e856384f`; задача прогона:
`145f6c66-cf18-4701-8b42-30a35facd544` (заголовок `ARISTOTLE_SUMMARY.md` ответа).

## Что отправлено

Три `sorry` заготовки `PhaseSelection`: `exists_phase_value`, `convex_phase_values` и
итоговая `exists_odd_phase` (утверждение 3 записи `C19`). Формулировку итоговой теоремы
менять нельзя, две вспомогательные разрешено переформулировать или заменить. Отдельный
проект, зависящий только от Mathlib: `Involution.lean`, заготовка
`Involution/PhaseSelection.lean`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `prompt.md`. Заготовка собрана локально в закреплённых версиях (три
предупреждения `declaration uses sorry`). Задача отправлена командой `/day`; по
действующему правилу отправка допускается только по прямому запросу пользователя.

- Пакет: `output/aristotle-phase`.
- Дата отправки: 2026-10-13.

## Что вернулось

- Статус `COMPLETE`: заголовки трёх теорем совпадают с заготовкой, `sorry` и `axiom`
  нет. Добавлены три вспомогательные леммы `phase_lt_two_iff`, `exists_phase_u`,
  `quad_neg_ordConnected`; две исходные вспомогательные формулировки сохранены.
- Вместо покрытия и разбиения единицы из наброска использована теорема Mathlib
  `exists_contMDiffMap_forall_mem_convex_of_local_const`; $\psi$ строится как
  $g(x)-g(-x)$ и равна нулю при $\lvert x\rvert<\delta$.
- Выписка сервиса: `#print axioms Involution.exists_odd_phase` —
  `[propext, Classical.choice, Quot.sound]`; сборка даёт одно стилевое предупреждение о
  заголовке файла без строки copyright, заголовок не менялся.
- Архив: `output/aristotle-phase-result.tar.gz`; выписка — `answer/note.md`.

## Сверка

- Заголовки объявлений: по `blueprint.md` заголовки трёх теорем совпадают с заготовкой.
- `sorry` и `axiom`: нет.
- Локальная сборка: пройдена; при переносе `public import Mathlib` заменён четырьмя
  импортами модулей Mathlib, остальной текст не менялся (`blueprint.md`).
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` — для
  `exists_odd_phase` и её специализаций (запись `C19`, выписка сервиса).

## Источники сведений

`blueprint.md` (строка 10 и абзац о задаче 10), `output/aristotle-phase/prompt.md`,
`output/aristotle-phase-result/aristotle-phase_aristotle/ARISTOTLE_SUMMARY.md`, запись
`C19`. Отдельного файла квитанции или статуса в `output/` нет — это пробел исходных
данных; номер проекта и факт принятия известны только из `blueprint.md`. Перенос —
`report.md`.
