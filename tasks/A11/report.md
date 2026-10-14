# A11: отчёт о переносе

- Куда перенесено: модуль `PhaseSelection` (в текущем дереве
  `Involution/Setup/PhaseSelection.lean`). Объявления: `Involution.exists_phase_value`,
  `Involution.convex_phase_values`, `Involution.exists_odd_phase`; запись `C19` называет
  все три и относит к утверждению 3.
- Правки после переноса: `public import Mathlib` заменён четырьмя импортами модулей
  Mathlib; остальной текст не менялся.
- Сверено: заголовки трёх теорем совпадают с отправленной заготовкой; `sorry` и `axiom`
  отсутствуют; модуль собран локально, аудит аксиом пройден.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-phase-result.tar.gz`.
- Пробел: квитанции и статуса в `output/` нет, поэтому идентификатор задачи прогона
  известен только из сводки ответа, а номер проекта — из `blueprint.md`.
