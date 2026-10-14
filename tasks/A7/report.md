# A7: отчёт о переносе

- Куда перенесено: модуль `MarkusMatsaev` и 17 модулей `MM*` (в текущем дереве —
  `Involution/Estimates/MarkusMatsaev.lean` и `Involution/Estimates/MM*.lean`;
  список: `MMCompact`, `MMContour`, `MMCore`, `MMCuts`, `MMEstimates`, `MMGoodCut`,
  `MMMinModulus`, `MMOperators`, `MMPointwise`, `MMRiesz`, `MMRieszBasis`, `MMScalar`,
  `MMSideInt`, `MMTotal`, `MMWindow`, `MMWindowCut`, `MMWoodbury`). Всего 4881 строка
  по квитанции.
- Главное объявление: `Involution.exists_bracket_basis_of_subordinate_general`;
  из него в записи `C16` идут `signDefinite_bracket_basis_general`,
  `markusMatsaevStatement`, `signDefinite_bracket_basis_W2`.
- Правки после переноса: только стиль — устаревшие имена лемм, длинные строки,
  неиспользуемый аргумент `simp`, три вызова `simp` заменены на `simp only`; по
  квитанции — отключение стилевых линтеров (длинные строки в 7 модулях, несколько
  целей в 1 модуле, гибкая тактика в 3 объявлениях). Формулировки не менялись.
- Сверено: формулировка цели и предсуществовавшие файлы проекта не менялись; `sorry`
  и `axiom` отсутствуют; сборка и аудит аксиом пройдены.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архивы: `output/aristotle-markus-result.tar.gz`,
  `output/aristotle-markus-result2.tar.gz`.
