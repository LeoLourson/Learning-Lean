# A3: отчёт о переносе

- Куда перенесено: модуль `SchurMultiplier` (в текущем дереве
  `Involution/Model/SchurMultiplier.lean`); целевые объявления — `Involution.SchurBound.blockSum`,
  `Involution.SchurBound.of_hasSum`, `Involution.schurBound_separated_upper`,
  `Involution.schurBound_separated_lower`, `Involution.exists_weighted_extension`,
  `Involution.diagOp_norm_le`. В цепочке записи `C13` используются
  `SchurBound.product`, `SchurBound.of_hasSum`, `SchurBound.blockSum`,
  `schurBound_separated_upper`, `schurBound_separated_lower`,
  `exists_weighted_extension`.
- Правки после переноса: только стиль — `show` заменён на `change`, убран
  неиспользуемый `CompleteSpace`, переименован неиспользуемый биндер.
- Сверено: определения и формулировки совпадают с заготовкой; `sorry`, `admit`,
  `axiom` отсутствуют; модуль собран локально, аудит аксиом пройден.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-schur-result.tar.gz`.
