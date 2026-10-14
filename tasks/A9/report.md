# A9: отчёт о переносе

- Куда перенесено: модули `HalfSlope`, `HalfSlopeProfile`, `RieszEigenCount` (в
  текущем дереве `Involution/Estimates/`). Объявления:
  `Involution.halfSlope_no_riesz_eigenbasis`, `Involution.halfSlope_quasimodes`,
  `Involution.rieszEigenbasis_count`, `Involution.RieszBasis.card_le_of_finiteRank_approx`;
  запись `C18` называет первые три и профильные леммы.
- Правки после переноса: три модуля перенесены без правок; добавленный сервисом
  `Target.lean` не перенесён.
- Сверено: определения `halfSlopeCoefficient`, `halfSlopeClass` и заголовки трёх
  теорем совпадают с заготовкой; `sorry` и `axiom` отсутствуют; модули собраны
  локально, аудит аксиом пройден.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-halfslope-result.tar.gz`.
