# A2: отчёт о переносе

- Куда перенесено: модуль `ModelBasis` (в текущем дереве
  `Involution/Model/ModelBasis.lean`). Объявления: `Involution.constantModel_orthonormal`,
  `Involution.constantModel_dense_span`, `Involution.constantModelHilbertBasis`,
  `Involution.constantModelRieszBasis`; запись `C3` называет первые два.
- Импорт модуля зарегистрирован в `Involution.lean`.
- Правки после переноса: не зафиксированы; принятие выборочное, ревизии совпали.
- Сверено: заголовки двух целей совпадают с отправленной заготовкой; `sorry`,
  `admit`, `axiom` отсутствуют; модуль собран локально, аудит аксиом пройден.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-model-result.tar.gz`.
