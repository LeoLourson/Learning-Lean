# A5: отчёт о переносе

- Куда перенесено: модуль `SparseCuts` (в текущем дереве
  `Involution/Model/SparseCuts.lean`). Объявления: `Involution.exists_similarity_fixedPoint`,
  `Involution.exists_sparse_cuts`, `Involution.card_le_of_finiteRank_approx`; они
  названы в абзаце «Lean» записи `C13`.
- Правки после переноса: переименованы два неиспользуемых биндера; формулировки не
  менялись. Гипотезы `hω` и `hC₀` оставлены, хотя теорема верна без них.
- Сверено: заголовки и формулировки совпадают с отправленной заготовкой; `sorry`,
  `admit`, `axiom` отсутствуют; модуль собран локально, аудит аксиом пройден.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- Архив: `output/aristotle-cuts-result.tar.gz`.
