# A5: что вернул сервис

- Заполнены все три `sorry` в `Involution/SparseCuts.lean`; `lake build` проходит,
  `sorry`, `admit`, `axiom` нет, формулировки не менялись.
- `#print axioms` (выписка сервиса):
  `exists_similarity_fixedPoint`, `exists_sparse_cuts`,
  `card_le_of_finiteRank_approx` — у каждой `[propext, Classical.choice, Quot.sound]`.
- Добавлена одна вспомогательная лемма `exists_gap_point`.
- Замечание сервиса: «the build prints two linter warnings because `hω` (positivity of
  `ω`) and `hC₀` (`0 ≤ C₀`) in `exists_sparse_cuts` are never used. That theorem
  therefore holds without them. I left them in place because you asked me not to change
  the statements.»
- Архив: `output/aristotle-cuts-result.tar.gz`; распакованный ответ —
  `output/aristotle-cuts-result/aristotle-cuts_aristotle/`.
