# A7: что вернул сервис

- Первый прогон (`63224d6a-5993-4188-aa64-9beefd477ff0`): сводка —
  «I reached this run's time limit. Send "continue" to pick up where I left off.»;
  недоказанной осталась `Involution.MMData.exists_cuts` в `Involution/MMGoodCut.lean`.
- Продолжение (`ecce65e9-e25e-4af0-8613-29225712bd50`): `exists_cuts` доказана как
  сформулирована; `exists_bracket_basis_of_subordinate_general`, `MMCore` и другие
  существующие формулировки не менялись, аксиом нет, `lake build` проходит,
  `#print axioms Involution.exists_bracket_basis_of_subordinate_general` —
  `[propext, Classical.choice, Quot.sound]`.
- Добавлено: `Involution/MMWindowCut.lean` (`window_cut`, `isUnit_of_det`,
  `det_lower_of_isUnit`, `min_modulus_segment` и др.), `Involution/MMGoodCut.lean`
  (`finite_of_count`, `exists_sparse_window`, `exists_cuts`); в `MMWindow` исправлены
  два шага доказательства `inv_one_sub_K_eq` без изменения формулировок; `MMWindow` и
  `MMWindowCut` добавлены в импорты `Involution.lean`.
- Архивы: `output/aristotle-markus-result.tar.gz` (первый прогон),
  `output/aristotle-markus-result2.tar.gz` (итог); распакованные ответы —
  `output/aristotle-markus-result/aristotle-markus_aristotle/` и
  `output/aristotle-markus-result2/output-final_aristotle/`.
