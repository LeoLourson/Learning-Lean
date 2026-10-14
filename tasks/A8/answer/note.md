# A8: что вернул сервис

- Обе теоремы доказаны без `sorry` и новых аксиом; определения `IsTestPair` и
  `MemIntervalH01` не менялись, `lake build` проходит.
- `#print axioms` (выписка сервиса):
  `Involution.memIntervalH01_iff_trace` и `Involution.memDirichletH2_iff_h2_and_h01` —
  `[propext, Classical.choice, Quot.sound]`.
- Путь доказательства не совпал с наброском запроса: вместо плотности гладких
  финитных функций в $L_2$ использовано $K^{\perp\perp}=\overline K$
  (`Submodule.orthogonal_orthogonal_eq_closure`). Добавлены `inner_add_inner_eq_boundary`,
  `testPairSubmodule`, `approx_iff_mem_closure`, `hasIntervalWeakDeriv_of_mem_orthogonal`,
  `mem_orthogonal_of_boundary`, `boundary_combination_eq_zero_of_mem_closure` (всего
  десять вспомогательных объявлений по `blueprint.md`) и импорт `Involution.ComplexAC`.
- Из сводки сервиса: «I proved both theorems… I didn't change any existing statement or
  definition, including `IsTestPair` and `MemIntervalH01`. The full `lake build`
  succeeds, and there are no `sorry`s or `axiom` declarations anywhere under
  `Involution/`.»
- Архив: `output/aristotle-domain-result.tar.gz`; распакованный ответ —
  `output/aristotle-domain-result/aristotle-open-nodes_aristotle/`.
