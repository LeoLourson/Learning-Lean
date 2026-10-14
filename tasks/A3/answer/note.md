# A3: что вернул сервис

- Заполнены все 20 `sorry` в `Involution/SchurMultiplier.lean`; сравнение с исходным
  коммитом: удалены только строки `sorry`.
- `#print axioms` (выписка сервиса):
  `SchurBound.blockSum`, `SchurBound.of_hasSum`, `schurBound_separated_upper`,
  `schurBound_separated_lower`, `exists_weighted_extension`, `diagOp_norm_le` —
  у каждого `[propext, Classical.choice, Quot.sound]`.
- Из сводки сервиса: «the only lines removed are the `sorry` lines, so no definition
  or theorem statement changed… There are no axioms and no `sorry`/`admit`. None of
  the statements turned out to be false.»
- Замечание сервиса: остаются предупреждения линтера об неиспользуемых
  `CompleteSpace H` в исходных формулировках и о неиспользуемом `hC0` в
  `SchurBound.of_hasSum`; подавлять их сервис не стал, чтобы не менять сигнатуры.
- Архив: `output/aristotle-schur-result.tar.gz`; распакованный ответ —
  `output/aristotle-schur-result/aristotle-schur_aristotle/`.
