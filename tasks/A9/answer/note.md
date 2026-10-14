# A9: что вернул сервис

- `Involution.halfSlope_no_riesz_eigenbasis` доказана как сформулирована;
  `halfSlope_quasimodes` и `rieszEigenbasis_count` доказаны под исходными
  формулировками; определения не менялись, линтеры не подавлялись, `lake build`
  проходит без ошибок и предупреждений.
- `#print axioms Involution.halfSlope_no_riesz_eigenbasis` —
  `[propext, Classical.choice, Quot.sound]`.
- Замечание сервиса: в загруженном проекте `lakefile.toml` объявлял цель `Target`, но
  файла `Target.lean` не было, поэтому `lake build` не запускался; сервис добавил
  свой `Target.lean` с проверкой аксиом. Этот файл не перенесён.
- Добавленные модули: `Involution/RieszEigenCount.lean`
  (`RieszBasis.card_le_of_finiteRank_approx`), `Involution/HalfSlopeProfile.lean`
  (`halfSlopeS`, `halfSlopeU`, `halfSlopeCut`, `halfSlopeZ_equation`,
  `halfSlopeR_norm_le`, `halfSlopeZ_norm_ge`).
- Архив: `output/aristotle-halfslope-result.tar.gz`; распакованный ответ —
  `output/aristotle-halfslope-result/aristotle-halfslope_aristotle/`.
