# A11: что вернул сервис

- Заполнены все `sorry` в `Involution/PhaseSelection.lean`; `exists_odd_phase` доказана
  как сформулирована, две вспомогательные леммы сохранены под исходными
  формулировками; `lake build` проходит, `sorry`, `admit`, `axiom` нет.
- `#print axioms Involution.exists_odd_phase` — `[propext, Classical.choice, Quot.sound]`.
- Добавленные леммы: `phase_lt_two_iff` (замена $u=e^t$), `exists_phase_u` (четыре
  случая $q=0$, $p=0$, $pq<0$, $pq>0$), `quad_neg_ordConnected` (множество
  $\{u>0: qu^2-2u+p<0\}$ без промежутков).
- Отличие от наброска: вместо покрытия и разбиения единицы используется Mathlib-теорема
  `exists_contMDiffMap_forall_mem_convex_of_local_const`; далее $\psi(x)=g(x)-g(-x)$.
- Из сводки сервиса: «The build gives one warning: the style linter flags the original
  file header because it has no copyright line. I didn't change the header.»
- Архив: `output/aristotle-phase-result.tar.gz`; распакованный ответ —
  `output/aristotle-phase-result/aristotle-phase_aristotle/`.
- Квитанции и файла статуса для этой задачи в `output/` нет.
