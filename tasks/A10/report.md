# A10: отчёт о переносе

- Куда перенесено: `ResolventAux` без правок (в текущем дереве
  `Involution/Estimates/ResolventAux.lean`) и теорема
  `Involution.principalOperator_boundedInverse` в модуль `ResolventBound`
  (`Involution/Estimates/ResolventBound.lean`). Локально там же доказана
  `resolvent_ray_estimate` — вторая оценка (3) записи `C17`.
- Осталось в архиве: `ResolventCounter.lean` (опровержения двух формулировок) и
  версия `Involution/Estimates/ResolventBound.lean` с двумя `sorry`; в библиотеку они не входят.
- Правки после переноса: формулировки не менялись; ошибка записи `C17` (оценка
  $\lVert G\rVert/(s+1-\alpha)$) исправлена 12.10.2026 в самой записи, постоянная
  записана через $\lVert T_a\rVert$.
- Сверено: заголовок доказанной теоремы совпадает с отправленной заготовкой; в
  перенесённых модулях нет `sorry` и `axiom`; сборка и аудит аксиом пройдены.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` для
  `principalOperator_boundedInverse`, `resolvent_estimate_corrected`,
  `resolvent_ray_estimate`.
- Архив: `output/aristotle-resolvent-result.tar.gz`.
