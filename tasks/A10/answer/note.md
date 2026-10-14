# A10: что вернул сервис

- Статус `COMPLETE_WITH_ERRORS`: заполнена одна из трёх целей.
- Доказана `principalOperator_boundedInverse` как сформулирована; аксиомы —
  `propext`, `Classical.choice`, `Quot.sound`.
- `reflectedMultiplier_re_inner_bound` ложна как сформулирована: нет требования
  вещественности `A`; отрицание доказано в `not_reflectedMultiplier_re_inner_bound`
  при $A=i\operatorname{sign}x$, $\alpha=0$. С гипотезой
  $\forall^{\mathrm{a.e.}}x,\ \overline{A x}=A x$ утверждение доказано как
  `reflectedMultiplier_re_inner_bound_of_real`.
- `resolvent_estimate` ложна как сформулирована: оценка с $s+1-\alpha$ неверна уже при
  $a=0$; отрицание доказано в `not_resolvent_estimate` при $s=10$ с использованием
  $\lVert G\rVert\le5/6$. Исправление — `resolvent_estimate_corrected`.
- Сервис также указал, что вторая посылка `prompt.md` неверна: из $|a(x)+a(-x)|\le2\alpha$
  не следует $|a(x)a(-x)|\le\alpha$ (пример $a(x)=5$, $a(-x)=-5$), поэтому
  `determinantInverse` в общем случае не применим.
- Файлы ответа: `Involution/ResolventAux.lean` (исправленные результаты и лемма об
  обратном операторе), `Involution/ResolventCounter.lean` (опровержения),
  `Involution/ResolventBound.lean` (три исходные формулировки, две с `sorry`).
  Из сводки сервиса: «A plain `lake build` fails because the lakefile's default target
  `Target` has no `Target.lean`. That was already the case before my changes.»
- Архив: `output/aristotle-resolvent-result.tar.gz`; распакованный ответ —
  `output/aristotle-resolvent-result/aristotle-resolvent_aristotle/`.
