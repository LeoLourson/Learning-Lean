---
id: C1
title: Сведение к двум компонентам
status: proved-lean
depends_on: []
lean_theorem: Involution.memDirichletH2_iff_h2_and_h01
final: false
---

**Условия.** $y\in H^2(-1,1)\cap H_0^1(-1,1)$, коэффициент как в постановке.

**Утверждение.** Для $U=(u,v)^{T}=(y(x),y(-x))^{T}$ на $(0,1)$

$$
M U''=-\lambda U,\qquad
M=\begin{pmatrix}1&a(x)\\ a(-x)&1\end{pmatrix},
$$

с условиями $U(1)=0$, $u(0)=v(0)$, $u'(0)+v'(0)=0$. Обратно, две $H^2$-функции с этими
условиями склеиваются в функцию из $H^2(-1,1)$ с нулевыми следами. Нормы связаны равенством

$$
\int_0^1\bigl(\lvert u\rvert^2+\lvert v\rvert^2\bigr)\,dx=\int_{-1}^{1}\lvert y\rvert^2\,dx.
$$

**Доказательство.** Записываем уравнение в точках $x$ и $-x$; $v'(x)=-y'(-x)$,
$v''(x)=y''(-x)$. Непрерывность следов $y$, $y'$ в нуле даёт условия склейки.

**Lean.** Слабые производные, их единственность и отражение — `Involution/Setup/WeakDerivative.lean`;
$H^2$ через две слабые производные — `Involution/Setup/IntervalSobolev.lean`; следы — `Involution/Setup/IntervalTrace.lean`.
Регулярные представители: `MemIntervalH2.exists_regular_pair`,
`regular_pair_representatives_unique`; они опираются на
`HasWeakDerivOn.ae_eq_const_of_zero` и `hasWeakDerivOn_of_absolutelyContinuous`.
Склейка: `memIntervalH2_intervalJoin`, `weak_derivatives_fold`,
`memDirichletH2_reflectedJoin`. Унитарное складывание $L_2(-1,1)\to L_2(0,1)^2$ с
евклидовой нормой пары: `l2FoldingEquiv`, обратное — `l2Unfold`. Эквивалентность областей:
`memDirichletH2_iff_fold`, `memFoldedDirichletH2_iff_unfold`. Редукция оператора с
коэффициентом класса $L_\infty$ и перенос уравнения $(L_a-\lambda)f=g$ в обе стороны:
`variableSobolevOperator_unitary_reduction` в `Involution/Folding/FoldedOperator.lean`. Точечные значения
вторых производных нигде не используются.
