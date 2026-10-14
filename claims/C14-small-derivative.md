---
id: C14
title: Знакопостоянный коэффициент с малой производной
status: proved-lean
depends_on: [C10, C13]
lean_theorem: Involution.tiltedCoefficient_bracket_basis
final: true
---

**Условия.** Вещественный $a\in W^2_\infty(-1,1)$, $0<m\le\lvert a\rvert\le M$,
$\lvert a(x)a(-x)\rvert\le\kappa<1$, $\lvert a'\rvert\le\varepsilon$ п.в. и

$$
320\,(1+\sqrt\kappa)\,\varepsilon<\pi\,(1-\sqrt\kappa)\,m.
$$

Чётность не предполагается.

**Утверждение.** Существует последовательность конечномерных подпространств $W_k$
слабой области Дирихле с $L_aW_k\subset W_k$, образующая базис Рисса со скобками в
$L_2(-1,1)$. Каждое $W_k$ порождено корневыми векторами ограничения $L_a$ на $W_k$.

**Доказательство.** Калибровка C10 даёт $L_a(rf)=r(L_bf+Sf)$ с $r=\sqrt{\lvert a\rvert}$,
чётным $b=\sigma\sqrt{a(x)a(-x)}$ и $S=T_bB_0$. В каналах чётности положим
$W=(1\pm b)^{-1/2}$, $V=W^{-1}$. Оператор $K=WGW$ компактен, симметричен и имеет
гильбертов базис собственных векторов $u_i$, $Ku_i=\mu_iu_i$,
$\mu_i=\lVert(GWu_i)'\rVert^2>0$, причём $L_b=VK^{-1}V^{-1}$. В координатах $V^{-1}$
получаем диагональный оператор $K^{-1}$ с $\lambda_i=1/\mu_i$ и $B=WT_bB_0GW$.

1. *Счётная функция.* Срезка спектрального ряда $G=F_N+E_N$ с
   $\operatorname{rank}F_N\le2N$, $\lVert E_N\rVert\le(N\pi)^{-2}$ даёт $K=WF_NW+WE_NW$.
   Если $\lVert W\rVert^2(N\pi)^{-2}<t^{-2}$, то собственных значений $\mu_i\ge t^{-2}$ не
   больше $2N$: иначе в их линейной оболочке нашёлся бы ненулевой вектор из ядра
   $WF_NW$. Отсюда $N(t)\le(2\nu/\pi)t+2$, $\nu=(1-\sqrt\kappa)^{-1/2}$. Минимакс не
   используется.
2. *Возмущение.* $\lVert(GWg)'\rVert^2=\langle Kg,g\rangle$ и
   $\lVert GWg\rVert\le\lVert V\rVert\lVert Kg\rVert$, поэтому
   $\lVert Bg\rVert\le b_1\langle Kg,g\rangle^{1/2}+b_0\lVert Kg\rVert$ с
   $b_1=\nu(1+\sqrt\kappa)\cdot2\lVert wr'\rVert_\infty\le\nu(1+\sqrt\kappa)\varepsilon/m$.
3. *Малость.* При $c_2=2\nu/\pi$ неравенство $160b_1c_2<1$ равносильно условию записи.
4. C13 даёт блоки $V_k$; обратное подобие $M_rV$ переносит их в $W_k$.

**Общая форма.** Достаточно веса $r\in W^2_\infty$ с ограниченным обратным, сохраняющего
слабую область Дирихле, для которого $b(x)r(x)=a(x)r(-x)$ с вещественным чётным $b$,
$\lvert b(x)b(-x)\rvert\le\kappa<1$ и $\lvert r'/r\rvert\le c$,
$640(1+\sqrt\kappa)c<\pi(1-\sqrt\kappa)$. Коэффициент $a$ здесь может быть комплексным
классом $L_\infty$.

**Пример.** $a(x)=1/2+x/1000$: $m=499/1000$, $\kappa=1/4$, $\varepsilon=1/1000$; условие
малости $0{,}48<\pi\cdot0{,}2495$ выполнено. Коэффициент не чётен, C5 неприменимо.

**Lean.** `Involution/Model/EigenvalueCounting.lean` (`spectralGreen_eq_diagOp`,
`green_sandwich_eigen_count`), `Involution/Model/GaugeOperators.lean` (`greenDeriv`, `gaugeLowerOp`,
`parityMultiplierSum_symmetric`, `principalOperator_weight`),
`Involution/Estimates/SignDefiniteBrackets.lean` (`RieszBasisWithBrackets.map`, `signDefinite_gauge_data`,
`bracket_basis_of_gauge_core`, `bracket_basis_of_gauge`, `signDefinite_bracket_basis`),
`Involution/Estimates/BracketCorollaries.lean` (`invariant_block_rootVectors`,
`signDefinite_bracket_rootVectors`, `tiltedCoefficient_bracket_basis`). Теорема
`bracket_basis_of_gauge_core` принимает абстрактную теорему о возмущениях как гипотезу
и малость не использует; на неё опирается C16.

**Границы.** Постоянная $320$ не оптимальна. Коэффициенты с нулями и сменой знака не
охвачены.
