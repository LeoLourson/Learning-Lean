---
id: C10
title: Калибровка на всём интервале
status: proved-lean
depends_on: [C5, C8]
lean_theorem: Involution.signDefinite_perturbed_riesz_model
final: false
---

**Тождество.** Пусть $r,w\in W^2_\infty$, $rw=1$ п.в., $a,b\in L_\infty$ и
$b(x)r(x)=a(x)r(-x)$ п.в. Тогда $T_aM_r=M_rT_b$ и для каждого $f$ из области

$$
L_a(rf)=r\bigl(L_bf+T_bB_0f\bigr),\qquad B_0f=-2wr'f'-wr''f.
$$

Умножение на $r$ сохраняет слабую область Дирихле в обе стороны, поэтому складывание
интервала и условия склейки не нужны.

**Знакопостоянный случай.** Если $a\in W^2_\infty$ вещественна, $0<m\le\lvert a\rvert\le M$
и $\lvert a(x)a(-x)\rvert\le\kappa<1$, то знак $\sigma$ постоянен, и при
$r=\sqrt{\lvert a\rvert}$ коэффициент $b(x)=\sigma\sqrt{a(x)a(-x)}$ чётен,
$\lvert b(x)b(-x)\rvert=\lvert a(x)a(-x)\rvert\le\kappa$. К $L_b$ применимо C5.

**Подчинённость.** Энергетическое тождество даёт
$\lVert f'\rVert^2\le\lVert f\rVert\lVert f''\rVert$; из $f=G(-f'')$ следует
$\lVert f\rVert\le\lVert G\rVert\lVert f''\rVert$, а из C8 —
$\lVert f''\rVert\le\lVert T_b^{-1}\rVert\lVert L_bf\rVert$. Поэтому

$$
\lVert T_bB_0f\rVert\le C\,\lVert f\rVert^{1/2}\lVert L_bf\rVert^{1/2},\qquad
C=\lVert T_b\rVert\bigl(2\lVert w\rVert\lVert r'\rVert+\lVert w\rVert\lVert r''\rVert\lVert G\rVert^{1/2}\bigr)\lVert T_b^{-1}\rVert^{1/2}.
$$

**Lean.** `Involution/Model/GaugeSimilarity.lean`: `principalOperator_gauge`, `gauge_similarity`,
`firstWeakDeriv_norm_sq_le`, `gaugeLowerOrder_norm_le`, `gaugePerturbation_subordinate`,
`real_coefficient_constant_sign`, `signDefinite_gauge_reduction`; сводка —
`signDefinite_perturbed_riesz_model`.
