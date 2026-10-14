---
id: C2
title: Обратимость главной матрицы
status: proved-lean
depends_on: []
lean_theorem: Involution.solve_system
final: false
---

**Условия.** $a,b\in\mathbb R$, $\lvert ab\rvert\le\kappa<1$.

**Утверждение.** $\det M=1-ab\ge1-\kappa>0$ и

$$
M^{-1}=\frac{1}{1-ab}\begin{pmatrix}1&-a\\ -b&1\end{pmatrix}.
$$

**Доказательство.** $ab\le\lvert ab\rvert\le\kappa$. Из $u+av=f$, $bu+v=g$ вычитанием
получаем $(1-ab)u=f-ag$, $(1-ab)v=g-bf$; обратное проверяется подстановкой.

**Следствие.** Система C1 принимает вид $-U''=\lambda M^{-1}U$. При ограниченном $a$
элементы $M^{-1}$ ограничены. Базисность из обратимости $M$ не следует (C11).

**Lean.** `principalMatrix_det`, `determinant_lower_bound`, `determinant_pos`,
`solve_system`, `reduction_under_product_bound`; равенство с `Matrix.inv` —
`principalMatrix_inv`; комплексный вариант — `Involution/Folding/ComplexReduction.lean`.
