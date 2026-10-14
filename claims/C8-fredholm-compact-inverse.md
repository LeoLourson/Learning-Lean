---
id: C8
title: Весь класс постановки: факторизация и компактный обратный
status: proved-lean
depends_on: [C4]
lean_theorem: Involution.productBound_compact_inverse
final: true
---

**Условия.** Вещественный $a\in L_\infty(-1,1)$, $\lvert a(x)a(-x)\rvert\le\kappa<1$ п.в.

**Утверждение.** $L_a=T_a(-D^2)$ на области, оператор $T_a$ ограниченно обратим,

$$
T_a^{-1}=d\,(I-aR),\qquad d(x)=\frac{1}{1-a(x)a(-x)},
$$

и $K_a=GT_a^{-1}$ — компактный инъективный оператор, обратный к $L_a$. Нуль — не
собственное значение; при $\lambda\ne0$ равенство $L_af=\lambda f$ равносильно
$K_af=\lambda^{-1}f$; собственные подпространства конечномерны; для каждого
$\lambda\in\mathbb C$ либо $\lambda$ — собственное значение, либо задача
$(L_a-\lambda)f=g$ однозначно разрешима на области для каждого $g\in L_2$.

**Доказательство.** $(aR)(aR)f=a(x)a(-x)f$, откуда
$(I-aR)(I+aR)=(I+aR)(I-aR)=1-a(x)a(-x)$; функция $d$ чётна и ограничена числом
$1/(1-\kappa)$. Остальное следует из компактности $G$ и альтернативы Фредгольма.

**Lean.** `Involution/Model/CompactInverse.lean`: `variableSobolevOperator_eq_principal`,
`principalOperatorInverse_left`, `principalOperatorInverse_right`, `variableGreen_compact`,
`variableOperator_solution_iff`, `variableOperator_eigen_iff`,
`variableOperator_finiteDimensional_eigenspace`, `variableOperator_fredholm`; для
вещественного коэффициента — `productBound_compact_inverse`, `productBound_fredholm`.

**Граница $\kappa<1$.** При $a\equiv1$ каждая функция $\sin(m\pi x)$ лежит в ядре
(`unit_coefficient_sine_kernel`): компактного обратного нет. Синусы и косинусы C3
остаются при этом ортогональным базисом из собственных функций.

**Границы.** Полнота и базисность из C8 не следуют (C11, C12).
