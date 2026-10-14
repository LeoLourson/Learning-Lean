---
id: C4
title: Пример $a(x)=x/2$
status: proved-lean
depends_on: [C1, C2, I5]
lean_theorem: Involution.oddCoefficient_unitary_multiplication
final: true
---

**Утверждение.** $a(x)a(-x)=-x^2/4$, $\lvert a(x)a(-x)\rvert\le1/4$, $\det M=1+x^2/4\ge1$.

**Смысл.** Редукция C1–C2 работает без диагонализации через $\sqrt{a(x)a(-x)}$.
Базисность для этого коэффициента не установлена.

**Lean.** `odd_coefficient_product`, `odd_coefficient_determinant`,
`odd_coefficient_product_bound`, `odd_coefficient_determinant_ge_one`.

**Нечётный коэффициент.** Пусть $a\in L_\infty(-1,1;\mathbb C)$ и $a(-x)=-a(x)$ п.в.;
оценка произведения не нужна. Положим $P_\pm=(I\pm R)/2$ и $U=P_++iP_-$. Тогда $U$
унитарен в $L_2$, сохраняет $H^2$ и слабую область Дирихле, и для каждого $f\in H^2$

$$
UL_af=(1+ia)\bigl(-(Uf)''\bigr).
$$

Уравнение $L_af=\lambda f$ равносильно уравнению $(1+ia)(-Z'')=\lambda Z$ для $Z=Uf$, то
есть задаче $-Z''=\lambda\rho Z$ с комплексным весом $\rho=1/(1+ia)$.

**Доказательство.** $U=\alpha I+\beta R$ с $\alpha=(1+i)/2$, $\beta=(1-i)/2$; обратный
оператор — $\beta I+\alpha R$, так как $2\alpha\beta=1$ и $\alpha^2+\beta^2=0$. Чётная и
нечётная части ортогональны, поэтому $\lVert Uf\rVert=\lVert f\rVert$. Умножение на
нечётную $a$ антикоммутирует с отражением: $R(ag)=-aRg$. Отсюда

$$
U(g+aRg)=\alpha g+\beta Rg+a(\alpha Rg-\beta g)=Ug+ia\,Ug,
$$

поскольку $i\alpha=-\beta$ и $i\beta=\alpha$. Вторая слабая производная коммутирует с $R$
и потому с $U$; остаётся подставить $g=-f''$ в $L_af=g+aRg$ (C8).

**Lean.** `Involution/Estimates/OddCoefficient.lean`: `parityRotation`, `parityRotationInv_parityRotation`,
`parityRotation_norm`, `boundedMultiplier_reflect_odd`, `parityRotation_principalOperator`,
`memDirichletH2_parityRotation`, `secondWeakDeriv_parityRotation`,
`oddCoefficient_unitary_multiplication`, `oddCoefficient_eigen_iff`.

**Границы.** Базисность корневых функций для нечётного $a$ не доказана. Сектор
собственных значений и полнота — C17. При $a=x/2$ базиса Рисса из собственных функций
нет (C18); численный расчёт — `claims/I*.md`, I5.
