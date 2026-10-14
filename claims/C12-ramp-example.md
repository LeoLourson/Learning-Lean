---
id: C12
title: Пример в классе $W^1_\infty$: $a(x)=\max(x,0)$
status: proved-lean
depends_on: [C11]
lean_theorem: Involution.ramp_no_riesz_eigenbasis
final: true
---

**Условия.** $a$ липшицева с константой $1$, вещественна, $a(x)a(-x)=0$: выполнены все
условия постановки с $\kappa=0$.

**Утверждение.** Не существует базиса Рисса пространства $L_2(-1,1)$ из собственных
функций $L_a$.

**Доказательство.**

1. *Область без собственных значений.* Пусть $L_ay=\lambda y$, $y\ne0$,
   $\lvert\lambda\rvert\ge1/8$ и
   $\bigl\lvert\lvert\lambda\rvert-\lambda\bigr\rvert\le\kappa'\sqrt{\lvert\lambda\rvert}$.
   Тогда $\lvert\lambda\rvert\le32e^{2\kappa'}$. В самом деле, на $(0,1)$ для
   $u(x)=y(x)$, $v(x)=y(-x)$ имеем $v''=-\lambda v$, $u''=-\lambda u+\lambda xv$.
   Функция $p=u+\tfrac{x^2}{4}v'-\tfrac{x}{4}v$ решает $p''=-\lambda p$, $p(0)=y(0)$,
   $p'(0)=y'(0)-y(0)/4$, $p(1)=-y'(-1)/4$. Энергия
   $\lvert w'\rvert^2+\lvert\lambda\rvert\lvert w\rvert^2$ решения $w''=-\lambda w$ растёт на
   отрезке длины $1$ не более чем в $e^{\kappa'}$ раз. Применяя это к $y$ на $[-1,0]$ и к
   $p$ на $[0,1]$, получаем
   $\lvert\lambda\rvert\lvert y'(-1)\rvert^2/16\le2e^{2\kappa'}\lvert y'(-1)\rvert^2$. Если
   $y'(-1)=0$, то $y\equiv0$ по единственности задачи Коши.
2. *Квазимоды.* Пусть $\psi$ гладкая, $\psi=0$ при $x\le0$, $\psi(1)=0$ и
   $y_\omega=\psi(x)e^{i\omega x}$. Тогда $y_\omega$ лежит в области,
   $L_ay_\omega=-y_\omega''$, так как $a(x)y_\omega''(-x)=0$, и
   $\lVert(L_a-\omega^2)y_\omega\rVert\le A+B\omega$, а $\lVert y_\omega\rVert$ не зависит
   от $\omega$.
3. *Базис Рисса.* Если $\lbrace e_i\rbrace$ — базис Рисса из собственных функций с
   собственными значениями $\lambda_i$ и $\lvert\lambda_i-\mu\rvert\ge\delta$ для всех $i$,
   то $\lVert(L_a-\mu)y\rVert\ge\delta\lVert y\rVert/C$. По шагу 2 для каждого $\omega$
   найдётся $\lambda_i$ с $\lvert\lambda_i-\omega^2\rvert<D_0+D_1\omega$. При большом
   $\omega$ это противоречит шагу 1 с $\kappa'=4(D_0+D_1)$.

**Причина.** Как в C11, $(aR)^2=0$. На $(0,1)$ оператор действует на функции с носителем
справа как $-d^2/dx^2$ и допускает квазимоды на всей положительной полуоси, а
собственные значения удалены от неё дальше, чем на $O(\sqrt{\lvert\lambda\rvert})$.

**Lean.** `Involution/Estimates/RampSpectrum.lean`: `cauchy_energy_bound`, `rampCoefficient_lipschitz`,
`ramp_eigenvalue_bound`; `Involution/Estimates/RampNoBasis.lean`: `quasiMode_second_deriv`, `ramp_quasimodes`,
`rieszEigenbasis_lower_bound`, `ramp_no_riesz_eigenbasis`.

**Границы.** Исключён базис Рисса из собственных функций. Базисы с присоединёнными
функциями и базисы со скобками не исключены. Корневые функции полны, а собственные
значения лежат в секторе $\lvert\operatorname{Im}\lambda\rvert\le\operatorname{Re}\lambda$
(C17, $\alpha=\beta=1/2$).

**Расчёт.** Характеристическое уравнение для этого коэффициента:
$\sin2\omega+\omega/4-(1-\cos2\omega)/(8\omega)=0$, $\lambda=\omega^2$. В Lean оно не
используется.
