---
id: C15
title: Коэффициент, близкий к чётному
status: proved-aristotle
depends_on: [C14]
lean_theorem: Involution.nearlyEven_bracket_basis
final: true
---

**Условия.** Вещественный $a\in W^2_\infty(-1,1)$, $0<m\le\lvert a\rvert\le M$,
$\lvert a(x)a(-x)\rvert\le\kappa<1$ и п.в.

$$
\Bigl\lvert\frac{a'(x)}{a(x)}+\frac{a'(-x)}{a(-x)}\Bigr\rvert\le\eta,\qquad
160\,(1+\sqrt\kappa)\,\eta<\pi\,(1-\sqrt\kappa).
$$

В Lean первое неравенство записано без деления:
$\lvert a'(x)a(-x)+a'(-x)a(x)\rvert\le\eta\lvert a(x)a(-x)\rvert$.

**Утверждение.** То же, что в C14.

**Смысл условия.** Знакопостоянный коэффициент однозначно записывается как
$a=\sigma se^{\varphi}$ с чётной $s>0$ и нечётной $\varphi$. Тогда $a'/a=s'/s+\varphi'$,
где $s'/s$ нечётна, а $\varphi'$ чётна, и $a'(x)/a(x)+a'(-x)/a(-x)=2\varphi'(x)$.
Условие означает $\lvert\varphi'\rvert\le\eta/2$: мала производная нечётной части
$\log\lvert a\rvert$. Производная чётной части $s$ не ограничивается. C14 — частный
случай: из $\lvert a'\rvert\le\varepsilon$, $\lvert a\rvert\ge m$ следует
$\eta=2\varepsilon/m$.

**Доказательство.** Вместо $r=\sqrt{\lvert a\rvert}$ берём калибровку
$r=e^{\varphi/2}=(\lvert a(x)\rvert/\lvert a(-x)\rvert)^{1/4}$. Тогда
$b(x)r(x)=a(x)r(-x)$ с тем же чётным $b=\sigma\sqrt{a(x)a(-x)}$, $r\in W^2_\infty$ и
$r'/r=\varphi'/2$. Применяем общую форму C14 с $c=\eta/4$.

**Lean.** `Involution/Estimates/NearlyEvenBrackets.lean`: `reflectCoefficient`,
`HasACMultiplierDerivative.reflect`, `nearlyEven_gauge_data`, `nearlyEven_bracket_basis`,
`nearlyEven_bracket_rootVectors`. Для чётного $a$ левая часть условия равна нулю
(`even_coefficient_deviation_zero`, `evenSignDefinite_bracket_basis`); в этом случае C5
сильнее: базис Рисса уже при $a\in L_\infty$. Модуль `Involution/Estimates/NearlyEvenBrackets.lean` с
объявлениями `nearlyEven_gauge_data`, `nearlyEven_bracket_basis`,
`nearlyEven_bracket_rootVectors` принят из задачи A6.

**Границы.** Постоянная $160$ не оптимальна. Даёт ли малость $\varphi'$ обычный базис
Рисса, не установлено.
