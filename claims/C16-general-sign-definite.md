---
id: C16
title: Общий знакопостоянный случай
status: proved-aristotle
depends_on: [C6, C10, C13, C14, S3, S4]
lean_theorem: Involution.bracketBasis_of_signDefinite
final: true
---

**Условия.** Вещественный $a\in W^2_\infty(-1,1)$, $0<m\le\lvert a\rvert\le M$,
$\lvert a(x)a(-x)\rvert\le\kappa<1$. Чётность и малость не предполагаются.

**Утверждение.** То же, что в C14.

**Доказательство.**

1. *Редукция.* `bracket_basis_of_gauge_core` приводит $L_a$ к виду $G+S$ с диагональным
   $G$, линейной счётной функцией частот и оценкой
   $\lVert Su\rVert\le b_1\langle Gu,u\rangle^{1/2}+b_0\lVert u\rVert$.
2. *Теорема Маркуса–Мацаева при $p=1/2$:* утверждение C13 без условия $160b_1c_2<1$.
   Доказательство следует S4, §2–6, в переменной $\omega=\sqrt z$. После сдвига $G+c$
   спектр $G+S$ лежит в полосе $\lvert\operatorname{Im}\omega\rvert\le\alpha$. Из оценки
   счётной функции по принципу Дирихле находятся окна фиксированной ширины с
   ограниченным числом частот. В окне собственные значения отщепляются, оставшееся
   возмущение конечного ранга обращается формулой Вудбери; её определитель —
   ограниченная голоморфная функция $\omega$, отделённая от нуля высоко над осью.
   Оценка минимума модуля (теорема Бореля–Каратеодори для голоморфного логарифма после
   деления на нули) даёт вертикальный разрез с равномерной оценкой резольвенты.
   Проекторы Рисса $P_k$ прямоугольников между соседними разрезами идемпотентны, взаимно
   аннулируются, имеют конечный ранг и инвариантные образы. Оценки
   $\sum_k\lvert((P_k-Q_k)u,v)\rvert\le C\lVert u\rVert\lVert v\rVert$ получены из явных
   интегралов, полнота — из интеграла по большому симметричному прямоугольнику.

**Источник.** S4, теорема 6.1; S3, теорема 6.6, с. 140, при $\alpha=2$, $p=1/2$. В Lean
формализован частный случай: самосопряжённый положительный диагональный $G$, один луч,
$p=1/2$.

**Lean.** `Involution/Estimates/GeneralBrackets.lean`: `MarkusMatsaevStatement`,
`signDefinite_bracket_basis_general`, `markusMatsaevStatement`,
`signDefinite_bracket_basis_W2`, `signDefinite_bracket_rootVectors_W2`. Теорема о
возмущениях — `exists_bracket_basis_of_subordinate_general` в `Involution/Estimates/MarkusMatsaev.lean`.
Модули: `MMContour` (интегралы по прямоугольникам, теорема Коши), `MMRiesz` (проекторы
Рисса пучка $1+B-zK$), `MMOperators`, `MMCompact`, `MMCuts`, `MMScalar`, `MMSideInt`,
`MMPointwise`, `MMEstimates` (S4, леммы 5.1–5.3), `MMTotal` (полнота), `MMRieszBasis`
(S4, предложение 3.7), `MMWoodbury`, `MMWindow`, `MMMinModulus` (вариант леммы 5.4),
`MMWindowCut`, `MMGoodCut` (предложение 5.5), `MMCore`. Сводка —
`bracketBasis_of_signDefinite`. Модули `Involution/Estimates/MarkusMatsaev.lean` и `MM*.lean` с
объявлениями `markusMatsaevStatement`, `signDefinite_bracket_basis_general` и
`exists_bracket_basis_of_subordinate_general` приняты из задачи A7.

**Границы.** Размер скобок не оценён, обычный базис Рисса не утверждается (C7).

**Расчёт: почему малость не снимается методом C13.** Член первого порядка связывает
каналы чётности со скоростями $1\pm b$, $b\ne0$, и внутри интервала устраняется подобием
порядка $-1$. На концах $\pm1$ остаётся слагаемое ранга два вида
$f\mapsto\psi(\pm1)f'(\pm1)\varphi_\pm$; функционал $f\mapsto f'(\pm1)$ имеет порядок
$3/4$ относительно $G$, а не $1/2$. Оно исчезает при $\varphi'(\pm1)=0$. Поэтому без
малости нужны оценки резольвенты возмущённого оператора в спектральных лакунах.
