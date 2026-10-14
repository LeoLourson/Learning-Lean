---
id: C13
title: Малые возмущения порядка $1/2$: метод подобных операторов
status: proved-aristotle
depends_on: []
lean_theorem: Involution.exists_bracket_basis_of_subordinate
final: false
---

**Условия.** $\mathcal H$ — комплексное гильбертово пространство, $(e_i)$ — гильбертов
базис, $Ge_i=\lambda_ie_i$, $\lambda_i>0$. Счётная функция частот линейна:

$$
N(t)=\operatorname{card}\lbrace i:\lambda_i\le t^2\rbrace\le c_2t+C_0\quad\text{при } t\ge0.
$$

Возмущение $S$ определено на $D(G)$ и задано ограниченным $B=SG^{-1}$ с оценкой
$\lVert Bg\rVert\le b_1\langle G^{-1}g,g\rangle^{1/2}+b_0\lVert G^{-1}g\rVert$, то есть
$\lVert Su\rVert\le b_1\langle Gu,u\rangle^{1/2}+b_0\lVert u\rVert$ на $D(G)$. Условие
малости: $160b_1c_2<1$; постоянная $b_0$ произвольна.

**Утверждение.** Существуют конечномерные подпространства $V_k\subset D(G)$,
инвариантные относительно $G+S$, с плотной суммой и оценками
$A\sum\lVert v_k\rVert^2\le\lVert\sum v_k\rVert^2\le B\sum\lVert v_k\rVert^2$ для конечных
наборов $v_k\in V_k$.

**Доказательство** (метод подобных операторов, ср. S5).

1. *Сдвиг.* Заменяем $G$ на $G+c$, частоты $\omega_i=\sqrt{\lambda_i+c}$. Оператор
   $\hat S=S(G+c)^{-1/2}$ ограничен, $\lVert\hat S\rVert\le b_1+b_0/\sqrt c$.
   Инвариантные подпространства от сдвига не зависят.
2. *Разрезы.* Пусть $\delta=1/(4c_2)$. В окне $[T,T+2\delta N]$ с $N>2c_2T+2C_0$ среди
   точек $T+\delta(2q+1)$ есть точка на расстоянии не меньше $\delta$ от всех частот:
   иначе нашлось бы $N$ различных частот ниже $T+2\delta N$. Выбираем разрезы
   $\xi_{k+1}\ge2\xi_k$ с зазором $\delta$. Блок $\mathcal H_k$ натянут на $e_i$ с
   $\xi_k<\omega_i<\xi_{k+1}$; блоки конечномерны, их размерности не ограничены в
   совокупности.
3. *Мультипликаторы Шура.* Если $\omega_i\ge v$ для строк и $\omega_l\le u<v$ для
   столбцов, то $1/(\omega_i\mp\omega_l)=\sum_n(\pm\omega_l)^n/\omega_i^{n+1}$ — сумма
   произведений диагональных операторов, и поэлементное умножение на этот множитель
   ограничено числом $1/(v-u)$. Пары блоков с одной разностью номеров имеют
   ортогональные строки и столбцы, поэтому норма суммы равна максимуму норм. Удвоение
   разрезов даёт для разности номеров $n+1$ оценку $2^{-n}/\delta$; в сумме множитель
   вне диагональных блоков ограничен числом $4/\delta$.
4. *Уравнение.* Пусть $R=(G+c)^{-1/2}$, $J$ — блочно-диагональная часть, $\Gamma_0$,
   $\Gamma_1$ — множители $\omega_l/(\omega_i^2-\omega_l^2)$ и
   $\omega_i/(\omega_i^2-\omega_l^2)$ вне блоков. Тогда
   $\Gamma_0X\cdot R^2=R^2\cdot\Gamma_0X+R^2(X-JX)R$ и
   $\Gamma_1X\cdot R=R\cdot\Gamma_0X+R(X-JX)R$. Отображение
   $\Phi(X)=\hat S-\hat S\Gamma_1X+\Gamma_0X\cdot JX$ сжимает шар радиуса
   $2\lVert\hat S\rVert$, если $40\lVert\hat S\rVert\le\delta$.
5. *Подобие.* Для неподвижной точки $X$ оператор $U=I-\Gamma_0X$ обратим
   ($\lVert\Gamma_0X\rVert\le1/5$), сохраняет область и
   $(G+c+S)U=U\bigl(G+c+JX\cdot(G+c)^{1/2}\bigr)$; правая часть блочно-диагональна.
6. *Блоки.* $V_k=U\mathcal H_k$ инвариантны, конечномерны и образуют базис Рисса
   подпространств как образ полной ортогональной системы при обратимом $U$.

**Lean.** `Involution/Model/SchurMultiplier.lean` (`Involution.SchurBound.product`,
`Involution.SchurBound.of_hasSum`, `Involution.SchurBound.blockSum`, `schurBound_separated_upper`, `schurBound_separated_lower`,
`exists_weighted_extension`), `Involution/Model/SparseCuts.lean` (`exists_similarity_fixedPoint`,
`exists_sparse_cuts`, `card_le_of_finiteRank_approx`), `Involution/Model/BlockMultiplier.lean`
(`SpectralBlocks`, `offMult_bound`, `diagMult_bound`), `Involution/Model/BlockPerturbation.lean`
(`gamma0_sylvester`, `gamma1_invFreq`, `exists_block_similarity`), `Involution/Model/BlockInvariant.lean`
(`rieszBracketsOfOrthogonal`, `exists_invariant_blocks`, `exists_bracket_basis`),
`Involution/Model/SubordinatePerturbation.lean` (`exists_bracket_basis_of_subordinate`).

**Границы.** Блоки растут геометрически, размер скобок не оценён. Условие малости —
ограничение метода: шаг 4 требует $\lVert\hat S\rVert\lesssim\delta$, а $\delta$ не
превосходит среднего расстояния между частотами. Без малости утверждение доказано в C16
другим методом.
