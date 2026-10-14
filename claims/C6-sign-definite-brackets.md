---
id: C6
title: Гладкий коэффициент постоянного знака: базис со скобками
status: proved-aristotle
depends_on: [C1, C10, S3, S4]
lean_theorem: Involution.signDefinite_bracket_basis_W2
final: true
---

**Условия.** Постановка, $a\in W^2_\infty(-1,1)$ и $\lvert a\rvert\ge m>0$ п.в. Знак
$\sigma=\pm1$ непрерывного представителя постоянен.

**Утверждение.** Корневые функции $L_a$ полны и образуют базис Рисса со скобками: есть
последовательность конечномерных инвариантных подпространств области, порождённых
корневыми функциями и образующих базис Рисса подпространств.

**Доказательство по S4.** На $(0,1)$ положим

$$
r(x)=\sqrt{\lvert a(x)\rvert},\quad t(x)=\sqrt{\lvert a(-x)\rvert},\quad
D=\operatorname{diag}(r,t),\quad s=\sqrt{a(x)a(-x)}=rt.
$$

Умножение на $D$ и $D^{-1}$ ограниченно в $L_2$ и в $H^2$. При $U=DY$ из C1 получаем

$$
D^{-1}MD=K=\begin{pmatrix}1&\sigma s\\ \sigma s&1\end{pmatrix},\qquad
D^{-1}(-M\partial_x^2)DY=-KY''-2KD^{-1}D'Y'-KD^{-1}D''Y,
$$

где $0<s\le\sqrt\kappa<1$. Область сохраняется: $r(0)=t(0)$ и $r'(0)+t'(0)=0$, так как
$t$ — отражение $r$; поэтому условия склейки для $U$ и для $Y$ совпадают. Ортогональная
замена

$$
Z=H^{T}Y,\qquad H=\frac{1}{\sqrt2}\begin{pmatrix}1&1\\ 1&-1\end{pmatrix},
$$

даёт $Z_+'(0)=0$, $Z_-(0)=0$, $Z(1)=0$ и оператор $G_0+B$, где
$G_0=\operatorname{diag}(-p_+\partial^2,-p_-\partial^2)$, $p_\pm=1\pm\sigma s$, а
$B=F(x)\partial+V(x)$ с ограниченными матрицами $F$, $V$. В пространстве
$L_2(p_+^{-1}dx)\oplus L_2(p_-^{-1}dx)$ оператор $G_0$ положителен, самосопряжён и имеет
компактную резольвенту (как в C5). Проверяем гипотезы теоремы 6.1 из S4.

1. Спектр $G_0$ лежит на положительном луче. По минимаксу $\mu_n^{+}$ заключены между
   постоянными кратными $(n+\tfrac12)^2$, а $\mu_n^{-}$ — между кратными $n^2$, поэтому
   $N(R,G_0)=O(\sqrt R)$ с учётом кратностей.
2. $\lVert Z'\rVert^2=(G_0Z,Z)\le\lVert G_0Z\rVert\lVert Z\rVert$, откуда
   $\lVert BZ\rVert\le C\lVert Z\rVert^{1/2}\lVert G_0Z\rVert^{1/2}$; слагаемое с
   $\lVert Z\rVert$ поглощается, так как $G_0\ge cI>0$. Это подчинённость с показателем
   $p=1/2$.
3. $\liminf N(R,G_0)/R^{1-p}<\infty$. Теорема 6.1 даёт базис Рисса конечномерных
   инвариантных спектральных подпространств и полноту корневых подпространств.
4. Композиция склеивания, умножения на $D$ и матрицы $H$ ограниченно обратима и
   переносит вывод на $L_a$ вместе с областью и жордановыми цепочками.

**Вторая опора.** S3, теорема 6.6, с. 140, при порядке $\alpha=2$ и $p=1/2$.

**Lean.** Вывод доказан полностью, другим путём: калибровка на всём интервале без
складывания (C10), счётная функция без минимакса (C14, шаг 1), теорема о возмущениях
(C16). Итог — `signDefinite_bracket_basis_W2`, `signDefinite_bracket_rootVectors_W2`.
Вспомогательные результаты о коэффициентах класса $W^2_\infty$: правило произведения и
сохранение области (`secondWeakDeriv_mul_coefficient`, `Involution/Model/SobolevMultiplier.lean`),
регулярность $1/a$ (`Involution/Model/CoefficientInverse.lean`), регулярность $\sqrt{\lvert a\rvert}$ и
сохранение области в обе стороны (`sqrt_abs_weights_memW2Infinity`,
`sqrt_abs_dirichlet_iff`). Модули `Involution/Estimates/GeneralBrackets.lean` и `Involution/Estimates/MarkusMatsaev.lean`
с объявлениями `signDefinite_bracket_basis_W2`, `signDefinite_bracket_rootVectors_W2`
и `markusMatsaevStatement` приняты из задачи A7.

**Пример.** $a(x)=1/2+x/4$: $1/4\le a\le3/4$, $a(x)a(-x)=1/4-x^2/16\le1/4$;
`steepCoefficient_bracket_basis`.

**Границы.** Размер скобок не оценён. Отсутствие обычного базиса Рисса не доказано.
