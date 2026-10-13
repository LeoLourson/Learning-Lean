# Контекст и проверенные записи

Обозначения — в `question.md`, реестр источников — в `sources/README.md`.
У каждой записи один из трёх статусов.

- **Lean** — утверждение доказано в библиотеке `Involution/`; `#print axioms` показывает
  только `propext`, `Classical.choice`, `Quot.sound`. Какие модули доказаны локально, а
  какие получены от Aristotle, записано в `blueprint.md`.
- **Расчёт** — собственное рассуждение, в Lean не формализовано.
- **Источник** — теорема статьи; гипотезы сверены в `sources/results.md`.

Теоремы Lean сформулированы на слабой области Дирихле `MemDirichletH2`: класс $L_2$ с
двумя слабыми производными в $L_2$ и непрерывным представителем, равным нулю в $\pm1$.
Она эквивалентна описанию через абсолютно непрерывные $F$, $F'$ с $F''\in L_2$
(`memDirichletH2_iff_acRealization`) и совпадает с $H^2\cap H_0^1$; см. следующий раздел.

Всюду $(Rf)(x)=f(-x)$, $T_a=I+aR$, $G$ — обратный к $-D^2$ с условиями Дирихле.

## 0. Область определения

**Определение.** Пробная пара — $(u,u')$ с $u\in C^\infty(\mathbb R;\mathbb C)$,
$\operatorname{supp}u\subset(-1,1)$ (`IsTestPair`). Класс $H_0^1(-1,1)$ состоит из
$f\in L_2$ со слабой производной $g\in L_2$, для которых при каждом $\varepsilon>0$ есть
пробная пара с $\lVert f-u\rVert<\varepsilon$ и $\lVert g-u'\rVert<\varepsilon$
(`MemIntervalH01`): это замыкание пробных функций по норме $H^1$.

**Утверждение.** $f\in H_0^1(-1,1)$ тогда и только тогда, когда у $f$ есть слабая
производная в $L_2$ и непрерывный представитель $f$ равен нулю в точках $\pm1$. Поэтому
слабая область Дирихле равна $H^2(-1,1)\cap H_0^1(-1,1)$.

**Доказательство.** Пусть $K\subset L_2\times L_2$ — подпространство пробных пар; условие
приближения означает $(f,g)\in\overline K$. Для абсолютно непрерывных $B$, $F$ с
$B'=\bar a$, $F'=g$, где $B$ — представитель $\bar b$, а $F$ — представитель $f$,
интегрирование по частям даёт

$$
\langle a,f\rangle+\langle b,g\rangle=B(1)F(1)-B(-1)F(-1).\tag{1}
$$

Если $(a,b)\perp K$, то $\bar b$ имеет слабую производную $\bar a$, и у $\bar b$ есть
абсолютно непрерывный представитель $B$. Если след $f$ нулевой, правая часть (1) равна
нулю для каждой пары $(a,b)\in K^\perp$, откуда $(f,g)\in K^{\perp\perp}=\overline K$.
Обратно, пары $(\psi',\psi)$ с вещественной $\psi\in C^1$ лежат в $K^\perp$, так как
пробные функции равны нулю в $\pm1$. Для $(f,g)\in\overline K$ равенство (1) при
$\psi(x)=x+1$ и $\psi(x)=x-1$ даёт $F(1)=0$ и $F(-1)=0$.

**Lean.** `SobolevClosure.lean`: `inner_add_inner_eq_boundary`, `testPairSubmodule`,
`approx_iff_mem_closure`, `memIntervalH01_iff_trace`, `memDirichletH2_iff_h2_and_h01`.
Модуль получен от Aristotle (задача 7 в `blueprint.md`).

**Границы.** Итоговые теоремы по-прежнему записаны через `MemDirichletH2`; переход к
$H^2\cap H_0^1$ даёт `memDirichletH2_iff_h2_and_h01`. Пространство $H^2$ здесь —
`MemIntervalH2` (две слабые производные в $L_2$).

## 1. Сводка

| Дополнительные условия | Вывод | Запись |
| --- | --- | --- |
| $a(-x)=a(x)$ п.в. | базис Рисса из собственных функций; присоединённых функций нет | C5, Lean |
| $a\in W^2_\infty$, $0<m\le\lvert a\rvert\le M$ | полнота корневых функций; базис Рисса со скобками из конечномерных инвариантных подпространств области, порождённых корневыми функциями | C6, C16, Lean |
| то же и $\lvert a'\rvert\le\varepsilon$, $320(1+\sqrt\kappa)\varepsilon<\pi(1-\sqrt\kappa)m$ | тот же вывод методом подобных операторов | C13–C14, Lean |
| то же и $\bigl\lvert a'(x)/a(x)+a'(-x)/a(-x)\bigr\rvert\le\eta$, $160(1+\sqrt\kappa)\eta<\pi(1-\sqrt\kappa)$ | тот же вывод | C15, Lean |
| вес $r\in W^2_\infty$, $b(x)r(x)=a(x)r(-x)$ с чётным $b$, $\lvert r'/r\rvert\le c$, $640(1+\sqrt\kappa)c<\pi(1-\sqrt\kappa)$ | тот же вывод | C14, общая форма, Lean |
| блоки предыдущих строк и равномерно обусловленный выбор корневых функций внутри блоков | базис Рисса | C7, критерий в Lean |
| только $a\in L_\infty$ | компактный обратный, конечномерные собственные подпространства, альтернатива Фредгольма; базисность не следует | C8, C11, Lean |
| $a=4$ на $(0,1)$, $a=0$ на $(-1,0)$ | собственных значений нет; нет базиса Рисса из собственных функций и базиса со скобками из инвариантных блоков | C11, Lean |
| $a(x)=\max(x,0)$ | нет базиса Рисса из собственных функций | C12, Lean |
| $a\in L_\infty$, $\lvert a(x)+a(-x)\rvert\le2\alpha$, $\alpha<1$, $\lvert a(x)-a(-x)\rvert\le2\beta$ | собственные значения в секторе $(1-\alpha)\lvert\operatorname{Im}\lambda\rvert\le\beta\operatorname{Re}\lambda$, $\operatorname{Re}\lambda>0$ | C17, Lean |
| то же | $T_a$ обратим, $\lVert(L_a+s)^{-1}\rVert\le C/s$ при $s>0$ | C17, Lean |
| то же | корневые функции полны | C17, источник S3 |
| $a(x)=x/2$ | нет базиса Рисса из собственных функций | C18, Lean |
| $a\in L_\infty$, нечётная $\psi\in W^2_\infty$ с $\operatorname{ess\,sup}\lvert a(x)e^{-\psi(x)}+a(-x)e^{\psi(x)}\rvert<2$ | $T_a$ обратим, $\lVert(L_a+s)^{-1}\rVert\le C/s$ при $s\ge s_0$ | C19, расчёт |
| то же | корневые функции полны | C19, источник S3 |
| $a$ непрерывна на $[-1,1]$, $\lvert a(x)a(-x)\rvert<1$; в частности весь класс постановки | такая $\psi$ существует: оценка на луче и полнота | C19, расчёт и источник S3 |

Во всех строках, кроме строк C17 и C19, сохраняется условие
$\lvert a(x)a(-x)\rvert\le\kappa<1$ из постановки; в C17 и в первых двух строках C19
оно не используется. Это
достаточные условия; необходимых условий и классификации всех коэффициентов нет.
Во второй строке вещественный $a$ имеет постоянный знак; чётность не требуется.
Сводка в Lean — `Involution/BasisConditions.lean`: `rieszBasis_of_even`,
`bracketBasis_of_signDefinite`, `bracketBasis_of_nearlyEven`.

## 2. Записи

### C1. Сведение к двум компонентам

**Условия.** $y\in H^2(-1,1)\cap H_0^1(-1,1)$, коэффициент как в постановке.

**Утверждение.** Для $U=(u,v)^{T}=(y(x),y(-x))^{T}$ на $(0,1)$

$$
M U''=-\lambda U,\qquad
M=\begin{pmatrix}1&a(x)\\ a(-x)&1\end{pmatrix},
$$

с условиями $U(1)=0$, $u(0)=v(0)$, $u'(0)+v'(0)=0$. Обратно, две $H^2$-функции с этими
условиями склеиваются в функцию из $H^2(-1,1)$ с нулевыми следами. Нормы связаны равенством

$$
\int_0^1\bigl(\lvert u\rvert^2+\lvert v\rvert^2\bigr)\,dx=\int_{-1}^{1}\lvert y\rvert^2\,dx.
$$

**Доказательство.** Записываем уравнение в точках $x$ и $-x$; $v'(x)=-y'(-x)$,
$v''(x)=y''(-x)$. Непрерывность следов $y$, $y'$ в нуле даёт условия склейки.

**Lean.** Слабые производные, их единственность и отражение — `WeakDerivative.lean`;
$H^2$ через две слабые производные — `IntervalSobolev.lean`; следы — `IntervalTrace.lean`.
Регулярные представители: `MemIntervalH2.exists_regular_pair`,
`regular_pair_representatives_unique`; они опираются на
`HasWeakDerivOn.ae_eq_const_of_zero` и `hasWeakDerivOn_of_absolutelyContinuous`.
Склейка: `memIntervalH2_intervalJoin`, `weak_derivatives_fold`,
`memDirichletH2_reflectedJoin`. Унитарное складывание $L_2(-1,1)\to L_2(0,1)^2$ с
евклидовой нормой пары: `l2FoldingEquiv`, обратное — `l2Unfold`. Эквивалентность областей:
`memDirichletH2_iff_fold`, `memFoldedDirichletH2_iff_unfold`. Редукция оператора с
коэффициентом класса $L_\infty$ и перенос уравнения $(L_a-\lambda)f=g$ в обе стороны:
`variableSobolevOperator_unitary_reduction` в `FoldedOperator.lean`. Точечные значения
вторых производных нигде не используются.

### C2. Обратимость главной матрицы

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
`principalMatrix_inv`; комплексный вариант — `ComplexReduction.lean`.

### C3. Постоянный коэффициент

**Условия.** $a(x)=c\in(-1,1)$.

**Утверждение.** На чётных функциях $L=-(1+c)d^2/dx^2$, на нечётных
$L=-(1-c)d^2/dx^2$. Собственные пары:

$$
e_n(x)=\cos\bigl((n+\tfrac12)\pi x\bigr),\quad
\lambda_n^{+}=(1+c)(n+\tfrac12)^2\pi^2,\quad n\ge0;
$$

$$
o_m(x)=\sin(m\pi x),\quad \lambda_m^{-}=(1-c)m^2\pi^2,\quad m\ge1.
$$

Система $\lbrace e_n\rbrace\cup\lbrace o_m\rbrace$ — ортонормированный базис $L_2(-1,1)$.

**Доказательство.** Подстановка; полнота — нечётное продолжение относительно $x=1$ и
равенство Парсеваля для периода $4$. При $c=0$ первые значения: $\pi^2/4$, $\pi^2$,
$9\pi^2/4$. При $c=1/2$ в чётном канале $3\pi^2/8$, $27\pi^2/8$, в нечётном $\pi^2/2$,
$2\pi^2$.

**Источник.** S2, теорема 4.1, с. 4: вещественная постоянная модель Дирихле.

**Lean.** `constant_diagonalization`; `constant_cosine_eigenpair`,
`constant_sine_eigenpair`; `constantModel_orthonormal`, `constantModel_dense_span`;
собственные уравнения всех векторов базиса — `ModelEigenbasis.lean`.

### C4. Пример $a(x)=x/2$

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

**Lean.** `OddCoefficient.lean`: `parityRotation`, `parityRotationInv_parityRotation`,
`parityRotation_norm`, `boundedMultiplier_reflect_odd`, `parityRotation_principalOperator`,
`memDirichletH2_parityRotation`, `secondWeakDeriv_parityRotation`,
`oddCoefficient_unitary_multiplication`, `oddCoefficient_eigen_iff`.

**Границы.** Базисность корневых функций для нечётного $a$ не доказана. Сектор
собственных значений и полнота — C17. При $a=x/2$ базиса Рисса из собственных функций
нет (C18); численный расчёт — `ideas.md`, I5.

### C5. Чётный коэффициент: базис Рисса

**Условия.** Постановка и $a(-x)=a(x)$ п.в. Тогда $\lvert a\rvert\le\rho=\sqrt\kappa<1$ и
$1-\rho\le p_\pm\le1+\rho$ для $p_\pm=1\pm a$.

**Утверждение.** Собственные функции $L_a$ можно выбрать так, что они образуют базис
Рисса в $L_2(-1,1)$. Если $(L_a-\lambda)f=0$ и $(L_a-\lambda)g=f$, то $f=0$:
нетривиальных жордановых цепочек нет.

**Доказательство.** Чётность сохраняется оператором. На чётных и нечётных функциях
после ограничения на $(0,1)$

$$
T_\pm f=-p_\pm f'',\qquad
D(T_+)=\lbrace f\in H^2: f'(0)=0,\ f(1)=0\rbrace,\quad
D(T_-)=\lbrace f\in H^2: f(0)=f(1)=0\rbrace.
$$

В $H_\pm=L_2((0,1),p_\pm^{-1}dx)$ оператор $T_\pm$ порождён замкнутой положительной формой
$t[f,g]=\int_0^1 f'\overline{g'}dx$ с областью $\lbrace f\in H^1:f(1)=0\rbrace$ для
плюса и $H_0^1(0,1)$ для минуса: слабое уравнение даёт $-f''=p_\pm^{-1}h\in L_2$, а
интегрирование по частям — граничные условия. Вложение $H^1(0,1)\to L_2(0,1)$ компактно,
поэтому резольвента компактна, и в $H_\pm$ есть ортонормированный базис собственных
функций. Нормы $H_\pm$ и $L_2$ эквивалентны:

$$
(1+\rho)^{-1}\lVert f\rVert_2^2\le\lVert f\rVert_{H_\pm}^2\le(1-\rho)^{-1}\lVert f\rVert_2^2,
$$

поэтому этот базис — базис Рисса в $L_2(0,1)$. Объединение каналов и обратное склеивание
дают базис Рисса в $L_2(-1,1)$. Оператор самосопряжён в эквивалентном скалярном
произведении, отсюда отсутствие цепочек. В исходном $L_2$ при непостоянном $a$ оператор
$L_a$ не самосопряжён.

**Lean.** Доказательство устроено иначе, через компактный обратный. Оператор $G$ задан
рядом операторов ранга один по модельному базису C3; он компактен, симметричен и
инъективен (`SpectralGreen.lean`). В канале $Ru=su$, $s=\pm1$, берём вес $w$ с
$(1+sa)w^2=1$ п.в. (`PositiveWeight.lean`). Оператор $K=M_wGM_w$ компактен и
симметричен; его собственные векторы образуют гильбертов базис канала
(`CompactEigenbasis.lean`). Если $Ku=\mu u$, то $y=GM_wu$ лежит в области и
$L_ay=\mu^{-1}y$ (`WeightedGreen.lean`), а обратимое умножение переводит базис в базис
Рисса (`MultiplicationEquiv.lean`, `WeightedEigenbasis.lean`). Итог:
`evenCoefficient_channel_riesz_eigenbasis`, `evenCoefficient_riesz_eigenbasis`,
`evenCoefficient_noJordan`; на области абсолютно непрерывных представителей —
`ACSpectral.lean`. Достаточно вещественного $a\in L_\infty$; условие $W^1_\infty$ не
используется.

**Примеры.** $a(x)=x^2/2$; постоянный $a=c\in(-1,1)$ даёт ортонормированный базис C3.

### C6. Гладкий коэффициент постоянного знака: базис со скобками

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
сохранение области (`secondWeakDeriv_mul_coefficient`, `SobolevMultiplier.lean`),
регулярность $1/a$ (`CoefficientInverse.lean`), регулярность $\sqrt{\lvert a\rvert}$ и
сохранение области в обе стороны (`sqrt_abs_weights_memW2Infinity`,
`sqrt_abs_dirichlet_iff`).

**Пример.** $a(x)=1/2+x/4$: $1/4\le a\le3/4$, $a(x)a(-x)=1/4-x^2/16\le1/4$;
`steepCoefficient_bracket_basis`.

**Границы.** Размер скобок не оценён. Отсутствие обычного базиса Рисса не доказано.

### C7. Когда скобки можно снять

Пусть $E_j$ — блоки базиса со скобками и в каждом выбраны векторы $e_{j,k}$.

**Утверждение.** Объединённая система $\lbrace e_{j,k}\rbrace$ — базис Рисса тогда и
только тогда, когда каждая внутренняя семья полна в своём блоке и существуют общие
$0<m\le M<\infty$ с

$$
m\sum_k\lvert c_k\rvert^2\le\Bigl\lVert\sum_k c_k e_{j,k}\Bigr\rVert^2\le M\sum_k\lvert c_k\rvert^2
\quad\text{для всех } j.
$$

**Доказательство.** Блочное неравенство Рисса и внутренние неравенства перемножаются;
обратно, глобальное неравенство ограничивается на каждый блок. Конечное число плохо
обусловленных блоков поглощается константами, бесконечное — нет.

**Источник.** S4, определение 3.1, предложение 3.2, лемма 3.3, с. 5–6.

**Lean.** `RieszBasisWithBrackets` (конечномерные блоки, плотность суммы, двусторонние
блочные оценки; общая граница размерностей не предполагается),
`exists_uniformBlockBounds_iff_global`, `flattenedBlockVector_dense`,
`exists_uniformBlockBounds_iff_finiteRiesz`, `exists_rieszBasis_iff_uniformBlockBounds`.

**Границы.** Для чётного $a$ базис Рисса получен напрямую (C5). Для блоков C6 и C16
равномерные внутренние константы не проверены; одной простоты собственных значений для
них недостаточно. Достаточный частный случай — одномерные блоки вне конечной части
(S4, замечание 6.3); для $L_a$ он не доказан.

### C8. Весь класс постановки: факторизация и компактный обратный

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

**Lean.** `CompactInverse.lean`: `variableSobolevOperator_eq_principal`,
`principalOperatorInverse_left`, `principalOperatorInverse_right`, `variableGreen_compact`,
`variableOperator_solution_iff`, `variableOperator_eigen_iff`,
`variableOperator_finiteDimensional_eigenspace`, `variableOperator_fredholm`; для
вещественного коэффициента — `productBound_compact_inverse`, `productBound_fredholm`.

**Граница $\kappa<1$.** При $a\equiv1$ каждая функция $\sin(m\pi x)$ лежит в ядре
(`unit_coefficient_sine_kernel`): компактного обратного нет. Синусы и косинусы C3
остаются при этом ортогональным базисом из собственных функций.

**Границы.** Полнота и базисность из C8 не следуют (C11, C12).

### C9. Когда главный множитель симметричен

**Утверждение.** Для вещественного $a\in L_\infty$ оператор $T_a=I+aR$ симметричен в
$L_2$ тогда и только тогда, когда $a(-x)=a(x)$ п.в.

**Доказательство.** $(aR)^{\ast}=Ra$, поэтому симметричность равносильна $aRg=R(ag)$ для
всех $g$; при $g\equiv1$ получаем $a(x)=a(-x)$. Обратное проверяется подстановкой.

**Lean.** `principalOperator_isSymmetric_iff`.

**Смысл.** При чётном $a$ оператор $T_a$ положителен, и $L_a=T_a(-D^2)$ подобен
самосопряжённому $T_a^{1/2}(-D^2)T_a^{1/2}$ — механизм C5. При ненулевой нечётной части
он не работает; отсутствие базиса Рисса отсюда не следует.

**Расчёт.** Пусть $a=se^{\varphi}$ с чётной $s$ и нечётной $\varphi$. Калибровка весом
$e^{\varphi/2}$ (C10) даёт в каналах чётности диагональную часть, самосопряжённую во
взвешенных пространствах, и кососимметричную связь каналов первого порядка. Оператор
самосопряжён в индефинитной метрике: спектр симметричен относительно вещественной оси,
но может быть невещественным. Поэтому в C6 применяется теория возмущений.

### C10. Калибровка на всём интервале

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

**Lean.** `GaugeSimilarity.lean`: `principalOperator_gauge`, `gauge_similarity`,
`firstWeakDeriv_norm_sq_le`, `gaugeLowerOrder_norm_le`, `gaugePerturbation_subordinate`,
`real_coefficient_constant_sign`, `signDefinite_gauge_reduction`; сводка —
`signDefinite_perturbed_riesz_model`.

### C11. Пример без базисности: односторонний коэффициент

**Условия.** $a(x)=4$ при $0<x<1$, $a(x)=0$ при $-1<x\le0$. Тогда $a\in L_\infty$ и
$a(x)a(-x)=0$, $\kappa=0$. Коэффициент разрывен в нуле и не принадлежит $W^1_\infty$:
пример лежит в классе C8, но вне исходной постановки.

**Утверждение.** Для каждого $\lambda\in\mathbb C$ уравнение $L_ay=\lambda y$ на области
Дирихле имеет только нулевое решение. Оператор $K_a$ компактен, инъективен и не имеет
ненулевых конечномерных инвариантных подпространств. Поэтому нет базиса Рисса из
собственных функций $L_a$ и нет базиса Рисса со скобками, блоки которого инвариантны
относительно $K_a$.

**Доказательство.** Пусть $u(x)=y(x)$, $v(x)=y(-x)$ на $(0,1)$. Тогда $v''=-\lambda v$,
$u''=-\lambda u+4\lambda v$, $u(0)=v(0)$, $u'(0)=-v'(0)$, $u(1)=v(1)=0$. Функция
$d=u+2xv'-v$ удовлетворяет $d''=-\lambda d$, $d(0)=0$, $d'(0)=u'(0)+v'(0)=0$, значит
$d\equiv0$ и $u=v-2xv'$. При $x=1$ получаем $v'(1)=0$; вместе с $v(1)=0$ это даёт
$v\equiv0$, затем $u\equiv0$.

**Причина.** $(aR)^2=0$: множитель $I+aR$ унипотентен, связь половин интервала
односторонняя. При $a=4$ частное решение $-2xv'$ согласовано с условиями склейки, и
краевое условие в точке $1$ становится вторым условием Коши. Задача вольтеррова.

**Lean.** `OneSidedExample.lean`: `cauchy_zero_unique` (через лемму Гронуолла),
`oneSided_no_eigenfunction`, `oneSidedGreen_no_eigenvector`,
`oneSided_invariant_block_eq_bot`, `oneSided_no_riesz_eigenbasis`,
`oneSided_no_bracket_basis`.

### C12. Пример в классе $W^1_\infty$: $a(x)=\max(x,0)$

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

**Lean.** `RampSpectrum.lean`: `cauchy_energy_bound`, `rampCoefficient_lipschitz`,
`ramp_eigenvalue_bound`; `RampNoBasis.lean`: `quasiMode_second_deriv`, `ramp_quasimodes`,
`rieszEigenbasis_lower_bound`, `ramp_no_riesz_eigenbasis`.

**Границы.** Исключён базис Рисса из собственных функций. Базисы с присоединёнными
функциями и базисы со скобками не исключены. Корневые функции полны, а собственные
значения лежат в секторе $\lvert\operatorname{Im}\lambda\rvert\le\operatorname{Re}\lambda$
(C17, $\alpha=\beta=1/2$).

**Расчёт.** Характеристическое уравнение для этого коэффициента:
$\sin2\omega+\omega/4-(1-\cos2\omega)/(8\omega)=0$, $\lambda=\omega^2$. В Lean оно не
используется.

### C13. Малые возмущения порядка $1/2$: метод подобных операторов

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

**Lean.** `SchurMultiplier.lean` (`SchurBound.product`, `SchurBound.of_hasSum`,
`SchurBound.blockSum`, `schurBound_separated_upper`, `schurBound_separated_lower`,
`exists_weighted_extension`), `SparseCuts.lean` (`exists_similarity_fixedPoint`,
`exists_sparse_cuts`, `card_le_of_finiteRank_approx`), `BlockMultiplier.lean`
(`SpectralBlocks`, `offMult_bound`, `diagMult_bound`), `BlockPerturbation.lean`
(`gamma0_sylvester`, `gamma1_invFreq`, `exists_block_similarity`), `BlockInvariant.lean`
(`rieszBracketsOfOrthogonal`, `exists_invariant_blocks`, `exists_bracket_basis`),
`SubordinatePerturbation.lean` (`exists_bracket_basis_of_subordinate`).

**Границы.** Блоки растут геометрически, размер скобок не оценён. Условие малости —
ограничение метода: шаг 4 требует $\lVert\hat S\rVert\lesssim\delta$, а $\delta$ не
превосходит среднего расстояния между частотами. Без малости утверждение доказано в C16
другим методом.

### C14. Знакопостоянный коэффициент с малой производной

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

**Lean.** `EigenvalueCounting.lean` (`spectralGreen_eq_diagOp`,
`green_sandwich_eigen_count`), `GaugeOperators.lean` (`greenDeriv`, `gaugeLowerOp`,
`parityMultiplierSum_symmetric`, `principalOperator_weight`),
`SignDefiniteBrackets.lean` (`RieszBasisWithBrackets.map`, `signDefinite_gauge_data`,
`bracket_basis_of_gauge_core`, `bracket_basis_of_gauge`, `signDefinite_bracket_basis`),
`BracketCorollaries.lean` (`invariant_block_rootVectors`,
`signDefinite_bracket_rootVectors`, `tiltedCoefficient_bracket_basis`). Теорема
`bracket_basis_of_gauge_core` принимает абстрактную теорему о возмущениях как гипотезу
и малость не использует; на неё опирается C16.

**Границы.** Постоянная $320$ не оптимальна. Коэффициенты с нулями и сменой знака не
охвачены.

### C15. Коэффициент, близкий к чётному

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

**Lean.** `NearlyEvenBrackets.lean`: `reflectCoefficient`,
`HasACMultiplierDerivative.reflect`, `nearlyEven_gauge_data`, `nearlyEven_bracket_basis`,
`nearlyEven_bracket_rootVectors`. Для чётного $a$ левая часть условия равна нулю
(`even_coefficient_deviation_zero`, `evenSignDefinite_bracket_basis`); в этом случае C5
сильнее: базис Рисса уже при $a\in L_\infty$.

**Границы.** Постоянная $160$ не оптимальна. Даёт ли малость $\varphi'$ обычный базис
Рисса, не установлено.

### C16. Общий знакопостоянный случай

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

**Lean.** `GeneralBrackets.lean`: `MarkusMatsaevStatement`,
`signDefinite_bracket_basis_general`, `markusMatsaevStatement`,
`signDefinite_bracket_basis_W2`, `signDefinite_bracket_rootVectors_W2`. Теорема о
возмущениях — `exists_bracket_basis_of_subordinate_general` в `MarkusMatsaev.lean`.
Модули: `MMContour` (интегралы по прямоугольникам, теорема Коши), `MMRiesz` (проекторы
Рисса пучка $1+B-zK$), `MMOperators`, `MMCompact`, `MMCuts`, `MMScalar`, `MMSideInt`,
`MMPointwise`, `MMEstimates` (S4, леммы 5.1–5.3), `MMTotal` (полнота), `MMRieszBasis`
(S4, предложение 3.7), `MMWoodbury`, `MMWindow`, `MMMinModulus` (вариант леммы 5.4),
`MMWindowCut`, `MMGoodCut` (предложение 5.5), `MMCore`. Сводка —
`bracketBasis_of_signDefinite`.

**Границы.** Размер скобок не оценён, обычный базис Рисса не утверждается (C7).

**Расчёт: почему малость не снимается методом C13.** Член первого порядка связывает
каналы чётности со скоростями $1\pm b$, $b\ne0$, и внутри интервала устраняется подобием
порядка $-1$. На концах $\pm1$ остаётся слагаемое ранга два вида
$f\mapsto\psi(\pm1)f'(\pm1)\varphi_\pm$; функционал $f\mapsto f'(\pm1)$ имеет порядок
$3/4$ относительно $G$, а не $1/2$. Оно исчезает при $\varphi'(\pm1)=0$. Поэтому без
малости нужны оценки резольвенты возмущённого оператора в спектральных лакунах.

### C17. Сектор собственных значений и полнота

**Условия.** Вещественный $a\in L_\infty(-1,1)$. Положим
$a_e(x)=\tfrac12\bigl(a(x)+a(-x)\bigr)$, $a_o(x)=\tfrac12\bigl(a(x)-a(-x)\bigr)$ и пусть
$\lvert a_e\rvert\le\alpha<1$, $\lvert a_o\rvert\le\beta$ п.в. Оценка произведения
$a(x)a(-x)$ и гладкость не предполагаются.

**Утверждение 1 (Lean).** Если $L_af=\lambda f$, $f\ne0$, $f$ из слабой области Дирихле, то

$$
\operatorname{Re}\lambda>0,\qquad(1-\alpha)\,\lvert\operatorname{Im}\lambda\rvert\le\beta\operatorname{Re}\lambda .
$$

**Доказательство.** Пусть $W=-f''$. По C8 $L_af=T_aW$, а энергетическое тождество даёт
$\langle W,f\rangle=\lVert f'\rVert^2=E>0$. Умножая $T_aW=\lambda f$ скалярно на $W$,
получаем $\lVert W\rVert^2+X=\lambda E$, $X=\langle W,aRW\rangle$. Для вещественного $a$
сопряжённый к $aR$ оператор равен $Ra$, и $(aR\pm Ra)g=(a(x)\pm a(-x))g(-x)$. Поэтому
$2\operatorname{Re}X=\langle W,(aR+Ra)W\rangle$,
$2i\operatorname{Im}X=\langle W,(aR-Ra)W\rangle$ и

$$
\lvert\operatorname{Re}X\rvert\le\alpha\lVert W\rVert^2,\qquad
\lvert\operatorname{Im}X\rvert\le\beta\lVert W\rVert^2 .\tag{2}
$$

Отсюда $E\operatorname{Re}\lambda\ge(1-\alpha)\lVert W\rVert^2>0$ и
$(1-\alpha)E\lvert\operatorname{Im}\lambda\rvert\le(1-\alpha)\beta\lVert W\rVert^2\le\beta E\operatorname{Re}\lambda$.

**Утверждение 2 (Lean).** Оператор $T_a$ ограниченно обратим,
$\lVert T_a^{-1}\rVert\le(1-\alpha)^{-1}$. При каждом $s\ge0$ уравнение $(L_a+s)f=h$
однозначно разрешимо на области, и

$$
\lVert f\rVert\le\frac{\lVert G\rVert}{1-\alpha}\,\lVert h\rVert\quad(s\ge0),\qquad
\lVert f\rVert\le\frac{\lVert T_a\rVert^2}{(1-\alpha)^2\,s}\,\lVert h\rVert\quad(s>0).\tag{3}
$$

Здесь $\lVert T_a\rVert\le1+\alpha+\beta$ (расчёт: $T_a=I+a_eR+a_oR$).

**Доказательство.** Оценки (2) верны для каждого $W\in L_2$, поэтому

$$
\operatorname{Re}\langle W,T_aW\rangle\ge(1-\alpha)\lVert W\rVert^2 .\tag{4}
$$

Из (4) следует $\lVert T_aW\rVert\ge(1-\alpha)\lVert W\rVert$: оператор $T_a$ инъективен
и имеет замкнутый образ. Если $v$ ортогонален образу, то $\langle T_av,v\rangle=0$ и по
(4) $v=0$. Значит, $T_a$ обратим и $\lVert T_a^{-1}\rVert\le(1-\alpha)^{-1}$.

Пусть $s\ge0$. Для $f$ из области и $W=-f''$ имеем $f=GW$ (S-GREEN:
`spectralGreen_left_inverse`) и по факторизации $L_a=T_a(-D^2)$ из C8, которая оценку
произведения не использует, $(L_a+s)f=(T_a+sG)W$. Энергетическое тождество
(`negativeSecondWeakDeriv_energy`) и равенство $-(GW)''=W$ дают
$\langle W,GW\rangle=\lVert(GW)'\rVert^2\ge0$, поэтому $T_a+sG$ удовлетворяет (4) с той
же постоянной и обратим с нормой обратного не больше $(1-\alpha)^{-1}$. Функция
$f=G(T_a+sG)^{-1}h$ лежит в области и решает уравнение: $-f''=(T_a+sG)^{-1}h$. Другого
решения нет, откуда первая оценка (3).

Пусть $s>0$ и $u=T_a^{-1}f$. Применяя $T_a^{-1}$ к равенству $T_aW+sf=h$, получаем
$W+su=T_a^{-1}h$. Скалярное умножение на $f$ и $\langle f,W\rangle=\lVert f'\rVert^2\ge0$
дают

$$
s\operatorname{Re}\langle f,u\rangle\le\operatorname{Re}\langle f,T_a^{-1}h\rangle
\le\frac{\lVert f\rVert\,\lVert h\rVert}{1-\alpha}.
$$

По (4) $\operatorname{Re}\langle f,u\rangle=\operatorname{Re}\langle T_au,u\rangle\ge(1-\alpha)\lVert u\rVert^2$,
а $\lVert f\rVert\le\lVert T_a\rVert\lVert u\rVert$. Отсюда
$s(1-\alpha)\lVert f\rVert^2\le\lVert T_a\rVert^2\lVert f\rVert\lVert h\rVert/(1-\alpha)$,
то есть вторая оценка (3).

**Граница точности.** Оценка $\lVert f\rVert\le\lVert G\rVert\lVert h\rVert/(s+1-\alpha)$
неверна при $s>0$: при $a=0$, $\alpha=0$, $f=\cos(\pi x/2)$, $h=(\lambda_1+s)f$ левая часть равна
$\lVert h\rVert/(\lambda_1+s)$, правая — $\lVert h\rVert/(\lambda_1(s+1))$, а
$\lambda_1=\pi^2/4>1$. Из равенства
$\langle W,T_aW\rangle+s\lVert f'\rVert^2=\langle W,h\rangle$ следует только
$(1-\alpha)\lVert W\rVert^2+s\lVert f'\rVert^2\le\lVert W\rVert\lVert h\rVert$: слагаемое
$s\lVert f'\rVert^2$ не оценивается снизу через $s\lVert W\rVert^2$. Отрицание этой
оценки доказано в Lean в ответе Aristotle на задачу 9 (`not_resolvent_estimate`, файл
`ResolventCounter.lean` в архиве; в библиотеку не входит).

**Утверждение 3 (источник).** Система корневых функций $L_a$ полна в $L_2(-1,1)$.

**Доказательство.** S3, теорема 4.7, с. 129: оператор порядка $\alpha_0$, у которого есть
лучи наилучшего убывания резольвенты с углами между соседними не больше $\pi\alpha_0$,
имеет полную систему корневых векторов. Порядок $L_a$ равен $2$: собственные значения
$G$ равны $\bigl((n+\tfrac12)\pi\bigr)^{-2}$ и $(m\pi)^{-2}$, поэтому
$s_j(K_a)\le\lVert T_a^{-1}\rVert s_j(G)\le cj^{-2}$, $K_a=GT_a^{-1}$. По второй оценке
(3) $\lVert(L_a+s)^{-1}\rVert\le C/s$ при $s>0$,
$C=(1+\alpha+\beta)^2/(1-\alpha)^2$, а это и есть определение (2.9) из S3 с
$\lvert\lambda\rvert^{-1}$. Оператор $L_a$ замкнут, плотно определён и имеет компактный
обратный $K_a$. Одного луча достаточно для класса $\mathscr K_2$ (S3, абзац после
замечания 4.6).

**Следствия.** Для нечётного вещественного $a\in L_\infty$ любой величины $\alpha=0$:
$\lvert\operatorname{Im}\lambda\rvert\le\lVert a\rVert_\infty\operatorname{Re}\lambda$,
корневые функции полны; при $a=x/2$ раствор сектора задаётся неравенством
$\lvert\operatorname{Im}\lambda\rvert\le\tfrac12\operatorname{Re}\lambda$. Для чётного $a$
с $\lvert a\rvert\le\alpha<1$ собственные значения вещественны и положительны. Для
коэффициента C12 $\alpha=\beta=1/2$: корневые функции полны, хотя базиса Рисса из
собственных функций нет. Для коэффициента C11 $a_e=2$, условие $\alpha<1$ нарушено, и
собственных значений нет вовсе.

**Lean.** `EigenvalueSector.lean`: `reflectedMultiplier_add_adjoint_ae`,
`reflectedMultiplier_sub_adjoint_ae`, `inner_reflectedMultiplier_left`,
`eigenvalue_sector`, `oddCoefficient_eigenvalue_sector`,
`evenCoefficient_eigenvalue_real`, `ramp_eigenvalue_sector`. В `eigenvalue_sector`
условия записаны как $\lVert a(x)\pm a(-x)\rVert\le2\alpha$, $2\beta$. Утверждение 2:
`ResolventAux.lean` (задача 9 Aristotle) — `reflectedMultiplier_re_inner_bound_of_real`,
`exists_inverse_of_coercive`, `resolvent_estimate_corrected` (разрешимость и первая
оценка (3)); `ResolventBound.lean` — `principalOperator_boundedInverse` и
`resolvent_ray_estimate` (вторая оценка (3), доказана локально). В
`resolvent_ray_estimate` постоянная записана через $\lVert T_a\rVert$; оценка
$\lVert T_a\rVert\le1+\alpha+\beta$ в Lean не выписана. Утверждение 3 в Lean не
формализовано.

**Проверка.** `output/ideas/halfslope_check.py`: коллокация Чебышёва для $a=x/2$,
$a=1/2+x/4$, $a=\max(x,0)$, $a=2x$; неравенство сектора выполнено с запасом.

**Границы.** Условие $\alpha<1$ достаточно; необходимость не исследована. Доказательство
теоремы 4.7 в S3 опирается на оценки определителей возмущения и теорему
Фрагмена–Линделёфа и в проекте не проверялось. Из полноты базисность не следует (C12).

**Рецензия (12.10.2026).** Проверены утверждения 2 и 3 и абзац «Граница точности».
Вердикт: **принято**; ошибок и пробелов нет, неточностей пять.

1. *Утверждение 2, ссылки.* Равенства $f=GW$, $-(GW)''=W$, принадлежность $GW$ области и
   тождество $\langle W,GW\rangle=\lVert(GW)'\rVert^2$ использованы без ссылки. Из C8
   берётся только факторизация $L_af=T_a(-f'')$, которая не зависит от условия
   $\lvert a(x)a(-x)\rvert\le\kappa<1$ записи C8; в C17 этого условия нет, и это стоит
   сказать явно. Обратимость $T_a$ в C17 получена из (4), формула
   $T_a^{-1}=d(I-aR)$ не используется.
2. *Утверждение 2, существование.* В шаге «единственное решение —
   $f=G(T_a+sG)^{-1}h$» единственность следует из инъективности $T_a+sG$ и $f=GW$;
   существование требует обратной проверки: $W=(T_a+sG)^{-1}h$, $f=GW$ лежит в области,
   $-f''=W$, $(L_a+s)f=h$. Проверка занимает строку и в тексте опущена.
3. *Граница точности.* Контрпример работает только при $s>0$: неравенство
   $1/(\lambda_1+s)>1/(\lambda_1(s+1))$ равносильно $(\lambda_1-1)s>0$, при $s=0$ обе части
   равны. Нужно дописать «при $s>0$» и $h=(\lambda_1+s)f$.
4. *Утверждение 3, стоячие предположения S3.* Теорема 4.7 сформулирована для замкнутого
   плотно определённого $T$ с компактным $T^{-1}$ (S3, §4, с. 125). Для $L_a$ это верно:
   $L_a=T_a(-D^2)$ с ограниченно обратимым $T_a$ замкнут, область плотна,
   $L_a^{-1}=GT_a^{-1}$ компактен (обратимость при $s=0$ — утверждение 2). В тексте не
   выписано. Фраза «одного луча достаточно для $\mathscr K_2$» стоит в S3 в абзаце после
   замечания 4.6, а само замечание 4.6 ($\mathscr K_\gamma\subset\mathscr K_{\gamma-\varepsilon}$)
   нужно теореме для граничного случая $\gamma=\alpha=2$: по замечанию 2.4 луч расширяется
   до сектора, раствор дополнения строго меньше $2\pi$, и теорема Фрагмена–Линделёфа
   применима при порядке $1/2$ нормального типа. Без этого расширения граничный случай
   неверен: функция $\sin^2\sqrt{-\lambda}/(-\lambda)$ целая, порядка $1/2$ и убывает как
   $1/s$ на луче $\lambda=-s$.
5. *Карточка S3, «Применимость к C17»* противоречит записи: в ней стоит оценка
   $\lVert G\rVert/(s+1-\alpha)$, опровергнутая в абзаце «Граница точности», и
   утверждение об отсутствии равномерной оценки $C/s$, тогда как вторая оценка (3) даёт
   $C=(1+\alpha+\beta)^2/(1-\alpha)^2$ при всех $s>0$. Карточку нужно привести к (3).
   Отметки агента `source-verifier` («Сверка») у карточки нет; доказательства теорем 4.2
   и 4.4 не читались.

Гипотезы теоремы 4.7 сверены по распознанному тексту S3: порядок
$s_j(T^{-1})\le cj^{-\alpha}$ (с. 125) выполнен с $\alpha=2$, так как
$s_j(G)=4/(\pi^2j^2)$ и $s_j(GT_a^{-1})\le\lVert T_a^{-1}\rVert s_j(G)$; луч
$\arg\lambda=\pi$ удовлетворяет (2.9) с $r_0=0$; $\gamma=2\le\alpha$. Пересчитаны вручную:
сопряжённый к $aR$ и оценки (2) для произвольного $W$; (4) и обратимость $T_a$;
$\lVert T_a\rVert\le1+\alpha+\beta$; цепочка второй оценки (3); контрпример при $a=0$;
спектр $G$. Независимая проверка утверждения 3: оператор $M=G^{1/2}T_a^{-1}G^{1/2}$
ядерный, $\operatorname{Re}\langle Mv,v\rangle>0$ при $G^{1/2}v\ne0$, $\ker M=0$; по
теореме Лидского его корневые векторы полны, а $K_aG^{1/2}=G^{1/2}M$ и образ $G^{1/2}$
плотен. Этот путь не опирается на теоремы 4.2 и 4.4 из S3.

**Соответствие формализации (12.10.2026).** Объявления: `principalOperator_boundedInverse`,
`resolvent_ray_estimate` (`ResolventBound.lean`), `resolvent_estimate_corrected`
(`ResolventAux.lean`). Обратный перевод. Даны функция $a\colon\mathbb R\to\mathbb R$,
существенно ограниченная на $(-1,1)$, и число $\alpha<1$ с
$\lvert a(x)+a(-x)\rvert\le2\alpha$ п.в. на $(-1,1)$; коэффициент оператора — класс
комплексной функции $x\mapsto a(x)$ в $L_\infty$. (i) Существует ограниченный оператор
$S$ в $L_2(-1,1;\mathbb C)$ с $ST_a=T_aS=I$ и $\lVert S\rVert\le(1-\alpha)^{-1}$, где
$(T_ag)(x)=g(x)+a(x)g(-x)$ п.в. (ii) При $s\ge0$ и $h\in L_2$ существует ровно один $f$
из слабой области Дирихле (две слабые производные в $L_2$, непрерывный на $[-1,1]$
представитель равен нулю в $\pm1$) с $-f''-a\,f''(-\cdot)+sf=h$, и каждый такой $f$
удовлетворяет $\lVert f\rVert\le\lVert G\rVert\lVert h\rVert/(1-\alpha)$, где
$G$ = `spectralGreen`. (iii) При $s>0$ каждый $f$ из области с тем же уравнением
удовлетворяет $\lVert f\rVert\le\lVert T_a\rVert^2\lVert h\rVert/((1-\alpha)^2s)$; это
априорная оценка, существование решения даёт (ii). Сравнение: вещественность
$a\in L_\infty$ и $\lvert a_e\rvert\le\alpha<1$ — совпадает ($\alpha<0$ в Lean допустимо, но
гипотеза тогда несовместна, как и в записи); $\lvert a_o\rvert\le\beta$ в Lean нет — Lean
сильнее, в выводах утверждения 2 $\beta$ не участвует; обратимость $T_a$ с оценкой нормы —
совпадает; однозначная разрешимость при $s\ge0$ и обе оценки (3) — совпадают; $G$ задан
рядом по модельному базису, а его совпадение с обратным к $-D^2$ на области доказано
(`spectralGreen_left_inverse`, `spectralGreen_right_inverse`); значение $\lVert G\rVert$ в
Lean не вычислено, запись его и не называет. Фраза «$\lVert T_a\rVert\le1+\alpha+\beta$»
стоит под пометкой «(Lean)», но в Lean не доказана: это оговорено в абзаце «Lean», а
постоянная $C$ утверждения 3 опирается на неё вне Lean. Проверки
(`output/fidelity/C17_C18.lean`, компилируется): гипотезы выполнены для $a=x/2$,
$\alpha=0$; специализация даёт $\lVert T_a^{-1}\rVert\le1$,
$\lVert f\rVert\le\lVert T_a\rVert^2\lVert h\rVert/s$ и однозначную разрешимость
$L_af=h$ с $\lVert f\rVert\le\lVert G\rVert\lVert h\rVert$; при $\alpha<0$ из гипотезы
выведено противоречие; аксиомы трёх теорем — `propext`, `Classical.choice`, `Quot.sound`.
Не проверено в Lean: необратимость $T_a$ на границе $\alpha=1$ (например, $a=-1$).
Вердикт: соответствует с оговорками — единственное расхождение (оценка
$\lVert T_a\rVert$) безвредно и уже названо в записи; «Границы» менять не нужно.

### C18. Пример $a(x)=x/2$: нет базиса Рисса из собственных функций

**Условия.** $a(x)=x/2$; $a\in W^1_\infty$, $a$ нечётна,
$\lvert a(x)a(-x)\rvert\le1/4$.

**Утверждение (Lean).** Не существует базиса Рисса пространства $L_2(-1,1)$, каждый
элемент которого — собственная функция $L_a$ из слабой области Дирихле.

**Доказательство.** Шаг 1, точное решение. Пусть $s(x)=1+ix/2$, $t\ge0$ и
$u_t=s^{1/4}\exp(-4ts^{1/2})$ с главными ветвями. Дифференцирование даёт

$$
s\,(-u_t'')-t^2u_t=-\frac{3}{64\,s}\,u_t .
$$

Шаг 2, квазимоды. Имеем $\lvert u_t\rvert=\lvert s\rvert^{1/4}e^{-4t\operatorname{Re}\sqrt s}$
и $(\operatorname{Re}\sqrt s)^2=(\lvert s\rvert+1)/2$, поэтому
$\operatorname{Re}\sqrt s\le1+1/512$ при $\lvert x\rvert\le1/4$ и
$\operatorname{Re}\sqrt s\ge1+1/200$ при $\lvert x\rvert\ge1/2$. Пусть $\chi$ — гладкая
срезка, $\chi=1$ на $[-1/2,1/2]$, $\chi(\pm1)=0$, и $Z_t=\chi u_t$. Тогда
$s(-Z_t'')-t^2Z_t=-\tfrac{3}{64s}Z_t-R_t$, где $R_t$ содержит $\chi'$, $\chi''$ и
сосредоточен на $\lvert x\rvert\ge1/2$:
$\lVert R_t\rVert\le K(1+t)e^{-4t(1+1/200)}$, тогда как
$\lVert Z_t\rVert\ge c_0e^{-4t(1+1/512)}$. По C4 $UL_aU^{-1}=s\cdot(-D^2)$, и для
$y_t=U^{-1}Z_t$ получаем $\lVert(L_a-t^2)y_t\rVert\le C\lVert y_t\rVert$ с постоянной
$C$, не зависящей от $t\ge0$.

Шаг 3. Пусть $\lbrace e_i\rbrace$ — базис Рисса из собственных функций, $L_ae_i=\lambda_ie_i$,
с постоянной $C_b$. Разложение $y_t$ по базису даёт для каждого $t$ индекс $i$ с
$\lvert\lambda_i-t^2\rvert<D=C_bC+1$ (`rieszEigenbasis_lower_bound`, C12).

Шаг 4, счёт. Если $\lvert\lambda_i\rvert\le r$ для $i$ из конечного множества $S$, то
$\operatorname{card}S\le c\sqrt r+2$: оператор $K_a=GT_a^{-1}$ есть сумма оператора
ранга не больше $2N$ и оператора нормы не больше $\lVert T_a^{-1}\rVert(N\pi)^{-2}$, а
$K_ae_i=\lambda_i^{-1}e_i$. Если хвост по норме меньше $1/(rC_b)$, то на оболочке
$\lbrace e_i\rbrace_{i\in S}$ конечномерная часть инъективна, и
$\operatorname{card}S\le2N$; достаточно $N=\lfloor\sqrt{Ar}/\pi\rfloor+1$,
$A=C_b\lVert T_a^{-1}\rVert+1$.

Шаг 5. Точкам $t^2=3Dk$, $k=1,\dots,n$, по шагу 3 отвечают $n$ разных индексов с
$\lvert\lambda_i\rvert\le4Dn$. По шагу 4 $n\le c\sqrt{4Dn}+2$, что неверно при больших
$n$.

**Lean.** Задача 8 Aristotle. `HalfSlopeProfile.lean`: функции `halfSlopeS`, `halfSlopeU`,
срезка `halfSlopeCut`, `halfSlopeZ_equation`, оценки `halfSlopeR_norm_le`,
`halfSlopeZ_norm_ge`; ветви записаны как $\exp(\tfrac14\log s)$ и $\exp(\tfrac12\log s)$.
`RieszEigenCount.lean`: `RieszBasis.card_le_of_finiteRank_approx`. `HalfSlope.lean`:
`halfSlopeCoefficient`, `halfSlopeClass`, `halfSlope_quasimodes`, `rieszEigenbasis_count`,
`halfSlope_no_riesz_eigenbasis`. Лемма `rieszEigenbasis_count` верна для любого
$a\in L_\infty$ с обратимым определителем $1-a(x)a(-x)$.

**Проверка.** `output/ideas/halfslope_check.py`: тождество шага 1 выполнено с точностью
$10^{-14}$ в десяти точках; $\lVert(A-t^2)Z_t\rVert/\lVert Z_t\rVert\le44$ при
$t=2,5,10,20,40,80$ для $A=s\cdot(-D^2)$.

**Границы.** Базис Рисса со скобками и базис с присоединёнными функциями не исключены.
Корневые функции полны (C17). Для других нечётных коэффициентов точного решения нет;
гипотеза о квазимодах при $a(x)a(-x)<0$ — `ideas.md`, I9.

**Соответствие формализации (12.10.2026).** Объявление: `halfSlope_no_riesz_eigenbasis`
(`HalfSlope.lean`). Обратный перевод. Не существует типа индексов $\iota$ (в `Type`),
линейного гомеоморфизма $J\colon L_2(-1,1;\mathbb C)\to\ell_2(\iota;\mathbb C)$, для
которых каждый вектор $e_i=J^{-1}\delta_i$ лежит в слабой области Дирихле (две слабые
производные в $L_2$; непрерывный на $[-1,1]$ представитель равен нулю в $\pm1$) и
при некотором $\lambda_i\in\mathbb C$ выполнено
$-e_i''-a\,e_i''(-\cdot)=\lambda_ie_i$ в $L_2$, где $a$ — класс функции $x/2$ в
$L_\infty$. Коэффициент зафиксирован определением и параметром теоремы не служит; вторая
слабая производная выбрана через `Classical.choose`, но единственна
(`MemIntervalH2.derivatives_unique`); условие $e_i\ne0$ не выписано и следует из
$Je_i=\delta_i$; на $\lambda_i$ ограничений нет. Сравнение: коэффициент $a=x/2$ —
совпадает (`realIntervalCoefficient_ae`); свойства «$a\in W^1_\infty$, нечётна,
$\lvert a(x)a(-x)\rvert\le1/4$» — свойства фиксированного коэффициента, в формулировку
не входят (два последних доказаны: `halfSlopeClass_odd`, `halfSlopeClass_product`);
«базис Рисса» — структура проекта `RieszBasis`, её равносильность плотности оболочки и
двусторонним оценкам Рисса доказана (`exists_rieszBasis_iff_finiteBounds_dense`), образ
ортонормированного базиса при изоморфизме даёт `rieszBasisOfHilbertBasis`; «собственная
функция из слабой области Дирихле» — совпадает; вывод «не существует» — совпадает.
Ограничение $\iota$ : `Type` безвредно: $L_2(-1,1)$ сепарабельно, и множество индексов
счётно. Проверки (`output/fidelity/C17_C18.lean`, компилируется): тип
`RieszBasis (ℕ ⊕ ℕ) IntervalL2` непуст (`constantModelRieszBasis`), то есть отрицание не
следует из отсутствия базисов; тот же предикат с коэффициентом $a=0$ выполнен
(`zero_coefficient_has_riesz_eigenbasis`, из `evenCoefficient_AC_riesz_eigenbasis`), то
есть формулировка различает коэффициенты; векторы базиса ненулевые; модельные функции
лежат в области, постоянная $1$ не лежит (`one_not_memDirichletH2`); аксиомы —
`propext`, `Classical.choice`, `Quot.sound`. Не проверено в Lean: существование хотя бы
одной собственной функции $L_a$ при $a=x/2$ и пример системы, не являющейся `RieszBasis`.
Вердикт: соответствует; абзац «Границы» (скобки и присоединённые функции не исключены)
точно описывает, чего теорема не утверждает.

### C19. Калибровка нечётной фазой: полнота для всего класса постановки

**Условия.** Вещественный $a\in L_\infty(-1,1)$. Существует нечётная вещественная
$\psi\in W^2_\infty(-1,1)$, для которой

$$
\operatorname{ess\,sup}_{x}\,\bigl\lvert a(x)e^{-\psi(x)}+a(-x)e^{\psi(x)}\bigr\rvert=2\alpha<2. \tag{5}
$$

При $\psi=0$ это условие $\lvert a_e\rvert\le\alpha<1$ записи C17. Оценка произведения
$a(x)a(-x)$ снизу и гладкость $a$ не предполагаются.

**Обозначения.** $r=e^{\psi/2}$, $w=e^{-\psi/2}$, $b=ae^{-\psi}$,
$\rho=\tfrac12\psi''+\tfrac14\psi'^2$, $B_0g=-\psi'g'-\rho g$, $D$ — слабая область
Дирихле, $G$ — обратный к $-D^2$ на $D$.

**Утверждение 1 (собственный расчёт).** Оператор $T_a$ ограниченно обратим. Существуют
$C>0$ и $s_0\ge0$, для которых при каждом $s>0$, $s\ge s_0$, оператор $L_a+s$ взаимно
однозначно отображает $D$ на $L_2(-1,1)$ и

$$
\lVert(L_a+s)^{-1}\rVert\le\frac{C}{s},\qquad
C=\frac{2\lVert T_b\rVert^2e^{\lVert\psi\rVert_\infty}}{(1-\alpha)^2},\qquad
s_0=4C_2^2C_1(1+C_1), \tag{6}
$$

где $C_1=\lVert T_b\rVert^2/(1-\alpha)^2$ и
$C_2=\lVert T_b\rVert\bigl(\lVert\psi'\rVert_\infty+\lVert\rho\rVert_\infty\lVert G\rVert^{1/2}\bigr)(1-\alpha)^{-1/2}$.

**Доказательство.** Шаг 1, калибровка. Функции $r$, $w$ лежат в $W^2_\infty$, $rw=1$,
$r'=\tfrac12\psi'r$, $r''=\rho r$, поэтому $2wr'=\psi'$ и $wr''=\rho$. Так как $\psi$
нечётна, $r(-x)=e^{-\psi(x)/2}$ и $b(x)r(x)=a(x)e^{-\psi(x)/2}=a(x)r(-x)$. По C10
$T_aM_r=M_rT_b$, умножения на $r$ и на $w$ отображают $D$ в $D$ и взаимно обратны, и для
$g\in D$

$$
L_a(rg)=r\bigl(L_bg+T_bB_0g\bigr). \tag{7}
$$

Шаг 2, коэффициент $b$. Функция $b$ вещественна и существенно ограничена,
$b(-x)=a(-x)e^{\psi(x)}$, поэтому $b(x)+b(-x)$ — выражение под модулем в (5) и
$\lvert b_e\rvert\le\alpha<1$ п.в. К $L_b$ применимо утверждение 2 записи C17: $T_b$
обратим, $\lVert T_b^{-1}\rVert\le(1-\alpha)^{-1}$, при $s>0$ оператор $L_b+s$ взаимно
однозначно отображает $D$ на $L_2$, и $R_s=(L_b+s)^{-1}$ удовлетворяет
$\lVert R_s\rVert\le C_1/s$. Из $T_a=M_rT_bM_w$ следует обратимость $T_a$. Из C8 берём
только факторизацию $L_bg=T_b(-g'')$, которая не зависит от оценки произведения
$b(x)b(-x)$; формула $T_b^{-1}=d(I-bR)$ не используется.

Шаг 3, подчинённость. Пусть $g\in D$. Энергетическое тождество даёт
$\lVert g'\rVert^2\le\lVert g\rVert\lVert g''\rVert$, а из $g=G(-g'')$ следует
$\lVert g\rVert\le\lVert G\rVert^{1/2}\lVert g\rVert^{1/2}\lVert g''\rVert^{1/2}$. Так как
$L_bg=T_b(-g'')$, имеем $\lVert g''\rVert\le(1-\alpha)^{-1}\lVert L_bg\rVert$. Поэтому

$$
\lVert T_bB_0g\rVert\le\lVert T_b\rVert\bigl(\lVert\psi'\rVert_\infty\lVert g'\rVert+\lVert\rho\rVert_\infty\lVert g\rVert\bigr)
\le C_2\lVert g\rVert^{1/2}\lVert L_bg\rVert^{1/2}. \tag{8}
$$

Шаг 4, ряд Неймана. Пусть $s>0$, $h\in L_2$, $g=R_sh$. Тогда
$\lVert g\rVert\le C_1\lVert h\rVert/s$ и
$\lVert L_bg\rVert=\lVert h-sg\rVert\le(1+C_1)\lVert h\rVert$. Оператор $K_s=T_bB_0R_s$
линеен, и по (8)

$$
\lVert K_sh\rVert\le C_2\sqrt{C_1(1+C_1)/s}\,\lVert h\rVert .
$$

При $s\ge s_0$ правая часть не больше $\tfrac12\lVert h\rVert$, оператор $I+K_s$ обратим и
$\lVert(I+K_s)^{-1}\rVert\le2$. На $D$ выполнено $L_b+T_bB_0+s=(I+K_s)(L_b+s)$, поэтому
$L_b+T_bB_0+s$ взаимно однозначно отображает $D$ на $L_2$, и обратный оператор
$R_s(I+K_s)^{-1}$ имеет норму не больше $2C_1/s$.

Шаг 5, перенос. По (7) $(L_a+s)(rg)=r(L_b+T_bB_0+s)g$ при $g\in D$. Умножение на $r$ —
биекция $D$ и биекция $L_2$, поэтому $L_a+s$ взаимно однозначно отображает $D$ на $L_2$ и
$(L_a+s)^{-1}=M_rR_s(I+K_s)^{-1}M_w$. Так как
$\lVert r\rVert_\infty\lVert w\rVert_\infty\le e^{\lVert\psi\rVert_\infty}$, получаем (6).

**Утверждение 2 (источник).** В условиях записи система корневых функций $L_a$ полна в
$L_2(-1,1)$.

**Доказательство.** S3, теорема 4.7, с. 129, как в утверждении 3 записи C17. Оператор
$L_a=T_a(-D^2)$ с ограниченно обратимым $T_a$ замкнут и плотно определён,
$L_a^{-1}=GT_a^{-1}$ компактен и $s_j(L_a^{-1})\le\lVert T_a^{-1}\rVert s_j(G)\le cj^{-2}$:
порядок равен $2$. По (6) $\lVert(L_a-\lambda)^{-1}\rVert\le C\lvert\lambda\rvert^{-1}$ на
луче $\lambda=-s$, $s>r_0=s_0$; это определение (2.9) из S3. Одного луча
достаточно для класса $\mathscr K_2$ (S3, абзац после замечания 4.6).

**Утверждение 3 (собственный расчёт).** Пусть $a$ вещественна и непрерывна на $[-1,1]$ и
$\lvert a(x)a(-x)\rvert<1$ при каждом $x\in[0,1]$. Тогда существует нечётная
$\psi\in C^\infty[-1,1]$, равная нулю в окрестности нуля, с условием (5).

**Доказательство.** Положим $F(x,t)=a(x)e^{-t}+a(-x)e^{t}$ на $[0,1]\times\mathbb R$ и
$I(x)=\lbrace t\in\mathbb R:\lvert F(x,t)\rvert<2\rbrace$.

Шаг 1: $I(x)$ — непустой интервал. Пусть $p=a(x)$, $q=a(-x)$; по условию $\lvert pq\rvert<1$.
Если $pq>0$, то $\lvert F(x,t)\rvert=\lvert p\rvert e^{-t}+\lvert q\rvert e^{t}$ — выпуклая
функция $t$, равная $2\sqrt{pq}<2$ при $t=\tfrac12\ln(\lvert p\rvert/\lvert q\rvert)$;
множество, где выпуклая функция меньше $2$, выпукло. Если $pq<0$, то производная
$-pe^{-t}+qe^{t}$ имеет знак $q$ при всех $t$, функция $F(x,\cdot)$ строго монотонна и
принимает все вещественные значения; прообраз интервала $(-2,2)$ — непустой интервал.
Если $p=q=0$, то $I(x)=\mathbb R$. Если $q=0\ne p$, то
$I(x)=(\ln(\lvert p\rvert/2),+\infty)$; если $p=0\ne q$, то
$I(x)=(-\infty,\ln(2/\lvert q\rvert))$.

Шаг 2: покрытие. Функция $x\mapsto F(x,0)=a(x)+a(-x)$ непрерывна и
$\lvert F(0,0)\rvert=2\lvert a(0)\rvert<2$, поскольку $a(0)^2<1$. Выберем $\delta\in(0,1/2)$
с $\lvert F(x,0)\rvert<2$ при $x\in[0,2\delta]$ и положим $U_0=(-1,2\delta)$, $t_0=0$.
Для каждого $y\in[\delta,1]$ возьмём $t_y\in I(y)$; функция $x\mapsto F(x,t_y)$
непрерывна, поэтому есть открытый интервал $U_y\ni y$, $U_y\subset(\delta/2,+\infty)$, с
$\lvert F(x,t_y)\rvert<2$ при $x\in U_y\cap[0,1]$. Множества $U_0$ и $U_y$ покрывают
$[0,1]$; выберем конечное подпокрытие $U_0,U_1,\dots,U_n$ с числами $t_0=0,t_1,\dots,t_n$
(множество $U_0$ в него входит: точка $0$ лежит только в $U_0$).
При $x\in U_i\cap[0,1]$ имеем $t_i\in I(x)$.

Шаг 3: склейка. Пусть $\chi_0,\dots,\chi_n\in C^\infty(\mathbb R)$ — гладкое разбиение
единицы, подчинённое покрытию компакта $[0,1]$:
$\chi_i\ge0$, $\operatorname{supp}\chi_i\subset U_i$, $\sum_i\chi_i=1$ на $[0,1]$. Положим
$\psi(x)=\sum_i\chi_i(x)t_i$ при $x\in[0,1]$. Число $\psi(x)$ — выпуклая комбинация тех
$t_i$, для которых $x\in U_i$; все они лежат в интервале $I(x)$, поэтому
$\psi(x)\in I(x)$. При $x\in[0,\delta/2]$ точка $x$ лежит только в $U_0$, и $\psi(x)=0$.
Продолжим $\psi$ на $[-1,0)$ равенством $\psi(x)=-\psi(-x)$: функция нечётна и гладка на
$[-1,1]$, так как равна нулю на $[-\delta/2,\delta/2]$.

Шаг 4: оценка. Функция $x\mapsto\lvert F(x,\psi(x))\rvert$ непрерывна на $[0,1]$ и меньше
$2$ в каждой точке; обозначим её максимум через $2\alpha$, $\alpha<1$. При $x\in[-1,0)$ и
$y=-x$ имеем $a(x)e^{-\psi(x)}+a(-x)e^{\psi(x)}=a(-y)e^{\psi(y)}+a(y)e^{-\psi(y)}=F(y,\psi(y))$.
Значит, (5) выполнено на всём $[-1,1]$.

**Следствие (оценка — собственный расчёт, полнота — источник).** Для каждого коэффициента постановки `question.md` ($a\in W^1_\infty$
вещественна, $\lvert a(x)a(-x)\rvert\le\kappa<1$ п.в.) корневые функции $L_a$ полны в
$L_2(-1,1)$ и верна оценка (6): липшицев представитель $a$ непрерывен, и оценка
произведения верна в каждой точке.

**Замечания.** 1. Из (5) следует $a(x)a(-x)=b(x)b(-x)=b_e^2-b_o^2\le\alpha^2$ п.в.; снизу
произведение не ограничено ничем, кроме $-\lVert a\rVert_\infty^2$. 2. Для коэффициента C11
($a=4\cdot\mathbf 1_{(0,1)}$) функции $\psi$ нет: $\psi$ непрерывна и $\psi(0)=0$, поэтому
при $x\to0+$ выражение под модулем в (5) равно $4e^{-\psi(x)}\to4$. 3. Пример вне C6 и
C17: $a(x)=4\max(x,0)$, $a_e(x)=2\lvert x\rvert$ достигает $2$. При $\psi(x)=2x$ получаем
$b(x)=4xe^{-2x}$ при $x>0$, $b=0$ при $x\le0$, $\alpha=1/e$, $B_0g=-2g'-g$.

**Lean.** Утверждение 1 — `GaugeResolvent.lean` (доказано локально 13.10.2026):
`gauge_principalOperator_boundedInverse`, `gauge_shifted_similarity`,
`gaugeShiftedOperator_solvable`, `gauge_resolvent_ray_estimate`. Теоремы записаны в
калибровочных данных: вещественные $a,b\in L_\infty$, веса $r,w\in W^2_\infty$ с $rw=1$,
$b(x)r(x)=a(x)r(-x)$ и $\lvert b(x)+b(-x)\rvert\le2\alpha<2$ п.в.; вывод — существование
$C>0$, $s_0>0$ с однозначной разрешимостью $(L_a+s)f=h$ на слабой области Дирихле и
$\lVert f\rVert\le C\lVert h\rVert/s$ при $s\ge s_0$. Построение $r=e^{\psi/2}$,
$w=e^{-\psi/2}$, $b=ae^{-\psi}$ по функции $\psi$ в Lean не формализовано. Постоянные в
формулировке не выписаны; в доказательстве $C=2\lVert r\rVert\lVert w\rVert C_1+1$,
$s_0=4C_2^2C_1(1+C_1)+1$, где $C_2$ записана через $2\lVert w\rVert\lVert r'\rVert$ и
$\lVert w\rVert\lVert r''\rVert$ вместо $\lVert\psi'\rVert_\infty$ и
$\lVert\rho\rVert_\infty$. Вместо ряда Неймана на области доказательство Lean работает с
ограниченными операторами в переменной $W=-g''$. Утверждение 3 — `PhaseSelection.lean`
(задача 10 Aristotle): `exists_phase_value`, `convex_phase_values`, `exists_odd_phase`;
функция $\psi$ класса $C^\infty(\mathbb R)$, нечётна, равна нулю при $\lvert x\rvert<\delta$,
оценка (5) выполнена в каждой точке $[-1,1]$. Вместо покрытия и разбиения единицы
доказательство Lean использует теорему Mathlib
`exists_contMDiffMap_forall_mem_convex_of_local_const`. Утверждение 2 и следствие в Lean
не формализованы.

**Проверка.** `output/ideas/i17_ray_check.py`, `output/ideas/i17_critic.py`: SymPy-проверка
тождества (7) для $a=4\max(x,0)$, $r=e^x$ на трёх пробных функциях отдельно на $(0,1)$ и
$(-1,0)$; коллокация Чебышёва, $N=300$ и $N=600$: $s\lVert(L_a+s)^{-1}\rVert$ равно
$0{,}329;\ 0{,}982;\ 1{,}107;\ 1{,}174;\ 1{,}213;\ 1{,}233$ при $s=1,10,\dots,10^5$.

**Границы.** Lean подтверждает утверждение 1 в калибровочных данных $(b,r,w)$ и только
существование $C$ и $s_0$; построение $r=e^{\psi/2}$, $w=e^{-\psi/2}$, $b=ae^{-\psi}$ по
$\psi$ и значения постоянных (6) — собственный расчёт без проверки в Lean (узел S-GLUE в
`blueprint.md`). Сектор для собственных значений $L_a$ отсюда не следует: спектр исключён
только на луче $(-\infty,-s_0]$. Постоянные $C$ и $s_0$ растут вместе с
$\lVert\psi'\rVert_\infty$, $\lVert\psi''\rVert_\infty$ и не оценены через $a$.
Доказательство теоремы 4.7 в S3 в проекте не проверялось. Для разрывных $a\in L_\infty$
условие (5) может не выполняться (C11). Из полноты базисность не следует (C12, C18).

**Рецензия (13.10.2026).** Проверены утверждения 1–3, следствие, замечания 1–3, абзацы
«Lean» и «Границы». Вердикт: **принято**; ошибок и пробелов нет, неточностей пять.

1. *Утверждение 1, шаги 2–3, ссылка на C8.* Равенство $L_bg=T_b(-g'')$ взято из C8 без
   ссылки. Условие C8 $\lvert b(x)b(-x)\rvert\le\kappa<1$ для $b$ может не выполняться:
   $b(x)b(-x)=a(x)a(-x)$ ограничено сверху числом $\alpha^2$, а снизу только числом
   $-\lVert a\rVert_\infty^2$. Используется лишь факторизация, которая от этого условия не
   зависит (как в C17); обратимость $T_b$ берётся из C17, а не из формулы
   $T_b^{-1}=d(I-bR)$. Это нужно сказать в тексте.
2. *Утверждение 2, луч.* Достаточно $r_0=s_0$: по (6) оценка верна при всех $s>0$,
   $s\ge s_0$; $\max(s_0,1)$ не нужен, но и не вредит. Граничный случай
   $\gamma=\alpha=2$ теоремы 4.7 опирается на замечание 4.6 из S3 (п. 4 рецензии C17); в
   C19 это покрыто ссылкой «как в утверждении 3 записи C17».
3. *Карточка S3.* Абзаца «Применимость к C19» в карточке нет; по правилу проекта его
   добавляют вместе с записью. Раздела «Сверка» агента `source-verifier` у карточки нет;
   доказательства теорем 4.2 и 4.4 не читались. Утверждение 2 и следствие имеют статус
   «источник»; в заголовке следствия статус не указан.
4. *Утверждение 3, шаг 2.* Не сказано, что $U_0$ входит в конечное подпокрытие; это так,
   поскольку точка $0$ лежит только в $U_0$ (все $U_y\subset(\delta/2,+\infty)$). Шаг 3
   опирается на гладкое разбиение единицы, подчинённое конечному открытому покрытию
   компакта, — стандартный факт, не назван.
5. *Абзац «Lean».* В `gaugePerturbation_subordinate` постоянная записана через
   $\lVert w\rVert$, $\lVert r'\rVert$, $\lVert r''\rVert$ и
   $\lVert T_b^{-1}\rVert^{1/2}$ с $T_b^{-1}=d_b(I-bR)$; постоянная $C_2$ записи получена
   иначе ($2wr'=\psi'$, $wr''=\rho$, $\lVert T_b^{-1}\rVert\le(1-\alpha)^{-1}$ из C17).
   Числа $C_2$, $s_0$, $C$ из (6) этими леммами в таком виде не даются; шаги 4–5 и
   утверждение 3 опор в библиотеке не имеют.

Использование гипотез: нечётность $\psi$ — в равенствах $r(-x)=w(x)$, $br=a\,r(-\cdot)$ и
$b(-x)=a(-x)e^{\psi(x)}$; $\psi\in W^2_\infty$ — в $r,w\in W^2_\infty$ и в ограниченности
$\psi'$, $\rho$; (5) — в $\lvert b_e\rvert\le\alpha$; вещественность $a$ — в C17. В
утверждении 3 непрерывность $a$ даёт окрестности $U_y$ и максимум в шаге 4, условие
$\lvert a(x)a(-x)\rvert<1$ — непустоту $I(x)$ и $\lvert a(0)\rvert<1$. Липшицевость в
следствии используется только как источник непрерывности: следствие верно для каждой
вещественной непрерывной $a$ с $\lvert a(x)a(-x)\rvert<1$ на $[0,1]$.

Пересчитано. В SymPy: тождество (7) для $\psi=x^3+2x+\sin x$, $a=e^x+x$,
$g=(1-x^2)(x+e^x)$ и для $\psi=2x$, $a=4x$, $g=(1-x^2)\sin(3x+1)$ (пробные функции не
чётны и не нечётны), разность равна нулю; максимум $4xe^{-2x}$ на $[0,1]$ равен $2/e$ при
$x=1/2$, откуда $\alpha=1/e$ в замечании 3; там же $\rho=1$, $B_0g=-2g'-g$. Вручную:
$r''=\rho r$; оценка (8) и вид $C_2$; порог
$C_2\sqrt{C_1(1+C_1)/s}\le\tfrac12\Leftrightarrow s\ge s_0$; равенство
$L_b+T_bB_0+s=(I+K_s)(L_b+s)$ на $D$; постоянная $C=2C_1e^{\lVert\psi\rVert_\infty}$;
пять случаев шага 1 утверждения 3 (минимум $2\sqrt{pq}$, знак производной при $pq<0$,
границы $\ln(\lvert p\rvert/2)$ и $\ln(2/\lvert q\rvert)$); перенос (5) на $x<0$;
замечание 1 ($b(x)b(-x)=a(x)a(-x)$) и замечание 2 (предел $4$ при $x\to0+$). Гипотезы
теоремы 4.7 сверены с карточкой: $L_a$ замкнут, плотно определён, $L_a^{-1}=GT_a^{-1}$
компактен, $s_j(L_a^{-1})\le cj^{-2}$, луч $\arg\lambda=\pi$ удовлетворяет (2.9),
$\gamma=2\le\alpha=2$. Скрипты абзаца «Проверка» не перезапускались.

**Соответствие формализации (13.10.2026).** Проверено утверждение 1. Объявления:
`gauge_principalOperator_boundedInverse`, `gauge_resolvent_ray_estimate`
(`GaugeResolvent.lean`).

Обратный перевод. Даны функции $a,b\colon\mathbb R\to\mathbb R$, существенно ограниченные
на $(-1,1)$; коэффициенты операторов — классы комплексных функций $x\mapsto a(x)$,
$x\mapsto b(x)$ в $L_\infty(-1,1;\mathbb C)$. Даны классы $r,w\in L_\infty(-1,1;\mathbb C)$
с $r(x)w(x)=1$ п.в., равенство $b(x)r(x)=a(x)r(-x)$ п.в. на $(-1,1)$ и число $\alpha<1$ с
$\lvert b(x)+b(-x)\rvert\le2\alpha$ п.в. на $(-1,1)$. Значение $r(-x)$ берётся у
представителя класса; от его выбора равенство п.в. не зависит, поскольку $x\mapsto-x$
сохраняет меру на $(-1,1)$. (i) `gauge_principalOperator_boundedInverse`: существует
ограниченный оператор $S$ в $L_2(-1,1;\mathbb C)$ с $ST_a=T_aS=I$, где
$(T_ag)(x)=g(x)+a(x)g(-x)$ п.в.; оценки $\lVert S\rVert$ в выводе нет, гладкость $r$, $w$
не требуется. (ii) `gauge_resolvent_ray_estimate`: пусть дополнительно каждый из классов
$r$, $w$ имеет две слабые производные в $L_\infty(-1,1;\mathbb C)$ (`MemIntervalW2Infinity`:
существуют $r',r''\in L_\infty$, интегральное тождество с вещественными пробными функциями
из $C_c^\infty(-1,1)$). Тогда существуют числа $C>0$ и $s_0>0$, зависящие только от
$a,b,r,w,\alpha$, для которых при каждом $s\ge s_0$ и каждом $h\in L_2$ существует ровно
один $f$ из слабой области Дирихле (две слабые производные в $L_2$, непрерывный на
$[-1,1]$ представитель равен нулю в $\pm1$) с $-f''-af''(-\cdot)+sf=h$, и каждый такой $f$
удовлетворяет $\lVert f\rVert\le C\lVert h\rVert/s$. Значения $C$ и $s_0$ в формулировке
не названы. Функции $\psi$ в формулировках нет: $r$ и $w$ — параметры теоремы, они не
обязаны быть вещественными, положительными или иметь вид $e^{\pm\psi/2}$ с нечётной
$\psi$; $b$ — тоже параметр, связанный с $a$ только равенством $br=a\cdot r(-\cdot)$.

| Запись | Lean | Оценка |
| --- | --- | --- |
| $a\in L_\infty$ вещественна | `ha`, класс `realIntervalCoefficient a ha` | совпадает |
| нечётная вещественная $\psi\in W^2_\infty$; $r=e^{\psi/2}$, $w=e^{-\psi/2}$, $b=ae^{-\psi}$ | параметры $b$, $r$, $w$ с `hb`, `hr`, `hw`, `hrw`, `hg` | иное: Lean берёт результат шага 1 доказательства как гипотезу; переход от $\psi$ к $(r,w,b)$ в Lean не доказан |
| условие (5) с $\alpha<1$ | `hα1`, `hα` для $b$ | совпадает после подстановки $b=ae^{-\psi}$ ($b(-x)=a(-x)e^{\psi(x)}$ — шаг 2 записи, вне Lean); при $\alpha<0$ гипотеза Lean несовместна |
| $T_a$ ограниченно обратим | двусторонний ограниченный обратный | совпадает; Lean сильнее в гипотезах: $r,w\in L_\infty$ без производных |
| $s_0\ge0$; $s>0$, $s\ge s_0$ | $s_0>0$; $s\ge s_0$ | совпадает: из пары записи получается пара Lean заменой $s_0$ на $s_0+1$ |
| $L_a+s$ — биекция $D$ на $L_2$ | $\exists!f\in D$ при каждом $h$ | совпадает; $D$ — слабая область Дирихле в обоих текстах |
| $\lVert(L_a+s)^{-1}\rVert\le C/s$ | $\lVert f\rVert\le C\lVert h\rVert/s$ для каждого решения | совпадает |
| значения $C$, $s_0$, $C_1$, $C_2$ из (6) | $\exists C,s_0$ | Lean слабее: значения (6) формулировкой не подтверждены |

Проверки (`output/fidelity/C19.lean`, компилируется без ошибок и предупреждений).
Контрольный случай — замечание 3: $a(x)=4\max(x,0)$, $\psi(x)=2x$, $r=e^x$, $w=e^{-x}$,
$b(x)=4\max(x,0)e^{-2x}$, $\alpha=1/e$. Непустота: для этих данных доказаны все гипотезы
обеих теорем (`rClass_W2`, `wClass_W2`, `rw_one`, `gauge_relation`, `bRamp_even_part`).
Специализация: `ramp_principal_inverse` — обратимость $T_a$; `ramp_ray_estimate` — оценка на
луче; `ramp_no_eigenvalue_on_ray` — при $s\ge s_0$ число $-s$ не собственное значение
$L_a$. Специализация не сводится к C17: `aRamp_not_C17` показывает, что
$\lvert a(x)+a(-x)\rvert\le2\alpha$ п.в. не выполнено ни при каком $\alpha<1$.
Вырожденность: при $\alpha<0$ из `hα` выведено противоречие (`alpha_neg_empty`); нулевой
вес исключён гипотезой $rw=1$ (`zero_weight_excluded`); вывод требует существования
решения при каждом $h$ и потому не выполняется на пустой области. Определения: класс
`MemIntervalW2Infinity` проверен на $e^{\pm x}$; область `MemDirichletH2`, оператор
`variableSobolevOperator`, `principalOperator` и `spectralGreen` проверены в
`output/fidelity/C17_C18.lean`. Аксиомы обеих теорем и трёх специализаций — `propext`,
`Classical.choice`, `Quot.sound`. Не проверено в Lean: построение $(r,w,b)$ по
произвольной нечётной $\psi\in W^2_\infty$ (сделано только для $\psi=2x$); значения
постоянных (6); отсутствие калибровки для коэффициента C11 (замечание 2); случай
`MemIntervalW2Infinity` на функции без второй производной в $L_\infty$.

Вердикт: **соответствует с оговорками**. 1. Теоремы Lean сформулированы в калибровочных
данных $(b,r,w)$, а не через $\psi$; утверждение 1 в форме записи следует из них вместе с
шагом 1 и первой фразой шага 2 доказательства, которые в Lean не формализованы. Это
названо в абзаце «Lean»; для утверждения 2 безвредно, если шаг 1 принят рецензией.
2. Lean доказывает существование $C$ и $s_0$, но не формулы (6): в доказательстве стоят
$2\lVert r\rVert\lVert w\rVert C_1+1$ и $4C_2^2C_1(1+C_1)+1$ с $C_2$ через
$\lVert w\rVert\lVert r'\rVert$, $\lVert w\rVert\lVert r''\rVert$. Это тоже названо в абзаце
«Lean»; утверждению 2 нужны только существование $C$ и луч $s\ge s_0$. В «Границы» стоит
вписать: «Lean подтверждает утверждение 1 в калибровочных данных $(b,r,w)$ и только
существование $C$ и $s_0$; построение $r=e^{\psi/2}$, $w=e^{-\psi/2}$, $b=ae^{-\psi}$ по
$\psi$ и значения постоянных (6) — собственный расчёт без проверки в Lean». 3. Lean
допускает комплексные $r$, $w$ без связи $r(-x)=w(x)$ и не требует гладкости весов для
обратимости $T_a$: Lean сильнее, безвредно.

**Соответствие формализации, утверждение 3 (13.10.2026).** Объявление: `exists_odd_phase`
(`PhaseSelection.lean`).

Обратный перевод. Дана функция $a\colon\mathbb R\to\mathbb R$, определённая на всей прямой;
её сужение на $[-1,1]$ непрерывно (`ContinuousOn`), и $\lvert a(x)a(-x)\rvert<1$ в каждой
точке $x\in[-1,1]$. Значения $a$ вне $[-1,1]$ ни в гипотезы, ни в вывод не входят. Тогда
существует функция $\psi\colon\mathbb R\to\mathbb R$ со свойствами: $\psi$ бесконечно
дифференцируема на всей прямой (показатель `(⊤ : ℕ∞)`, то есть $C^\infty$, а не
аналитичность); $\psi(-x)=-\psi(x)$ при каждом вещественном $x$; есть $\delta>0$ с
$\psi(x)=0$ при $\lvert x\rvert<\delta$; есть вещественное $\alpha<1$, для которого
$\lvert a(x)e^{-\psi(x)}+a(-x)e^{\psi(x)}\rvert\le2\alpha$ в каждой точке $x\in[-1,1]$.
Нижней границы для $\alpha$ в формулировке нет; из оценки в точке $0$ следует
$\alpha\ge0$. Оценка поточечная, с нестрогим неравенством, существенного супремума и
классов функций п.в. в формулировке нет. Определений проекта формулировка не содержит:
только `ContinuousOn`, `ContDiff`, `Real.exp`, `Set.Icc`. Свидетели $\psi$, $\delta$,
$\alpha$ стоят под кванторами существования, зависимость от $a$ не описана.

| Запись | Lean | Оценка |
| --- | --- | --- |
| $a$ вещественна и непрерывна на $[-1,1]$ | $a\colon\mathbb R\to\mathbb R$, `ContinuousOn a (Icc (-1) 1)` | совпадает; значения вне $[-1,1]$ не используются |
| $\lvert a(x)a(-x)\rvert<1$ при $x\in[0,1]$ | то же при $x\in[-1,1]$ | совпадает: произведение не меняется при $x\mapsto-x$ (`prod_of_half`) |
| $\psi\in C^\infty[-1,1]$ | $\psi\in C^\infty(\mathbb R)$ | Lean сильнее |
| $\psi$ нечётна на $[-1,1]$ | $\psi(-x)=-\psi(x)$ на $\mathbb R$ | Lean сильнее |
| $\psi=0$ в окрестности нуля | $\exists\delta>0$: $\psi=0$ при $\lvert x\rvert<\delta$ | совпадает |
| условие (5): $\operatorname{ess\,sup}\lvert\cdot\rvert=2\alpha<2$ на $(-1,1)$ | $\exists\alpha<1$: $\lvert\cdot\rvert\le2\alpha$ в каждой точке $[-1,1]$ | Lean сильнее: поточечная оценка на отрезке даёт оценку п.в. (`gauge_bound`); равенство в (5) получается выбором $\alpha$ равным половине существенного супремума |
| $\psi\in W^2_\infty(-1,1)$ вещественна (условия записи, к которым отсылает (5)) | $\psi\in C^\infty(\mathbb R)$ | иное: принадлежность $e^{\pm\psi/2}$ классу `MemIntervalW2Infinity` проекта из гладкости в Lean не выведена |

Проверки (`output/fidelity/C19_phase.lean`, компилируется без ошибок и предупреждений).
Непустота: гипотезы выполнены для $a(x)=4\max(x,0)$ (замечание 3, `ramp_phase`) и для
$a(x)=x/2$ (случай 3 из `question.md`, `halfSlope_phase`). Специализация: для
$a(x)=4\max(x,0)$ теорема даёт фазу, а $\psi=0$ не годится ни при каком $\alpha<1$
(`ramp_zero_phase_fails`); каждый свидетель удовлетворяет $\psi(1)>0$
(`ramp_phase_nonzero`). Для $a(x)=x/2$ вывод выполнен уже при $\psi=0$, и эта
специализация ничего не проверяет. Форма записи с гипотезой на $[0,1]$ выведена из
теоремы (`statement3`). Вырожденность: без оценки произведения вывод ложен — для
$a\equiv2$ фазы нет (`const_two_no_phase`); без непрерывности вывод ложен — для
коэффициента C11 $a=4\cdot\mathbf 1_{(0,\infty)}$ произведение равно нулю, а фазы нет
(`step_no_phase`; довод замечания 2, но через пункт «$\psi=0$ при $\lvert x\rvert<\delta$»
вывода, без него не проверялось). Мост к утверждению 1: из вывода и нечётности $\psi$
получена гипотеза `hα` теорем `GaugeResolvent.lean` для $b=ae^{-\psi}$, то есть
$\lvert b(x)+b(-x)\rvert\le2\alpha$ п.в. по `intervalMeasure` (`gauge_bound`);
$\alpha\ge0$ — `alpha_nonneg`. Аксиомы `exists_odd_phase` и специализаций — `propext`,
`Classical.choice`, `Quot.sound`. Не проверено в Lean: что для гладкой $\psi$ классы
$e^{\pm\psi/2}$ лежат в `MemIntervalW2Infinity`, а $ae^{-\psi}$ существенно ограничена
(остальные гипотезы утверждения 1); отсутствие фазы для коэффициента C11 без пункта о
нуле в окрестности нуля.

Вердикт: **соответствует с оговорками**. 1. Утверждение 3 в форме записи следует из
`exists_odd_phase`; в трёх строках таблицы Lean сильнее, безвредно. 2. Замена
$x\in[0,1]$ на $x\in[-1,1]$ в оценке произведения и поточечная оценка вместо
существенного супремума равносильны формулировке записи, безвредно. 3. Теорема даёт
$\psi\in C^\infty(\mathbb R)$, а утверждение 1 в Lean требует классы $r,w$ с
`MemIntervalW2Infinity` и $b\in L_\infty$; этот переход в Lean не сделан, поэтому цепочка
«утверждение 3 — утверждение 1» в Lean не замкнута. В «Границы» стоит вписать:
«`exists_odd_phase` даёт $\psi\in C^\infty(\mathbb R)$ и поточечную оценку (5) на
$[-1,1]$; принадлежность $e^{\pm\psi/2}$ классу $W^2_\infty$ проекта и существенная
ограниченность $ae^{-\psi}$ в Lean не выведены, так что следствие для непрерывных $a$
формулировками Lean не покрыто (узел S-GLUE)».

## 3. Литература

Получены 36 полных статей (S1–S35, S39), у S36–S38 и S40–S42 есть только описание: реестр — `sources/catalog.md` и `sources/papers.json`, PDF и
извлечённые тексты — `output/literature/`. Номера теорем, страницы, гипотезы и
применимость проверенных результатов — `sources/results.md`. Наличие полного текста не
означает проверку его теорем.

- S4, Wyss, arXiv:0906.2631v1, теорема 6.1, с. 21 — теорема о подчинённых возмущениях
  для C6 и C16; определение 3.1 и предложение 3.2 — критерий C7.
- S3, Шкаликов, УМН 71:5 (2016), теорема 6.6, с. 140 — вторая опора для C6; теорема 4.7,
  с. 129 — полнота в C17 и C19.
- S2, Копжассарова и Сарсенби, теорема 4.1, с. 4 — постоянная модель C3.
- S1, Бондаренко, §2.1, с. 4 — образец матричной редукции C1.
- S5, Поляков — метод подобных операторов для оператора более высокого порядка; схема C13.
- S8, Лунёв и Маламуд — различие регулярных и строго регулярных условий для систем
  первого порядка; на нашу задачу теоремы не перенесены.

## 4. Что нельзя переносить из `main.tex` без проверки

- $W^1_\infty$ означает существенно ограниченную производную; одной абсолютной
  непрерывности мало.
- Оценка с произвольно малой относительной гранью не задаёт показатель $p$ в определении
  подчинённости.
- Для коэффициента из $L_\infty$ значение в точке $0$ не определено; граничное условие
  формулируется через след квазипроизводной, если её регулярность доказана.
- Базис Рисса со скобками не равносилен базису Рисса; граница размера скобок требует
  отдельного доказательства.

## 5. Нерешённое

- Коэффициенты $a\in W^1_\infty$ вне C5: с нулями и сменой знака, например $a=x/2$.
  Полнота есть (C17, C19), базиса Рисса из собственных функций при $a=x/2$ нет (C18); базис
  со скобками и базис с присоединёнными функциями не исследованы.
- Полнота для разрывных $a\in L_\infty$ с $\operatorname{ess\,sup}\lvert a_e\rvert\ge1$, не
  удовлетворяющих условию (5) записи C19; для коэффициента C11 собственных значений нет.
- Необходимые условия базисности.
- Размер скобок в C6, C14–C16.
- Обычный базис Рисса для C6: проверяемые условия на $a$, дающие равномерные константы
  C7; в частности, случай малой $\varphi'$.
- Оптимальные постоянные в условиях малости C14–C15.
- Базисы с присоединёнными функциями и со скобками для коэффициента C12.
