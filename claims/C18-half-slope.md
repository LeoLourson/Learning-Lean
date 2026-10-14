---
id: C18
title: Пример $a(x)=x/2$: нет базиса Рисса из собственных функций
status: proved-aristotle
depends_on: [C4, C11, C17, I9]
lean_theorem: Involution.halfSlope_no_riesz_eigenbasis
final: true
checked_by: [fidelity-checker 2026-10-12]
---

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

**Lean.** Задача 8 Aristotle. `Involution/Estimates/HalfSlopeProfile.lean`: функции `halfSlopeS`, `halfSlopeU`,
срезка `halfSlopeCut`, `halfSlopeZ_equation`, оценки `halfSlopeR_norm_le`,
`halfSlopeZ_norm_ge`; ветви записаны как $\exp(\tfrac14\log s)$ и $\exp(\tfrac12\log s)$.
`Involution/Estimates/RieszEigenCount.lean`: `RieszBasis.card_le_of_finiteRank_approx`. `Involution/Estimates/HalfSlope.lean`:
`halfSlopeCoefficient`, `halfSlopeClass`, `halfSlope_quasimodes`, `rieszEigenbasis_count`,
`halfSlope_no_riesz_eigenbasis`. Лемма `rieszEigenbasis_count` верна для любого
$a\in L_\infty$ с обратимым определителем $1-a(x)a(-x)$. Модули `Involution/Estimates/HalfSlope.lean`,
`Involution/Estimates/HalfSlopeProfile.lean` и `Involution/Estimates/RieszEigenCount.lean` приняты из задачи A9.

**Проверка.** `output/ideas/halfslope_check.py`: тождество шага 1 выполнено с точностью
$10^{-14}$ в десяти точках; $\lVert(A-t^2)Z_t\rVert/\lVert Z_t\rVert\le44$ при
$t=2,5,10,20,40,80$ для $A=s\cdot(-D^2)$.

**Границы.** Базис Рисса со скобками и базис с присоединёнными функциями не исключены.
Корневые функции полны (C17). Для других нечётных коэффициентов точного решения нет;
гипотеза о квазимодах при $a(x)a(-x)<0$ — `claims/I*.md`, I9.

**Соответствие формализации (12.10.2026).** Объявление: `halfSlope_no_riesz_eigenbasis`
(`Involution/Estimates/HalfSlope.lean`). Обратный перевод. Не существует типа индексов $\iota$ (в `Type`),
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
