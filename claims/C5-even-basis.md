---
id: C5
title: Чётный коэффициент: базис Рисса
status: proved-aristotle
depends_on: []
lean_theorem: Involution.evenCoefficient_riesz_eigenbasis
final: true
---

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
инъективен (`Involution/Model/SpectralGreen.lean`). В канале $Ru=su$, $s=\pm1$, берём вес $w$ с
$(1+sa)w^2=1$ п.в. (`Involution/Model/PositiveWeight.lean`). Оператор $K=M_wGM_w$ компактен и
симметричен; его собственные векторы образуют гильбертов базис канала
(`Involution/Model/CompactEigenbasis.lean`). Если $Ku=\mu u$, то $y=GM_wu$ лежит в области и
$L_ay=\mu^{-1}y$ (`Involution/Model/WeightedGreen.lean`), а обратимое умножение переводит базис в базис
Рисса (`Involution/Model/MultiplicationEquiv.lean`, `Involution/Model/WeightedEigenbasis.lean`). Итог:
`evenCoefficient_channel_riesz_eigenbasis`, `evenCoefficient_riesz_eigenbasis`,
`evenCoefficient_noJordan`; на области абсолютно непрерывных представителей —
`Involution/Model/ACSpectral.lean`. Достаточно вещественного $a\in L_\infty$; условие $W^1_\infty$ не
используется. Модули `Involution/Model/EvenEigenbasis.lean`, `Involution/Model/EvenCoefficient.lean` и `Involution/Model/EvenNoJordan.lean`
приняты из задач A2 и A5.

**Примеры.** $a(x)=x^2/2$; постоянный $a=c\in(-1,1)$ даёт ортонормированный базис C3.
