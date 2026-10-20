---
id: C21
title: Оценка резольвенты вне сектора и суммируемость по Абелю–Лидскому
status: proved-lean
depends_on: [C8, C17, S3]
lean_theorem: Involution.resolvent_sector_ray_estimate
checked_by: [referee 2026-10-20, fidelity-checker 2026-10-20]
---

**Условия.** Как в C17: вещественный $a\in L_\infty(-1,1)$,
$\lvert a_e\rvert\le\alpha<1$, $\lvert a_o\rvert\le\beta_0$ п.в. (в C17 вторая постоянная
обозначена $\beta$; здесь буква $\beta$ занята порядком суммирования). Положим

$$
\tau=\frac2\pi\arctan\frac{\beta_0}{1-\alpha}\in[0,1),\qquad
\Lambda_\theta=\lbrace\lambda\in\mathbb C:\lvert\arg\lambda\rvert\le\theta\pi/2\rbrace .
$$

**Лемма (оценка на лучах).** Пусть $0<\delta\le\pi/2$ и
$\lvert\arg\lambda\rvert\ge\pi\tau/2+\delta$ или $\lambda=0$. Тогда $\lambda\in\rho(L_a)$ и

$$
\lvert\lambda\rvert\,\lVert(L_a-\lambda)^{-1}\rVert\le
\frac{\lVert T_a\rVert}{(1-\alpha)\sin\delta}+1,\qquad
\lVert T_a\rVert\le1+\alpha+\beta_0 .
$$

**Доказательство.** Пусть $f$ из слабой области Дирихле, $(L_a-\lambda)f=g$, $W=-f''$.
По C8 $L_af=T_aW$ (факторизация не использует оценку произведения $a(x)a(-x)$), поэтому
$T_aW-\lambda f=g$. Скалярное умножение на $W$ слева и энергетическое тождество
$\langle W,f\rangle=\lVert f'\rVert^2=:E\ge0$ дают

$$
z_1-\lambda E=\langle W,g\rangle,\qquad z_1=\langle W,T_aW\rangle .
$$

По оценкам (2) записи C17, верным для любого $W\in L_2$,
$\operatorname{Re}z_1\ge(1-\alpha)\lVert W\rVert^2$ и
$\lvert\operatorname{Im}z_1\rvert\le\beta_0\lVert W\rVert^2$, откуда
$\lvert\arg z_1\rvert\le\pi\tau/2$ и $\lvert z_1\rvert\ge(1-\alpha)\lVert W\rVert^2$ (при
$W\ne0$). Точка $\lambda E$ лежит на луче $\lbrace r\e^{i\arg\lambda}:r\ge0\rbrace$, угол
между этим лучом и направлением $z_1$ не меньше $\delta$. Расстояние от $z_1$ до луча равно
$\lvert z_1\rvert\sin\varphi$ при угле $\varphi\le\pi/2$ и $\lvert z_1\rvert$ при
$\varphi>\pi/2$; в обоих случаях оно не меньше $\lvert z_1\rvert\sin\delta$. Значит,

$$
(1-\alpha)\sin\delta\,\lVert W\rVert^2\le\lvert z_1-\lambda E\rvert\le\lVert W\rVert\,\lVert g\rVert,
\qquad \lVert W\rVert\le\frac{\lVert g\rVert}{(1-\alpha)\sin\delta}.
$$

Из $\lambda f=T_aW-g$ получаем
$\lvert\lambda\rvert\lVert f\rVert\le\lVert T_a\rVert\lVert W\rVert+\lVert g\rVert$, то есть
оценку леммы для всякого решения. При $g=0$ она даёт $\lambda f=0$; при $\lambda\ne0$ это
$f=0$, а $\lambda=0$ лежит в $\rho(L_a)$ по C17, утверждение 2. Итак, $L_a-\lambda$
инъективен. Оператор $L_a^{-1}=GT_a^{-1}$ компактен (C17, утверждение 2), поэтому спектр
$L_a$ состоит из собственных значений, и инъективность влечёт $\lambda\in\rho(L_a)$.
Оценка $\lVert T_a\rVert\le1+\alpha+\beta_0$: $T_a=I+a_eR+a_oR$, $\lVert R\rVert=1$.

**Утверждение.** При каждом $\beta\in(1/2,\tau^{-1})$ (при $\tau=0$ — при каждом $\beta>1/2$)
система корневых векторов $L_a$ образует базис для метода суммирования Абеля–Лидского
порядка $\beta$ в смысле (5.2)–(5.3) обзора S3: существуют замкнутые контуры $\Gamma_k$,
не зависящие от $x$ и $t$, такие что ряд

$$
S(t)x=\sum_k-\frac1{2\pi i}\int_{\Gamma_k}e^{-\lambda^\beta t}(L_a-\lambda)^{-1}x\,d\lambda
$$

сходится при каждом $t>0$ и $x\in L_2(-1,1)$ и $S(t)x\to x$ при $t\to0+$. Скобки (контуры
$\Gamma_k$) берутся из доказательства теоремы 5.1 обзора S3; явно они не указаны.

**Доказательство.** Проверяем гипотезы теоремы 5.1 обзора S3 (карточка S3, раздел
«Суммирование Абеля–Лидского»).

1. Стоячие условия § 4 и порядок $2$: $L_a=T_a(-D^2)$ замкнут, область плотна,
   $L_a^{-1}=GT_a^{-1}$ компактен и $s_j(L_a^{-1})\le\lVert T_a^{-1}\rVert s_j(G)\le cj^{-2}$,
   так как $s_j(G)=4/(\pi^2j^2)$ (карточка S3, «Применимость к C17»).
2. Спектр в $\Lambda_\tau$: спектр состоит из собственных значений (компактная
   резольвента), и по C17, утверждение 1,
   $(1-\alpha)\lvert\operatorname{Im}\lambda\rvert\le\beta_0\operatorname{Re}\lambda$,
   $\operatorname{Re}\lambda>0$, то есть
   $\lvert\arg\lambda\rvert\le\arctan\frac{\beta_0}{1-\alpha}=\pi\tau/2$. Исключений нет.
3. $\alpha_{S3}=2>\tau$, так как $\tau<1$.
4. Лучи: луч $\arg\lambda=\varphi$ вне $\Lambda_\tau$ имеет $\lvert\varphi\rvert>\pi\tau/2$;
   при $\delta=\min(\lvert\varphi\rvert-\pi\tau/2,\pi/2)>0$ лемма даёт (2.9) с $r_0=0$.
   Доказательство теоремы 5.1 использует оценку
   $\lVert(L_a-\lambda)^{-1}\rVert\le C\lvert\lambda\rvert^{-1}$ сразу во всём дополнении
   $\Lambda_{\tau+\delta'}$ с одной постоянной; лемма даёт её с
   $C=\frac{\lVert T_a\rVert}{(1-\alpha)\sin\delta}+1$, $\delta=\min(\pi\delta'/2,\pi/2)$.

Вывод теоремы 5.1 — при $\beta\in(\alpha_{S3}^{-1},\tau^{-1})=(1/2,\tau^{-1})$; при $\tau=0$ интервал читается как $(1/2,\infty)$. Полнота,
на которую опирается доказательство в S3 (теорема 4.7), для $L_a$ — C17, утверждение 3.

**Контрольный случай.** $a=x/2$: $\alpha=0$, $\beta_0=1/2$,
$\tau=\frac2\pi\arctan\frac12=0{,}2952$, $\beta\in(0{,}5;\ 3{,}39)$. Для $a=\max(x,0)$
(C12): $\alpha=\beta_0=1/2$, $\tau=1/2$, $\beta\in(1/2,2)$; базиса Рисса из собственных
функций там нет, и утверждение с этим совместимо. Для чётного $a$ ($\beta_0=0$) $\tau=0$ и
утверждение слабее C5.

**Lean.** `Involution/Estimates/RayResolvent.lean`: `resolvent_sector_ray_estimate` —
априорная оценка леммы для всякого решения из слабой области Дирихле; условия записаны как
в `eigenvalue_sector` ($\lVert a(x)\pm a(-x)\rVert\le2\alpha$, $2\beta_0$), порог угла —
`Real.arctan (β / (1 - α))`, постоянная — через $\lVert T_a\rVert$. Вспомогательные:
`abs_arg_le_arctan`, `norm_mul_sin_le_norm_sub_ray`, `cos_le_cos_of_abs_mem`. В Lean не
формализованы: $\lambda\in\rho(L_a)$ (разрешимость), оценка $\lVert T_a\rVert\le1+\alpha+\beta_0$
и утверждение (теорема 5.1 S3).

**Границы.** В Lean доказана только априорная оценка $\lvert\lambda\rvert\lVert f\rVert\le C\lVert(L_a-\lambda)f\rVert$ для $f$ из слабой области Дирихле при $\lambda\ne0$; принадлежность $\lambda\in\rho(L_a)$ (через компактность $L_a^{-1}$, C17) и оценка $\lVert T_a\rVert\le1+\alpha+\beta_0$ доказаны только на бумаге. Скобки из теоремы Тичмарша явно не указаны, их размер не оценён. Порядок
$\beta\le1/2$ не исследован; при отрицательном произведении $a(x)a(-x)$ для доминантной
модели I23 без скобок он недостижим, для $L_a$ и сумм по блокам это не доказано (I23,
пункт (D)). Утверждение относится к классу C17; перенос на весь класс постановки через
калибровку C19 (луч только на отрицательной полуоси, $s\ge s_0$) не сделан: лемма опирается
на коэрцитивность (4) записи C17, которой у калиброванного оператора может не быть.
Доказательства теорем 4.2, 4.7 и 5.1 в S3 в проекте не проверялись (теорема Тичмарша и
приём Мацаева взяты из обзора).

**Рецензия (2026-10-20).**

1. *Утверждение, пункт 4.* Постоянная $C=\frac{\lVert T_a\rVert}{(1-\alpha)\sin(\pi\delta'/2)}+1$ получена подстановкой $\delta=\pi\delta'/2$, а лемма требует $\delta\le\pi/2$, то есть $\delta'\le1$. При $\delta'>1$ надо брать $\delta=\min(\pi\delta'/2,\pi/2)$; доказательству S3 достаточно малых $\delta'$. Вес: неточность.
2. *Утверждение, пункт 1, и случай $\tau=0$.* Интервал $(\alpha_{S3}^{-1},\tau^{-1})$ при $\tau=0$ читается как $(1/2,\infty)$; в формулировке теоремы 5.1 S3 это не оговорено, условие $\beta\tau<1$ тогда выполнено при всех $\beta$. Вес: неточность, достаточно оговорки.
3. *Источник S3.* Последняя сверка карточки (2026-10-20) по разделу «Применимость к C21» закончилась расхождением: тогда записи C21 не было, и буквы параметров совпадали с буквами теоремы 5.1. Текст карточки с тех пор исправлен ($\alpha_0$, $\beta_0$, явное $2>1>\tau$), но повторной сверки нет. Сверка формулировок (5.1)–(5.3) и теоремы 5.1 пройдена. Сам источник отмечает, что доказательство теоремы 5.1 использует оценку с одной постоянной вне $\Lambda_{\tau+\delta}$; лемма C21 даёт именно её, так что этот разрыв источника для нас закрыт. Требуется: повторная сверка раздела «Применимость к C21» карточки S3.

Проверено: угол между лучом $\arg\lambda$ и $z_1$ не меньше $\delta$ во всех случаях (обход через $\pm\pi$: $2\pi-(\pi+\pi\tau/2)\ge\pi/2\ge\delta$); расстояние от точки до луча $\ge\lvert z_1\rvert\sin\delta$ при $\delta\le\pi/2$; вырожденные случаи $W=0$ и $\lambda=0$; $\lVert T_a\rVert\le1+\alpha+\beta_0$; $s_j(G)=4/(\pi^2j^2)$ (собственные значения $-D^2$ с Дирихле на $(-1,1)$ равны $(j\pi/2)^2$); $\tau=\frac2\pi\arctan\frac12\approx0{,}2952$, $\tau^{-1}\approx3{,}39$; гипотезы C17 (вещественность $a$ для (2), $\alpha<1$ для (4) и обратимости $T_a$) использованы и применяются в своих пределах; C8 и C17 имеют статус `proved-lean`. Гипотезы теоремы 5.1 сверены с карточкой по одной. Абзац «Границы» не заявляет лишнего.

Вердикт: принято (замечания 1–2 — неточности; замечание 3 касается сверки карточки, а не доказательства).

**Соответствие формализации (2026-10-20).** Объявление `Involution.resolvent_sector_ray_estimate` (модуль `Involution/Estimates/RayResolvent.lean`) сверено с леммой «оценка на лучах».

*Обратный перевод (до чтения записи).* Пространство $H=L_2((-1,1);\mathbb C)$ — классы по мере Лебега, ограниченной на $(-1,1)$. Дано: класс $a\in L_\infty((-1,1);\mathbb C)$, почти всюду вещественный ($\bar a=a$ п.в.); числа $\alpha<1$ и $\beta$, для которых п.в. $\lvert a(x)+a(-x)\rvert\le2\alpha$ и $\lvert a(x)-a(-x)\rvert\le2\beta$. Значение $a(-x)$ берётся у представителя, но из-за симметрии интервала условие от представителя не зависит. Даны $\delta\in(0,\pi/2]$ и $\lambda\in\mathbb C$ с $\arctan\frac{\beta}{1-\alpha}+\delta\le\lvert\arg\lambda\rvert$, где $\arg$ — главное значение из $(-\pi,\pi]$, $\arg0=0$. Даны $f,g\in H$, причём $f$ лежит в слабой области Дирихле: у $f$ есть слабые производные $f',f''\in L_2$ на $(-1,1)$ (производные выбраны через `Classical.choose`, но слабая производная единственна, так что выбор роли не играет), и непрерывный на $[-1,1]$ представитель $f$ обращается в нуль в $\pm1$. Наконец, $-f''-a\cdot(f'')(-\cdot)-\lambda f=g$ в $H$. Вывод: $\lvert\lambda\rvert\,\lVert f\rVert\le\bigl(\frac{\lVert T_a\rVert}{(1-\alpha)\sin\delta}+1\bigr)\lVert g\rVert$, где $T_a=I+aR$, $(Rf)(x)=f(-x)$, $\lVert T_a\rVert$ — операторная норма в $H$. Это априорная оценка всякого решения. Существование решения, обратимость $L_a-\lambda$ и норма резольвенты в формулировке не участвуют. При $\beta<0$ гипотеза на $a$ несовместна (мера интервала положительна). При $\lambda=0$ гипотеза угла ложна, так как $\arctan\frac{\beta}{1-\alpha}\ge0$.

*Сравнение.*

| Запись | Lean | Оценка |
| --- | --- | --- |
| $a$ вещественный, $a\in L_\infty(-1,1)$ | `ha`: $\bar a=a$ п.в., `a : IntervalLInfinity` | совпадает |
| $\lvert a_e\rvert\le\alpha<1$ | `hα`: $\lvert a(x)+a(-x)\rvert\le2\alpha$, `hα1` | совпадает |
| $\lvert a_o\rvert\le\beta_0$ | `hβ`: $\lvert a(x)-a(-x)\rvert\le2\beta$ | совпадает |
| $0<\delta\le\pi/2$ | `hδ0`, `hδ` | совпадает |
| $\lvert\arg\lambda\rvert\ge\pi\tau/2+\delta$ или $\lambda=0$ | `hlam`; случай $\lambda=0$ не охвачен | Lean слабее (безвредно: при $\lambda=0$ оценка тривиальна, а $0\in\rho(L_a)$ — C17) |
| $f$ из области $L_a$ | `MemDirichletH2 f` (слабая область, равна $H^2\cap H_0^1$ по `memDirichletH2_iff_h2_and_h01`) | совпадает |
| вывод: $\lambda\in\rho(L_a)$ | нет | Lean слабее |
| вывод: $\lvert\lambda\rvert\lVert(L_a-\lambda)^{-1}\rVert\le C$ | $\lvert\lambda\rvert\lVert f\rVert\le C\lVert g\rVert$ для всякого решения | Lean слабее (равносильно при $\lambda\in\rho(L_a)$) |
| вывод: $\lVert T_a\rVert\le1+\alpha+\beta_0$ | нет | Lean слабее |

*Проверки* (файл `output/fidelity/C21_ray.lean`, `lake env lean` без ошибок и предупреждений). Непустота и специализация: для $a=x/2$ (`halfSlopeClass`), $\alpha=0$, $\beta=1/2$, $\delta=\pi/2$, $\lambda=-1$ все гипотезы доказаны, теорема применена к ненулевой модельной функции `constantModelVector i` и дала $\lVert f\rVert\le(\lVert T_a\rVert+1)\lVert(L_a+1)f\rVert$ — нетривиальное неравенство. Вырожденность: гипотеза угла при $\lambda=0$ ложна (проверено), других способов получить вывод даром не найдено; при $\beta<0$ гипотезы несовместны, что не вредит. Определения: постоянная $1$ не лежит в `MemDirichletH2` (проверено), модельные функции лежат. Отдельная проверка вещественности и чётной/нечётной частей $a=x/2$ также в этом файле.

*Вердикт: соответствует с оговорками.* Lean доказывает априорную часть леммы. Утверждения $\lambda\in\rho(L_a)$ и $\lVert T_a\rVert\le1+\alpha+\beta_0$ остаются бумажными (абзац «Lean» записи это честно называет). Для «Границ» предлагается текст: «В Lean доказана только априорная оценка $\lvert\lambda\rvert\lVert f\rVert\le C\lVert(L_a-\lambda)f\rVert$ для $f$ из слабой области Дирихле при $\lambda\ne0$; принадлежность $\lambda\in\rho(L_a)$ (через компактность $L_a^{-1}$, C17) и оценка $\lVert T_a\rVert\le1+\alpha+\beta_0$ доказаны только на бумаге.»
