---
id: C17
title: Сектор собственных значений и полнота
status: proved-lean
depends_on: [C8, S3]
lean_theorem: Involution.resolvent_ray_estimate
final: true
checked_by: [referee 2026-10-12, fidelity-checker 2026-10-12]
---

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

**Lean.** `Involution/Estimates/EigenvalueSector.lean`: `reflectedMultiplier_add_adjoint_ae`,
`reflectedMultiplier_sub_adjoint_ae`, `inner_reflectedMultiplier_left`,
`eigenvalue_sector`, `oddCoefficient_eigenvalue_sector`,
`evenCoefficient_eigenvalue_real`, `ramp_eigenvalue_sector`. В `eigenvalue_sector`
условия записаны как $\lVert a(x)\pm a(-x)\rVert\le2\alpha$, $2\beta$. Утверждение 2:
`Involution/Estimates/ResolventAux.lean` (задача 9 Aristotle) — `reflectedMultiplier_re_inner_bound_of_real`,
`exists_inverse_of_coercive`, `resolvent_estimate_corrected` (разрешимость и первая
оценка (3)); `Involution/Estimates/ResolventBound.lean` — `principalOperator_boundedInverse` и
`resolvent_ray_estimate` (вторая оценка (3), доказана локально). В
`resolvent_ray_estimate` постоянная записана через $\lVert T_a\rVert$; оценка
$\lVert T_a\rVert\le1+\alpha+\beta$ в Lean не выписана. Утверждение 3 в Lean не
формализовано.

**Проверка.** `output/ideas/halfslope_check.py`: коллокация Чебышёва для $a=x/2$,
$a=1/2+x/4$, $a=\max(x,0)$, $a=2x$; неравенство сектора выполнено с запасом.

**Границы.** Условие $\alpha<1$ достаточно; необходимость не исследована. Доказательство
теоремы 4.7 в S3 опирается на оценки определителей возмущения и теорему
Фрагмена–Линделёфа и в проекте не проверялось; теорема 4.4, на которую оно ссылается, в
обзоре не доказана (ссылка [3] обзора). Из полноты базисность не следует (C12).

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
`resolvent_ray_estimate` (`Involution/Estimates/ResolventBound.lean`), `resolvent_estimate_corrected`
(`Involution/Estimates/ResolventAux.lean`). Обратный перевод. Даны функция $a\colon\mathbb R\to\mathbb R$,
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
