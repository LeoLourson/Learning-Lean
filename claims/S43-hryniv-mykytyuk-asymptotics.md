---
id: S43
title: Асимптотика собственных значений при комплексном потенциале
status: verified
source: S43, теорема 1.2 и следствие 1.3, с. 4; замечание 6.3, с. 20
applies_to: [I19]
checked_by: source-verifier 2026-10-13
---

**Авторы:** R. O. Hryniv, Ya. V. Mykytyuk. **Версия:** arXiv:math/0407252v2, «Eigenvalue
asymptotics for Sturm–Liouville operators with singular potentials».
[PDF](../output/literature/math-0407252v2.pdf),
[LaTeX](../output/literature/math-0407252v2.tex). Страницы — по PDF arXiv v2 (25 с.).

**Определения, с. 1–2.** $q$ — комплексное распределение из $W^{\alpha-1}_2(0,1)$,
$\alpha\in[0,1]$; $\sigma\in W^\alpha_2(0,1)$ — первообразная $q$;
$l_\sigma(f)=-(f'-\sigma f)'-\sigma f'$ с областью
$\operatorname{dom}l_\sigma=\lbrace f\in W^1_1(0,1): f'-\sigma f\in W^1_1(0,1),\ l_\sigma(f)\in L_2(0,1)\rbrace$;
$T_{\mathrm D}$ — сужение $l_\sigma$ на
$\lbrace f\in\operatorname{dom}l_\sigma: f(0)=f(1)=0\rbrace$. Через $\lambda_n^2$ обозначены
собственные значения $T_{\mathrm D}$, занумерованные с учётом кратности по возрастанию
вещественной, затем мнимой части $\lambda_n$, где $-\pi/2<\arg\lambda_n\le\pi/2$ или
$\lambda_n=0$; вид кратности на с. 2 не назван. С. 7, § 3, при условии строгой
аккретивности формы $\mathfrak t_{\sigma,\mathrm N}$: числа $\pm\lambda_n$ — нули
характеристической функции $s(1,\cdot)$, порядок нуля равен алгебраической кратности
собственного значения. Общий случай статья сводит к этому сдвигом $\hat q=q+C$ (с. 18).
Обозначения: $s_n(f)=\int_0^1f(x)\sin(\pi nx)\,dx$, $c_n(f)=\int_0^1f(x)\cos(\pi nx)\,dx$,
$(Vf)(x)=(1-2x)f(x)$.

**Теорема 1.1, с. 4.** Если $q\in W^{\alpha-1}_2(0,1)$, $\alpha\in[0,1]$, и
$\sigma\in W^\alpha_2(0,1)$ — первообразная $q$, то существует
$\tilde\sigma\in W^{2\alpha}_2(0,1)$ с $\lambda_n=\pi n-s_{2n}(\sigma)-s_{2n}(\tilde\sigma)$.

**Теорема 1.2 и следствие 1.3, с. 4.** В тех же условиях существует
$\omega\in W^\gamma_2(0,1)$, $\gamma=\min\lbrace3\alpha,1+\alpha\rbrace$, с

$$
\lambda_n=\pi n+s_{2n}(\sigma^-)-s_{2n}(\sigma)c_{2n}(V\sigma)+s_{2n}(\omega),\qquad
\sigma^-(x)=-\sigma(x)+\int_0^x\sigma^2(t)\,dt+\int_0^{1-x}\sigma(x+t)\sigma(t)\,dt,
$$

и $\lambda_n=\pi n+s_{2n}(\sigma^-)-s_{2n}(\sigma)c_{2n}(V\sigma)+O(n^{-\gamma})$ при
$n\to\infty$. Теорема 1.2 доказана на с. 18–19, следствие 1.3 — на с. 19. Следствие
выводится из теоремы 1.2 и работы [31] статьи (Савчук, Шкаликов, Труды ММО 64 (2003);
S44 реестра): при $\alpha\in(1/3,1]$ доказательство использует теорему 3.12 из [31],
карточки которой нет.

**Замечание 6.3, с. 20** (без доказательства). При $\alpha=1$ имеем
$\sigma(x)=h+\int_0^xq$ и
$\lambda_n=\pi n+\dfrac{\int_0^1q}{2\pi n}+\dfrac{\tilde\lambda_n'}{n}$ с
$(\tilde\lambda_n')\in\ell_2$.

**Применимость к I19.** После замены $w=\ell x$ потенциал $\ell^2q(\ell x)$ лежит в
$L_2(0,1)$, то есть $\alpha=1$, $\gamma=2$, $\sigma\in W^1_2$; собственное значение
$\lambda$ задачи на $[0,\ell]$ равно $\lambda_n^2/\ell^2$. При $\sigma\in W^1_2$ область
$T_{\mathrm D}$ совпадает с $H^2\cap H_0^1$ (расчёт: $f'-\sigma f\in W^1_1$ равносильно
$f'\in W^1_1$, а $l_\sigma(f)=-f''+qf$). Теорема 1.2 даёт представление $\lambda_n$ с
нумерацией по кратности; учёт именно алгебраической кратности наследует условие с. 7 и
сдвиг $\hat q=q+C$. Остаток $O(n^{-2})$ — вывод следствия 1.3, которое при $\alpha=1$
опирается на теорему 3.12 из S44 без карточки. По замечанию 6.3
$\lambda_n^2=\pi^2n^2+\int_0^1q+o(1)$: постоянный член $q_0$ идеи I19 — среднее значение
потенциала; замечание в статье не доказано. Асимптотику собственных функций статья не
содержит (с. 3–4). Простоту больших собственных значений даёт S47, а не эта статья.

### Сверка (13.10.2026)

Сверка по изображениям страниц файла 1–7, 18–20, 25 PDF `math-0407252v2.pdf`; печатные
номера совпадают с номерами страниц файла. Версия: штамп arXiv на с. 1 —
«arXiv:math/0407252v2 [math.SP] 3 Oct 2006», в реестре та же; 25 страниц.

- **Комплексность, класс потенциала, с. 1** — совпадает: «we assume that $q$ is a
  complex-valued distribution from the Sobolev space $W_2^{\alpha-1}(0,1)$,
  $\alpha\in[0,1]$».
- **$l_\sigma$ и $\operatorname{dom}l_\sigma$, с. 1** — совпадает:
  «$l(f)=l_\sigma(f):=-(f'-\sigma f)'-\sigma f'$», «$\operatorname{dom}l_\sigma=\lbrace f\in W_1^1(0,1)\mid f^{[1]}\in W_1^1(0,1),\ l_\sigma(f)\in L_2(0,1)\rbrace$»,
  $f^{[1]}=f'-\sigma f$.
- **$T_{\mathrm D}$, с. 2, (1.3)** — совпадает:
  «$\operatorname{dom}T_{\mathrm D}=\lbrace f\in\operatorname{dom}l_\sigma\mid f(0)=f(1)=0\rbrace$».
- **Нумерация $\lambda_n$, с. 2, (1.4)** — совпадает: «the eigenvalues of
  $T_{\mathrm D}$ … counted with multiplicities and arranged by increasing of the
  real—and then, if equal, imaginary—parts of $\lambda_n$», «$\Omega:=\lbrace z\in\mathbb C\mid-\pi/2<\arg z\le\pi/2\rbrace\cup\lbrace z=0\rbrace$».
  Вид кратности на с. 2 не назван — верно. В карточке не указано начало нумерации: в
  источнике $n\in\mathbb N$, то есть $n\ge1$ («$(\tilde\lambda_n)_{n\in\mathbb N}$»,
  с. 2; «$n\in\mathbb N$», с. 18).
- **Учёт кратности, с. 7, § 3** — совпадает, включая условие: «Assume that
  $\sigma\in L_2$ is such that the quadratic form $\mathfrak t_{\sigma,\mathrm N}$ is
  strictly accretive», «the numbers $\pm\lambda_n$ coincide with the zeros of the entire
  even function $s(1,\cdot)$ … if some $\lambda^2$ is an eigenvalue of $T_{\mathrm D}$ of
  algebraic multiplicity $m$, then $\lambda$ is a zero of $s(1,\cdot)$ of order $m$».
  Статья приводит это без доказательства и без ссылки; в карточке это не оговорено.
  Строгая аккретивность определена на с. 6:
  «$\operatorname{Re}\mathfrak t_{\mathrm N}[f]>0$ for all nonzero
  $f\in\operatorname{dom}\mathfrak t_{\mathrm N}$».
- **Сдвиг, с. 18** — совпадает: «In a generic situation we add a suitable constant $C$
  to the potential $q$ to get a potential $\hat q:=q+C$ that falls into the
  above-considered case».
- **Обозначения $s_n$, $c_n$, $V$, с. 4** — совпадает.
- **Теорема 1.1, с. 4** — совпадает: «Assume that $q\in W_2^{\alpha-1}(0,1)$ for some
  $\alpha\in[0,1]$ and fix an arbitrary distributional primitive
  $\sigma\in W_2^\alpha(0,1)$ of $q$. Then there exists a function
  $\tilde\sigma\in W_2^{2\alpha}(0,1)$ such that
  $\lambda_n=\pi n-s_{2n}(\sigma)-s_{2n}(\tilde\sigma)$». Формула для $\mu_n$ в
  карточку не внесена; для задачи Дирихле она не нужна.
- **Теорема 1.2, с. 4, (1.11)** — совпадает: гипотезы те же, $\omega\in W_2^\gamma(0,1)$,
  «$\gamma:=\min\lbrace3\alpha,1+\alpha\rbrace$», формула для $\lambda_n$ и $\sigma^-$
  (нижний знак в $\sigma^\pm$) переписаны верно. Доказательство на с. 18–19 — верно.
- **Следствие 1.3, с. 4, (1.12)** — совпадает: «Under the assumptions (and in the
  notations) of Theorem 1.2 … $+\mathrm O(n^{-\gamma}),\ n\to\infty$». Доказательство на
  с. 19 — верно.
- **Опора следствия 1.3** — совпадает: с. 4: «Theorem 1.2 and [31] imply the following»;
  с. 19: «Let now $\alpha\in(1/3,1]$. Since the function $\sigma\in W_2^\alpha$ satisfy
  then condition (vi) of Theorem 3.12 of [31], one has
  $\lambda_n=\pi n-s_{2n}(\sigma)+a_n$ with $(a_n)\in\ell_1$». При $\alpha\in[0,1/3]$
  доказательство обходится леммой A.5 статьи. Ссылка [31], с. 25: «A. M. Savchuk and
  A. A. Shkalikov, Sturm–Liouville operators with distributional potentials, Trudy Mosk.
  Matem. Ob-va, 64 (2003), 159–212». Замечание к карточке: в реестре S44 — препринт
  arXiv:math/0301077v1, а статья цитирует журнальную версию; номер «теорема 3.12» и её
  условие (vi) в препринте не сверены.
- **Замечание 6.3, с. 20** — совпадает: «If $\alpha=1$, then
  $\sigma(x)=h+\int_0^xq$ for some $h\in\mathbb C$, and formulae (1.11) give
  $\lambda_n=\pi n+\dfrac{\int_0^1q}{2\pi n}+\dfrac{\tilde\lambda_n'}{n}$ … for some
  $\ell_2$-sequences $(\tilde\lambda_n')$». Вывод из (1.11) в статье не выписан — пометка
  «без доказательства» верна.
- **Условия вне текста теорем.** Других условий на теоремы 1.1, 1.2 и следствие 1.3 не
  найдено: «Throughout the paper» на с. 5 вводит только обозначения; строгая аккретивность
  (с. 6–7, 18) — промежуточное предположение, снятое сдвигом на с. 18.
- **Отсутствие асимптотики собственных функций, с. 3–4** — совпадает: «Also [31] gives
  the eigenfunction asymptotics, which we do not study here».

**Применимость к I19, список гипотез.** Названы проверки: класс потенциала ($\alpha=1$
после замены $w=\ell x$), первообразная $\sigma\in W^1_2$, отрезок $[0,1]$ и пересчёт
$\lambda=\lambda_n^2/\ell^2$, область $T_{\mathrm D}$, вид кратности, опора следствия 1.3
на [31]. Гипотез теорем 1.1, 1.2 без названной проверки нет. Не закрыто:

1. Остаток $O(1/n)$ утверждения (B) идеи I19. Замечание 6.3 даёт для $\lambda_n^2$
   остаток $2\pi\tilde\lambda_n'+O(n^{-2})$ с $(\tilde\lambda_n')\in\ell_2$, то есть
   $o(1)$, как и записано в карточке. Вывод $O(1/n)$ из следствия 1.3 требует оценки
   $s_{2n}(\sigma^-)$ и $s_{2n}(\sigma)c_{2n}(V\sigma)$ для гладкого $q$ с точностью
   $O(n^{-2})$; этого расчёта в карточке нет.
2. Теорема 3.12 из [31] при $\alpha=1$ остаётся без карточки (в карточке это сказано), и
   версия S44 в реестре отличается от цитируемой.
3. Алгебраичность кратности в нумерации $\lambda_n$ для потенциала без строгой
   аккретивности — вывод карточки из с. 7 и с. 18, а не утверждение статьи: на с. 18
   статья пишет $\lambda_n=\sqrt{\hat\lambda_n^2-C}$ и о кратностях и о согласовании
   нумераций $\lambda_n$ и $\hat\lambda_n$ не говорит.

Предлагаемые правки карточки: дописать $n\in\mathbb N$ в определение нумерации; пометить,
что утверждение с. 7 о порядке нуля дано в статье без доказательства; в абзаце о следствии
1.3 указать, что [31] — журнальная версия, а S44 реестра — препринт.

**Вердикт: совпадает.** Номера утверждений, страницы, гипотезы, выводы и определения
карточки соответствуют PDF; замечания выше — неполнота, расхождений с источником нет.
