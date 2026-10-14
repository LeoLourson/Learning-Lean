---
id: C3
title: Постоянный коэффициент
status: proved-aristotle
depends_on: []
lean_theorem: Involution.constantModel_dense_span
final: false
---

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
собственные уравнения всех векторов базиса — `Involution/Model/ModelEigenbasis.lean`. Модуль
`Involution/Model/ModelBasis.lean` с объявлениями `constantModel_orthonormal` и `constantModel_dense_span`
принят из задачи A2.
