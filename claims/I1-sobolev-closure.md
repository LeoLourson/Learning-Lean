---
id: I1
title: $H_0^1$ как замыкание пробных функций
status: promoted
next: Доказательство — раздел «Область определения» постановки (claims/question.md); в Lean — `Involution.memDirichletH2_iff_h2_and_h01`.
---

- Дата: 10.10.2026, принято 11.10.2026. Статус: доказано в Lean (`Involution/Estimates/SobolevClosure.lean`,
  задача 7 Aristotle). Формулировка и доказательство — `claims/C*.md`, раздел 0.
- Набросок с первообразными и вычитанием $\bigl(\int\psi_n\bigr)\eta$ не понадобился:
  Aristotle доказал утверждение через $K^{\perp\perp}=\overline K$.
- Определения `IsTestPair` и `MemIntervalH01` приняты 11.10.2026: пользователь оставил
  решение за циклом, а определение совпадает со стандартным замыканием
  $C_c^\infty(-1,1)$ по норме $H^1$.
