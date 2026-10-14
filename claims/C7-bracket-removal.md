---
id: C7
title: Когда скобки можно снять
status: proved-aristotle
depends_on: [C5, C8, S4]
lean_theorem: Involution.exists_rieszBasis_iff_uniformBlockBounds
final: false
---

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
`exists_uniformBlockBounds_iff_finiteRiesz`, `exists_rieszBasis_iff_uniformBlockBounds`. Модули `Involution/Model/BracketBounds.lean` и
`Involution/Model/FiniteSynthesis.lean` с этими объявлениями приняты из задачи A5.

**Границы.** Для чётного $a$ базис Рисса получен напрямую (C5). Для блоков C6 и C16
равномерные внутренние константы не проверены; одной простоты собственных значений для
них недостаточно. Достаточный частный случай — одномерные блоки вне конечной части
(S4, замечание 6.3); для $L_a$ он не доказан.
