module

public import Involution.Model.BracketBounds
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Формулировка теоремы 6.9 обзора А. А. Шкаликова (S3) о возмущении формой.

`FormMarkusMatsaevStatement` — теорема 6.9 обзора S3 для самосопряжённого положительного
оператора `T` с ортонормированным базисом собственных векторов: оператор порядка `α`
(условие (4.2) обзора), форма `𝔟`, `p`-подчинённая `T` в смысле (3.6), `p ∈ [0, 1)`,
`α⁻¹ ≤ 1 - p`. Сумма `A = T + B` понимается как оператор, порождённый суммой форм
(теорема 2.1 обзора). Теорема в проекте не доказывается; редукции принимают её гипотезой.

Область формы `T`: `D(T^{1/2}) = {x : ∑ λᵢ |⟨eᵢ, x⟩|² < ∞}` (`formDomain`), где
`‖T^{1/2} x‖² = formEnergy e lam x`, а `formPairing e lam y x = ⟨T^{1/2} y, T^{1/2} x⟩`. -/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Область формы `D(T^{1/2})` диагонального оператора `T eᵢ = λᵢ eᵢ`. -/
def formDomain (e : HilbertBasis ι ℂ H) (lam : ι → ℝ) : Submodule ℂ H where
  carrier := {x | Summable fun i => lam i * ‖e.repr x i‖ ^ 2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    refine Summable.of_norm_bounded (hx.abs.mul_left 2 |>.add (hy.abs.mul_left 2)) ?_
    intro i
    simp only [map_add, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    have h1 : ‖(e.repr x + e.repr y) i‖ ≤ ‖e.repr x i‖ + ‖e.repr y i‖ := by
      rw [lp.coeFn_add, Pi.add_apply]
      exact norm_add_le _ _
    have h2 : ‖(e.repr x + e.repr y) i‖ ^ 2 ≤ 2 * ‖e.repr x i‖ ^ 2 + 2 * ‖e.repr y i‖ ^ 2 := by
      nlinarith [norm_nonneg ((e.repr x + e.repr y) i), norm_nonneg (e.repr x i),
        norm_nonneg (e.repr y i), sq_nonneg (‖e.repr x i‖ - ‖e.repr y i‖)]
    nlinarith [abs_nonneg (lam i), mul_le_mul_of_nonneg_left h2 (abs_nonneg (lam i))]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have : (fun i => lam i * ‖e.repr (c • x) i‖ ^ 2) =
        fun i => ‖c‖ ^ 2 * (lam i * ‖e.repr x i‖ ^ 2) := by
      funext i
      rw [map_smul, lp.coeFn_smul, Pi.smul_apply, norm_smul]
      ring
    rw [this]
    exact hx.mul_left _

/-- Энергия `‖T^{1/2} x‖² = ∑ λᵢ |⟨eᵢ, x⟩|²`. -/
def formEnergy (e : HilbertBasis ι ℂ H) (lam : ι → ℝ) (x : H) : ℝ :=
  ∑' i, lam i * ‖e.repr x i‖ ^ 2

/-- Форма оператора `T`: `⟨T^{1/2} y, T^{1/2} x⟩ = ∑ λᵢ conj ⟨eᵢ, y⟩ ⟨eᵢ, x⟩`. -/
def formPairing (e : HilbertBasis ι ℂ H) (lam : ι → ℝ) (y x : H) : ℂ :=
  ∑' i, (lam i : ℂ) * (conj (e.repr y i) * e.repr x i)

/-- **Теорема 6.9 обзора S3 для самосопряжённого положительного `T`.**
Пусть `T eᵢ = λᵢ eᵢ`, `λᵢ > 0`, в ортонормированном базисе `e`, и `T` имеет порядок `α > 0`:
счётная функция `n(t) = #{i : λᵢ ≤ t}` не превосходит `c t^{1/α} + C`. Пусть полуторалинейная
форма `𝔟` на `D(T^{1/2})` удовлетворяет (3.6):
`|𝔟[x, x]| ≤ b ‖T^{1/2} x‖^{2p} ‖x‖^{2 - 2p} + M ‖x‖²` при `p ∈ [0, 1)`, `α⁻¹ ≤ 1 - p`.
Оператор `A = T + B` суммы форм: `x ∈ D(A)`, `A x = z`, если `x ∈ D(T^{1/2})` и
`⟨T^{1/2} y, T^{1/2} x⟩ + 𝔟[y, x] = ⟨y, z⟩` для всех `y ∈ D(T^{1/2})`.
Вывод: корневые векторы `A` образуют безусловный базис (в гильбертовом пространстве —
базис Рисса) со скобками; скобки — конечномерные подпространства из `D(A)`,
инвариантные относительно `A` (спектральные проекторы по контурам). -/
def FormMarkusMatsaevStatement : Prop :=
  ∀ (ι H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : HilbertBasis ι ℂ H) (lam : ι → ℝ), (∀ i, 0 < lam i) →
    ∀ α c C : ℝ, 0 < α →
    (∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t) →
      (s.card : ℝ) ≤ c * t ^ α⁻¹ + C) →
    ∀ p b M : ℝ, 0 ≤ p → p < 1 → α⁻¹ ≤ 1 - p → 0 ≤ b → 0 ≤ M →
    ∀ 𝔟 : formDomain e lam →ₗ⋆[ℂ] formDomain e lam →ₗ[ℂ] ℂ,
    (∀ x : formDomain e lam, ‖𝔟 x x‖ ≤
      b * formEnergy e lam x ^ p * (‖(x : H)‖ ^ 2) ^ (1 - p) + M * ‖(x : H)‖ ^ 2) →
    ∃ V : ℕ → Submodule ℂ H, Nonempty (RieszBasisWithBrackets V) ∧
      ∀ k, ∀ v ∈ V k, ∃ hv : v ∈ formDomain e lam, ∃ z ∈ V k,
        ∀ y : formDomain e lam,
          formPairing e lam y v + 𝔟 y ⟨v, hv⟩ = inner ℂ (y : H) z

end Involution
