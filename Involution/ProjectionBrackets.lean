module

public import Involution.BracketBounds
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! Критерий базиса Рисса подпространств через знакопеременные суммы проекторов
(Wyss, arXiv:0906.2631v1, леммы 3.5–3.6 и предложение 3.7). Если попарно
аннулирующие друг друга проекторы `P k` таковы, что все конечные суммы
`∑ ε k • P k` со знаками `ε k = ±1` ограничены по норме числом `C`, то для векторов
`x k` из образов `P k` выполнены двусторонние оценки
`C⁻² ∑ ‖x k‖² ≤ ‖∑ x k‖² ≤ C² ∑ ‖x k‖²`. -/

@[expose] public noncomputable section

namespace Involution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Знаки можно выбрать так, чтобы квадрат нормы знакопеременной суммы не превосходил
суммы квадратов норм. -/
theorem exists_signs_norm_sq_le (t : Finset ℕ) (x : ℕ → E) :
    ∃ ε : ℕ → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧
      ‖∑ k ∈ t, (ε k : ℂ) • x k‖ ^ 2 ≤ ∑ k ∈ t, ‖x k‖ ^ 2 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε, hε, hle⟩ := ih
    set y := ∑ k ∈ s, (ε k : ℂ) • x k with hy
    have hpar := parallelogram_law_with_norm ℂ y (x a)
    have hcongr : ∀ c : ℝ, (∑ k ∈ s, ((Function.update ε a c k : ℝ) : ℂ) • x k) = y := by
      intro c
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Function.update_of_ne (fun h : k = a => ha (h ▸ hk))]
    by_cases hcase : ‖y + x a‖ ^ 2 ≤ ‖y‖ ^ 2 + ‖x a‖ ^ 2
    · refine ⟨Function.update ε a 1, fun k => ?_, ?_⟩
      · by_cases hk : k = a
        · rw [hk, Function.update_self]
          exact Or.inl rfl
        · rw [Function.update_of_ne hk]
          exact hε k
      · rw [Finset.sum_insert ha, Finset.sum_insert ha, hcongr 1, Function.update_self,
          Complex.ofReal_one, one_smul, add_comm (x a) y]
        linarith
    · refine ⟨Function.update ε a (-1), fun k => ?_, ?_⟩
      · by_cases hk : k = a
        · rw [hk, Function.update_self]
          exact Or.inr rfl
        · rw [Function.update_of_ne hk]
          exact hε k
      · have hsub : ‖y - x a‖ ^ 2 ≤ ‖y‖ ^ 2 + ‖x a‖ ^ 2 := by
          have hlt := not_le.mp hcase
          linarith
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hcongr (-1), Function.update_self,
          Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, add_comm (-x a) y,
          ← sub_eq_add_neg]
        linarith

/-- Знаки можно выбрать и так, чтобы квадрат нормы был не меньше суммы квадратов. -/
theorem exists_signs_norm_sq_ge (t : Finset ℕ) (x : ℕ → E) :
    ∃ ε : ℕ → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) ∧
      ∑ k ∈ t, ‖x k‖ ^ 2 ≤ ‖∑ k ∈ t, (ε k : ℂ) • x k‖ ^ 2 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε, hε, hle⟩ := ih
    set y := ∑ k ∈ s, (ε k : ℂ) • x k with hy
    have hpar := parallelogram_law_with_norm ℂ y (x a)
    have hcongr : ∀ c : ℝ, (∑ k ∈ s, ((Function.update ε a c k : ℝ) : ℂ) • x k) = y := by
      intro c
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Function.update_of_ne (fun h : k = a => ha (h ▸ hk))]
    by_cases hcase : ‖y‖ ^ 2 + ‖x a‖ ^ 2 ≤ ‖y + x a‖ ^ 2
    · refine ⟨Function.update ε a 1, fun k => ?_, ?_⟩
      · by_cases hk : k = a
        · rw [hk, Function.update_self]
          exact Or.inl rfl
        · rw [Function.update_of_ne hk]
          exact hε k
      · rw [Finset.sum_insert ha, Finset.sum_insert ha, hcongr 1, Function.update_self,
          Complex.ofReal_one, one_smul, add_comm (x a) y]
        linarith
    · refine ⟨Function.update ε a (-1), fun k => ?_, ?_⟩
      · by_cases hk : k = a
        · rw [hk, Function.update_self]
          exact Or.inr rfl
        · rw [Function.update_of_ne hk]
          exact hε k
      · have hsub : ‖y‖ ^ 2 + ‖x a‖ ^ 2 ≤ ‖y - x a‖ ^ 2 := by
          have hlt := not_le.mp hcase
          linarith
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hcongr (-1), Function.update_self,
          Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, add_comm (-x a) y,
          ← sub_eq_add_neg]
        linarith

/-- Двусторонние оценки Рисса для образов проекторов с равномерно ограниченными
знакопеременными суммами. -/
theorem projection_riesz_bounds (P : ℕ → E →L[ℂ] E)
    (hPP : ∀ j k, j ≠ k → ∀ x, P j (P k x) = 0)
    (C : ℝ) (hC : 0 < C)
    (hsum : ∀ (t : Finset ℕ) (ε : ℕ → ℝ), (∀ k, ε k = 1 ∨ ε k = -1) →
      ∀ u : E, ‖∑ k ∈ t, (ε k : ℂ) • P k u‖ ≤ C * ‖u‖)
    (t : Finset ℕ) (x : ℕ → E) (hx : ∀ k ∈ t, P k (x k) = x k) :
    (C ^ 2)⁻¹ * (∑ k ∈ t, ‖x k‖ ^ 2) ≤ ‖∑ k ∈ t, x k‖ ^ 2 ∧
      ‖∑ k ∈ t, x k‖ ^ 2 ≤ C ^ 2 * ∑ k ∈ t, ‖x k‖ ^ 2 := by
  classical
  -- действие знакопеременной суммы проекторов на знакопеременную сумму векторов
  have hact : ∀ ε δ : ℕ → ℝ,
      (∑ k ∈ t, (ε k : ℂ) • P k (∑ j ∈ t, (δ j : ℂ) • x j)) =
        ∑ k ∈ t, ((ε k * δ k : ℝ) : ℂ) • x k := by
    intro ε δ
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_sum, Finset.sum_eq_single k]
    · rw [map_smul, hx k hk, smul_smul, Complex.ofReal_mul]
    · intro j hj hjk
      rw [map_smul, ← hx j hj, hPP k j (Ne.symm hjk), smul_zero]
    · intro hk'
      exact absurd hk hk'
  have hone : (∑ k ∈ t, ((1 : ℝ) : ℂ) • x k) = ∑ k ∈ t, x k := by
    simp
  constructor
  · obtain ⟨ε, hε, hge⟩ := exists_signs_norm_sq_ge t x
    have h := hsum t ε hε (∑ j ∈ t, ((1 : ℝ) : ℂ) • x j)
    rw [hact ε (fun _ => 1), hone] at h
    simp only [mul_one] at h
    have hsq : ‖∑ k ∈ t, (ε k : ℂ) • x k‖ ^ 2 ≤ C ^ 2 * ‖∑ k ∈ t, x k‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [inv_mul_le_iff₀ (by positivity)]
    exact hge.trans hsq
  · obtain ⟨ε, hε, hle⟩ := exists_signs_norm_sq_le t x
    have h := hsum t ε hε (∑ j ∈ t, (ε j : ℂ) • x j)
    rw [hact ε ε] at h
    have hsq1 : ∀ k, ε k * ε k = 1 := fun k => by
      rcases hε k with h1 | h1 <;> rw [h1] <;> norm_num
    simp only [hsq1] at h
    rw [hone] at h
    calc
      ‖∑ k ∈ t, x k‖ ^ 2 ≤ (C * ‖∑ j ∈ t, (ε j : ℂ) • x j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ 2 * ‖∑ j ∈ t, (ε j : ℂ) • x j‖ ^ 2 := mul_pow _ _ _
      _ ≤ C ^ 2 * ∑ k ∈ t, ‖x k‖ ^ 2 := mul_le_mul_of_nonneg_left hle (by positivity)

end Involution
