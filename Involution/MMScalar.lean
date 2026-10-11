module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Scalar estimates used for the sums of Riesz projections: the integral of
`1 / ((x - p)² + α²)`, sums of inverse squares over separated points, and an AM–GM lemma. -/

@[expose] public noncomputable section

open Set intervalIntegral

namespace Involution

theorem integral_inv_sq_add_sq_le (p α a b : ℝ) (hα : 0 < α) :
    ∫ x in a..b, 1 / ((x - p) ^ 2 + α ^ 2) ≤ Real.pi / α := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun x => Real.arctan ((x - p) / α) / α)
      (1 / ((x - p) ^ 2 + α ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => (x - p) / α) (1 / α) x := by
      simpa using ((hasDerivAt_id x).sub_const p).div_const α
    have h2 := (h1.arctan).div_const α
    convert h2 using 1
    field_simp
    ring
  have hcont : Continuous fun x : ℝ => 1 / ((x - p) ^ 2 + α ^ 2) := by
    refine Continuous.div continuous_const (by fun_prop) fun x => ?_
    positivity
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have h1 := Real.arctan_lt_pi_div_two ((b - p) / α)
  have h2 := Real.neg_pi_div_two_lt_arctan ((a - p) / α)
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hα.le

theorem sum_inv_sq_tele (ε d : ℝ) (hε : 0 < ε) (hd : 0 < d) (N : ℕ) :
    ∑ r ∈ Finset.range N, 1 / (ε + r * d) ^ 2 ≤ 1 / ε ^ 2 + 1 / (ε * d) := by
  have key : ∀ N : ℕ, ∑ r ∈ Finset.range (N + 1), 1 / (ε + r * d) ^ 2 ≤
      1 / ε ^ 2 + 1 / (ε * d) - 1 / (d * (ε + N * d)) := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul,
        add_zero]
      have : 1 / (ε * d) - 1 / (d * ε) = 0 := by rw [mul_comm]; ring
      linarith
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 0 < ε + n * d := by positivity
      have h2 : 0 < ε + (n + 1 : ℕ) * d := by positivity
      have e : 1 / (d * (ε + n * d)) - 1 / (d * (ε + (n + 1 : ℕ) * d)) =
          1 / ((ε + n * d) * (ε + (n + 1 : ℕ) * d)) := by
        push_cast; field_simp; ring
      have h3 : 1 / (ε + (n + 1 : ℕ) * d) ^ 2 ≤ 1 / ((ε + n * d) * (ε + (n + 1 : ℕ) * d)) := by
        apply one_div_le_one_div_of_le (by positivity)
        rw [sq]
        apply mul_le_mul_of_nonneg_right _ h2.le
        push_cast; nlinarith
      linarith
  rcases N with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]; positivity
  · have := key N
    have : 0 ≤ 1 / (d * (ε + N * d)) := by positivity
    linarith

theorem xi_add_le (ξ : ℕ → ℝ) (d : ℝ) (hgap : ∀ k, ξ k + d ≤ ξ (k + 1)) {j k : ℕ} (h : j ≤ k) :
    ξ j + (k - j : ℕ) * d ≤ ξ k := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have := hgap k
    rw [Nat.succ_sub hjk]
    push_cast
    linarith

/-- Sum of inverse squares of distances from `p` to separated points. -/
theorem sum_inv_sq_sep (ξ : ℕ → ℝ) (ε d : ℝ) (hε : 0 < ε) (hd : 0 < d)
    (hgap : ∀ k, ξ k + d ≤ ξ (k + 1)) (p : ℝ) (hsep : ∀ k, ε ≤ |ξ k - p|) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / (ξ j - p) ^ 2 ≤ 2 * (1 / ε ^ 2 + 1 / (ε * d)) := by
  classical
  set g : ℕ → ℝ := fun r => 1 / (ε + r * d) ^ 2
  have hT := sum_inv_sq_tele ε d hε hd N
  have hne : ∀ j, ξ j ≠ p := fun j h => by
    have := hsep j; rw [h, sub_self, abs_zero] at this; linarith
  set U := (Finset.range N).filter (fun j => p < ξ j)
  set U' := (Finset.range N).filter (fun j => ¬ p < ξ j)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun j => p < ξ j)]
  have hU : ∑ j ∈ U, 1 / (ξ j - p) ^ 2 ≤ 1 / ε ^ 2 + 1 / (ε * d) := by
    rcases U.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty]; positivity
    set j0 := U.min' h
    have hj0 : j0 ∈ U := U.min'_mem h
    have hj0p : p < ξ j0 := (Finset.mem_filter.mp hj0).2
    have hj0e : ε ≤ ξ j0 - p := by
      have := hsep j0; rwa [abs_of_pos (by linarith)] at this
    calc ∑ j ∈ U, 1 / (ξ j - p) ^ 2 ≤ ∑ j ∈ U, g (j - j0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjj : j0 ≤ j := U.min'_le j hj
          have h1 := xi_add_le ξ d hgap hjj
          apply one_div_le_one_div_of_le (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          linarith
      _ = ∑ r ∈ U.image (fun j => j - j0), g r := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have := U.min'_le a ha
          have := U.min'_le b hb
          simp only at hab
          omega
      _ ≤ ∑ r ∈ Finset.range N, g r := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro r hr
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
          have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          exact Finset.mem_range.mpr (by omega)
      _ ≤ _ := hT
  have hU' : ∑ j ∈ U', 1 / (ξ j - p) ^ 2 ≤ 1 / ε ^ 2 + 1 / (ε * d) := by
    rcases U'.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty]; positivity
    set j1 := U'.max' h
    have hj1 : j1 ∈ U' := U'.max'_mem h
    have hj1p : ξ j1 < p := lt_of_le_of_ne (not_lt.mp (Finset.mem_filter.mp hj1).2) (hne j1)
    have hj1e : ε ≤ p - ξ j1 := by
      have := hsep j1; rwa [abs_of_neg (by linarith), neg_sub] at this
    calc ∑ j ∈ U', 1 / (ξ j - p) ^ 2 ≤ ∑ j ∈ U', g (j1 - j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjj : j ≤ j1 := U'.le_max' j hj
          have h1 := xi_add_le ξ d hgap hjj
          apply one_div_le_one_div_of_le (by positivity)
          rw [← neg_sub, neg_sq]
          apply pow_le_pow_left₀ (by positivity)
          linarith
      _ = ∑ r ∈ U'.image (fun j => j1 - j), g r := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have := U'.le_max' a ha
          have := U'.le_max' b hb
          simp only at hab
          omega
      _ ≤ ∑ r ∈ Finset.range N, g r := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro r hr
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
          have := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
          exact Finset.mem_range.mpr (by omega)
      _ ≤ _ := hT
  linarith

/-- If `L ≤ τ a + b / τ` for all `τ > 0`, then `L ≤ 2 √(a b)`. -/
theorem le_of_forall_amgm {L a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ τ : ℝ, 0 < τ → L ≤ τ * a + b / τ) : L ≤ 2 * Real.sqrt (a * b) := by
  have key : ∀ δ : ℝ, 0 < δ → L ≤ 2 * Real.sqrt ((a + δ) * (b + δ)) := by
    intro δ hδ
    set τ := Real.sqrt (b + δ) / Real.sqrt (a + δ)
    have hsa : 0 < Real.sqrt (a + δ) := Real.sqrt_pos.mpr (by linarith)
    have hsb : 0 < Real.sqrt (b + δ) := Real.sqrt_pos.mpr (by linarith)
    have hτ : 0 < τ := div_pos hsb hsa
    have h1 := h τ hτ
    have h2 : τ * a + b / τ ≤ τ * (a + δ) + (b + δ) / τ := by
      have : 0 < δ / τ := div_pos hδ hτ
      rw [add_div]
      nlinarith
    have h3 : τ * (a + δ) + (b + δ) / τ = 2 * Real.sqrt ((a + δ) * (b + δ)) := by
      have ea : Real.sqrt (a + δ) ^ 2 = a + δ := Real.sq_sqrt (by linarith)
      have eb : Real.sqrt (b + δ) ^ 2 = b + δ := Real.sq_sqrt (by linarith)
      calc τ * (a + δ) + (b + δ) / τ = (Real.sqrt (b + δ) / Real.sqrt (a + δ)) *
            Real.sqrt (a + δ) ^ 2 + Real.sqrt (b + δ) ^ 2 /
              (Real.sqrt (b + δ) / Real.sqrt (a + δ)) := by rw [ea, eb]
        _ = 2 * (Real.sqrt (a + δ) * Real.sqrt (b + δ)) := by field_simp; ring
        _ = _ := by rw [Real.sqrt_mul (by linarith)]
    linarith
  have hcont : Continuous fun δ : ℝ => 2 * Real.sqrt ((a + δ) * (b + δ)) := by fun_prop
  have ht := hcont.tendsto 0
  simp only [add_zero] at ht
  refine ge_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0))) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact key δ hδ

end Involution
