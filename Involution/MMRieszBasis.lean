module

public import Involution.BracketBounds

/-! From projections close to orthogonal ones to two-sided Riesz inequalities
(cf. Wyss, Proposition 3.7). -/

@[expose] public noncomputable section

namespace Involution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem le_of_sq_le_mul {X a : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (h : X ^ 2 ≤ a * X) : X ≤ a := by
  rcases hX.lt_or_eq with hX | hX
  · nlinarith
  · rw [← hX]; exact ha

/-- Two-sided Riesz inequalities for elements of the ranges of disjoint idempotents `P k`,
given orthogonal-type projections `Q k` and summable estimates for `P k - Q k`. -/
theorem riesz_bounds_of_estimates (P Q : ℕ → E →L[ℂ] E) (c : ℝ) (hc : 0 ≤ c)
    (hdisj : ∀ j k, j ≠ k → P j * P k = 0)
    (hQ : ∀ (t : Finset ℕ) (u : E), ∑ k ∈ t, ‖Q k u‖ ^ 2 ≤ ‖u‖ ^ 2)
    (hQs : ∀ k (x y : E), inner ℂ (Q k x) y = inner ℂ x (Q k y))
    (hD1 : ∀ (t : Finset ℕ) (x : ℕ → E) (w : E),
      ∑ k ∈ t, ‖inner ℂ w ((P k - Q k) (x k))‖ ≤ c * Real.sqrt (∑ k ∈ t, ‖x k‖ ^ 2) * ‖w‖)
    (hD2 : ∀ (t : Finset ℕ) (u : E) (w : ℕ → E),
      ∑ k ∈ t, ‖inner ℂ (w k) ((P k - Q k) u)‖ ≤ c * ‖u‖ * Real.sqrt (∑ k ∈ t, ‖w k‖ ^ 2))
    (t : Finset ℕ) (v : ℕ → E) (hv : ∀ k, P k (v k) = v k) :
    ∑ k ∈ t, ‖v k‖ ^ 2 ≤ (1 + c) ^ 2 * ‖∑ k ∈ t, v k‖ ^ 2 ∧
      ‖∑ k ∈ t, v k‖ ^ 2 ≤ (1 + c) ^ 2 * ∑ k ∈ t, ‖v k‖ ^ 2 := by
  set S := ∑ k ∈ t, ‖v k‖ ^ 2 with hS
  set u := ∑ k ∈ t, v k with hu
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsqS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
  constructor
  · -- lower bound
    have hPu : ∀ k ∈ t, P k u = v k := by
      intro k hk
      rw [hu, map_sum, Finset.sum_eq_single k]
      · exact hv k
      · intro j _ hjk
        rw [← hv j, ← mul_apply_eq_comp, hdisj k j (Ne.symm hjk), zero_apply]
      · intro h; exact absurd hk h
    have h1 : S ≤ ∑ k ∈ t, ‖inner ℂ (v k) (Q k u)‖ + ∑ k ∈ t, ‖inner ℂ (v k) ((P k - Q k) u)‖ := by
      rw [← Finset.sum_add_distrib, hS]
      refine Finset.sum_le_sum fun k hk => ?_
      have e : ‖v k‖ ^ 2 = RCLike.re (inner ℂ (v k) (P k u)) := by
        rw [hPu k hk]; exact (inner_self_eq_norm_sq _).symm
      rw [e, show P k u = Q k u + (P k - Q k) u by simp, inner_add_right, map_add]
      exact add_le_add ((RCLike.re_le_norm _)) ((RCLike.re_le_norm _))
    have h2 : ∑ k ∈ t, ‖inner ℂ (v k) (Q k u)‖ ≤ Real.sqrt S * ‖u‖ := by
      calc ∑ k ∈ t, ‖inner ℂ (v k) (Q k u)‖ ≤ ∑ k ∈ t, ‖v k‖ * ‖Q k u‖ :=
            Finset.sum_le_sum fun k _ => norm_inner_le_norm _ _
        _ ≤ Real.sqrt S * Real.sqrt (∑ k ∈ t, ‖Q k u‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ ≤ Real.sqrt S * ‖u‖ := by
            gcongr
            rw [Real.sqrt_le_left (norm_nonneg _)]
            exact hQ t u
    have h3 := hD2 t u v
    have h4 : Real.sqrt S ^ 2 ≤ ((1 + c) * ‖u‖) * Real.sqrt S := by
      rw [hsqS]; nlinarith [norm_nonneg u, Real.sqrt_nonneg S]
    have h5 := le_of_sq_le_mul (Real.sqrt_nonneg S) (by positivity) h4
    calc S = Real.sqrt S ^ 2 := hsqS.symm
      _ ≤ ((1 + c) * ‖u‖) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg S) h5 2
      _ = _ := by ring
  · -- upper bound
    have h1 : ‖u‖ ^ 2 ≤ ∑ k ∈ t, ‖inner ℂ u (Q k (v k))‖ +
        ∑ k ∈ t, ‖inner ℂ u ((P k - Q k) (v k))‖ := by
      rw [← Finset.sum_add_distrib, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      conv_lhs => rw [show inner ℂ u u = ∑ k ∈ t, inner ℂ u (v k) by rw [← inner_sum]]
      rw [map_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have e : inner ℂ u (v k) = inner ℂ u (Q k (v k)) + inner ℂ u ((P k - Q k) (v k)) := by
        rw [← inner_add_right, sub_apply, add_sub_cancel, hv k]
      rw [e, map_add]
      exact add_le_add ((RCLike.re_le_norm _)) ((RCLike.re_le_norm _))
    have h2 : ∑ k ∈ t, ‖inner ℂ u (Q k (v k))‖ ≤ ‖u‖ * Real.sqrt S := by
      calc ∑ k ∈ t, ‖inner ℂ u (Q k (v k))‖ ≤ ∑ k ∈ t, ‖Q k u‖ * ‖v k‖ := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [← hQs]; exact norm_inner_le_norm _ _
        _ ≤ Real.sqrt (∑ k ∈ t, ‖Q k u‖ ^ 2) * Real.sqrt S :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ ≤ ‖u‖ * Real.sqrt S := by
            gcongr
            rw [Real.sqrt_le_left (norm_nonneg _)]
            exact hQ t u
    have h3 := hD1 t v u
    have h4 : ‖u‖ ^ 2 ≤ ((1 + c) * Real.sqrt S) * ‖u‖ := by
      nlinarith [norm_nonneg u, Real.sqrt_nonneg S]
    have h5 := le_of_sq_le_mul (norm_nonneg u) (by positivity) h4
    calc ‖u‖ ^ 2 ≤ ((1 + c) * Real.sqrt S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
      _ = (1 + c) ^ 2 * Real.sqrt S ^ 2 := by ring
      _ = _ := by rw [hsqS]

end Involution
