module

public import Involution.EigenvalueSector

/-! Auxiliary results for `Involution.ResolventBound`.

* `reflectedMultiplier_re_inner_bound_of_real`: for a **real** coefficient `A`,
  `|Re ⟪W, A R W⟫| ≤ α ‖W‖²` whenever `‖A(x) + A(-x)‖ ≤ 2α` a.e.
* `exists_inverse_of_coercive`: a coercive operator `c ‖W‖² ≤ Re ⟪W, T W⟫` on `L₂(-1,1)` has a
  two-sided bounded inverse of norm at most `c⁻¹`.
* `resolvent_estimate_corrected`: unique solvability of `(L_a + s) f = h` for `s ≥ 0` with the
  bound `‖f‖ ≤ ‖spectralGreen‖ / (1 - α) * ‖h‖`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Step 1 for a real coefficient: only the even part of `A` contributes to `Re ⟪W, A R W⟫`. -/
theorem reflectedMultiplier_re_inner_bound_of_real (A : IntervalLInfinity)
    (hA : ∀ᵐ x ∂intervalMeasure, star (A x) = A x) (α : ℝ)
    (hα : ∀ᵐ x ∂intervalMeasure, ‖A x + A (-x)‖ ≤ 2 * α) (W : IntervalL2) :
    |(inner ℂ W (reflectedMultiplier A W)).re| ≤ α * ‖W‖ ^ 2 := by
  set X : ℂ := inner ℂ W (reflectedMultiplier A W) with hX
  have hconj : (starRingEnd ℂ) X = inner ℂ W (l2Reflect (boundedMultiplier A W)) := by
    rw [hX, inner_conj_symm]
    exact inner_reflectedMultiplier_left A hA W W
  have h1 : ‖X + (starRingEnd ℂ) X‖ ≤ ‖W‖ * (2 * α * ‖W‖) := by
    rw [hconj, hX, ← inner_add_right]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (reflectedMultiplier_add_adjoint_norm_le A _ hα W) (norm_nonneg _))
  have h2 : (X + (starRingEnd ℂ) X).re = 2 * X.re := by
    rw [Complex.add_re, Complex.conj_re]
    ring
  have h3 := Complex.abs_re_le_norm (X + (starRingEnd ℂ) X)
  rw [h2, abs_mul, abs_two] at h3
  nlinarith

theorem realIntervalCoefficient_sum_norm_le (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α) :
    ∀ᵐ x ∂intervalMeasure,
      ‖realIntervalCoefficient a ha x + realIntervalCoefficient a ha (-x)‖ ≤ 2 * α := by
  have hax := realIntervalCoefficient_ae a ha
  have han : ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient a ha (-x) = ((a (-x) : ℝ) : ℂ) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hax] with x hx
    exact hx
  filter_upwards [hax, han, hα] with x h1 h2 h3
  have h1' : realIntervalCoefficient a ha x = ((a x : ℝ) : ℂ) := h1
  rw [h1', h2, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  exact h3

theorem principalOperator_re_inner_lower (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α) (W : IntervalL2) :
    (1 - α) * ‖W‖ ^ 2 ≤
      (inner ℂ W (principalOperator (realIntervalCoefficient a ha) W)).re := by
  have hb := reflectedMultiplier_re_inner_bound_of_real (realIntervalCoefficient a ha)
    (realIntervalCoefficient_real a ha) α (realIntervalCoefficient_sum_norm_le a ha α hα) W
  have hT : principalOperator (realIntervalCoefficient a ha) W =
      W + reflectedMultiplier (realIntervalCoefficient a ha) W := rfl
  have hre : (inner ℂ W W).re = ‖W‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) W
  rw [hT, inner_add_right, Complex.add_re, hre]
  linarith [(abs_le.mp hb).1]

/-- A coercive bounded operator on `L₂(-1,1)` is boundedly invertible, `‖T⁻¹‖ ≤ c⁻¹`. -/
theorem exists_inverse_of_coercive (T : IntervalL2 →L[ℂ] IntervalL2) (c : ℝ) (hc : 0 < c)
    (hT : ∀ W, c * ‖W‖ ^ 2 ≤ (inner ℂ W (T W)).re) :
    ∃ Tinv : IntervalL2 →L[ℂ] IntervalL2, Tinv.comp T = 1 ∧ T.comp Tinv = 1 ∧
      ‖Tinv‖ ≤ c⁻¹ := by
  have hlow : ∀ W, c * ‖W‖ ≤ ‖T W‖ := by
    intro W
    rcases (norm_nonneg W).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · have h1 := (hT W).trans ((Complex.re_le_norm _).trans (norm_inner_le_norm W (T W)))
      apply le_of_mul_le_mul_left _ hpos
      nlinarith
  have hle : ∀ W, ‖W‖ ≤ ((⟨c⁻¹, (inv_pos.mpr hc).le⟩ : NNReal) : ℝ) * ‖T W‖ := by
    intro W
    change ‖W‖ ≤ c⁻¹ * ‖T W‖
    rw [le_inv_mul_iff₀ hc]
    exact hlow W
  have hanti := T.antilipschitz_of_bound hle
  have hker : (T : IntervalL2 →ₗ[ℂ] IntervalL2).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hanti.injective
  have hclosed : IsClosed (Set.range T) := hanti.isClosed_range T.uniformContinuous
  have hrange : (T : IntervalL2 →ₗ[ℂ] IntervalL2).range = ⊤ := by
    set K := (T : IntervalL2 →ₗ[ℂ] IntervalL2).range with hK
    have hKc : IsClosed (K : Set IntervalL2) := by
      exact hclosed
    have : CompleteSpace K := hKc.completeSpace_coe
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro v hv
    have h0 : inner ℂ (T v) v = 0 := (Submodule.mem_orthogonal K v).mp hv (T v) ⟨v, rfl⟩
    have h := hT v
    rw [← inner_conj_symm, h0, map_zero, Complex.zero_re] at h
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp this
  let e := ContinuousLinearEquiv.ofBijective T hker hrange
  have he : ∀ x, e x = T x := fun x => rfl
  refine ⟨e.symm.toContinuousLinearMap, ?_, ?_, ?_⟩
  · ext1 x
    change e.symm (T x) = x
    rw [← he, e.symm_apply_apply]
  · ext1 x
    change T (e.symm x) = x
    rw [← he, e.apply_symm_apply]
  · refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) fun g => ?_
    have h := hle (e.symm g)
    change ‖e.symm g‖ ≤ c⁻¹ * ‖T (e.symm g)‖ at h
    rw [← he, e.apply_symm_apply] at h
    exact h


/-- The operator `T_a + s G`, where `G = spectralGreen`; on the Dirichlet domain
`(L_a + s) f = (T_a + s G) (-f'')`. -/
def shiftedPrincipalOperator (A : IntervalLInfinity) (s : ℝ) : IntervalL2 →L[ℂ] IntervalL2 :=
  principalOperator A + (s : ℂ) • spectralGreen

theorem variableSobolevOperator_add_smul_eq (A : IntervalLInfinity) (s : ℝ) (f : IntervalL2)
    (hf : MemDirichletH2 f) :
    variableSobolevOperator A f hf.1 + s • f =
      shiftedPrincipalOperator A s (-secondWeakDeriv f hf.1) := by
  rw [variableSobolevOperator_eq_principal, shiftedPrincipalOperator,
    add_apply, smul_apply,
    spectralGreen_left_inverse f hf, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem spectralGreen_re_inner_nonneg (W : IntervalL2) :
    0 ≤ (inner ℂ W (spectralGreen W)).re := by
  set f := spectralGreen W
  have hf := spectralGreen_memDirichletH2 W
  have hW : -secondWeakDeriv f hf.1 = W := spectralGreen_right_inverse W
  have h := negativeSecondWeakDeriv_energy f f hf hf.1
  rw [hW] at h
  rw [← inner_conj_symm, Complex.conj_re, h]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem shiftedPrincipalOperator_re_inner_lower (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α) (s : ℝ) (hs : 0 ≤ s)
    (W : IntervalL2) :
    (1 - α) * ‖W‖ ^ 2 ≤
      (inner ℂ W (shiftedPrincipalOperator (realIntervalCoefficient a ha) s W)).re := by
  have h1 := principalOperator_re_inner_lower a ha α hα W
  have h2 := spectralGreen_re_inner_nonneg W
  rw [shiftedPrincipalOperator, add_apply, smul_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  nlinarith


/-- **Corrected resolvent estimate.** For real `a` with `|a(x) + a(-x)| ≤ 2α`, `α < 1`, and
`s ≥ 0`, the equation `(L_a + s) f = h` has a unique solution in the weak Dirichlet domain, and
`‖f‖ ≤ ‖spectralGreen‖ / (1 - α) * ‖h‖`. -/
theorem resolvent_estimate_corrected (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α)
    (s : ℝ) (hs : 0 ≤ s) (h : IntervalL2) :
    (∃! f : IntervalL2, ∃ hf : MemDirichletH2 f,
      variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 + s • f = h) ∧
    (∀ (f : IntervalL2) (hf : MemDirichletH2 f),
      variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 + s • f = h →
      ‖f‖ ≤ ‖spectralGreen‖ / (1 - α) * ‖h‖) := by
  set A := realIntervalCoefficient a ha
  obtain ⟨Sinv, hl, hr, hn⟩ := exists_inverse_of_coercive (shiftedPrincipalOperator A s)
    (1 - α) (by linarith) (shiftedPrincipalOperator_re_inner_lower a ha α hα s hs)
  have hleft : ∀ W, Sinv (shiftedPrincipalOperator A s W) = W := fun W => by
    simpa using congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T W) hl
  have hright : ∀ g, shiftedPrincipalOperator A s (Sinv g) = g := fun g => by
    simpa using congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T g) hr
  have key : ∀ (f : IntervalL2) (hf : MemDirichletH2 f),
      variableSobolevOperator A f hf.1 + s • f = h → f = spectralGreen (Sinv h) := by
    intro f hf heq
    rw [variableSobolevOperator_add_smul_eq A s f hf] at heq
    rw [← heq, hleft, spectralGreen_left_inverse f hf]
  refine ⟨⟨spectralGreen (Sinv h), ⟨spectralGreen_memDirichletH2 (Sinv h), ?_⟩, ?_⟩, ?_⟩
  · rw [variableSobolevOperator_add_smul_eq A s _ (spectralGreen_memDirichletH2 (Sinv h)),
      spectralGreen_right_inverse, hright]
  · rintro f ⟨hf, heq⟩
    exact key f hf heq
  · intro f hf heq
    rw [key f hf heq]
    calc ‖spectralGreen (Sinv h)‖ ≤ ‖spectralGreen‖ * ‖Sinv h‖ := spectralGreen.le_opNorm _
      _ ≤ ‖spectralGreen‖ * ((1 - α)⁻¹ * ‖h‖) := by
          gcongr
          exact (Sinv.le_opNorm h).trans (by gcongr)
      _ = ‖spectralGreen‖ / (1 - α) * ‖h‖ := by ring

end Involution
