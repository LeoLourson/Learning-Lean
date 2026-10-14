module

public import Involution.Setup.WeakDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact

/-! Первообразная гладкой пробной функции нулевого среднего.
Компактность носителя первообразной позволяет использовать её в определении
слабой производной. Этот шаг нужен для доказательства постоянства функций
с нулевой слабой производной и существования регулярных представителей.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Involution

theorem smooth_primitive_with_compact_support (φ : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Icc a b)
    (hz : (∫ x, φ x) = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Icc a b ∧ deriv ψ = φ := by
  let ψ : ℝ → ℝ := fun x => ∫ t in a..x, φ t
  have hd : ∀ x, HasDerivAt ψ (φ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hφ.continuous.intervalIntegrable _ _)
      hφ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hφ.continuous.continuousAt
  have hderiv : deriv ψ = φ := funext fun x => (hd x).deriv
  have hsmooth : ContDiff ℝ ∞ ψ := contDiff_infty_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt, hderiv.symm ▸ hφ⟩
  have hzero {x : ℝ} (hx : x ∉ Icc a b) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
  have habint : (∫ x in a..b, φ x) = 0 := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero hx)]
    exact hz
  have hleft {x : ℝ} (hx : x < a) : ψ x = 0 := by
    change (∫ t in a..x, φ t) = 0
    rw [intervalIntegral.integral_symm]
    have hi : (∫ t in x..a, φ t) = 0 := by
      calc
        _ = ∫ t in x..a, (0 : ℝ) := intervalIntegral.integral_congr_Ioo_of_le hx.le
          (fun t ht => hzero (fun hc => (not_lt_of_ge hc.1) ht.2))
        _ = 0 := by simp
    rw [hi, neg_zero]
  have hright {x : ℝ} (hx : b < x) : ψ x = 0 := by
    have hi : (∫ t in b..x, φ t) = 0 := by
      calc
        _ = ∫ t in b..x, (0 : ℝ) := intervalIntegral.integral_congr_Ioo_of_le hx.le
          (fun t ht => hzero (fun hc => (not_lt_of_ge hc.2) ht.1))
        _ = 0 := by simp
    change (∫ t in a..x, φ t) = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hφ.continuous.intervalIntegrable a b) (hφ.continuous.intervalIntegrable b x), habint, hi,
      add_zero]
  have hsupport : Function.support ψ ⊆ Icc a b := by
    intro x hx
    by_contra hnot
    have hcases : x < a ∨ b < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hnot
    exact hx (hcases.elim hleft hright)
  have htsupport : tsupport ψ ⊆ Icc a b := closure_minimal hsupport isClosed_Icc
  exact ⟨ψ, hsmooth, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport,
    htsupport, hderiv⟩

theorem IsSmoothTestOn.exists_primitive {l r : ℝ} {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn (Ioo l r) φ) (hz : (∫ x, φ x) = 0) :
    ∃ ψ : ℝ → ℝ, IsSmoothTestOn (Ioo l r) ψ ∧ _root_.deriv ψ = φ := by
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨a, ha, hmin⟩ := hφ.2.1.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨b, hb, hmax⟩ := hφ.2.1.exists_isMaxOn hne continuous_id.continuousOn
    have hab : a ≤ b := hmin hb
    have hs : tsupport φ ⊆ Icc a b := fun x hx => ⟨hmin hx, hmax hx⟩
    obtain ⟨ψ, hdiff, hcompact, hsupp, hderiv⟩ :=
      smooth_primitive_with_compact_support φ a b hab hφ.1 hs hz
    refine ⟨ψ, ⟨hdiff, hcompact, hsupp.trans ?_⟩, hderiv⟩
    have ha' := hφ.2.2 ha
    have hb' := hφ.2.2 hb
    intro x hx
    exact ⟨ha'.1.trans_le hx.1, hx.2.trans_lt hb'.2⟩
  · have hzero : φ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hne ⟨x, hx⟩)
    subst φ
    exact ⟨0, ⟨contDiff_const, HasCompactSupport.zero, by simp⟩, by simp⟩

theorem HasWeakDerivOn.integral_smul_eq_zero_of_integral_eq_zero
    {l r : ℝ} {f : ℝ → ℂ} (hf : HasWeakDerivOn (Ioo l r) f 0)
    {φ : ℝ → ℝ} (hφ : IsSmoothTestOn (Ioo l r) φ) (hz : (∫ x, φ x) = 0) :
    (∫ x in Ioo l r, φ x • f x) = 0 := by
  obtain ⟨ψ, hψ, hderiv⟩ := hφ.exists_primitive hz
  have h := hf.2.2 ψ hψ
  simpa only [hderiv, Pi.zero_apply, smul_zero, integral_zero, neg_zero] using h

end Involution
