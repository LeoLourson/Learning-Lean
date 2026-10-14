module

public import Involution.Model.CoefficientInverse
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-! Слабые производные квадратного корня положительного коэффициента. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Involution

def coefficientRealPartMap : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

def coefficientRealPart (a : IntervalLInfinity) : IntervalLInfinity :=
  coefficientRealPartMap.compLp a

theorem coefficientRealPart_ae (a : IntervalLInfinity) :
    coefficientRealPart a =ᵐ[intervalMeasure] fun x => ((a x).re : ℂ) :=
  coefficientRealPartMap.coeFn_compLp' a

theorem HasACMultiplierDerivative.coeff_realPart {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') :
    HasACMultiplierDerivative (coefficientRealPart a) (coefficientRealPart a') := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  refine ⟨fun x => coefficientRealPartMap (A x),
    coefficientRealPartMap.lipschitzWith.comp_absolutelyContinuousOnInterval hAac, ?_, ?_⟩
  · filter_upwards [hA, coefficientRealPart_ae a] with x ha hc
    rw [ha, hc]
    rfl
  · filter_upwards [hdA, interval_ae_closed (coefficientRealPart_ae a')] with x ha hc hx
    rw [hc hx]
    exact coefficientRealPartMap.hasFDerivAt.comp_hasDerivAt x (ha hx)

theorem HasACMultiplierDerivative.coeff_smul {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (c : ℂ) :
    HasACMultiplierDerivative (c • a) (c • a') := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  refine ⟨fun x => c • A x, hAac.const_smul c, ?_, ?_⟩
  · filter_upwards [hA, Lp.coeFn_smul c a] with x ha hc
    rw [ha, hc]
    rfl
  · filter_upwards [hdA, interval_ae_closed (Lp.coeFn_smul c a')] with x ha hc hx
    rw [hc hx]
    exact (ha hx).const_smul c

theorem continuous_real_representative_lower {P p : ℝ → ℝ}
    (hPc : ContinuousOn P (Icc (-1 : ℝ) 1)) (hP : P =ᵐ[intervalMeasure] p)
    (m : ℝ) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    ∀ x ∈ Icc (-1 : ℝ) 1, m ≤ P x := by
  have heq : (fun x => max m (P x)) =ᵐ[intervalMeasure] P := by
    filter_upwards [hP, hlower] with x hp hx
    exact max_eq_right (by rwa [hp])
  have hmax : ContinuousOn (fun x => max m (P x)) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.sup hPc
  have hi := Measure.eqOn_Ioo_of_ae_eq volume heq
    (hmax.mono Ioo_subset_Icc_self) (hPc.mono Ioo_subset_Icc_self)
  have hc := hi.of_subset_closure hmax hPc Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  intro x hx
  exact (le_max_left m (P x)).trans_eq (hc hx)

theorem sqrt_lipschitzOn_positive (m : ℝ) (hm : 0 < m) :
    LipschitzOnWith ⟨(2 * Real.sqrt m)⁻¹, by positivity⟩ Real.sqrt (Ici m) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact (Real.hasDerivAt_sqrt (ne_of_gt (lt_of_lt_of_le hm hx))).differentiableAt
  · intro x hx
    apply NNReal.coe_le_coe.mpr
    change ‖deriv Real.sqrt x‖ ≤ (2 * Real.sqrt m)⁻¹
    rw [(Real.hasDerivAt_sqrt (ne_of_gt (lt_of_lt_of_le hm hx))).deriv,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div]
    gcongr
    exact hx
  · exact convex_Ici m

def sqrtCoefficientDeriv (a' w : IntervalLInfinity) : IntervalLInfinity :=
  (1 / 2 : ℂ) • coefficientProduct (coefficientRealPart a') w

theorem sqrtCoefficientDeriv_ae (a' w : IntervalLInfinity) :
    sqrtCoefficientDeriv a' w =ᵐ[intervalMeasure] fun x =>
      (1 / 2 : ℂ) * ((a' x).re : ℂ) * w x := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (coefficientProduct (coefficientRealPart a') w),
    coefficientProduct_ae (coefficientRealPart a') w, coefficientRealPart_ae a']
    with x hc hp hr
  change ((1 / 2 : ℂ) • coefficientProduct (coefficientRealPart a') w) x = _
  rw [hc]
  change (1 / 2 : ℂ) * coefficientProduct (coefficientRealPart a') w x = _
  rw [hp, hr]
  ring

theorem sqrtWeight_hasACDerivative (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M) (a' : IntervalLInfinity)
    (ha : HasACMultiplierDerivative (realIntervalCoefficient p hp) a') :
    HasACMultiplierDerivative (sqrtWeight p hp M hupper)
      (sqrtCoefficientDeriv a' (inverseSqrtWeight p hp m hm hlower)) := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  let P : ℝ → ℝ := fun x => (A x).re
  have hPac : AbsolutelyContinuousOnInterval P (-1) 1 :=
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hAac
  have hPc : ContinuousOn P (Icc (-1 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hPac.continuousOn
  have hP : P =ᵐ[intervalMeasure] p := by
    filter_upwards [hA, realIntervalCoefficient_ae p hp] with x ha hp
    change (A x).re = p x
    rw [ha, hp]
    rfl
  have hPlower := continuous_real_representative_lower hPc hP m hlower
  have hPzero : ∀ x ∈ Icc (-1 : ℝ) 1, P x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le hm (hPlower x hx))
  have hmaps : MapsTo P (uIcc (-1 : ℝ) 1) (Ici m) := by
    intro x hx
    exact hPlower x (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)
  have hSac : AbsolutelyContinuousOnInterval (fun x => Real.sqrt (P x)) (-1) 1 :=
    (sqrt_lipschitzOn_positive m hm).comp_absolutelyContinuousOnInterval hmaps hPac
  refine ⟨fun x => (Real.sqrt (P x) : ℂ),
    Complex.ofRealLI.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hSac, ?_, ?_⟩
  · filter_upwards [hP, sqrtWeight_ae p hp M hupper] with x hp hs
    rw [hp, hs]
  · have heq : sqrtCoefficientDeriv a' (inverseSqrtWeight p hp m hm hlower)
        =ᵐ[intervalMeasure] fun x => (((a' x).re / (2 * Real.sqrt (P x)) : ℝ) : ℂ) := by
      filter_upwards [sqrtCoefficientDeriv_ae a' (inverseSqrtWeight p hp m hm hlower),
        inverseSqrtWeight_ae p hp m hm hlower, hP] with x hd hw hp
      rw [hd, hw, hp]
      push_cast
      ring
    filter_upwards [hdA, interval_ae_closed heq] with x ha he hx
    rw [he hx]
    have hdP := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (ha hx)
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hdP.sqrt (hPzero x hx))

theorem sqrtWeight_norm_lower (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M) :
    ∀ᵐ x ∂intervalMeasure, Real.sqrt m ≤ ‖sqrtWeight p hp M hupper x‖ := by
  filter_upwards [sqrtWeight_ae p hp M hupper, hlower] with x hs hx
  rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hx

theorem sqrtWeight_memW2Infinity (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) :
    MemIntervalW2Infinity (sqrtWeight p hp M hupper) := by
  obtain ⟨a', a'', h0, h1⟩ := ha
  let S := sqrtWeight p hp M hupper
  let W := inverseSqrtWeight p hp m hm hlower
  have hS := sqrtWeight_hasACDerivative p hp m M hm hlower hupper a'
    (HasACMultiplierDerivative.of_weak h0)
  have hslow : ∀ᵐ x ∂intervalMeasure, Real.sqrt m ≤ ‖S x‖ :=
    sqrtWeight_norm_lower p hp m M hlower hupper
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hW := hS.coeff_inv (Real.sqrt m) hsm hslow
  have heq : inverseCoefficient S (Real.sqrt m) hsm hslow = W := by
    apply Lp.ext
    filter_upwards [inverseCoefficient_reciprocal S (Real.sqrt m) hsm hslow,
      sqrtWeight_inverseSqrtWeight p hp m M hm hlower hupper, hslow] with x hi hw hl
    exact mul_left_cancel₀ (norm_pos_iff.mp (lt_of_lt_of_le hsm hl)) (hi.trans hw.symm)
  change HasACMultiplierDerivative (inverseCoefficient S (Real.sqrt m) hsm hslow)
    (inverseCoefficientDeriv (sqrtCoefficientDeriv a' W)
      (inverseCoefficient S (Real.sqrt m) hsm hslow)) at hW
  rw [heq] at hW
  have hC := ((HasACMultiplierDerivative.of_weak h1).coeff_realPart.coeff_mul hW).coeff_smul
    (1 / 2 : ℂ)
  exact ⟨sqrtCoefficientDeriv a' W, _, hS.to_weak, hC.to_weak⟩

theorem inverseSqrtWeight_memW2Infinity (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) :
    MemIntervalW2Infinity (inverseSqrtWeight p hp m hm hlower) :=
  MemIntervalW2Infinity.reciprocal (sqrtWeight p hp M hupper)
    (inverseSqrtWeight p hp m hm hlower) (sqrtWeight_memW2Infinity p hp m M hm hlower hupper ha)
    (Real.sqrt m) (Real.sqrt_pos.mpr hm) (sqrtWeight_norm_lower p hp m M hlower hupper)
    (sqrtWeight_inverseSqrtWeight p hp m M hm hlower hupper)

theorem sqrtWeight_dirichlet_iff (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) (f : IntervalL2) :
    MemDirichletH2 (boundedMultiplier (sqrtWeight p hp M hupper) f) ↔ MemDirichletH2 f :=
  memDirichletH2_mul_iff (sqrtWeight p hp M hupper) (inverseSqrtWeight p hp m hm hlower)
    (sqrtWeight_memW2Infinity p hp m M hm hlower hupper ha)
    (inverseSqrtWeight_memW2Infinity p hp m M hm hlower hupper ha)
    (sqrtWeight_inverseSqrtWeight p hp m M hm hlower hupper) f

theorem continuous_nonzero_constant_sign (P : ℝ → ℝ)
    (hP : ContinuousOn P (Icc (-1 : ℝ) 1))
    (hnz : ∀ x ∈ Icc (-1 : ℝ) 1, P x ≠ 0) :
    (∀ x ∈ Icc (-1 : ℝ) 1, 0 < P x) ∨ (∀ x ∈ Icc (-1 : ℝ) 1, P x < 0) := by
  rcases lt_or_gt_of_ne (hnz (-1) (by norm_num)) with hn | hp
  · right
    intro x hx
    by_contra hnot
    have hcont : ContinuousOn P (Icc (-1 : ℝ) x) :=
      hP.mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)
    obtain ⟨y, hy, hz⟩ := intermediate_value_Icc hx.1 hcont ⟨hn.le, le_of_not_gt hnot⟩
    exact hnz y ⟨hy.1, hy.2.trans hx.2⟩ hz
  · left
    intro x hx
    by_contra hnot
    have hcont : ContinuousOn P (Icc (-1 : ℝ) x) :=
      hP.mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)
    obtain ⟨y, hy, hz⟩ := intermediate_value_Icc' hx.1 hcont ⟨le_of_not_gt hnot, hp.le⟩
    exact hnz y ⟨hy.1, hy.2.trans hx.2⟩ hz

theorem MemIntervalW2Infinity.coeff_smul {a : IntervalLInfinity}
    (ha : MemIntervalW2Infinity a) (c : ℂ) : MemIntervalW2Infinity (c • a) := by
  obtain ⟨a', a'', h0, h1⟩ := ha
  exact ⟨c • a', c • a'',
    ((HasACMultiplierDerivative.of_weak h0).coeff_smul c).to_weak,
    ((HasACMultiplierDerivative.of_weak h1).coeff_smul c).to_weak⟩

theorem real_abs_memLp (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure) :
    MemLp (fun x => |p x|) ∞ intervalMeasure := by
  simpa only [Real.norm_eq_abs] using hp.norm

theorem real_abs_memW2Infinity (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (ε : ℝ) (hε : 0 < ε) (hlower : ∀ᵐ x ∂intervalMeasure, ε ≤ |p x|)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) :
    MemIntervalW2Infinity (realIntervalCoefficient (fun x => |p x|) (real_abs_memLp p hp)) := by
  obtain ⟨a', a'', h0, h1⟩ := ha
  obtain ⟨A, hAac, hA, _⟩ := HasACMultiplierDerivative.of_weak h0
  let P : ℝ → ℝ := fun x => (A x).re
  have hPc : ContinuousOn P (Icc (-1 : ℝ) 1) := by
    have hc := hAac.continuousOn
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hc
    exact Complex.reCLM.continuous.comp_continuousOn hc
  have hP : P =ᵐ[intervalMeasure] p := by
    filter_upwards [hA, realIntervalCoefficient_ae p hp] with x ha hp
    change (A x).re = p x
    rw [ha, hp]
    rfl
  have hcastP : (fun x => (P x : ℂ)) =ᵐ[intervalMeasure] realIntervalCoefficient p hp := by
    filter_upwards [hP, realIntervalCoefficient_ae p hp] with x hp ha
    rw [hp, ha]
  have hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖realIntervalCoefficient p hp x‖ := by
    filter_upwards [hlower, realIntervalCoefficient_ae p hp] with x hx ha
    simpa only [ha, Complex.norm_real, Real.norm_eq_abs] using hx
  have hPlower := continuous_representative_norm_lower
    (Complex.continuous_ofReal.comp_continuousOn hPc) hcastP ε hbound
  have hPnz : ∀ x ∈ Icc (-1 : ℝ) 1, P x ≠ 0 := by
    intro x hx hz
    have h := hPlower x hx
    change ε ≤ ‖(P x : ℂ)‖ at h
    simp only [hz, Complex.ofReal_zero, norm_zero] at h
    linarith
  have hweak : MemIntervalW2Infinity (realIntervalCoefficient p hp) := ⟨a', a'', h0, h1⟩
  rcases continuous_nonzero_constant_sign P hPc hPnz with hpos | hneg
  · have heq : realIntervalCoefficient (fun x => |p x|) (real_abs_memLp p hp) =
        realIntervalCoefficient p hp := by
      apply Lp.ext
      filter_upwards [realIntervalCoefficient_ae (fun x => |p x|) (real_abs_memLp p hp),
        realIntervalCoefficient_ae p hp, hP, ae_restrict_mem measurableSet_Ioo]
        with x hab ha hp hx
      have hxpos := hpos x (Ioo_subset_Icc_self hx)
      rw [hp] at hxpos
      rw [hab, ha, abs_of_pos hxpos]
    rwa [heq]
  · have heq : realIntervalCoefficient (fun x => |p x|) (real_abs_memLp p hp) =
        (-1 : ℂ) • realIntervalCoefficient p hp := by
      apply Lp.ext
      filter_upwards [realIntervalCoefficient_ae (fun x => |p x|) (real_abs_memLp p hp),
        realIntervalCoefficient_ae p hp, hP, ae_restrict_mem measurableSet_Ioo,
        Lp.coeFn_smul (-1 : ℂ) (realIntervalCoefficient p hp)] with x hab ha hpx hx hc
      have hxneg := hneg x (Ioo_subset_Icc_self hx)
      rw [hpx] at hxneg
      rw [hab, hc]
      change ((|p x| : ℝ) : ℂ) = (-1 : ℂ) * realIntervalCoefficient p hp x
      rw [ha, abs_of_neg hxneg, Complex.ofReal_neg]
      ring
    rw [heq]
    exact hweak.coeff_smul (-1)

theorem sqrt_abs_weights_memW2Infinity (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |p x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |p x| ≤ M)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) :
    MemIntervalW2Infinity (sqrtWeight (fun x => |p x|) (real_abs_memLp p hp) M hupper) ∧
      MemIntervalW2Infinity
        (inverseSqrtWeight (fun x => |p x|) (real_abs_memLp p hp) m hm hlower) := by
  have hab := real_abs_memW2Infinity p hp m hm hlower ha
  exact ⟨sqrtWeight_memW2Infinity _ _ m M hm hlower hupper hab,
    inverseSqrtWeight_memW2Infinity _ _ m M hm hlower hupper hab⟩

theorem sqrt_abs_dirichlet_iff (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |p x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |p x| ≤ M)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) (f : IntervalL2) :
    MemDirichletH2
      (boundedMultiplier (sqrtWeight (fun x => |p x|) (real_abs_memLp p hp) M hupper) f) ↔
        MemDirichletH2 f := by
  have hw := sqrt_abs_weights_memW2Infinity p hp m M hm hlower hupper ha
  exact memDirichletH2_mul_iff _ _ hw.1 hw.2
    (sqrtWeight_inverseSqrtWeight (fun x => |p x|) (real_abs_memLp p hp) m M hm hlower hupper) f

end Involution
