module

public import Involution.Model.SobolevMultiplier
public import Mathlib.Topology.Order.Lattice

/-! Обратный коэффициент, отделённый от нуля: представители и слабые производные. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Involution

theorem continuous_representative_norm_lower {A : ℝ → ℂ} {a : IntervalLInfinity}
    (hAc : ContinuousOn A (Icc (-1 : ℝ) 1)) (hA : A =ᵐ[intervalMeasure] a)
    (ε : ℝ) (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) :
    ∀ x ∈ Icc (-1 : ℝ) 1, ε ≤ ‖A x‖ := by
  have heq : (fun x => max ε ‖A x‖) =ᵐ[intervalMeasure] fun x => ‖A x‖ := by
    filter_upwards [hA, hbound] with x ha hx
    exact max_eq_right (by rwa [ha])
  have hmax : ContinuousOn (fun x => max ε ‖A x‖) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.sup hAc.norm
  have hi := Measure.eqOn_Ioo_of_ae_eq volume heq
    (hmax.mono Ioo_subset_Icc_self) (hAc.norm.mono Ioo_subset_Icc_self)
  have hc := hi.of_subset_closure hmax hAc.norm Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  intro x hx
  exact (le_max_left ε ‖A x‖).trans_eq (hc hx)

theorem inverse_coefficient_memLp (a : IntervalLInfinity) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) :
    MemLp (fun x => (a x)⁻¹) ∞ intervalMeasure := by
  apply memLp_top_of_bound (Lp.aestronglyMeasurable a).aemeasurable.inv.aestronglyMeasurable ε⁻¹
  filter_upwards [hbound] with x hx
  change ‖(a x)⁻¹‖ ≤ ε⁻¹
  rw [norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le hε hx) hε).mpr hx

def inverseCoefficient (a : IntervalLInfinity) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) : IntervalLInfinity :=
  (inverse_coefficient_memLp a ε hε hbound).toLp (fun x => (a x)⁻¹)

theorem inverseCoefficient_ae (a : IntervalLInfinity) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) :
    inverseCoefficient a ε hε hbound =ᵐ[intervalMeasure] fun x => (a x)⁻¹ :=
  MemLp.coeFn_toLp _

theorem inverseCoefficient_reciprocal (a : IntervalLInfinity) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) :
    ∀ᵐ x ∂intervalMeasure, a x * inverseCoefficient a ε hε hbound x = 1 := by
  filter_upwards [inverseCoefficient_ae a ε hε hbound, hbound] with x hx hb
  rw [hx, mul_inv_cancel₀ (norm_pos_iff.mp (lt_of_lt_of_le hε hb))]

theorem inverse_lipschitzOn_norm_lower (ε : ℝ) (hε : 0 < ε) :
    LipschitzOnWith ⟨ε⁻¹ * ε⁻¹, by positivity⟩ (fun z : ℂ => z⁻¹) {z | ε ≤ ‖z‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hz0 := norm_pos_iff.mp (lt_of_lt_of_le hε hz)
  have hw0 := norm_pos_iff.mp (lt_of_lt_of_le hε hw)
  rw [dist_inv_inv₀ hz0 hw0, div_eq_mul_inv, mul_inv]
  change dist z w * (‖z‖⁻¹ * ‖w‖⁻¹) ≤ (ε⁻¹ * ε⁻¹) * dist z w
  rw [mul_comm (ε⁻¹ * ε⁻¹)]
  gcongr <;> assumption

def coefficientProduct (a b : IntervalLInfinity) : IntervalLInfinity := a • b

theorem coefficientProduct_ae (a b : IntervalLInfinity) :
    coefficientProduct a b =ᵐ[intervalMeasure] fun x => a x * b x := by
  filter_upwards [Lp.coeFn_lpSMul (r := (∞ : ENNReal)) a b] with x hx
  exact hx

theorem infinity_coefficient_integrable (a : IntervalLInfinity) : Integrable a intervalMeasure := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1))
    infer_instance
  exact (Lp.memLp a).integrable (by simp : (1 : ENNReal) ≤ ∞)

theorem HasACMultiplierDerivative.to_weak {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') : HasIntervalWeakDeriv a a' := by
  obtain ⟨A, hAac, hA, hd⟩ := ha
  exact (hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hAac
    (infinity_coefficient_integrable a')
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hd)).congr
      hA Filter.EventuallyEq.rfl

theorem HasACMultiplierDerivative.coeff_mul {a a' b b' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (hb : HasACMultiplierDerivative b b') :
    HasACMultiplierDerivative (coefficientProduct a b)
      (coefficientProduct a' b + coefficientProduct a b') := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  obtain ⟨B, hBac, hB, hdB⟩ := hb
  let C := coefficientProduct a' b + coefficientProduct a b'
  have hC : C =ᵐ[intervalMeasure] fun x => a' x * B x + A x * b' x := by
    filter_upwards [Lp.coeFn_add (coefficientProduct a' b) (coefficientProduct a b'),
      coefficientProduct_ae a' b, coefficientProduct_ae a b', hA, hB] with x hc h1 h0 ha hb
    change C x = coefficientProduct a' b x + coefficientProduct a b' x at hc
    rw [hc, h1, h0, ha, hb]
  refine ⟨fun x => A x * B x, ?_, ?_, ?_⟩
  · convert hAac.smul hBac using 1
  · filter_upwards [hA, hB, coefficientProduct_ae a b] with x ha hb hc
    rw [ha, hb, hc]
  · filter_upwards [hdA, hdB, interval_ae_closed hC] with x ha hb hc hx
    rw [hc hx]
    exact (ha hx).mul (hb hx)

theorem HasACMultiplierDerivative.coeff_neg {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') : HasACMultiplierDerivative (-a) (-a') := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  refine ⟨fun x => -A x, ?_, ?_, ?_⟩
  · simpa only [neg_one_smul] using hAac.const_smul (-1 : ℂ)
  · filter_upwards [hA, Lp.coeFn_neg a] with x ha hn
    rw [ha, hn]
    rfl
  · filter_upwards [hdA, interval_ae_closed (Lp.coeFn_neg a')] with x ha hn hx
    rw [hn hx]
    exact (ha hx).neg

def inverseCoefficientDeriv (a' b : IntervalLInfinity) : IntervalLInfinity :=
  -coefficientProduct (coefficientProduct a' b) b

theorem inverseCoefficientDeriv_ae (a' b : IntervalLInfinity) :
    inverseCoefficientDeriv a' b =ᵐ[intervalMeasure] fun x => -(a' x * b x * b x) := by
  filter_upwards [Lp.coeFn_neg (coefficientProduct (coefficientProduct a' b) b),
    coefficientProduct_ae (coefficientProduct a' b) b, coefficientProduct_ae a' b]
    with x hn h0 h1
  change (-coefficientProduct (coefficientProduct a' b) b) x = _
  rw [hn]
  change -(coefficientProduct (coefficientProduct a' b) b x) = _
  rw [h0, h1]

theorem HasACMultiplierDerivative.coeff_inv {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) :
    HasACMultiplierDerivative (inverseCoefficient a ε hε hbound)
      (inverseCoefficientDeriv a' (inverseCoefficient a ε hε hbound)) := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  have hAc : ContinuousOn A (Icc (-1 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hAac.continuousOn
  have hAlower := continuous_representative_norm_lower hAc hA ε hbound
  have hAzero : ∀ x ∈ Icc (-1 : ℝ) 1, A x ≠ 0 := fun x hx =>
    norm_pos_iff.mp (lt_of_lt_of_le hε (hAlower x hx))
  have hmaps : MapsTo A (uIcc (-1 : ℝ) 1) {z : ℂ | ε ≤ ‖z‖} := by
    intro x hx
    exact hAlower x (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)
  refine ⟨fun x => (A x)⁻¹,
    (inverse_lipschitzOn_norm_lower ε hε).comp_absolutelyContinuousOnInterval hmaps hAac,
    ?_, ?_⟩
  · filter_upwards [hA, inverseCoefficient_ae a ε hε hbound] with x ha hb
    rw [ha, hb]
  · have heq : inverseCoefficientDeriv a' (inverseCoefficient a ε hε hbound)
        =ᵐ[intervalMeasure] fun x => -(a' x) / (A x)^2 := by
      filter_upwards [inverseCoefficientDeriv_ae a' (inverseCoefficient a ε hε hbound),
        inverseCoefficient_ae a ε hε hbound, hA] with x hd hb ha
      rw [hd, hb, ha]
      simp only [div_eq_mul_inv, pow_two]
      ring
    filter_upwards [hdA, interval_ae_closed heq] with x ha he hx
    rw [he hx]
    exact (ha hx).inv (hAzero x hx)

theorem MemIntervalW2Infinity.coeff_inv {a : IntervalLInfinity}
    (ha : MemIntervalW2Infinity a) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) :
    MemIntervalW2Infinity (inverseCoefficient a ε hε hbound) := by
  obtain ⟨a', a'', h0, h1⟩ := ha
  have hA := HasACMultiplierDerivative.of_weak h0
  have hA' := HasACMultiplierDerivative.of_weak h1
  have hB := hA.coeff_inv ε hε hbound
  have hB' := ((hA'.coeff_mul hB).coeff_mul hB).coeff_neg
  exact ⟨inverseCoefficientDeriv a' (inverseCoefficient a ε hε hbound), _,
    hB.to_weak, hB'.to_weak⟩

theorem inverseCoefficient_dirichlet_iff (a : IntervalLInfinity)
    (ha : MemIntervalW2Infinity a) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖) (f : IntervalL2) :
    MemDirichletH2 (boundedMultiplier (inverseCoefficient a ε hε hbound) f) ↔
      MemDirichletH2 f :=
  memDirichletH2_mul_iff _ a (ha.coeff_inv ε hε hbound) ha
    ((inverseCoefficient_reciprocal a ε hε hbound).mono fun x hx => by rwa [mul_comm]) f

theorem MemIntervalW2Infinity.reciprocal (a b : IntervalLInfinity)
    (ha : MemIntervalW2Infinity a) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖)
    (hab : ∀ᵐ x ∂intervalMeasure, a x * b x = 1) : MemIntervalW2Infinity b := by
  have heq : b = inverseCoefficient a ε hε hbound := by
    apply Lp.ext
    filter_upwards [hab, inverseCoefficient_reciprocal a ε hε hbound, hbound]
      with x hx hi hb
    exact mul_left_cancel₀ (norm_pos_iff.mp (lt_of_lt_of_le hε hb)) (hx.trans hi.symm)
  rw [heq]
  exact ha.coeff_inv ε hε hbound

theorem memDirichletH2_mul_iff_of_lower (a b : IntervalLInfinity)
    (ha : MemIntervalW2Infinity a) (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖a x‖)
    (hab : ∀ᵐ x ∂intervalMeasure, a x * b x = 1) (f : IntervalL2) :
    MemDirichletH2 (boundedMultiplier a f) ↔ MemDirichletH2 f :=
  memDirichletH2_mul_iff a b ha (ha.reciprocal a b ε hε hbound hab) hab f

end Involution
