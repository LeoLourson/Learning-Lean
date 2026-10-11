module

public import Involution.WeightedGreen
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Обратный квадратный корень равномерно положительного измеримого веса.
Все условия на представители и тождества коэффициентов понимаются почти всюду. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem inverseSqrt_memLp (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    MemLp (fun x => (Real.sqrt (p x))⁻¹) ∞ intervalMeasure := by
  apply memLp_top_of_bound
    (hp.aestronglyMeasurable.aemeasurable.sqrt.inv.aestronglyMeasurable) (Real.sqrt m)⁻¹
  filter_upwards [hbound] with x hx
  have hpos : 0 < p x := lt_of_lt_of_le hm hx
  change ‖(Real.sqrt (p x))⁻¹‖ ≤ (Real.sqrt m)⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hpos))]
  exact (inv_le_inv₀ (Real.sqrt_pos.mpr hpos) (Real.sqrt_pos.mpr hm)).mpr
    (Real.sqrt_le_sqrt hx)

def inverseSqrtWeight (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    IntervalLInfinity :=
  realIntervalCoefficient (fun x => (Real.sqrt (p x))⁻¹) (inverseSqrt_memLp p hp m hm hbound)

theorem inverseSqrtWeight_ae (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    inverseSqrtWeight p hp m hm hbound =ᵐ[intervalMeasure]
      fun x => (((Real.sqrt (p x))⁻¹ : ℝ) : ℂ) := realIntervalCoefficient_ae _ _

theorem inverseSqrtWeight_real (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    ∀ᵐ x ∂intervalMeasure, star (inverseSqrtWeight p hp m hm hbound x) =
      inverseSqrtWeight p hp m hm hbound x := by
  filter_upwards [inverseSqrtWeight_ae p hp m hm hbound] with x hx
  rw [hx]
  simp

theorem inverseSqrtWeight_nonzero (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    ∀ᵐ x ∂intervalMeasure, inverseSqrtWeight p hp m hm hbound x ≠ 0 := by
  filter_upwards [inverseSqrtWeight_ae p hp m hm hbound, hbound] with x hx hpx
  rw [hx]
  exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le hm hpx)))

theorem inverseSqrtWeight_even (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (heven : ∀ᵐ x ∂intervalMeasure, p (-x) = p x) :
    ∀ᵐ x ∂intervalMeasure, inverseSqrtWeight p hp m hm hbound (-x) =
      inverseSqrtWeight p hp m hm hbound x := by
  have href := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (inverseSqrtWeight_ae p hp m hm hbound)
  filter_upwards [inverseSqrtWeight_ae p hp m hm hbound, href, heven] with x hx hr he
  change inverseSqrtWeight p hp m hm hbound (-x) = ((Real.sqrt (p (-x)))⁻¹ : ℝ) at hr
  rw [hr, hx, he]

theorem inverseSqrtWeight_identity (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x) :
    ∀ᵐ x ∂intervalMeasure, (p x : ℂ) *
      (inverseSqrtWeight p hp m hm hbound x * inverseSqrtWeight p hp m hm hbound x) = 1 := by
  filter_upwards [inverseSqrtWeight_ae p hp m hm hbound, hbound] with x hx hpx
  rw [hx]
  have hpos : 0 < p x := lt_of_lt_of_le hm hpx
  have hs : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt hpos.le
  have he : p x * ((Real.sqrt (p x))⁻¹ * (Real.sqrt (p x))⁻¹) = 1 := by
    calc
      _ = p x * (Real.sqrt (p x) * Real.sqrt (p x))⁻¹ := by rw [mul_inv_rev]
      _ = 1 := by rw [hs, mul_inv_cancel₀ (ne_of_gt hpos)]
  exact_mod_cast he

theorem inverseSqrtWeight_channel_identity (a : IntervalLInfinity) (s : ℂ)
    (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure) (m : ℝ) (hm : 0 < m)
    (hbound : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hpchannel : ∀ᵐ x ∂intervalMeasure, (p x : ℂ) = 1 + s * a x) :
    ∀ᵐ x ∂intervalMeasure, (1 + s * a x) *
      (inverseSqrtWeight p hp m hm hbound x * inverseSqrtWeight p hp m hm hbound x) = 1 := by
  filter_upwards [inverseSqrtWeight_identity p hp m hm hbound, hpchannel] with x hi hx
  rw [← hx]
  exact hi

theorem sqrt_memLp_of_upper_bound (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (M : ℝ) (hbound : ∀ᵐ x ∂intervalMeasure, p x ≤ M) :
    MemLp (fun x => Real.sqrt (p x)) ∞ intervalMeasure := by
  apply memLp_top_of_bound hp.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    (Real.sqrt M)
  filter_upwards [hbound] with x hx
  change ‖Real.sqrt (p x)‖ ≤ Real.sqrt M
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hx

def sqrtWeight (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (M : ℝ) (hbound : ∀ᵐ x ∂intervalMeasure, p x ≤ M) : IntervalLInfinity :=
  realIntervalCoefficient (fun x => Real.sqrt (p x)) (sqrt_memLp_of_upper_bound p hp M hbound)

theorem sqrtWeight_ae (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (M : ℝ) (hbound : ∀ᵐ x ∂intervalMeasure, p x ≤ M) :
    sqrtWeight p hp M hbound =ᵐ[intervalMeasure] fun x => ((Real.sqrt (p x) : ℝ) : ℂ) :=
  realIntervalCoefficient_ae _ _

theorem sqrtWeight_even (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (M : ℝ) (hbound : ∀ᵐ x ∂intervalMeasure, p x ≤ M)
    (heven : ∀ᵐ x ∂intervalMeasure, p (-x) = p x) :
    ∀ᵐ x ∂intervalMeasure, sqrtWeight p hp M hbound (-x) = sqrtWeight p hp M hbound x := by
  have href := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (sqrtWeight_ae p hp M hbound)
  filter_upwards [sqrtWeight_ae p hp M hbound, href, heven] with x hx hr he
  change sqrtWeight p hp M hbound (-x) = (Real.sqrt (p (-x)) : ℂ) at hr
  rw [hr, hx, he]

theorem sqrtWeight_inverseSqrtWeight (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M) :
    ∀ᵐ x ∂intervalMeasure, sqrtWeight p hp M hupper x *
      inverseSqrtWeight p hp m hm hlower x = 1 := by
  filter_upwards [sqrtWeight_ae p hp M hupper,
    inverseSqrtWeight_ae p hp m hm hlower, hlower] with x hv hw hx
  rw [hv, hw]
  have hn : Real.sqrt (p x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le hm hx))
  exact_mod_cast mul_inv_cancel₀ hn

end Involution
