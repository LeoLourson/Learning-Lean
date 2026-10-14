module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Basic
public import Involution.Setup.L2Reflection
public import Mathlib.MeasureTheory.Function.L2Space

/-! Равенство интегралов при складывании интервала.
Обратимость склеивания на соболевской области — в `Involution.Folding.FoldedSobolev`. -/

public section

open MeasureTheory

namespace Involution

theorem folding_integral (g : ℝ → ℝ)
    (hleft : IntervalIntegrable g volume (-1) 0)
    (hright : IntervalIntegrable g volume 0 1) :
    (∫ x in (-1 : ℝ)..1, g x) = ∫ x in (0 : ℝ)..1, (g x + g (-x)) := by
  have hneg : IntervalIntegrable (fun x => g (-x)) volume 0 1 := by
    simpa only [neg_neg, neg_zero] using
      (IntervalIntegrable.iff_comp_neg (f := g) (a := (0 : ℝ)) (b := -1)).mp hleft.symm
  rw [intervalIntegral.integral_add hright hneg, intervalIntegral.integral_comp_neg]
  simpa only [neg_zero, neg_neg, add_comm] using
    (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

theorem folding_sq_norm (f : ℝ → ℂ)
    (hleft : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume (-1) 0)
    (hright : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume 0 1) :
    (∫ x in (-1 : ℝ)..1, ‖f x‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, (‖f x‖ ^ 2 + ‖f (-x)‖ ^ 2) :=
  folding_integral (fun x => ‖f x‖ ^ 2) hleft hright

theorem l2_folding_sq_norm (f : IntervalL2) :
    (∫ x in (-1 : ℝ)..1, ‖f x‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, (‖f x‖ ^ 2 + ‖f (-x)‖ ^ 2) := by
  have hi : IntegrableOn (fun x => ‖f x‖ ^ 2) (Set.Ioo (-1) 1) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hwhole : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr hi
  exact folding_sq_norm f
    (hwhole.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Set.Icc_subset_Icc le_rfl (by norm_num)))
    (hwhole.mono_set (by simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Set.Icc_subset_Icc (by norm_num) le_rfl))

end Involution
