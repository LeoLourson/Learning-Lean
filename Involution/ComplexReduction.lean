module

public import Involution.Reduction
public import Mathlib.Analysis.Complex.Basic

/-! Комплексная редукция при вещественном ограничении произведения коэффициентов. -/

public section

namespace Involution

theorem complex_determinant_ne_zero (a b κ : ℝ) (hκ : κ < 1) (hab : |a * b| ≤ κ) :
    (1 : ℂ) - (a : ℂ) * (b : ℂ) ≠ 0 := by
  have hreal : 1 - a * b ≠ 0 := (determinant_pos a b κ hκ hab).ne'
  have hc : ((1 - a * b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hreal
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul] using hc

theorem complex_reduction_under_product_bound (a b κ : ℝ) (u v f g : ℂ)
    (hκ : κ < 1) (hab : |a * b| ≤ κ) :
    (u + (a : ℂ) * v = f ∧ (b : ℂ) * u + v = g) ↔
      (u = (f - (a : ℂ) * g) / (1 - (a : ℂ) * (b : ℂ)) ∧
       v = (g - (b : ℂ) * f) / (1 - (a : ℂ) * (b : ℂ))) :=
  solve_system (a : ℂ) (b : ℂ) u v f g (complex_determinant_ne_zero a b κ hκ hab)

end Involution
