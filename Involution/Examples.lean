import Involution.Reduction

/-! # Algebraic checks for the three model cases -/

namespace Involution

/-- A coefficient allowed by this project but excluded by positive-product assumptions. -/
theorem odd_coefficient_product (x : ℝ) : (x / 2) * ((-x) / 2) = -(x ^ 2) / 4 := by
  ring

theorem odd_coefficient_determinant (x : ℝ) :
    0 < 1 - (x / 2) * ((-x) / 2) := by
  nlinarith [sq_nonneg x]

/-- Равномерная оценка произведения на замкнутом интервале. -/
theorem odd_coefficient_product_bound (x : ℝ) (hx : |x| ≤ 1) :
    |(x / 2) * ((-x) / 2)| ≤ 1 / 4 := by
  have hbounds := abs_le.mp hx
  have hprod : 0 ≤ (1 - x) * (1 + x) :=
    mul_nonneg (by linarith [hbounds.2]) (by linarith [hbounds.1])
  have hs : x ^ 2 ≤ 1 := by nlinarith
  rw [odd_coefficient_product, abs_of_nonpos (by nlinarith [sq_nonneg x])]
  nlinarith

theorem odd_coefficient_determinant_ge_one (x : ℝ) :
    1 ≤ 1 - (x / 2) * ((-x) / 2) := by
  rw [odd_coefficient_product]
  nlinarith [sq_nonneg x]

/-- Constant coefficients diagonalize in sum/difference coordinates. -/
theorem constant_diagonalization {K : Type*} [Field K] (a u v : K) :
    (u + a * v) + (a * u + v) = (1 + a) * (u + v) ∧
    (u + a * v) - (a * u + v) = (1 - a) * (u - v) := by
  constructor <;> ring

example : (principalMatrix (0 : ℝ) 0).det = 1 := by
  rw [principalMatrix_det]
  ring

example : (principalMatrix (1 / 2 : ℝ) (1 / 2)).det = 3 / 4 := by
  rw [principalMatrix_det]
  ring

end Involution
