module

public import Involution.Reduction
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Явная обратная главная матрица и её равенство обратной матрице Mathlib. -/

@[expose] public noncomputable section

namespace Involution

def principalInverse {K : Type*} [Field K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  (1 - a * b)⁻¹ • principalMatrix (-a) (-b)

theorem principalMatrix_mul_principalInverse {K : Type*} [Field K] (a b : K)
    (hdet : 1 - a * b ≠ 0) : principalMatrix a b * principalInverse a b = 1 := by
  have hdet' : 1 - b * a ≠ 0 := by simpa only [mul_comm] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalInverse, principalMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      smul_eq_mul] <;> field_simp [hdet, hdet'] <;> ring

theorem principalMatrix_inv {K : Type*} [Field K] (a b : K)
    (hdet : 1 - a * b ≠ 0) : (principalMatrix a b)⁻¹ = principalInverse a b :=
  Matrix.inv_eq_right_inv (principalMatrix_mul_principalInverse a b hdet)

theorem principalInverse_mul_principalMatrix {K : Type*} [Field K] (a b : K)
    (hdet : 1 - a * b ≠ 0) : principalInverse a b * principalMatrix a b = 1 := by
  rw [← principalMatrix_inv a b hdet]
  exact Matrix.nonsing_inv_mul _
    (by simpa only [principalMatrix_det, isUnit_iff_ne_zero] using hdet)

end Involution
