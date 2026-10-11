module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Algebraic reduction of a differential equation with reflection

The entries `a`, `b` stand for `a(x)`, `a(-x)`. These are pointwise
algebraic statements; no regularity, boundary or spectral claim is implicit.
-/

public section

namespace Involution

/-- The principal matrix after folding the interval at zero. -/
@[expose] def principalMatrix {K : Type*} [Field K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, a; b, 1]

theorem principalMatrix_det {K : Type*} [Field K] (a b : K) :
    (principalMatrix a b).det = 1 - a * b := by
  simp [principalMatrix, Matrix.det_fin_two]

/-- Uniform separation of the determinant from zero. -/
theorem determinant_lower_bound (a b κ : ℝ) (h : |a * b| ≤ κ) :
    1 - κ ≤ 1 - a * b := by
  have hab : a * b ≤ κ := le_trans (le_abs_self _) h
  linarith

theorem determinant_pos (a b κ : ℝ) (hκ : κ < 1) (h : |a * b| ≤ κ) :
    0 < 1 - a * b := by
  have := determinant_lower_bound a b κ h
  linarith

/-- Solving the folded two-by-two system, over any field. -/
theorem solve_system {K : Type*} [Field K] (a b u v f g : K)
    (hdet : 1 - a * b ≠ 0) :
    (u + a * v = f ∧ b * u + v = g) ↔
      (u = (f - a * g) / (1 - a * b) ∧
       v = (g - b * f) / (1 - a * b)) := by
  constructor
  · rintro ⟨hf, hg⟩
    constructor
    · apply (eq_div_iff hdet).2
      rw [← hf, ← hg]
      ring
    · apply (eq_div_iff hdet).2
      rw [← hf, ← hg]
      ring
  · rintro ⟨rfl, rfl⟩
    have hdet' : 1 - b * a ≠ 0 := by simpa [mul_comm] using hdet
    constructor <;> field_simp [hdet, hdet'] <;> ring

end Involution
