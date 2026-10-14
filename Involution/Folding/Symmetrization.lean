module

public import Involution.Folding.Reduction
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

/-! Алгебра симметризации главной матрицы и сохранения условий склейки.
Регулярность `sqrt |a|` — в `Involution.Model.CoefficientSqrt`. -/

@[expose] public noncomputable section

namespace Involution

def diagonalScale (r t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![r, 0; 0, t]

def symmetricPrincipal (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, s; s, 1]

theorem diagonalScale_det (r t : ℝ) : (diagonalScale r t).det = r * t := by
  simp [diagonalScale, Matrix.det_fin_two]

theorem diagonalScale_det_ne_zero (r t : ℝ) (hr : r ≠ 0) (ht : t ≠ 0) :
    (diagonalScale r t).det ≠ 0 := by
  rw [diagonalScale_det]
  exact mul_ne_zero hr ht

theorem principalMatrix_symmetrization (σ r t : ℝ) :
    principalMatrix (σ * r ^ 2) (σ * t ^ 2) * diagonalScale r t =
      diagonalScale r t * symmetricPrincipal (σ * r * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, principalMatrix, diagonalScale,
      symmetricPrincipal] <;> ring

theorem positive_principalMatrix_symmetrization (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    principalMatrix a b * diagonalScale (Real.sqrt |a|) (Real.sqrt |b|) =
      diagonalScale (Real.sqrt |a|) (Real.sqrt |b|) *
        symmetricPrincipal (Real.sqrt |a| * Real.sqrt |b|) := by
  have h := principalMatrix_symmetrization 1 (Real.sqrt |a|) (Real.sqrt |b|)
  simp only [one_mul, Real.sq_sqrt (abs_nonneg a), Real.sq_sqrt (abs_nonneg b)] at h
  simpa only [abs_of_pos ha, abs_of_pos hb] using h

theorem negative_principalMatrix_symmetrization (a b : ℝ) (ha : a < 0) (hb : b < 0) :
    principalMatrix a b * diagonalScale (Real.sqrt |a|) (Real.sqrt |b|) =
      diagonalScale (Real.sqrt |a|) (Real.sqrt |b|) *
        symmetricPrincipal (-(Real.sqrt |a| * Real.sqrt |b|)) := by
  have h := principalMatrix_symmetrization (-1) (Real.sqrt |a|) (Real.sqrt |b|)
  simp only [one_mul, Real.sq_sqrt (abs_nonneg a),
    Real.sq_sqrt (abs_nonneg b), neg_mul] at h
  simpa only [abs_of_neg ha, abs_of_neg hb, neg_neg] using h

theorem sqrt_abs_pos {a : ℝ} (ha : a ≠ 0) : 0 < Real.sqrt |a| :=
  Real.sqrt_pos.mpr (abs_pos.mpr ha)

theorem symmetrizing_scale_invertible (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (diagonalScale (Real.sqrt |a|) (Real.sqrt |b|)).det ≠ 0 :=
  diagonalScale_det_ne_zero _ _ (sqrt_abs_pos ha).ne' (sqrt_abs_pos hb).ne'

theorem positive_channel_bounds (s ρ : ℝ) (hs : |s| ≤ ρ) (hρ : ρ < 1) :
    0 < 1 - ρ ∧
      (1 - ρ ≤ 1 + s ∧ 1 + s ≤ 1 + ρ) ∧
      (1 - ρ ≤ 1 - s ∧ 1 - s ≤ 1 + ρ) := by
  have h := abs_le.mp hs
  constructor
  · linarith
  constructor <;> constructor <;> linarith [h.1, h.2]

theorem scaled_gluing_iff {K : Type*} [Field K] (r r' u v du dv : K) (hr : r ≠ 0) :
    (r * u = r * v ∧ (r' * u + r * du) + (-r' * v + r * dv) = 0) ↔
      (u = v ∧ du + dv = 0) := by
  constructor
  · rintro ⟨huv, hd⟩
    have heq : u = v := mul_left_cancel₀ hr huv
    refine ⟨heq, ?_⟩
    have hz : r * (du + dv) = 0 := by
      calc
        r * (du + dv) = (r' * u + r * du) + (-r' * v + r * dv) := by rw [heq]; ring
        _ = 0 := hd
    exact (mul_eq_zero.mp hz).resolve_left hr
  · rintro ⟨huv, hd⟩
    refine ⟨by rw [huv], ?_⟩
    calc
      (r' * u + r * du) + (-r' * v + r * dv) = r * (du + dv) := by rw [huv]; ring
      _ = 0 := by rw [hd, mul_zero]

end Involution
