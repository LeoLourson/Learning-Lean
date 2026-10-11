module

public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Involution.MMOperators

/-! The Woodbury formula for finite-rank perturbations `A + ∑ c_j φ_j(·) u_j` of an invertible
operator, in terms of the matrix `diag(1/c) + (φ_k(A⁻¹ u_j))`, and elementary bounds for
determinants and inverse matrices. -/

@[expose] public noncomputable section

open Complex

namespace Involution

section Woodbury

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Woodbury formula for a finite-rank perturbation of an invertible operator. -/
theorem woodbury (A Ai : E →L[ℂ] E) (hA1 : A * Ai = 1) (hA2 : Ai * A = 1) (u : J → E)
    (φ : J → E →L[ℂ] ℂ) (c d : J → ℂ) (hcd : ∀ j, c j * d j = 1) (Q : Matrix J J ℂ)
    (hQ1 : (Matrix.diagonal d + Matrix.of (fun k j => φ k (Ai (u j)))) * Q = 1)
    (hQ2 : Q * (Matrix.diagonal d + Matrix.of (fun k j => φ k (Ai (u j)))) = 1) :
    (A + ∑ j, c j • (φ j).smulRight (u j)) *
        ((1 - ∑ j, ∑ k, Q j k • (φ k).smulRight (Ai (u j))) * Ai) = 1 ∧
      ((1 - ∑ j, ∑ k, Q j k • (φ k).smulRight (Ai (u j))) * Ai) *
        (A + ∑ j, c j • (φ j).smulRight (u j)) = 1 := by
  set g : J → E := fun j => Ai (u j) with hg
  have hAg : ∀ j, A (g j) = u j := by
    intro j
    have := congrArg (fun T : E →L[ℂ] E => T (u j)) hA1
    simpa using this
  have hAiA : ∀ v, Ai (A v) = v := by
    intro v
    have := congrArg (fun T : E →L[ℂ] E => T v) hA2
    simpa using this
  have hAAi : ∀ v, A (Ai v) = v := by
    intro v
    have := congrArg (fun T : E →L[ℂ] E => T v) hA1
    simpa using this
  have e1 : ∀ i k, d i * Q i k + ∑ j, φ i (g j) * Q j k = if i = k then 1 else 0 := by
    intro i k
    have := congrFun (congrFun hQ1 i) k
    rw [add_mul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.one_apply]
      at this
    simpa [g] using this
  have e2 : ∀ j i, Q j i * d i + ∑ k, Q j k * φ k (g i) = if j = i then 1 else 0 := by
    intro j i
    have := congrFun (congrFun hQ2 j) i
    rw [mul_add, Matrix.add_apply, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.one_apply]
      at this
    simpa [g] using this
  set F : E →L[ℂ] E := 1 + ∑ j, c j • (φ j).smulRight (g j) with hF
  set Y : E →L[ℂ] E := 1 - ∑ j, ∑ k, Q j k • (φ k).smulRight (g j) with hY
  have hX : A + ∑ j, c j • (φ j).smulRight (u j) = A * F := by
    ext v
    simp [F, map_sum, map_smul, hAg]
  have hYv : ∀ v, Y v = v - ∑ j, (∑ k, Q j k * φ k v) • g j := by
    intro v
    simp [Y, Finset.sum_smul, smul_smul]
  have hFv : ∀ v, F v = v + ∑ j, (c j * φ j v) • g j := by
    intro v
    simp [F, smul_smul]
  have hFY : F * Y = 1 := by
    ext v
    have key : ∀ i, c i * φ i (Y v) = ∑ k, Q i k * φ k v := by
      intro i
      rw [hYv, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      have : ∑ j, (∑ k, Q j k * φ k v) * φ i (g j) =
          ∑ k, (∑ j, φ i (g j) * Q j k) * φ k v := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      have h2 : ∀ k, (∑ j, φ i (g j) * Q j k) = (if i = k then 1 else 0) - d i * Q i k := by
        intro k; rw [← e1 i k]; ring
      simp only [h2, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [mul_sub, mul_sub]
      have h3 : c i * ∑ k, d i * Q i k * φ k v = ∑ k, Q i k * φ k v := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← mul_assoc, hcd i, one_mul]
      rw [h3]; ring
    rw [mul_apply_eq_comp, hFv, one_apply_eq_self]
    simp only [key]
    rw [hYv]
    abel
  have hYF : Y * F = 1 := by
    ext v
    have key : ∀ j, ∑ k, Q j k * φ k (F v) = c j * φ j v := by
      intro j
      rw [hFv]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      have : ∑ k, Q j k * ∑ i, c i * φ i v * φ k (g i) =
          ∑ i, c i * φ i v * (∑ k, Q j k * φ k (g i)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [this]
      have h2 : ∀ i, (∑ k, Q j k * φ k (g i)) = (if j = i then 1 else 0) - Q j i * d i := by
        intro i; rw [← e2 j i]; ring
      simp only [h2, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      have h3 : ∑ i, c i * φ i v * (Q j i * d i) = ∑ k, Q j k * φ k v := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show c i * φ i v * (Q j i * d i) = (c i * d i) * (Q j i * φ i v) by ring, hcd i,
          one_mul]
      rw [h3]; ring
    rw [mul_apply_eq_comp, hYv, one_apply_eq_self]
    simp only [key]
    rw [hFv]
    abel
  rw [hX]
  constructor
  · ext v
    simp only [mul_apply_eq_comp, one_apply_eq_self]
    have := congrArg (fun T : E →L[ℂ] E => T (Ai v)) hFY
    simp only [mul_apply_eq_comp, one_apply_eq_self] at this
    rw [this, hAAi]
  · ext v
    simp only [mul_apply_eq_comp, one_apply_eq_self, hAiA]
    have := congrArg (fun T : E →L[ℂ] E => T v) hYF
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using this

/-- Conversely, an inverse of the perturbed operator gives an inverse of the matrix. -/
theorem woodbury_converse (A Ai : E →L[ℂ] E) (hA2 : Ai * A = 1) (u : J → E)
    (φ : J → E →L[ℂ] ℂ) (c d : J → ℂ) (hcd : ∀ j, c j * d j = 1) (Xi : E →L[ℂ] E)
    (hX : (A + ∑ j, c j • (φ j).smulRight (u j)) * Xi = 1) :
    (Matrix.diagonal d + Matrix.of (fun k j => φ k (Ai (u j)))) *
      Matrix.of (fun j k => (if j = k then c j else 0) - c j * c k * φ j (Xi (u k))) = 1 := by
  set g : J → E := fun j => Ai (u j) with hg
  have hw : ∀ k, Xi (u k) + ∑ j, (c j * φ j (Xi (u k))) • g j = g k := by
    intro k
    have h1 := congrArg (fun T : E →L[ℂ] E => Ai (T (u k))) hX
    simp only [mul_apply_eq_comp, one_apply_eq_self, add_apply, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_sum, map_smul] at h1
    have h2 : Ai (A (Xi (u k))) = Xi (u k) := by
      have := congrArg (fun T : E →L[ℂ] E => T (Xi (u k))) hA2
      simpa using this
    rw [h2] at h1
    simpa [g, smul_smul] using h1
  ext i k
  rw [add_mul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have key : φ i (Xi (u k)) = φ i (g k) - ∑ j, c j * φ j (Xi (u k)) * φ i (g j) := by
    rw [← hw k]; simp [map_add, map_sum, map_smul, smul_eq_mul]
  have h3 : ∑ j, φ i (g j) * (c j * c k * φ j (Xi (u k))) =
      c k * ∑ j, c j * φ j (Xi (u k)) * φ i (g j) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  simp only [g] at h3 key
  rw [h3]
  split_ifs with hik
  · subst hik
    rw [key]
    linear_combination (1 - c i * ((φ i) (Ai (u i)) -
      ∑ x, c x * (φ x) (Xi (u i)) * (φ i) (Ai (u x)))) * hcd i
  · rw [key]
    linear_combination (-c k * ((φ i) (Ai (u k)) -
      ∑ x, c x * (φ x) (Xi (u k)) * (φ i) (Ai (u x)))) * hcd i

omit [DecidableEq J] in
theorem norm_woodbury_le (Ai : E →L[ℂ] E) (u : J → E) (φ : J → E →L[ℂ] ℂ)
    (Q : Matrix J J ℂ) :
    ‖(1 - ∑ j, ∑ k, Q j k • (φ k).smulRight (Ai (u j))) * Ai‖ ≤
      (‖(1 : E →L[ℂ] E)‖ + ∑ j, ∑ k, ‖Q j k‖ * (‖φ k‖ * ‖Ai (u j)‖)) * ‖Ai‖ := by
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]

end Woodbury

section MatrixBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem norm_det_le (A : Matrix n n ℂ) (E : ℝ) (h : ∀ i j, ‖A i j‖ ≤ E) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * E ^ Fintype.card n := by
  have := Matrix.det_le (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) h
  simpa [nsmul_eq_mul] using this

theorem norm_inv_apply_le (A : Matrix n n ℂ) (E : ℝ) (hE : 1 ≤ E) (h : ∀ i j, ‖A i j‖ ≤ E)
    (i j : n) : ‖A⁻¹ i j‖ * ‖A.det‖ ≤ (Fintype.card n).factorial * E ^ Fintype.card n := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, norm_mul]
  by_cases hd : A.det = 0
  · rw [hd, norm_zero, mul_zero]; positivity
  rw [Ring.inverse_eq_inv', norm_inv, mul_assoc, mul_comm, mul_assoc, mul_inv_cancel₀
    (norm_ne_zero_iff.mpr hd), mul_one]
  apply norm_det_le
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp [hE, (zero_le_one.trans hE)]
  · exact h a b

theorem norm_det_ge_of_mul_eq_one (Z Q : Matrix n n ℂ) (hZQ : Z * Q = 1) (E : ℝ)
    (h : ∀ i j, ‖Q i j‖ ≤ E) :
    1 ≤ ‖Z.det‖ * ((Fintype.card n).factorial * E ^ Fintype.card n) := by
  have h1 : Z.det * Q.det = 1 := by rw [← Matrix.det_mul, hZQ, Matrix.det_one]
  have h2 := norm_det_le Q E h
  calc (1 : ℝ) = ‖Z.det‖ * ‖Q.det‖ := by rw [← norm_mul, h1, norm_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

end MatrixBounds

end Involution
