module

public import Involution.Estimates.MMOperators

/-! The pointwise estimate of `2 ω ⟨(R_T(ω²) - R_G(ω²)) y, w⟩` for finite coordinate vectors
(Wyss, Lemma 4.4 and the proof of Lemma 5.3). -/

@[expose] public noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace Involution

theorem norm_add_ge_of_re_nonneg {p : ℝ} (hp : 0 ≤ p) {ω : ℂ} (hre : 0 ≤ ω.re) :
    ‖ω‖ ≤ ‖(p : ℂ) + ω‖ ∧ p ≤ ‖(p : ℂ) + ω‖ := by
  have h1 : ‖(p : ℂ) + ω‖ ^ 2 = (p + ω.re) ^ 2 + ω.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖ω‖ ^ 2 = ω.re ^ 2 + ω.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  constructor
  · refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [h1, h2]; nlinarith
  · refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [h1]; nlinarith [sq_nonneg ω.im]

namespace MMData

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : MMData ι H)

theorem lam_eq_sq (i : ι) : (D.lam i : ℂ) = (D.ω i : ℂ) ^ 2 := by
  rw [← D.ω_sq]; push_cast; ring

/-- `‖λ - ω²‖ ≥ ‖ω_i - ω‖ ‖ω‖` and `≥ ‖ω_i - ω‖ ω_i` for `Re ω ≥ 0`. -/
theorem norm_lam_sub_ge {ω : ℂ} (hre : 0 ≤ ω.re) (i : ι) :
    ‖(D.ω i : ℂ) - ω‖ * ‖ω‖ ≤ ‖(D.lam i : ℂ) - ω ^ 2‖ ∧
      ‖(D.ω i : ℂ) - ω‖ * D.ω i ≤ ‖(D.lam i : ℂ) - ω ^ 2‖ := by
  have e : (D.lam i : ℂ) - ω ^ 2 = ((D.ω i : ℂ) - ω) * ((D.ω i : ℂ) + ω) := by
    rw [D.lam_eq_sq]; ring
  obtain ⟨h1, h2⟩ := norm_add_ge_of_re_nonneg (D.ω_pos i).le hre
  rw [e, norm_mul]
  exact ⟨mul_le_mul_of_nonneg_left h1 (norm_nonneg _),
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)⟩

/-- `R_G(z)` as a diagonal operator. -/
theorem res0_eq_diag {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) :
    Res D.K₀ 0 z = diagOp D.b (fun i => 1 / ((D.lam i : ℂ) - z)) ∧
      ∀ i, ‖1 / ((D.lam i : ℂ) - z)‖ ≤ ‖Ring.inverse (1 - z • D.K₀)‖ / D.m ^ 2 := by
  have hbd : ∀ i, ‖1 / ((D.lam i : ℂ) - z)‖ ≤ ‖Ring.inverse (1 - z • D.K₀)‖ / D.m ^ 2 := by
    intro i
    obtain ⟨hne, h⟩ := D.inv_one_sub_apply_basis hz i
    have h1 : ‖(D.lam i : ℂ) / ((D.lam i : ℂ) - z)‖ ≤ ‖Ring.inverse (1 - z • D.K₀)‖ := by
      have := (Ring.inverse (1 - z • D.K₀)).le_opNorm (D.b i)
      rwa [h, norm_smul, D.b.orthonormal.1 i, mul_one, mul_one] at this
    have hl : 0 < D.lam i := D.lam_pos i
    rw [le_div_iff₀ (pow_pos D.hm 2)]
    calc ‖1 / ((D.lam i : ℂ) - z)‖ * D.m ^ 2 ≤ ‖1 / ((D.lam i : ℂ) - z)‖ * D.lam i :=
          mul_le_mul_of_nonneg_left (D.hlam i) (norm_nonneg _)
      _ = ‖(D.lam i : ℂ) / ((D.lam i : ℂ) - z)‖ := by
          rw [norm_div, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
          ring
      _ ≤ _ := h1
  refine ⟨?_, hbd⟩
  apply clm_ext_basis D.b
  intro i
  rw [D.res0_apply_basis hz i, diagOp_apply_basis D.b _ _ hbd]

/-- The basic pointwise estimate. -/
theorem pointwise {ω : ℂ} (hre : 0 ≤ ω.re) (hz : IsUnit (1 - ω ^ 2 • D.K₀))
    (hN : IsUnit (1 + D.N (ω ^ 2))) {CW : ℝ} (hW : ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤ CW)
    (s : Finset ι) (y w : ι → ℂ) :
    ‖inner ℂ (∑ i ∈ s, w i • D.b i) ((cF D.K₀ D.B ω - cF D.K₀ 0 ω) (∑ i ∈ s, y i • D.b i))‖ ≤
      2 * CW * D.b₁ * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2) *
        Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2) := by
  set z := ω ^ 2 with hzdef
  set W := Ring.inverse (1 + D.N z)
  have hW1 : W * (1 + D.N z) = 1 := Ring.inverse_mul_cancel _ hN
  obtain ⟨hR0, hφ⟩ := D.res0_eq_diag hz
  set φ : ι → ℂ := fun i => 1 / ((D.lam i : ℂ) - z)
  set Cφ := ‖Ring.inverse (1 - z • D.K₀)‖ / D.m ^ 2
  have hdiff : cF D.K₀ D.B ω - cF D.K₀ 0 ω = -((2 * ω) • (Res D.K₀ 0 z * (W * D.N z))) := by
    have e : W - 1 = -(W * D.N z) := by
      rw [← hW1, mul_add, mul_one]; abel
    rw [cF, cF, D.Res_eq hz hN, ← smul_sub, ← mul_sub_one, e, mul_neg, smul_neg]
  set yv := ∑ i ∈ s, y i • D.b i
  set wv := ∑ i ∈ s, w i • D.b i
  set X := W (D.N z yv) with hX
  have hne : ∀ i, (D.lam i : ℂ) - z ≠ 0 := fun i => (D.inv_one_sub_apply_basis hz i).1
  have hsep : ∀ i, 0 < ‖(D.ω i : ℂ) - ω‖ := by
    intro i
    refine norm_pos_iff.mpr fun h => hne i ?_
    rw [hzdef, D.lam_eq_sq, sub_eq_zero.mp h, sub_self]
  -- the norm of `N yv`
  have hNy : ‖D.N z yv‖ ≤ D.b₁ * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2) := by
    have e : D.N z yv = D.B (∑ i ∈ s, ((D.lam i : ℂ) / ((D.lam i : ℂ) - z) * y i) • D.b i) := by
      rw [N, mul_apply_eq_comp, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (D.inv_one_sub_apply_basis hz i).2, smul_smul, mul_comm]
    rw [e]
    refine (D.B_sum_bound s _).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)) D.hb₁)
    have hl := D.lam_pos i
    obtain ⟨-, h2⟩ := D.norm_lam_sub_ge hre i
    have hs := hsep i
    have h3 : ‖(D.ω i : ℂ) - ω‖ ^ 2 * D.lam i ≤ ‖(D.lam i : ℂ) - z‖ ^ 2 := by
      have := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (D.ω_pos i).le) h2 2
      rw [mul_pow, D.ω_sq] at this; exact this
    have h4 : 0 < ‖(D.lam i : ℂ) - z‖ := norm_pos_iff.mpr (hne i)
    have e2 : ‖(D.lam i : ℂ) / ((D.lam i : ℂ) - z) * y i‖ ^ 2 / D.lam i =
        D.lam i * ‖y i‖ ^ 2 / ‖(D.lam i : ℂ) - z‖ ^ 2 := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
      field_simp
    rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖y i‖)]
  have hXn : ‖X‖ ≤ CW * (D.b₁ * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2)) :=
    (W.le_opNorm _).trans (mul_le_mul hW hNy (norm_nonneg _) ((norm_nonneg _).trans hW))
  -- the inner product
  have hinner : inner ℂ wv ((cF D.K₀ D.B ω - cF D.K₀ 0 ω) yv) =
      -(2 * ω) * ∑ i ∈ s, conj (w i) * (φ i * inner ℂ (D.b i) X) := by
    rw [hdiff, neg_apply, smul_apply, inner_neg_right, inner_smul_right,
      mul_apply_eq_comp, mul_apply_eq_comp, sum_inner, neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hR0, inner_basis_diagOp D.b φ Cφ hφ]
  rw [hinner, norm_mul, norm_neg]
  have hterm : ∀ i ∈ s, ‖2 * ω‖ * ‖conj (w i) * (φ i * inner ℂ (D.b i) X)‖ ≤
      2 * (‖w i‖ / ‖(D.ω i : ℂ) - ω‖) * ‖inner ℂ (D.b i) X‖ := by
    intro i _
    obtain ⟨h1, -⟩ := D.norm_lam_sub_ge hre i
    have hs := hsep i
    have h4 : 0 < ‖(D.lam i : ℂ) - z‖ := norm_pos_iff.mpr (hne i)
    simp only [norm_mul, Complex.norm_conj, φ, norm_div, norm_one]
    rw [show ‖(2 : ℂ)‖ = 2 by simp]
    have h5 : ‖ω‖ * (1 / ‖(D.lam i : ℂ) - z‖) ≤ 1 / ‖(D.ω i : ℂ) - ω‖ := by
      rw [mul_one_div, div_le_div_iff₀ h4 hs]; linarith
    have h6 : 0 ≤ ‖w i‖ * ‖inner ℂ (D.b i) X‖ := by positivity
    calc 2 * ‖ω‖ * (‖w i‖ * (1 / ‖(D.lam i : ℂ) - z‖ * ‖inner ℂ (D.b i) X‖))
        = 2 * (‖ω‖ * (1 / ‖(D.lam i : ℂ) - z‖)) * (‖w i‖ * ‖inner ℂ (D.b i) X‖) := by ring
      _ ≤ 2 * (1 / ‖(D.ω i : ℂ) - ω‖) * (‖w i‖ * ‖inner ℂ (D.b i) X‖) := by gcongr
      _ = _ := by ring
  calc ‖2 * ω‖ * ‖∑ i ∈ s, conj (w i) * (φ i * inner ℂ (D.b i) X)‖
      ≤ ‖2 * ω‖ * ∑ i ∈ s, ‖conj (w i) * (φ i * inner ℂ (D.b i) X)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ∑ i ∈ s, ‖2 * ω‖ * ‖conj (w i) * (φ i * inner ℂ (D.b i) X)‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, 2 * ((‖w i‖ / ‖(D.ω i : ℂ) - ω‖) * ‖inner ℂ (D.b i) X‖) :=
        Finset.sum_le_sum fun i hi => (hterm i hi).trans_eq (by ring)
    _ = 2 * ∑ i ∈ s, (‖w i‖ / ‖(D.ω i : ℂ) - ω‖) * ‖inner ℂ (D.b i) X‖ := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (Real.sqrt (∑ i ∈ s, (‖w i‖ / ‖(D.ω i : ℂ) - ω‖) ^ 2) *
          Real.sqrt (∑ i ∈ s, ‖inner ℂ (D.b i) X‖ ^ 2)) := by
        gcongr; exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ 2 * (Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2) * ‖X‖) := by
        simp only [div_pow]
        gcongr
        rw [Real.sqrt_le_left (norm_nonneg _)]
        exact D.b.orthonormal.sum_inner_products_le X
    _ ≤ 2 * (Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2) *
          (CW * (D.b₁ * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2)))) := by
        gcongr
    _ = _ := by ring

end MMData

end Involution
