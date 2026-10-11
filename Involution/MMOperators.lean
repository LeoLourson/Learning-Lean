module

public import Involution.MMRiesz
public import Involution.SchurMultiplier

/-! The concrete setting of the Markus–Matsaev theorem: a diagonal operator `G = diag(lam)`
given through `K₀ = G⁻¹`, a perturbation given through `B = S G⁻¹` with
`‖B g‖ ≤ b₁ ⟨K₀ g, g⟩^{1/2}`, and `lam i ≥ m²`. Here: finite coordinate sums,
diagonal inverses of `1 - z K₀`, the operator `N(z) = B (1 - z K₀)⁻¹ = S (G - z)⁻¹`,
and estimates away from the spectrum of `G` (in the variable `ω = √z`). -/

@[expose] public noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace Involution

/-- Data of the core setting. -/
structure MMData (ι : Type*) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  b : HilbertBasis ι ℂ H
  lam : ι → ℝ
  m : ℝ
  hm : 0 < m
  hlam : ∀ i, m ^ 2 ≤ lam i
  K₀ : H →L[ℂ] H
  B : H →L[ℂ] H
  hK : ∀ i, K₀ (b i) = (((lam i)⁻¹ : ℝ) : ℂ) • b i
  b₁ : ℝ
  hb₁ : 0 ≤ b₁
  hB : ∀ g : H, ‖B g‖ ≤ b₁ * Real.sqrt (RCLike.re (inner ℂ (K₀ g) g))

namespace MMData

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : MMData ι H)

/-- Square roots of the eigenvalues. -/
def ω (i : ι) : ℝ := Real.sqrt (D.lam i)

theorem lam_pos (i : ι) : 0 < D.lam i := lt_of_lt_of_le (pow_pos D.hm 2) (D.hlam i)

theorem ω_sq (i : ι) : D.ω i ^ 2 = D.lam i := Real.sq_sqrt (D.lam_pos i).le

theorem m_le_ω (i : ι) : D.m ≤ D.ω i := by
  rw [ω]
  exact Real.le_sqrt_of_sq_le (D.hlam i)

theorem ω_pos (i : ι) : 0 < D.ω i := D.hm.trans_le (D.m_le_ω i)

theorem K_eq_diag : D.K₀ = diagOp D.b (fun i => (((D.lam i)⁻¹ : ℝ) : ℂ)) := by
  have hb : ∀ i, ‖(((D.lam i)⁻¹ : ℝ) : ℂ)‖ ≤ (D.m ^ 2)⁻¹ := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.lam_pos i))]
    exact inv_anti₀ (pow_pos D.hm 2) (D.hlam i)
  apply clm_ext_basis D.b
  intro i
  rw [D.hK i, diagOp_apply_basis D.b _ _ hb]

theorem K_sum (s : Finset ι) (c : ι → ℂ) :
    D.K₀ (∑ i ∈ s, c i • D.b i) = ∑ i ∈ s, (c i * (((D.lam i)⁻¹ : ℝ) : ℂ)) • D.b i := by
  simp only [map_sum, map_smul, D.hK, smul_smul]

theorem re_inner_K_sum (s : Finset ι) (c : ι → ℂ) :
    RCLike.re (inner ℂ (D.K₀ (∑ i ∈ s, c i • D.b i)) (∑ i ∈ s, c i • D.b i)) =
      ∑ i ∈ s, ‖c i‖ ^ 2 / D.lam i := by
  rw [D.K_sum, D.b.orthonormal.inner_sum]
  have e : ∀ i, conj (c i * (((D.lam i)⁻¹ : ℝ) : ℂ)) * c i = ((‖c i‖ ^ 2 / D.lam i : ℝ) : ℂ) := by
    intro i
    rw [map_mul, Complex.conj_ofReal, mul_comm (conj (c i)), mul_assoc, Complex.conj_mul']
    push_cast; ring
  simp_rw [e]
  rw [← Complex.ofReal_sum, RCLike.re_to_complex, Complex.ofReal_re]

theorem B_sum_bound (s : Finset ι) (c : ι → ℂ) :
    ‖D.B (∑ i ∈ s, c i • D.b i)‖ ≤ D.b₁ * Real.sqrt (∑ i ∈ s, ‖c i‖ ^ 2 / D.lam i) := by
  have h := D.hB (∑ i ∈ s, c i • D.b i)
  rwa [D.re_inner_K_sum] at h

/-- Norm bound from bounds on finite coordinate sums. -/
theorem opNorm_le_of_sum (T : H →L[ℂ] H) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ (s : Finset ι) (c : ι → ℂ),
      ‖T (∑ i ∈ s, c i • D.b i)‖ ≤ M * Real.sqrt (∑ i ∈ s, ‖c i‖ ^ 2)) : ‖T‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
  have hs := D.b.hasSum_repr u
  have ht : Filter.Tendsto (fun s : Finset ι => T (∑ i ∈ s, D.b.repr u i • D.b i))
      Filter.atTop (nhds (T u)) := (T.continuous.tendsto u).comp hs
  refine le_of_tendsto' ((continuous_norm.tendsto _).comp ht) fun s => ?_
  refine (h s _).trans ?_
  gcongr
  rw [Real.sqrt_le_left (norm_nonneg u)]
  simp only [HilbertBasis.repr_apply_apply]
  exact D.b.orthonormal.sum_inner_products_le u

/-- The basic estimate `‖B diag(ψ)‖ ≤ b₁ C` when `|ψ i| ≤ C ω i`. -/
theorem norm_B_mul_diag (ψ : ι → ℂ) (C C' : ℝ) (hC : 0 ≤ C) (hψb : ∀ i, ‖ψ i‖ ≤ C')
    (hψ : ∀ i, ‖ψ i‖ ≤ C * D.ω i) : ‖D.B * diagOp D.b ψ‖ ≤ D.b₁ * C := by
  refine D.opNorm_le_of_sum _ _ (mul_nonneg D.hb₁ hC) fun s c => ?_
  have e : (D.B * diagOp D.b ψ) (∑ i ∈ s, c i • D.b i) =
      D.B (∑ i ∈ s, (ψ i * c i) • D.b i) := by
    simp only [mul_apply_eq_comp, map_sum, map_smul,
      diagOp_apply_basis D.b ψ C' hψb, smul_smul, mul_comm]
  rw [e]
  refine (D.B_sum_bound s _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ D.hb₁
  rw [← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
  gcongr with i
  rw [norm_mul, mul_pow, div_le_iff₀ (D.lam_pos i)]
  have h1 := hψ i
  have h2 : ‖ψ i‖ ^ 2 ≤ C ^ 2 * D.lam i := by
    rw [← D.ω_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg ‖c i‖]

/-- Inverse of `1 - z diag(κ)`. -/
theorem isUnit_one_sub_diag (κ : ι → ℂ) (Cκ : ℝ) (hκ : ∀ i, ‖κ i‖ ≤ Cκ) (z : ℂ) (C : ℝ)
    (hz : ∀ i, 1 - z * κ i ≠ 0) (hC : ∀ i, ‖(1 - z * κ i)⁻¹‖ ≤ C) :
    IsUnit (1 - z • diagOp D.b κ) ∧
      Ring.inverse (1 - z • diagOp D.b κ) = diagOp D.b (fun i => (1 - z * κ i)⁻¹) := by
  have h1 : (1 - z • diagOp D.b κ) * diagOp D.b (fun i => (1 - z * κ i)⁻¹) = 1 := by
    apply clm_ext_basis D.b
    intro i
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self,
      smul_apply, diagOp_apply_basis D.b _ C hC, map_smul,
      diagOp_apply_basis D.b κ Cκ hκ, smul_smul]
    rw [show D.b i - (z * κ i) • D.b i = (1 - z * κ i) • D.b i by rw [sub_smul, one_smul],
      smul_smul, inv_mul_cancel₀ (hz i), one_smul]
  have h2 : diagOp D.b (fun i => (1 - z * κ i)⁻¹) * (1 - z • diagOp D.b κ) = 1 := by
    apply clm_ext_basis D.b
    intro i
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self,
      smul_apply, diagOp_apply_basis D.b _ C hC, map_smul, map_sub,
      diagOp_apply_basis D.b κ Cκ hκ, smul_smul]
    rw [← sub_smul]
    rw [show (1 - z * κ i)⁻¹ - z * κ i * (1 - z * κ i)⁻¹ = (1 - z * κ i) * (1 - z * κ i)⁻¹ by
      ring, mul_inv_cancel₀ (hz i), one_smul]
  let u : (H →L[ℂ] H)ˣ := ⟨_, _, h1, h2⟩
  exact ⟨u.isUnit, by rw [show (1 - z • diagOp D.b κ) = (u : H →L[ℂ] H) from rfl,
    Ring.inverse_unit]; rfl⟩

/-- `N(z) = B (1 - z K₀)⁻¹`, i.e. `S (G - z)⁻¹`. -/
def N (z : ℂ) : H →L[ℂ] H := D.B * Ring.inverse (1 - z • D.K₀)

theorem norm_lam_sub_sq_ge {ω : ℂ} {r : ℝ} (hr : 0 < r) (i : ι)
    (h1 : r ≤ ‖(D.ω i : ℂ) - ω‖) (h2 : r ≤ ‖(D.ω i : ℂ) + ω‖) :
    r * D.ω i ≤ ‖(D.lam i : ℂ) - ω ^ 2‖ := by
  have e : (D.lam i : ℂ) - ω ^ 2 = ((D.ω i : ℂ) - ω) * ((D.ω i : ℂ) + ω) := by
    rw [← D.ω_sq]; push_cast; ring
  rw [e, norm_mul]
  have htri : 2 * D.ω i ≤ ‖(D.ω i : ℂ) - ω‖ + ‖(D.ω i : ℂ) + ω‖ := by
    have := norm_add_le ((D.ω i : ℂ) - ω) ((D.ω i : ℂ) + ω)
    rw [show (D.ω i : ℂ) - ω + ((D.ω i : ℂ) + ω) = ((2 * D.ω i : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [D.ω_pos i])] at this
    linarith
  rcases le_total ‖(D.ω i : ℂ) - ω‖ ‖(D.ω i : ℂ) + ω‖ with h | h
  · nlinarith [D.ω_pos i]
  · nlinarith [D.ω_pos i]

/-- Away from `±ω i`: `1 - ω² K₀` is invertible, with explicit diagonal inverse, and
`‖N(ω²)‖ ≤ b₁ / r`. -/
theorem far {ω : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ i, r ≤ ‖(D.ω i : ℂ) - ω‖ ∧ r ≤ ‖(D.ω i : ℂ) + ω‖) :
    IsUnit (1 - ω ^ 2 • D.K₀) ∧
      Ring.inverse (1 - ω ^ 2 • D.K₀) =
        diagOp D.b (fun i => (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2)) ∧
      ‖D.N (ω ^ 2)‖ ≤ D.b₁ / r := by
  have hlow := fun i => D.norm_lam_sub_sq_ge hr i (h i).1 (h i).2
  have hne : ∀ i, (D.lam i : ℂ) - ω ^ 2 ≠ 0 := fun i e => by
    have := hlow i; rw [e, norm_zero] at this; nlinarith [D.ω_pos i]
  have hlamne : ∀ i, (D.lam i : ℂ) ≠ 0 := fun i => by exact_mod_cast (D.lam_pos i).ne'
  have hκ : ∀ i, ‖(((D.lam i)⁻¹ : ℝ) : ℂ)‖ ≤ (D.m ^ 2)⁻¹ := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.lam_pos i))]
    exact inv_anti₀ (pow_pos D.hm 2) (D.hlam i)
  have e1 : ∀ i, 1 - ω ^ 2 * (((D.lam i)⁻¹ : ℝ) : ℂ) = ((D.lam i : ℂ) - ω ^ 2) / D.lam i := by
    intro i; push_cast; field_simp [hlamne i]
  have e2 : ∀ i, (1 - ω ^ 2 * (((D.lam i)⁻¹ : ℝ) : ℂ))⁻¹ =
      (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2) := by
    intro i; rw [e1, inv_div]
  have hbd : ∀ i, ‖(D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2)‖ ≤ 1 + ‖ω‖ ^ 2 / (r * D.m) := by
    intro i
    have e3 : (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2) = 1 + ω ^ 2 / ((D.lam i : ℂ) - ω ^ 2) := by
      field_simp [hne i]; ring
    rw [e3]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div, norm_pow]
    gcongr
    · exact mul_pos hr D.hm
    · exact (mul_le_mul_of_nonneg_left (D.m_le_ω i) hr.le).trans (hlow i)
  have hψ : ∀ i, ‖(D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2)‖ ≤ r⁻¹ * D.ω i := by
    intro i
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (D.lam_pos i),
      div_le_iff₀ (by have := hlow i; nlinarith [D.ω_pos i])]
    calc D.lam i = r⁻¹ * D.ω i * (r * D.ω i) := by
          rw [← D.ω_sq]; field_simp
      _ ≤ r⁻¹ * D.ω i * ‖(D.lam i : ℂ) - ω ^ 2‖ := by
          gcongr
          · exact mul_nonneg (inv_nonneg.mpr hr.le) (D.ω_pos i).le
          · exact hlow i
  obtain ⟨hu, hinv⟩ := D.isUnit_one_sub_diag _ _ hκ (ω ^ 2) (1 + ‖ω‖ ^ 2 / (r * D.m))
    (fun i => by rw [e1]; exact div_ne_zero (hne i) (hlamne i)) (fun i => by rw [e2]; exact hbd i)
  rw [← D.K_eq_diag] at hu hinv
  have hinv' : Ring.inverse (1 - ω ^ 2 • D.K₀) =
      diagOp D.b (fun i => (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2)) := by
    rw [hinv]; congr 1; funext i; exact e2 i
  refine ⟨hu, hinv', ?_⟩
  rw [N, hinv', div_eq_mul_inv, mul_comm D.b₁]
  have := D.norm_B_mul_diag _ r⁻¹ _ (inv_nonneg.mpr hr.le) hbd hψ
  linarith [this]

theorem Lop_eq {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) :
    Lop D.K₀ D.B z = (1 + D.N z) * (1 - z • D.K₀) := by
  rw [add_mul, one_mul, N, mul_assoc, Ring.inverse_mul_cancel _ hz, mul_one, Lop]
  abel

theorem Lop_zero (z : ℂ) : Lop D.K₀ 0 z = 1 - z • D.K₀ := by simp [Lop]

theorem isUnit_Lop {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) (hN : IsUnit (1 + D.N z)) :
    IsUnit (Lop D.K₀ D.B z) := by
  rw [D.Lop_eq hz]; exact hN.mul hz

/-- `R_T(z) = R_G(z) (1 + S (G - z)⁻¹)⁻¹`. -/
theorem Res_eq {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) (hN : IsUnit (1 + D.N z)) :
    Res D.K₀ D.B z = Res D.K₀ 0 z * Ring.inverse (1 + D.N z) := by
  obtain ⟨u, hu⟩ := hz
  obtain ⟨v, hv⟩ := hN
  rw [Res, Res, D.Lop_eq ⟨u, hu⟩, D.Lop_zero, ← hu, ← hv, ← Units.val_mul, Ring.inverse_unit,
    Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev, Units.val_mul, mul_assoc]

/-- Far from the eigenvalues, `ω²` is in the resolvent set of `T` with `‖W‖ ≤ 2`. -/
theorem good_far {ω : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ i, r ≤ ‖(D.ω i : ℂ) - ω‖ ∧ r ≤ ‖(D.ω i : ℂ) + ω‖) (hb : D.b₁ / r ≤ 1 / 2) :
    IsUnit (1 - ω ^ 2 • D.K₀) ∧ IsUnit (1 + D.N (ω ^ 2)) ∧
      ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤ 2 ∧ Good D.K₀ D.B ω := by
  obtain ⟨hu, -, hN⟩ := D.far hr h
  obtain ⟨hw, hwn⟩ := isUnit_one_add_of_norm_le (D.N (ω ^ 2)) (q := 1 / 2) (by norm_num)
    (hN.trans hb) ContinuousLinearMap.norm_id_le
  refine ⟨hu, hw, by norm_num at hwn ⊢; exact hwn, D.isUnit_Lop hu hw⟩

theorem inv_one_sub_apply_basis {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) (i : ι) :
    (D.lam i : ℂ) - z ≠ 0 ∧
      Ring.inverse (1 - z • D.K₀) (D.b i) = ((D.lam i : ℂ) / ((D.lam i : ℂ) - z)) • D.b i := by
  obtain ⟨L, hL⟩ := hz
  have hlam : (D.lam i : ℂ) ≠ 0 := by exact_mod_cast (D.lam_pos i).ne'
  have hLb : (L : H →L[ℂ] H) (D.b i) = (((D.lam i : ℂ) - z) / D.lam i) • D.b i := by
    rw [hL, sub_apply, one_apply_eq_self, smul_apply, D.hK, smul_smul, ← one_smul ℂ (D.b i),
      smul_smul, ← sub_smul, mul_one, one_smul]
    congr 1
    push_cast
    field_simp
  have hne : (D.lam i : ℂ) - z ≠ 0 := by
    intro h
    rw [h, zero_div, zero_smul] at hLb
    have h2 := congrArg (fun u => (↑L⁻¹ : H →L[ℂ] H) u) hLb
    simp only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_zero] at h2
    exact D.b.orthonormal.ne_zero i h2
  refine ⟨hne, ?_⟩
  rw [← hL, Ring.inverse_unit]
  have h2 := congrArg (fun u => (↑L⁻¹ : H →L[ℂ] H) u) hLb
  simp only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_smul] at h2
  have h3 := congrArg (fun u => ((D.lam i : ℂ) / ((D.lam i : ℂ) - z)) • u) h2
  simp only [smul_smul] at h3
  rw [show (D.lam i : ℂ) / ((D.lam i : ℂ) - z) * (((D.lam i : ℂ) - z) / D.lam i) = 1 by
    field_simp, one_smul] at h3
  exact h3.symm

theorem res0_apply_basis {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) (i : ι) :
    Res D.K₀ 0 z (D.b i) = (1 / ((D.lam i : ℂ) - z)) • D.b i := by
  obtain ⟨hne, h⟩ := D.inv_one_sub_apply_basis hz i
  have hlam : (D.lam i : ℂ) ≠ 0 := by exact_mod_cast (D.lam_pos i).ne'
  rw [Res, D.Lop_zero, mul_apply_eq_comp, h, map_smul, D.hK, smul_smul]
  congr 1
  push_cast
  field_simp

end MMData

end Involution
