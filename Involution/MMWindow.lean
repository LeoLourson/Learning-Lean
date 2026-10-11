module

public import Involution.MMWoodbury

/-! Splitting off the eigenvalues in a window: for a finite set `J` of indices, the operator
`A_J(z) = 1 + B ((1 - z K_J)⁻¹ - P_J)`, where `K_J` and `P_J` are the diagonal operators of
`K₀` with the entries in `J` removed and of the coordinate projection onto `J`. Far from the
eigenvalues outside `J`, `A_J` is invertible with `‖A_J⁻¹‖ ≤ 2`, and
`1 + N(z) = A_J(z) + ∑_{j ∈ J} c_j ⟨b_j, ·⟩ B b_j`. -/

@[expose] public noncomputable section

open Complex Set

namespace Involution

namespace MMData

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : MMData ι H) [DecidableEq ι]

/-- Diagonal entries of `K₀` with the indices in `J` removed. -/
def κJ (J : Finset ι) (i : ι) : ℂ := if i ∈ J then 0 else (((D.lam i)⁻¹ : ℝ) : ℂ)

/-- `K₀` with the indices in `J` removed. -/
def KJ (J : Finset ι) : H →L[ℂ] H := diagOp D.b (D.κJ J)

/-- Coordinate projection onto the indices in `J`. -/
def PJ (J : Finset ι) : H →L[ℂ] H := diagOp D.b (fun i => if i ∈ J then 1 else 0)

/-- `A_J(z) = 1 + B ((1 - z K_J)⁻¹ - P_J)`. -/
def AJ (J : Finset ι) (z : ℂ) : H →L[ℂ] H :=
  1 + D.B * (Ring.inverse (1 - z • D.KJ J) - D.PJ J)

theorem norm_κJ_le (J : Finset ι) (i : ι) : ‖D.κJ J i‖ ≤ (D.m ^ 2)⁻¹ := by
  unfold κJ
  split_ifs
  · simp only [norm_zero]; positivity
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.lam_pos i))]
    exact inv_anti₀ (pow_pos D.hm 2) (D.hlam i)

theorem PJ_apply_basis (J : Finset ι) (i : ι) :
    D.PJ J (D.b i) = (if i ∈ J then (1 : ℂ) else 0) • D.b i :=
  diagOp_apply_basis D.b _ 1 (fun i => by split_ifs <;> simp) i

omit [DecidableEq ι] in
theorem B_basis_norm (j : ι) : ‖D.B (D.b j)‖ ≤ D.b₁ / D.ω j := by
  have h := D.B_sum_bound {j} (fun _ => 1)
  simp only [Finset.sum_singleton, one_smul, norm_one, one_pow] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_div' _ (D.lam_pos j).le, Real.sqrt_one, ← div_eq_mul_one_div, ω]

/-- Away from the eigenvalues outside `J`. -/
theorem window_far (J : Finset ι) {ω : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ i ∉ J, r ≤ ‖(D.ω i : ℂ) - ω‖ ∧ r ≤ ‖(D.ω i : ℂ) + ω‖) (hb : D.b₁ / r ≤ 1 / 2) :
    IsUnit (1 - ω ^ 2 • D.KJ J) ∧ IsUnit (D.AJ J (ω ^ 2)) ∧
      ‖Ring.inverse (D.AJ J (ω ^ 2))‖ ≤ 2 := by
  classical
  set ψ : ι → ℂ := fun i => if i ∈ J then 1 else (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2)
  have hlow : ∀ i ∉ J, r * D.ω i ≤ ‖(D.lam i : ℂ) - ω ^ 2‖ :=
    fun i hi => D.norm_lam_sub_sq_ge hr i (h i hi).1 (h i hi).2
  have hne : ∀ i ∉ J, (D.lam i : ℂ) - ω ^ 2 ≠ 0 := fun i hi e => by
    have := hlow i hi; rw [e, norm_zero] at this; nlinarith [D.ω_pos i]
  have hlamne : ∀ i, (D.lam i : ℂ) ≠ 0 := fun i => by exact_mod_cast (D.lam_pos i).ne'
  have e1 : ∀ i ∉ J, 1 - ω ^ 2 * D.κJ J i = ((D.lam i : ℂ) - ω ^ 2) / D.lam i := by
    intro i hi; simp only [κJ, hi, ↓reduceIte]; push_cast; field_simp [hlamne i]
  have hz : ∀ i, 1 - ω ^ 2 * D.κJ J i ≠ 0 := by
    intro i
    by_cases hi : i ∈ J
    · simp [κJ, hi]
    · rw [e1 i hi]; exact div_ne_zero (hne i hi) (hlamne i)
  have e2 : ∀ i, (1 - ω ^ 2 * D.κJ J i)⁻¹ = ψ i := by
    intro i
    by_cases hi : i ∈ J
    · simp [κJ, ψ, hi]
    · simp only [ψ, hi, ↓reduceIte]; rw [e1 i hi, inv_div]
  have hψ : ∀ i, ‖ψ i‖ ≤ 1 + ‖ω‖ ^ 2 / (r * D.m) := by
    intro i
    by_cases hi : i ∈ J
    · simp only [ψ, hi, ↓reduceIte, norm_one]
      have : 0 ≤ ‖ω‖ ^ 2 / (r * D.m) := by have := D.hm; positivity
      linarith
    · simp only [ψ, hi, ↓reduceIte]
      have e3 : (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2) = 1 + ω ^ 2 / ((D.lam i : ℂ) - ω ^ 2) := by
        field_simp [hne i hi]; ring
      rw [e3]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div, norm_pow]
      gcongr
      · exact mul_pos hr D.hm
      · exact (mul_le_mul_of_nonneg_left (D.m_le_ω i) hr.le).trans (hlow i hi)
  obtain ⟨hu, hinv⟩ := D.isUnit_one_sub_diag (D.κJ J) _ (D.norm_κJ_le J) (ω ^ 2) _ hz
    (fun i => by rw [e2]; exact hψ i)
  refine ⟨hu, ?_⟩
  set ψ' : ι → ℂ := fun i => if i ∈ J then 0 else (D.lam i : ℂ) / ((D.lam i : ℂ) - ω ^ 2)
  have hψ'b : ∀ i, ‖ψ' i‖ ≤ 1 + ‖ω‖ ^ 2 / (r * D.m) := by
    intro i
    by_cases hi : i ∈ J
    · simp only [ψ', hi, ↓reduceIte, norm_zero]; have := D.hm; positivity
    · have := hψ i; simp only [ψ, hi, ↓reduceIte] at this; simpa [ψ', hi] using this
  have hψ'ω : ∀ i, ‖ψ' i‖ ≤ r⁻¹ * D.ω i := by
    intro i
    by_cases hi : i ∈ J
    · simp only [ψ', hi, ↓reduceIte, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hr.le) (D.ω_pos i).le
    · simp only [ψ', hi, ↓reduceIte]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (D.lam_pos i),
        div_le_iff₀ (by have := hlow i hi; nlinarith [D.ω_pos i])]
      calc D.lam i = r⁻¹ * D.ω i * (r * D.ω i) := by
            rw [← D.ω_sq]; field_simp
        _ ≤ r⁻¹ * D.ω i * ‖(D.lam i : ℂ) - ω ^ 2‖ := by
            gcongr
            · exact mul_nonneg (inv_nonneg.mpr hr.le) (D.ω_pos i).le
            · exact hlow i hi
  have hdiff : Ring.inverse (1 - ω ^ 2 • D.KJ J) - D.PJ J = diagOp D.b ψ' := by
    rw [KJ, hinv]
    apply clm_ext_basis D.b
    intro i
    rw [sub_apply, diagOp_apply_basis D.b _ _ (fun i => by rw [e2]; exact hψ i),
      D.PJ_apply_basis, diagOp_apply_basis D.b _ _ hψ'b, ← sub_smul, e2]
    congr 1
    by_cases hi : i ∈ J <;> simp [ψ, ψ', hi]
  have hX : ‖D.B * (Ring.inverse (1 - ω ^ 2 • D.KJ J) - D.PJ J)‖ ≤ 1 / 2 := by
    rw [hdiff]
    refine (D.norm_B_mul_diag ψ' r⁻¹ _ (inv_nonneg.mpr hr.le) hψ'b hψ'ω).trans ?_
    rw [← div_eq_mul_inv]; exact hb
  obtain ⟨hw, hwn⟩ := isUnit_one_add_of_norm_le _ (q := 1 / 2) (by norm_num) hX
    ContinuousLinearMap.norm_id_le
  refine ⟨hw, ?_⟩
  rw [AJ]; norm_num at hwn ⊢; exact hwn

omit [CompleteSpace H] in
theorem inv_apply_of_eigen {T : H →L[ℂ] H} (hT : IsUnit T) {v : H} (hv : v ≠ 0) {μ : ℂ}
    (h : T v = μ • v) : μ ≠ 0 ∧ Ring.inverse T v = μ⁻¹ • v := by
  obtain ⟨L, rfl⟩ := hT
  have h2 := congrArg (fun u => (↑L⁻¹ : H →L[ℂ] H) u) h
  simp only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_smul] at h2
  have hμ : μ ≠ 0 := by
    rintro rfl; rw [zero_smul] at h2; exact hv h2
  refine ⟨hμ, ?_⟩
  rw [Ring.inverse_unit]
  have h3 := congrArg (fun u => μ⁻¹ • u) h2
  simp only [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h3
  exact h3.symm

theorem KJ_apply_basis (J : Finset ι) (i : ι) : D.KJ J (D.b i) = D.κJ J i • D.b i :=
  diagOp_apply_basis D.b _ _ (D.norm_κJ_le J) i

/-- The resolvent of `G` split along `J`. -/
theorem inv_one_sub_K_eq (J : Finset ι) {z : ℂ} (hz : IsUnit (1 - z • D.K₀))
    (hzJ : IsUnit (1 - z • D.KJ J)) :
    Ring.inverse (1 - z • D.K₀) = Ring.inverse (1 - z • D.KJ J) - D.PJ J +
      ∑ j : J, ((D.lam j : ℂ) / ((D.lam j : ℂ) - z)) •
        (innerSL ℂ (D.b j)).smulRight (D.b j) := by
  apply clm_ext_basis D.b
  intro i
  obtain ⟨hne, h0⟩ := D.inv_one_sub_apply_basis hz i
  have hlamne : (D.lam i : ℂ) ≠ 0 := by exact_mod_cast (D.lam_pos i).ne'
  have hJi : (1 - z • D.KJ J) (D.b i) = (1 - z * D.κJ J i) • D.b i := by
    rw [sub_apply, one_apply_eq_self, smul_apply, D.KJ_apply_basis, smul_smul, sub_smul,
      one_smul]
  obtain ⟨-, h1⟩ := inv_apply_of_eigen hzJ (D.b.orthonormal.ne_zero i) hJi
  have hsum : (∑ j : J, ((D.lam j : ℂ) / ((D.lam j : ℂ) - z)) •
      (innerSL ℂ (D.b j)).smulRight (D.b j)) (D.b i) =
      if i ∈ J then ((D.lam i : ℂ) / ((D.lam i : ℂ) - z)) • D.b i else 0 := by
    rw [sum_apply]
    simp only [smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    split_ifs with hi
    · rw [Fintype.sum_eq_single ⟨i, hi⟩]
      · simp [inner_self_eq_norm_sq_to_K, D.b.orthonormal.1 i]
      · intro j hj
        have : (j : ι) ≠ i := fun e => hj (Subtype.ext e)
        rw [orthonormal_iff_ite.mp D.b.orthonormal j i, ite_eq_right this, zero_smul, smul_zero]
    · apply Finset.sum_eq_zero
      intro j _
      have : (j : ι) ≠ i := fun e => hi (e ▸ j.2)
      rw [orthonormal_iff_ite.mp D.b.orthonormal j i, ite_eq_right this, zero_smul, smul_zero]
  rw [h0, add_apply, sub_apply, h1, D.PJ_apply_basis, hsum]
  by_cases hi : i ∈ J
  · simp only [κJ, hi, ↓reduceIte, mul_zero, sub_zero, inv_one, one_smul, sub_self, zero_add]
  · simp only [κJ, hi, ↓reduceIte, zero_smul, sub_zero, add_zero]
    congr 1
    push_cast
    field_simp

/-- `1 + N(z) = A_J(z) + ∑_{j ∈ J} c_j ⟨b_j, ·⟩ B b_j`. -/
theorem one_add_N_eq (J : Finset ι) {z : ℂ} (hz : IsUnit (1 - z • D.K₀))
    (hzJ : IsUnit (1 - z • D.KJ J)) :
    1 + D.N z = D.AJ J z + ∑ j : J, ((D.lam j : ℂ) / ((D.lam j : ℂ) - z)) •
      (innerSL ℂ (D.b j)).smulRight (D.B (D.b j)) := by
  rw [N, D.inv_one_sub_K_eq J hz hzJ, AJ, mul_add, add_assoc, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm]
  congr 1
  ext v
  simp

end MMData

end Involution
