module

public import Involution.MMWindow
public import Involution.MMMinModulus

/-! Cut points inside a window with boundedly many eigenvalues (Wyss, Proposition 5.5, in the
variable `ω = √z`): the eigenvalues in the window are split off (`A_J`), the remaining
finite-rank perturbation is handled by the Woodbury formula, whose determinant is a bounded
holomorphic function of `ω`, bounded below at a reference point high above the axis; the
minimum-modulus lemma gives a vertical segment on which it is bounded below. -/

@[expose] public noncomputable section

open Complex Set Metric

namespace Involution

namespace MMData

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : MMData ι H) [DecidableEq ι]

theorem differentiableAt_AJ_entry (J : Finset ι) {ω₀ : ℂ} (h1 : IsUnit (1 - ω₀ ^ 2 • D.KJ J))
    (h2 : IsUnit (D.AJ J (ω₀ ^ 2))) (v w : H) :
    DifferentiableAt ℂ (fun ω : ℂ => inner ℂ w (Ring.inverse (D.AJ J (ω ^ 2)) v)) ω₀ := by
  have hg : DifferentiableAt ℂ (fun ω : ℂ => (1 : H →L[ℂ] H) - ω ^ 2 • D.KJ J) ω₀ := by
    fun_prop
  have hi1 : DifferentiableAt ℂ
      (fun ω : ℂ => Ring.inverse ((1 : H →L[ℂ] H) - ω ^ 2 • D.KJ J)) ω₀ := by
    have := differentiableAt_inverse (𝕜 := ℂ) h1
    exact this.comp (f := fun ω : ℂ => (1 : H →L[ℂ] H) - ω ^ 2 • D.KJ J) ω₀ hg
  have hA : DifferentiableAt ℂ (fun ω : ℂ => D.AJ J (ω ^ 2)) ω₀ := by
    unfold AJ
    exact (differentiableAt_const _).add
      ((differentiableAt_const _).mul (hi1.sub (differentiableAt_const _)))
  have hi2 : DifferentiableAt ℂ (fun ω : ℂ => Ring.inverse (D.AJ J (ω ^ 2))) ω₀ := by
    have := differentiableAt_inverse (𝕜 := ℂ) h2
    exact this.comp (f := fun ω : ℂ => D.AJ J (ω ^ 2)) ω₀ hA
  have hap : DifferentiableAt ℂ (fun ω : ℂ => Ring.inverse (D.AJ J (ω ^ 2)) v) ω₀ :=
    hi2.clm_apply (differentiableAt_const v)
  exact ((innerSL ℂ w).differentiableAt).comp ω₀ hap

omit [DecidableEq ι] in
theorem differentiableAt_det {n : Type*} [Fintype n] [DecidableEq n] (M : ℂ → Matrix n n ℂ)
    {ω₀ : ℂ} (h : ∀ i j, DifferentiableAt ℂ (fun ω => M ω i j) ω₀) :
    DifferentiableAt ℂ (fun ω => (M ω).det) ω₀ := by
  simp only [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_smul ?_ _
  exact DifferentiableAt.fun_finsetProd fun i _ => h _ _

/-- Scaled diagonal entries `x₀ (1 - ω²/λ_j)`. -/
def dW (x₀ : ℝ) (ω : ℂ) (j : ι) : ℂ := x₀ * (((D.lam j : ℂ) - ω ^ 2) / D.lam j)

/-- Their reciprocals. -/
def cW (x₀ : ℝ) (ω : ℂ) (j : ι) : ℂ := (D.lam j : ℂ) / (x₀ * ((D.lam j : ℂ) - ω ^ 2))

/-- Scaled vectors `x₀ B b_j`. -/
def uW (x₀ : ℝ) (j : ι) : H := (x₀ : ℂ) • D.B (D.b j)

/-- The Woodbury matrix. -/
def ZW (J : Finset ι) (x₀ : ℝ) (ω : ℂ) : Matrix J J ℂ :=
  Matrix.diagonal (fun j : J => D.dW x₀ ω j) +
    Matrix.of (fun (k j : J) => innerSL ℂ (D.b k) (Ring.inverse (D.AJ J (ω ^ 2)) (D.uW x₀ j)))

omit [DecidableEq ι] in
theorem cW_mul_dW {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {ω : ℂ} {j : ι} (h : (D.lam j : ℂ) - ω ^ 2 ≠ 0) :
    D.cW x₀ ω j * D.dW x₀ ω j = 1 := by
  have hl : (D.lam j : ℂ) ≠ 0 := by exact_mod_cast (D.lam_pos j).ne'
  have hx : (x₀ : ℂ) ≠ 0 := by exact_mod_cast hx₀
  unfold cW dW
  field_simp

/-- `1 + N(ω²) = A_J + ∑ c_j ⟨b_j, ·⟩ (x₀ B b_j)`. -/
theorem one_add_N_eq_W (J : Finset ι) {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {ω : ℂ}
    (hz : IsUnit (1 - ω ^ 2 • D.K₀)) (hzJ : IsUnit (1 - ω ^ 2 • D.KJ J)) :
    1 + D.N (ω ^ 2) = D.AJ J (ω ^ 2) +
      ∑ j : J, D.cW x₀ ω j • (innerSL ℂ (D.b j)).smulRight (D.uW x₀ j) := by
  rw [D.one_add_N_eq J hz hzJ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : (x₀ : ℂ) ≠ 0 := by exact_mod_cast hx₀
  ext v
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply, uW, smul_smul, cW]
  congr 1
  field_simp

omit [DecidableEq ι] in
theorem lam_sub_ne {z : ℂ} (hz : IsUnit (1 - z • D.K₀)) (j : ι) : (D.lam j : ℂ) - z ≠ 0 :=
  (D.inv_one_sub_apply_basis hz j).1

/-- Invertibility of `1 + N(ω²)` from the non-vanishing of the Woodbury determinant. -/
theorem isUnit_of_det (J : Finset ι) {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {ω : ℂ}
    (hz : IsUnit (1 - ω ^ 2 • D.K₀)) (hzJ : IsUnit (1 - ω ^ 2 • D.KJ J))
    (hA : IsUnit (D.AJ J (ω ^ 2))) (hdet : (D.ZW J x₀ ω).det ≠ 0) :
    IsUnit (1 + D.N (ω ^ 2)) ∧ ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤
      (1 + ∑ j : J, ∑ k : J, ‖(D.ZW J x₀ ω)⁻¹ j k‖ *
        ‖Ring.inverse (D.AJ J (ω ^ 2)) (D.uW x₀ j)‖) * ‖Ring.inverse (D.AJ J (ω ^ 2))‖ := by
  set A := D.AJ J (ω ^ 2)
  set Ai := Ring.inverse A
  have hdu : IsUnit (D.ZW J x₀ ω).det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨h1, h2⟩ := woodbury A Ai (Ring.mul_inverse_cancel A hA) (Ring.inverse_mul_cancel A hA)
    (fun j : J => D.uW x₀ j) (fun j : J => innerSL ℂ (D.b j)) (fun j : J => D.cW x₀ ω j)
    (fun j : J => D.dW x₀ ω j) (fun j => D.cW_mul_dW hx₀ (D.lam_sub_ne hz j))
    (D.ZW J x₀ ω)⁻¹ (Matrix.mul_nonsing_inv _ hdu) (Matrix.nonsing_inv_mul _ hdu)
  rw [← D.one_add_N_eq_W J hx₀ hz hzJ] at h1 h2
  set Y := (1 - ∑ j : J, ∑ k : J, (D.ZW J x₀ ω)⁻¹ j k •
    (innerSL ℂ (D.b k)).smulRight (Ai (D.uW x₀ j))) * Ai
  let U : (H →L[ℂ] H)ˣ := ⟨_, Y, h1, h2⟩
  have hU : IsUnit (1 + D.N (ω ^ 2)) := U.isUnit
  refine ⟨hU, ?_⟩
  rw [show (1 + D.N (ω ^ 2)) = (U : H →L[ℂ] H) from rfl, Ring.inverse_unit]
  change ‖Y‖ ≤ _
  refine (norm_woodbury_le Ai (fun j : J => D.uW x₀ j) (fun j : J => innerSL ℂ (D.b j))
    (D.ZW J x₀ ω)⁻¹).trans ?_
  gcongr
  · exact ContinuousLinearMap.norm_id_le
  · rw [innerSL_apply_norm, D.b.orthonormal.1, one_mul]

/-- A lower bound for the Woodbury determinant from invertibility of `1 + N(ω²)`. -/
theorem det_lower_of_isUnit (J : Finset ι) {x₀ : ℝ} (hx₀ : x₀ ≠ 0) {ω : ℂ}
    (hz : IsUnit (1 - ω ^ 2 • D.K₀)) (hzJ : IsUnit (1 - ω ^ 2 • D.KJ J))
    (hA : IsUnit (D.AJ J (ω ^ 2))) (hN : IsUnit (1 + D.N (ω ^ 2))) (EQ : ℝ)
    (hEQ : ∀ j k : J, ‖D.cW x₀ ω j‖ + ‖D.cW x₀ ω j‖ * ‖D.cW x₀ ω k‖ *
      (‖Ring.inverse (1 + D.N (ω ^ 2))‖ * ‖D.uW x₀ k‖) ≤ EQ) :
    1 ≤ ‖(D.ZW J x₀ ω).det‖ * ((Fintype.card J).factorial * EQ ^ Fintype.card J) := by
  set A := D.AJ J (ω ^ 2)
  set Ai := Ring.inverse A
  set Xi := Ring.inverse (1 + D.N (ω ^ 2))
  have hX : (A + ∑ j : J, D.cW x₀ ω j • (innerSL ℂ (D.b j)).smulRight (D.uW x₀ j)) * Xi = 1 := by
    rw [← D.one_add_N_eq_W J hx₀ hz hzJ]
    exact Ring.mul_inverse_cancel _ hN
  have hconv := woodbury_converse A Ai (Ring.inverse_mul_cancel A hA)
    (fun j : J => D.uW x₀ j) (fun j : J => innerSL ℂ (D.b j)) (fun j : J => D.cW x₀ ω j)
    (fun j : J => D.dW x₀ ω j) (fun j => D.cW_mul_dW hx₀ (D.lam_sub_ne hz j)) Xi hX
  refine norm_det_ge_of_mul_eq_one _ _ hconv EQ fun j k => ?_
  simp only [Matrix.of_apply]
  refine (norm_sub_le _ _).trans ?_
  refine le_trans (add_le_add ?_ ?_) (hEQ j k)
  · split_ifs <;> simp
  · rw [norm_mul, norm_mul, innerSL_apply_apply]
    gcongr
    refine (norm_inner_le_norm _ _).trans ?_
    rw [D.b.orthonormal.1, one_mul]
    exact ContinuousLinearMap.le_opNorm _ _

omit [DecidableEq ι] in
theorem lam_sub_sq (j : ι) (ω : ℂ) :
    (D.lam j : ℂ) - ω ^ 2 = ((D.ω j : ℂ) - ω) * ((D.ω j : ℂ) + ω) := by
  rw [← D.ω_sq]; push_cast; ring

omit [DecidableEq ι] in
theorem norm_ω_sub_le {j : ι} {x₀ W V : ℝ} {ω : ℂ} (hj : |D.ω j - x₀| ≤ W)
    (hω : ‖ω - x₀‖ ≤ V) : ‖(D.ω j : ℂ) - ω‖ ≤ W + V := by
  have : (D.ω j : ℂ) - ω = ((D.ω j - x₀ : ℝ) : ℂ) - (ω - x₀) := by push_cast; ring
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

omit [DecidableEq ι] in
theorem dW_bound {j : ι} {x₀ W V : ℝ} {ω : ℂ} (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hx : 2 * (W + V) ≤ x₀) (hj : |D.ω j - x₀| ≤ W) (hω : ‖ω - x₀‖ ≤ V) :
    ‖D.dW x₀ ω j‖ ≤ 16 * (W + V) := by
  have hj' := abs_le.mp hj
  have hωj : x₀ / 2 ≤ D.ω j := by linarith
  have hx0 : 0 < x₀ := by have := D.ω_pos j; linarith
  have h1 := D.norm_ω_sub_le hj hω
  have h2 : ‖(D.ω j : ℂ) + ω‖ ≤ 4 * x₀ := by
    have : (D.ω j : ℂ) + ω = ((2 * D.ω j : ℝ) : ℂ) - ((D.ω j : ℂ) - ω) := by push_cast; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hl : (0 : ℝ) < D.lam j := D.lam_pos j
  rw [dW, norm_mul, norm_div, D.lam_sub_sq, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hl, ← D.ω_sq]
  have hp : 0 < D.ω j ^ 2 := pow_pos (D.ω_pos j) 2
  rw [mul_div_assoc', div_le_iff₀ hp]
  have hsq : x₀ ^ 2 / 4 ≤ D.ω j ^ 2 := by nlinarith
  calc x₀ * (‖(D.ω j : ℂ) - ω‖ * ‖(D.ω j : ℂ) + ω‖) ≤ x₀ * ((W + V) * (4 * x₀)) := by
        gcongr
    _ = 16 * (W + V) * (x₀ ^ 2 / 4) := by ring
    _ ≤ 16 * (W + V) * D.ω j ^ 2 := by gcongr

omit [DecidableEq ι] in
theorem uW_bound {j : ι} {x₀ : ℝ} (hx0 : 0 < x₀) (hj : x₀ / 2 ≤ D.ω j) :
    ‖D.uW x₀ j‖ ≤ 2 * D.b₁ := by
  rw [uW, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have h := D.B_basis_norm j
  have hω := D.ω_pos j
  calc x₀ * ‖D.B (D.b j)‖ ≤ x₀ * (D.b₁ / D.ω j) := by gcongr
    _ = D.b₁ * (x₀ / D.ω j) := by ring
    _ ≤ D.b₁ * 2 := by
        gcongr
        · exact D.hb₁
        · rw [div_le_iff₀ hω]; linarith
    _ = 2 * D.b₁ := by ring

omit [DecidableEq ι] in
theorem cW_bound_at {j : ι} {x₀ y₀ : ℝ} (hx0 : 0 < x₀) (hy₀ : 0 < y₀) (hj : D.ω j ≤ 2 * x₀) :
    ‖D.cW x₀ ((x₀ : ℂ) + y₀ * I) j‖ ≤ 4 / y₀ := by
  set c : ℂ := (x₀ : ℂ) + y₀ * I
  have h1 : y₀ ≤ ‖(D.ω j : ℂ) - c‖ := by
    refine le_trans ?_ (abs_im_le_norm _)
    simp [c, abs_of_pos hy₀]
  have h2 : x₀ ≤ ‖(D.ω j : ℂ) + c‖ := by
    refine le_trans ?_ (abs_re_le_norm _)
    simp only [c, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    rw [abs_of_pos (by linarith [D.ω_pos j])]
    linarith [D.ω_pos j]
  have hl : (0 : ℝ) < D.lam j := D.lam_pos j
  rw [cW, norm_div, norm_mul, D.lam_sub_sq, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hl, ← D.ω_sq]
  have hpos : 0 < x₀ * (y₀ * x₀) := by positivity
  have hm : y₀ * x₀ ≤ ‖(D.ω j : ℂ) - c‖ * ‖(D.ω j : ℂ) + c‖ :=
    mul_le_mul h1 h2 hx0.le (norm_nonneg _)
  rw [div_le_div_iff₀ (lt_of_lt_of_le hpos (mul_le_mul_of_nonneg_left hm hx0.le)) hy₀]
  have hω2 : D.ω j ^ 2 ≤ 4 * x₀ ^ 2 := by nlinarith [D.ω_pos j]
  calc D.ω j ^ 2 * y₀ ≤ 4 * x₀ ^ 2 * y₀ := by gcongr
    _ = 4 * (x₀ * (y₀ * x₀)) := by ring
    _ ≤ 4 * (x₀ * (‖(D.ω j : ℂ) - c‖ * ‖(D.ω j : ℂ) + c‖)) := by gcongr

omit [DecidableEq ι] in
theorem far_outside {i : ι} {x₀ W V r : ℝ} {ω : ℂ} (hi : W ≤ |D.ω i - x₀|)
    (hω : ‖ω - x₀‖ ≤ V) (hWV : r ≤ W - V) (hx : r + V ≤ x₀) :
    r ≤ ‖(D.ω i : ℂ) - ω‖ ∧ r ≤ ‖(D.ω i : ℂ) + ω‖ := by
  constructor
  · have e : (D.ω i : ℂ) - ω = ((D.ω i - x₀ : ℝ) : ℂ) - (ω - x₀) := by push_cast; ring
    have := norm_sub_norm_le ((D.ω i - x₀ : ℝ) : ℂ) (ω - x₀)
    rw [Complex.norm_real, Real.norm_eq_abs, ← e] at this
    linarith
  · have h1 : |(ω - x₀).re| ≤ ‖ω - x₀‖ := abs_re_le_norm _
    have h2 : (ω - x₀).re = ω.re - x₀ := by simp
    rw [h2] at h1
    have h3 := (abs_le.mp h1).1
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [add_re, ofReal_re]
    have := D.ω_pos i
    linarith

theorem ZW_entry_le (J : Finset ι) (x₀ : ℝ) (ω : ℂ) {E₁ E₂ : ℝ} (hE₁ : 0 ≤ E₁)
    (hd : ∀ j : J, ‖D.dW x₀ ω j‖ ≤ E₁)
    (hu : ∀ j : J, ‖Ring.inverse (D.AJ J (ω ^ 2)) (D.uW x₀ j)‖ ≤ E₂) (k j : J) :
    ‖D.ZW J x₀ ω k j‖ ≤ E₁ + E₂ := by
  rw [ZW, Matrix.add_apply, Matrix.of_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; exact hd k
    · simpa using hE₁
  · rw [innerSL_apply_apply]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [D.b.orthonormal.1, one_mul]
    exact hu j

theorem differentiableAt_ZW_det (J : Finset ι) (x₀ : ℝ) {ω₀ : ℂ}
    (h1 : IsUnit (1 - ω₀ ^ 2 • D.KJ J)) (h2 : IsUnit (D.AJ J (ω₀ ^ 2))) :
    DifferentiableAt ℂ (fun ω => (D.ZW J x₀ ω).det) ω₀ := by
  refine differentiableAt_det _ fun k j => ?_
  simp only [ZW, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply, innerSL_apply_apply]
  refine DifferentiableAt.add ?_ (D.differentiableAt_AJ_entry J h1 h2 _ _)
  split_ifs
  · unfold dW; fun_prop
  · exact differentiableAt_const _

omit [DecidableEq ι] in
theorem card_factorial_pow_le {n Mp : ℕ} (h : n ≤ Mp) {X : ℝ} (hX : 1 ≤ X) :
    (n.factorial : ℝ) * X ^ n ≤ Mp.factorial * X ^ Mp := by
  have h1 : (n.factorial : ℝ) ≤ Mp.factorial := by exact_mod_cast Nat.factorial_le h
  have h2 : X ^ n ≤ X ^ Mp := pow_le_pow_right₀ hX h
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

end MMData

/-- Half-width of the windows. -/
def winW (β : ℝ) : ℝ := 6 * (2 * β + 1) + 6

namespace MMData

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Inside a window `|ω - x₀| < winW β` containing at most `Mp` of the `ω i`, there is a cut
point `x` with `|x - x₀| ≤ 1`, uniformly separated from all `ω i`, such that
`‖(1 + N(ω²))⁻¹‖` is uniformly bounded on the segment `Re ω = x`, `|Im ω| ≤ 2β + 1`. -/
theorem window_cut (β : ℝ) (hβ : 0 ≤ β) (Mp : ℕ) :
    ∃ X₀ ε CW : ℝ, 0 < ε ∧ 2 ≤ CW ∧ ∀ D : MMData ι H, D.b₁ = β → ∀ x₀ : ℝ, X₀ ≤ x₀ →
      ∀ J : Finset ι, (∀ i, i ∈ J ↔ |D.ω i - x₀| < winW β) → J.card ≤ Mp →
      ∃ x : ℝ, |x - x₀| ≤ 1 ∧ (∀ i, ε ≤ |x - D.ω i|) ∧ ∀ y : ℝ, |y| ≤ 2 * β + 1 →
        IsUnit (1 + D.N (((x : ℂ) + y * I) ^ 2)) ∧
        ‖Ring.inverse (1 + D.N (((x : ℂ) + y * I) ^ 2))‖ ≤ CW := by
  classical
  set α := 2 * β + 1 with hα
  have hα0 : 0 < α := by linarith
  set R₃ := 2 * (1 + α + α) + 4 with hR₃
  set W := winW β with hWdef
  have hW : W = α + R₃ + α := by simp only [W, winW, R₃, α]; ring
  set V := R₃ + α with hV
  have hV0 : 0 ≤ V := by positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  set E := 16 * (W + V) + 2 * (2 * β) + 1 with hE
  have hE1 : 1 ≤ E := by have : 0 ≤ 16 * (W + V) + 2 * (2 * β) := by positivity
                         linarith
  set EQ := 4 / α + 4 / α * (4 / α) * (2 * (2 * β)) + 1 with hEQ
  have hEQ1 : 1 ≤ EQ := by have : 0 ≤ 4 / α + 4 / α * (4 / α) * (2 * (2 * β)) := by positivity
                           linarith
  set Cu := (Mp.factorial : ℝ) * E ^ Mp with hCu
  have hCu0 : 0 < Cu := by positivity
  set δ := 1 / ((Mp.factorial : ℝ) * EQ ^ Mp) with hδ
  obtain ⟨ε₀, hε₀, κ, hκ, hmm⟩ := min_modulus_segment 1 α α Cu δ Mp one_pos hα0.le hα0.le
    (by positivity)
  set X₀ := 2 * (W + V) + α + 2 with hX₀
  set CW := max 2 ((1 + (Mp : ℝ) * Mp * (Cu / κ * (2 * (2 * β)))) * 2) with hCW
  refine ⟨X₀, min ε₀ 1, CW, lt_min hε₀ one_pos, le_max_left _ _, ?_⟩
  intro D hD x₀ hx₀ J hJ hJc
  have hx0 : 0 < x₀ := by linarith
  have hb : D.b₁ / α ≤ 1 / 2 := by
    rw [hD, div_le_iff₀ hα0]; linarith
  set c : ℂ := (x₀ : ℂ) + α * I with hc
  have hcx : ‖c - x₀‖ = α := by
    simp [c, abs_of_pos hα0]
  have hballV : ∀ ω ∈ ball c R₃, ‖ω - x₀‖ ≤ V := by
    intro ω hω
    have h1 : ‖ω - c‖ < R₃ := by simpa [dist_eq_norm] using hω
    have : ω - x₀ = (ω - c) + (c - x₀) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [hcx]; linarith
  have hfarJ : ∀ ω : ℂ, ‖ω - x₀‖ ≤ V → ∀ i ∉ J,
      α ≤ ‖(D.ω i : ℂ) - ω‖ ∧ α ≤ ‖(D.ω i : ℂ) + ω‖ := by
    intro ω hω i hi
    have hi' : W ≤ |D.ω i - x₀| := by
      by_contra h; push Not at h; exact hi ((hJ i).mpr h)
    exact D.far_outside hi' hω (by linarith) (by linarith)
  have hwin : ∀ ω : ℂ, ‖ω - x₀‖ ≤ V → IsUnit (1 - ω ^ 2 • D.KJ J) ∧
      IsUnit (D.AJ J (ω ^ 2)) ∧ ‖Ring.inverse (D.AJ J (ω ^ 2))‖ ≤ 2 :=
    fun ω hω => D.window_far J hα0 (hfarJ ω hω) hb
  have hjW : ∀ j : J, |D.ω j - x₀| ≤ W := fun j => ((hJ j).mp j.2).le
  have hjlo : ∀ j : J, x₀ / 2 ≤ D.ω j := by
    intro j; have := (abs_le.mp (hjW j)).1; linarith
  have hjhi : ∀ j : J, D.ω j ≤ 2 * x₀ := by
    intro j; have := (abs_le.mp (hjW j)).2; linarith
  have huW : ∀ j : J, ‖D.uW x₀ j‖ ≤ 2 * β := fun j => hD ▸ D.uW_bound hx0 (hjlo j)
  have hu : ∀ ω : ℂ, ‖ω - x₀‖ ≤ V → ∀ j : J,
      ‖Ring.inverse (D.AJ J (ω ^ 2)) (D.uW x₀ j)‖ ≤ 2 * (2 * β) := by
    intro ω hω j
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul (hwin ω hω).2.2 (huW j) (norm_nonneg _) (by norm_num)
  have hent : ∀ ω : ℂ, ‖ω - x₀‖ ≤ V → ∀ k j : J, ‖D.ZW J x₀ ω k j‖ ≤ E := by
    intro ω hω k j
    refine (D.ZW_entry_le J x₀ ω (E₁ := 16 * (W + V)) (by positivity)
      (fun j => D.dW_bound hW0 hV0 (by linarith) (hjW j) hω) (hu ω hω) k j).trans ?_
    linarith
  have hcard : Fintype.card J ≤ Mp := by rw [Fintype.card_coe]; exact hJc
  set f : ℂ → ℂ := fun ω => (D.ZW J x₀ ω).det with hf
  have hfd : DifferentiableOn ℂ f (ball c R₃) := by
    intro ω hω
    have h := hwin ω (hballV ω hω)
    exact (D.differentiableAt_ZW_det J x₀ h.1 h.2.1).differentiableWithinAt
  have hfC : ∀ ω ∈ ball c R₃, ‖f ω‖ ≤ Cu := by
    intro ω hω
    exact (norm_det_le _ E (hent ω (hballV ω hω))).trans (card_factorial_pow_le hcard hE1)
  -- the reference point
  have hfar_c : ∀ i, α ≤ ‖(D.ω i : ℂ) - c‖ ∧ α ≤ ‖(D.ω i : ℂ) + c‖ := by
    intro i
    constructor
    · refine le_trans ?_ (abs_im_le_norm _)
      simp [c, abs_of_pos hα0]
    · refine le_trans ?_ (abs_im_le_norm _)
      simp [c, abs_of_pos hα0]
  obtain ⟨hzc, hNc, hNcn, -⟩ := D.good_far hα0 hfar_c hb
  have hδc : δ ≤ ‖f c‖ := by
    have hwc := hwin c (by rw [hcx]; linarith)
    have h1 := D.det_lower_of_isUnit J hx0.ne' hzc hwc.1 hwc.2.1 hNc EQ (by
      intro j k
      have hcj := D.cW_bound_at hx0 hα0 (hjhi j)
      have hck := D.cW_bound_at hx0 hα0 (hjhi k)
      have : ‖D.cW x₀ c j‖ + ‖D.cW x₀ c j‖ * ‖D.cW x₀ c k‖ *
          (‖Ring.inverse (1 + D.N (c ^ 2))‖ * ‖D.uW x₀ k‖) ≤
          4 / α + 4 / α * (4 / α) * (2 * (2 * β)) := by
        gcongr
        exact huW k
      linarith)
    have h2 := card_factorial_pow_le hcard hEQ1
    rw [hδ, div_le_iff₀ (by positivity)]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  set pts : Finset ℝ := J.image D.ω with hpts
  have hptsc : pts.card ≤ Mp := Finset.card_image_le.trans hJc
  obtain ⟨x, hx, hsep, hlow⟩ := hmm x₀ f pts hptsc hfd hfC hδc
  have hsepall : ∀ i, min ε₀ 1 ≤ |x - D.ω i| := by
    intro i
    by_cases hi : i ∈ J
    · exact (min_le_left _ _).trans (hsep _ (Finset.mem_image_of_mem _ hi))
    · have hi' : W ≤ |D.ω i - x₀| := by
        by_contra h; push Not at h; exact hi ((hJ i).mpr h)
      refine (min_le_right _ _).trans ?_
      have := abs_sub_abs_le_abs_sub (D.ω i - x₀) (x - x₀)
      rw [show D.ω i - x₀ - (x - x₀) = -(x - D.ω i) by ring, abs_neg] at this
      linarith
  refine ⟨x, hx, hsepall, fun y hy => ?_⟩
  set ω : ℂ := (x : ℂ) + y * I with hω
  have hωV : ‖ω - x₀‖ ≤ V := by
    have e : ω - x₀ = ((x - x₀ : ℝ) : ℂ) + y * I := by simp [ω]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hz : IsUnit (1 - ω ^ 2 • D.K₀) := by
    refine (D.far (lt_min hε₀ one_pos) fun i => ⟨?_, ?_⟩).1
    · refine (hsepall i).trans (le_trans (le_of_eq ?_) (abs_re_le_norm _))
      simp [ω, abs_sub_comm]
    · refine (min_le_right _ _).trans (le_trans ?_ (Complex.re_le_norm _))
      simp only [ω, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      have := D.ω_pos i
      have := (abs_le.mp hx).1
      linarith
  have hwω := hwin ω hωV
  have hlowω := hlow y hy
  have hdet : f ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hlowω; linarith
  obtain ⟨hU, hUn⟩ := D.isUnit_of_det J hx0.ne' hz hwω.1 hwω.2.1 hdet
  refine ⟨hU, hUn.trans ?_⟩
  have hQ : ∀ j k : J, ‖(D.ZW J x₀ ω)⁻¹ j k‖ ≤ Cu / κ := by
    intro j k
    have h1 := norm_inv_apply_le (D.ZW J x₀ ω) E hE1 (hent ω hωV) j k
    have h2 := card_factorial_pow_le hcard hE1
    rw [le_div_iff₀ hκ]
    calc ‖(D.ZW J x₀ ω)⁻¹ j k‖ * κ ≤ ‖(D.ZW J x₀ ω)⁻¹ j k‖ * ‖f ω‖ := by gcongr
      _ ≤ Cu := h1.trans h2
  have hsum : ∑ j : J, ∑ k : J, ‖(D.ZW J x₀ ω)⁻¹ j k‖ *
      ‖Ring.inverse (D.AJ J (ω ^ 2)) (D.uW x₀ j)‖ ≤
      (Mp : ℝ) * Mp * (Cu / κ * (2 * (2 * β))) := by
    have hterm : ∀ j k : J, ‖(D.ZW J x₀ ω)⁻¹ j k‖ *
        ‖Ring.inverse (D.AJ J (ω ^ 2)) (D.uW x₀ j)‖ ≤ Cu / κ * (2 * (2 * β)) :=
      fun j k => mul_le_mul (hQ j k) (hu ω hωV j) (norm_nonneg _) (by positivity)
    have hcR : (Fintype.card J : ℝ) ≤ Mp := by exact_mod_cast hcard
    calc _ ≤ ∑ _j : J, ∑ _k : J, Cu / κ * (2 * (2 * β)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
      _ = (Fintype.card J : ℝ) * Fintype.card J * (Cu / κ * (2 * (2 * β))) := by
          simp [Finset.sum_const]; ring
      _ ≤ _ := by gcongr
  refine le_trans ?_ (le_max_right _ _)
  exact mul_le_mul (by linarith) hwω.2.2 (norm_nonneg _) (by positivity)

end MMData

end Involution
