module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Точное решение для коэффициента `a(x) = x / 2`. При `s(x) = 1 + i x / 2` функция
`u_t = s^{1/4} exp(-4 t s^{1/2})` (главные ветви, записанные через `exp (log s / 4)` и
`exp (log s / 2)`) удовлетворяет `s · (-u_t'') - t² u_t = -(3/64) s⁻¹ u_t`. -/

@[expose] public noncomputable section

open Complex

namespace Involution

/-- Множитель `s(x) = 1 + i x / 2`. -/
def halfSlopeS (x : ℝ) : ℂ := 1 + I * (x : ℂ) / 2

/-- `s(x)^{1/4}` (главная ветвь). -/
def halfSlopeP (x : ℝ) : ℂ := exp (log (halfSlopeS x) / 4)

/-- `s(x)^{1/2}` (главная ветвь). -/
def halfSlopeW (x : ℝ) : ℂ := exp (log (halfSlopeS x) / 2)

/-- `exp(-4 t s(x)^{1/2})`. -/
def halfSlopeE (t x : ℝ) : ℂ := exp (-4 * (t : ℂ) * halfSlopeW x)

/-- Точное решение `u_t = s^{1/4} exp(-4 t s^{1/2})`. -/
def halfSlopeU (t x : ℝ) : ℂ := halfSlopeP x * halfSlopeE t x

/-- Производная `u_t`. -/
def halfSlopeU1 (t x : ℝ) : ℂ :=
  I / 8 * halfSlopeP x * (halfSlopeS x)⁻¹ * (1 - 8 * (t : ℂ) * halfSlopeW x) * halfSlopeE t x

theorem halfSlopeS_re (x : ℝ) : (halfSlopeS x).re = 1 := by
  simp [halfSlopeS]

theorem halfSlopeS_mem_slitPlane (x : ℝ) : halfSlopeS x ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  rw [halfSlopeS_re]
  norm_num

theorem halfSlopeS_ne_zero (x : ℝ) : halfSlopeS x ≠ 0 :=
  slitPlane_ne_zero (halfSlopeS_mem_slitPlane x)

theorem halfSlopeS_norm_sq (x : ℝ) : ‖halfSlopeS x‖ ^ 2 = 1 + x ^ 2 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [halfSlopeS]
  ring

theorem one_le_halfSlopeS_norm (x : ℝ) : 1 ≤ ‖halfSlopeS x‖ := by
  have h := halfSlopeS_norm_sq x
  have h0 := norm_nonneg (halfSlopeS x)
  nlinarith [sq_nonneg x]

theorem halfSlopeS_norm_le_two {x : ℝ} (hx : |x| ≤ 1) : ‖halfSlopeS x‖ ≤ 2 := by
  have h := halfSlopeS_norm_sq x
  have h0 := norm_nonneg (halfSlopeS x)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  nlinarith

theorem halfSlopeS_hasDerivAt (x : ℝ) : HasDerivAt halfSlopeS (I / 2) x := by
  have dx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  exact (((dx.const_mul I).div_const 2).const_add 1).congr_deriv (by ring)

theorem halfSlopeLog_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => log (halfSlopeS y)) (I / 2 / halfSlopeS x) x :=
  (halfSlopeS_hasDerivAt x).clog_real (halfSlopeS_mem_slitPlane x)

theorem halfSlopeP_hasDerivAt (x : ℝ) :
    HasDerivAt halfSlopeP (I / 8 * halfSlopeP x / halfSlopeS x) x := by
  have := ((halfSlopeLog_hasDerivAt x).div_const 4).cexp
  refine this.congr_deriv ?_
  simp only [halfSlopeP]
  ring

theorem halfSlopeW_hasDerivAt (x : ℝ) :
    HasDerivAt halfSlopeW (I / 4 * halfSlopeW x / halfSlopeS x) x := by
  have := ((halfSlopeLog_hasDerivAt x).div_const 2).cexp
  refine this.congr_deriv ?_
  simp only [halfSlopeW]
  ring

theorem halfSlopeW_eq (x : ℝ) : halfSlopeW x = halfSlopeP x ^ 2 := by
  rw [halfSlopeW, halfSlopeP, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem halfSlopeW_sq (x : ℝ) : halfSlopeW x ^ 2 = halfSlopeS x := by
  rw [halfSlopeW, ← Complex.exp_nat_mul]
  push_cast
  rw [show (2 : ℂ) * (log (halfSlopeS x) / 2) = log (halfSlopeS x) by ring,
    exp_log (halfSlopeS_ne_zero x)]

theorem halfSlopeE_hasDerivAt (t x : ℝ) :
    HasDerivAt (halfSlopeE t)
      (-(I * (t : ℂ)) * halfSlopeW x * halfSlopeE t x / halfSlopeS x) x := by
  have := ((halfSlopeW_hasDerivAt x).const_mul (-4 * (t : ℂ))).cexp
  refine this.congr_deriv ?_
  simp only [halfSlopeE]
  ring

theorem halfSlopeU_hasDerivAt (t x : ℝ) : HasDerivAt (halfSlopeU t) (halfSlopeU1 t x) x := by
  have := (halfSlopeP_hasDerivAt x).mul (halfSlopeE_hasDerivAt t x)
  refine this.congr_deriv ?_
  simp only [halfSlopeU1]
  ring

theorem halfSlopeU1_hasDerivAt (t x : ℝ) :
    HasDerivAt (halfSlopeU1 t)
      (-(t : ℂ) ^ 2 * halfSlopeU t x / halfSlopeS x +
        3 / 64 * halfSlopeU t x / halfSlopeS x ^ 2) x := by
  have hS := halfSlopeS_hasDerivAt x
  have hSinv := hS.inv (halfSlopeS_ne_zero x)
  have hW := halfSlopeW_hasDerivAt x
  have h1 : HasDerivAt (fun y => 1 - 8 * (t : ℂ) * halfSlopeW y)
      (-(8 * (t : ℂ) * (I / 4 * halfSlopeW x / halfSlopeS x))) x :=
    (hW.const_mul (8 * (t : ℂ))).const_sub 1
  have := (((((halfSlopeP_hasDerivAt x).const_mul (I / 8)).mul hSinv).mul h1).mul
    (halfSlopeE_hasDerivAt t x))
  refine this.congr_deriv ?_
  have hS0 := halfSlopeS_ne_zero x
  have hW2 := halfSlopeW_sq x
  simp only [Pi.mul_apply, Pi.inv_apply, halfSlopeU]
  field_simp
  rw [← hW2]
  ring_nf
  rw [I_sq]
  ring

theorem halfSlopeS_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n halfSlopeS :=
  contDiff_const.add ((contDiff_const.mul ofRealCLM.contDiff).div_const 2)

theorem halfSlopeLog_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n (fun y => log (halfSlopeS y)) :=
  contDiff_iff_contDiffAt.2 fun x =>
    ((contDiffAt_log (halfSlopeS_mem_slitPlane x)).restrict_scalars ℝ).comp x
      halfSlopeS_contDiff.contDiffAt

theorem halfSlopeP_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n halfSlopeP :=
  (halfSlopeLog_contDiff.div_const 4).cexp

theorem halfSlopeW_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n halfSlopeW :=
  (halfSlopeLog_contDiff.div_const 2).cexp

theorem halfSlopeE_contDiff {n : WithTop ℕ∞} (t : ℝ) : ContDiff ℝ n (halfSlopeE t) :=
  (contDiff_const.mul halfSlopeW_contDiff).cexp

theorem halfSlopeU_contDiff {n : WithTop ℕ∞} (t : ℝ) : ContDiff ℝ n (halfSlopeU t) :=
  halfSlopeP_contDiff.mul (halfSlopeE_contDiff t)

theorem halfSlopeU1_continuous (t : ℝ) : Continuous (halfSlopeU1 t) := by
  have hSinv : Continuous fun y => (halfSlopeS y)⁻¹ :=
    (halfSlopeS_contDiff (n := 0)).continuous.inv₀ halfSlopeS_ne_zero
  exact ((((continuous_const.mul (halfSlopeP_contDiff (n := 0)).continuous).mul hSinv).mul
    (continuous_const.sub (continuous_const.mul (halfSlopeW_contDiff (n := 0)).continuous))).mul
    (halfSlopeE_contDiff (n := 0) t).continuous)

/-! ### Оценки -/

theorem halfSlopeP_pow_four (x : ℝ) : halfSlopeP x ^ 4 = halfSlopeS x := by
  rw [← halfSlopeW_sq, halfSlopeW_eq]
  ring

theorem halfSlopeP_norm_bounds {x : ℝ} (hx : |x| ≤ 1) :
    1 ≤ ‖halfSlopeP x‖ ∧ ‖halfSlopeP x‖ ≤ 2 := by
  have h4 : ‖halfSlopeP x‖ ^ 4 = ‖halfSlopeS x‖ := by
    rw [← norm_pow, halfSlopeP_pow_four]
  have h1 := one_le_halfSlopeS_norm x
  have h2 := halfSlopeS_norm_le_two hx
  have h0 := norm_nonneg (halfSlopeP x)
  have hge : 1 ≤ ‖halfSlopeP x‖ := by
    by_contra h
    push Not at h
    have : ‖halfSlopeP x‖ ^ 4 < 1 := pow_lt_one₀ h0 h (by norm_num)
    linarith
  refine ⟨hge, ?_⟩
  have : ‖halfSlopeP x‖ ≤ ‖halfSlopeP x‖ ^ 4 := by
    calc ‖halfSlopeP x‖ = ‖halfSlopeP x‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖halfSlopeP x‖ ^ 4 := pow_le_pow_right₀ hge (by norm_num)
  linarith

theorem halfSlopeW_norm_le_two {x : ℝ} (hx : |x| ≤ 1) : ‖halfSlopeW x‖ ≤ 2 := by
  have h2 : ‖halfSlopeW x‖ ^ 2 = ‖halfSlopeS x‖ := by
    rw [← norm_pow, halfSlopeW_sq]
  have := halfSlopeS_norm_le_two hx
  have h0 := norm_nonneg (halfSlopeW x)
  nlinarith

theorem halfSlopeW_re_pos (x : ℝ) : 0 < (halfSlopeW x).re := by
  rw [halfSlopeW, exp_re]
  apply mul_pos (Real.exp_pos _)
  have ha : |arg (halfSlopeS x)| < Real.pi / 2 :=
    abs_arg_lt_pi_div_two_iff.2 (Or.inl (by rw [halfSlopeS_re]; norm_num))
  have him : (log (halfSlopeS x) / 2).im = arg (halfSlopeS x) / 2 := by
    rw [div_ofNat_im, log_im]
  rw [him]
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at ha
  constructor <;> linarith [Real.pi_pos]

theorem halfSlopeW_re_sq (x : ℝ) : (halfSlopeW x).re ^ 2 = (‖halfSlopeS x‖ + 1) / 2 := by
  have h2 : ‖halfSlopeW x‖ ^ 2 = ‖halfSlopeS x‖ := by
    rw [← norm_pow, halfSlopeW_sq]
  have hre : (halfSlopeW x ^ 2).re = 1 := by rw [halfSlopeW_sq, halfSlopeS_re]
  rw [sq, mul_re] at hre
  rw [Complex.sq_norm, normSq_apply] at h2
  nlinarith

theorem halfSlopeW_re_le {x : ℝ} (hx : |x| ≤ 1 / 4) : (halfSlopeW x).re ≤ 1 + 1 / 512 := by
  have h := halfSlopeW_re_sq x
  have hS := halfSlopeS_norm_sq x
  have h0 := norm_nonneg (halfSlopeS x)
  have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith [abs_nonneg x, sq_abs x]
  have hSle : ‖halfSlopeS x‖ ≤ 1 + 1 / 128 := by nlinarith
  have hp := halfSlopeW_re_pos x
  nlinarith

theorem halfSlopeW_re_ge {x : ℝ} (hx : 1 / 2 ≤ |x|) : 1 + 1 / 200 ≤ (halfSlopeW x).re := by
  have h := halfSlopeW_re_sq x
  have hS := halfSlopeS_norm_sq x
  have h0 := norm_nonneg (halfSlopeS x)
  have hx2 : 1 / 4 ≤ x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hSge : 1 + 1 / 40 ≤ ‖halfSlopeS x‖ := by nlinarith
  have hp := halfSlopeW_re_pos x
  nlinarith

theorem halfSlopeE_norm (t x : ℝ) :
    ‖halfSlopeE t x‖ = Real.exp (-4 * t * (halfSlopeW x).re) := by
  rw [halfSlopeE, norm_exp]
  congr 1
  simp

theorem halfSlopeU1_norm_le {t x : ℝ} (ht : 0 ≤ t) (hx : |x| ≤ 1) :
    ‖halfSlopeU1 t x‖ ≤ (1 / 4) * (1 + 16 * t) * ‖halfSlopeE t x‖ := by
  have hP := (halfSlopeP_norm_bounds hx).2
  have hW := halfSlopeW_norm_le_two hx
  have hS := one_le_halfSlopeS_norm x
  have hSinv : ‖(halfSlopeS x)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hS
  have h1 : ‖1 - 8 * (t : ℂ) * halfSlopeW x‖ ≤ 1 + 16 * t := by
    calc ‖1 - 8 * (t : ℂ) * halfSlopeW x‖ ≤ ‖(1 : ℂ)‖ + ‖8 * (t : ℂ) * halfSlopeW x‖ :=
          norm_sub_le _ _
      _ = 1 + 8 * t * ‖halfSlopeW x‖ := by
          rw [norm_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
          norm_num
      _ ≤ 1 + 16 * t := by nlinarith
  have hI : ‖I / 8‖ = 1 / 8 := by simp
  rw [halfSlopeU1, norm_mul, norm_mul, norm_mul, norm_mul, hI]
  have hE := norm_nonneg (halfSlopeE t x)
  have hPn := norm_nonneg (halfSlopeP x)
  have hSn := norm_nonneg (halfSlopeS x)⁻¹
  have h1n := norm_nonneg (1 - 8 * (t : ℂ) * halfSlopeW x)
  calc 1 / 8 * ‖halfSlopeP x‖ * ‖(halfSlopeS x)⁻¹‖ * ‖1 - 8 * (t : ℂ) * halfSlopeW x‖ *
        ‖halfSlopeE t x‖ ≤ 1 / 8 * 2 * 1 * (1 + 16 * t) * ‖halfSlopeE t x‖ := by gcongr
    _ = _ := by ring

/-! ### Срезка -/

/-- Гладкая срезка: `1` на `[-1/2, 1/2]`, `0` в точках `±1`. -/
def halfSlopeCut (x : ℝ) : ℝ :=
  Real.smoothTransition (4 * (3 / 4 - x)) * Real.smoothTransition (4 * (3 / 4 + x))

theorem halfSlopeCut_contDiff {n : ℕ∞} : ContDiff ℝ n halfSlopeCut :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.add contDiff_id)))

theorem halfSlopeCut_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : halfSlopeCut x = 1 := by
  rw [abs_le] at hx
  rw [halfSlopeCut, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem halfSlopeCut_one : halfSlopeCut 1 = 0 := by
  rw [halfSlopeCut, Real.smoothTransition.zero_of_nonpos (by norm_num), zero_mul]

theorem halfSlopeCut_neg_one : halfSlopeCut (-1) = 0 := by
  rw [halfSlopeCut, Real.smoothTransition.zero_of_nonpos (x := 4 * (3 / 4 + -1)) (by norm_num),
    mul_zero]

theorem halfSlopeCut_bounds (x : ℝ) : 0 ≤ halfSlopeCut x ∧ halfSlopeCut x ≤ 1 :=
  ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) zero_le_one).trans (by norm_num)⟩

theorem halfSlopeCut_deriv_vanish {x : ℝ} (hx : |x| < 1 / 2) :
    deriv halfSlopeCut x = 0 ∧ deriv (deriv halfSlopeCut) x = 0 := by
  have hev : halfSlopeCut =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    have hmem : Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ∈ nhds x := by
      rw [abs_lt] at hx
      exact Ioo_mem_nhds hx.1 hx.2
    filter_upwards [hmem] with y hy
    exact halfSlopeCut_eq_one (abs_le.2 ⟨hy.1.le, hy.2.le⟩)
  constructor
  · rw [hev.deriv_eq]
    simp
  · rw [hev.deriv.deriv_eq]
    simp

/-! ### Срезанное решение -/

/-- Срезанное точное решение `Z_t = χ u_t`. -/
def halfSlopeZ (t x : ℝ) : ℂ := (halfSlopeCut x : ℂ) * halfSlopeU t x

/-- Остаток `s (χ'' u_t + 2 χ' u_t')`. -/
def halfSlopeR (t x : ℝ) : ℂ :=
  halfSlopeS x * (((deriv (deriv halfSlopeCut) x : ℝ) : ℂ) * halfSlopeU t x +
    2 * ((deriv halfSlopeCut x : ℝ) : ℂ) * halfSlopeU1 t x)

theorem halfSlopeCut_contDiff_two : ContDiff ℝ 2 halfSlopeCut :=
  halfSlopeCut_contDiff (n := 2)

theorem halfSlopeZ_contDiff (t : ℝ) : ContDiff ℝ 2 (halfSlopeZ t) :=
  (ofRealCLM.contDiff.comp halfSlopeCut_contDiff_two).mul (halfSlopeU_contDiff t)

theorem halfSlopeZ_equation (t x : ℝ) :
    halfSlopeS x * (-deriv (deriv (halfSlopeZ t)) x) - (t : ℂ) ^ 2 * halfSlopeZ t x =
      -(3 / 64) * halfSlopeZ t x / halfSlopeS x - halfSlopeR t x := by
  have h1 : ContDiff ℝ 1 (deriv halfSlopeCut) := ContDiff.deriv' halfSlopeCut_contDiff_two
  have dc : ∀ y, HasDerivAt (fun s : ℝ => (halfSlopeCut s : ℂ))
      ((deriv halfSlopeCut y : ℝ) : ℂ) y :=
    fun y => ((halfSlopeCut_contDiff_two.differentiable (by norm_num)).differentiableAt.hasDerivAt
      ).ofReal_comp
  have dc' : HasDerivAt (fun s : ℝ => ((deriv halfSlopeCut s : ℝ) : ℂ))
      ((deriv (deriv halfSlopeCut) x : ℝ) : ℂ) x :=
    ((h1.differentiable (by norm_num)).differentiableAt.hasDerivAt).ofReal_comp
  let Z1 : ℝ → ℂ := fun y => ((deriv halfSlopeCut y : ℝ) : ℂ) * halfSlopeU t y +
    (halfSlopeCut y : ℂ) * halfSlopeU1 t y
  have hfirst : deriv (halfSlopeZ t) = Z1 := by
    funext y
    exact ((dc y).mul (halfSlopeU_hasDerivAt t y)).deriv
  have hsecond : HasDerivAt Z1 _ x := (dc'.mul (halfSlopeU_hasDerivAt t x)).add
    ((dc x).mul (halfSlopeU1_hasDerivAt t x))
  rw [hfirst, hsecond.deriv]
  have hS0 := halfSlopeS_ne_zero x
  simp only [halfSlopeR, halfSlopeZ]
  field_simp
  ring

theorem halfSlopeR_norm_le {t x M₁ M₂ : ℝ} (ht : 0 ≤ t) (hx : |x| ≤ 1)
    (h₁ : ‖deriv halfSlopeCut x‖ ≤ M₁) (h₂ : ‖deriv (deriv halfSlopeCut) x‖ ≤ M₂) :
    ‖halfSlopeR t x‖ ≤ (4 * M₂ + 16 * M₁) * (1 + t) * Real.exp (-4 * t * (1 + 1 / 200)) := by
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans h₁
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans h₂
  rcases lt_or_ge |x| (1 / 2) with hlt | hge
  · obtain ⟨d1, d2⟩ := halfSlopeCut_deriv_vanish hlt
    rw [halfSlopeR, d1, d2]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, norm_zero]
    positivity
  · have hE : ‖halfSlopeE t x‖ ≤ Real.exp (-4 * t * (1 + 1 / 200)) := by
      rw [halfSlopeE_norm]
      apply Real.exp_le_exp.2
      have := halfSlopeW_re_ge hge
      nlinarith
    have hE0 := norm_nonneg (halfSlopeE t x)
    have hS := halfSlopeS_norm_le_two hx
    have hU : ‖halfSlopeU t x‖ ≤ 2 * ‖halfSlopeE t x‖ := by
      rw [halfSlopeU, norm_mul]
      exact mul_le_mul_of_nonneg_right (halfSlopeP_norm_bounds hx).2 hE0
    have hU1 := halfSlopeU1_norm_le ht hx
    have hin : ‖((deriv (deriv halfSlopeCut) x : ℝ) : ℂ) * halfSlopeU t x +
        2 * ((deriv halfSlopeCut x : ℝ) : ℂ) * halfSlopeU1 t x‖ ≤
        M₂ * (2 * ‖halfSlopeE t x‖) + 2 * M₁ * ((1 / 4) * (1 + 16 * t) * ‖halfSlopeE t x‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real]
        exact mul_le_mul h₂ hU (norm_nonneg _) hM₂
      · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_two]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by norm_num)) hU1 (norm_nonneg _)
          (by positivity)
    rw [halfSlopeR, norm_mul]
    have hin0 := norm_nonneg (((deriv (deriv halfSlopeCut) x : ℝ) : ℂ) * halfSlopeU t x +
        2 * ((deriv halfSlopeCut x : ℝ) : ℂ) * halfSlopeU1 t x)
    calc _ ≤ 2 * (M₂ * (2 * ‖halfSlopeE t x‖) +
          2 * M₁ * ((1 / 4) * (1 + 16 * t) * ‖halfSlopeE t x‖)) :=
          mul_le_mul hS hin hin0 (by norm_num)
      _ = (4 * M₂ + M₁ * (1 + 16 * t)) * ‖halfSlopeE t x‖ := by ring
      _ ≤ (4 * M₂ + 16 * M₁ * (1 + t)) * ‖halfSlopeE t x‖ := by
          apply mul_le_mul_of_nonneg_right _ hE0
          nlinarith
      _ ≤ (4 * M₂ + 16 * M₁ * (1 + t)) * Real.exp (-4 * t * (1 + 1 / 200)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ (4 * M₂ + 16 * M₁) * (1 + t) * Real.exp (-4 * t * (1 + 1 / 200)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          nlinarith

theorem halfSlopeZ_norm_ge {t x : ℝ} (ht : 0 ≤ t) (hx : |x| ≤ 1 / 4) :
    Real.exp (-4 * t * (1 + 1 / 512)) ≤ ‖halfSlopeZ t x‖ := by
  rw [halfSlopeZ, halfSlopeCut_eq_one (by linarith), Complex.ofReal_one, one_mul, halfSlopeU,
    norm_mul, halfSlopeE_norm]
  have hP := (halfSlopeP_norm_bounds (by linarith : |x| ≤ 1)).1
  have hE : Real.exp (-4 * t * (1 + 1 / 512)) ≤ Real.exp (-4 * t * (halfSlopeW x).re) := by
    apply Real.exp_le_exp.2
    have := halfSlopeW_re_le hx
    nlinarith
  calc _ ≤ 1 * Real.exp (-4 * t * (halfSlopeW x).re) := by rw [one_mul]; exact hE
    _ ≤ _ := mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le

theorem halfSlopeZ_div_norm_le (t x : ℝ) :
    ‖halfSlopeZ t x / halfSlopeS x‖ ≤ ‖halfSlopeZ t x‖ := by
  rw [norm_div]
  exact div_le_self (norm_nonneg _) (one_le_halfSlopeS_norm x)

theorem halfSlopeZ_one (t : ℝ) : halfSlopeZ t 1 = 0 := by
  simp [halfSlopeZ, halfSlopeCut_one]

theorem halfSlopeZ_neg_one (t : ℝ) : halfSlopeZ t (-1) = 0 := by
  simp [halfSlopeZ, halfSlopeCut_neg_one]

theorem halfSlopeR_continuous (t : ℝ) : Continuous (halfSlopeR t) := by
  have h1 : ContDiff ℝ 1 (deriv halfSlopeCut) := ContDiff.deriv' halfSlopeCut_contDiff_two
  have hc1 : Continuous (deriv halfSlopeCut) := h1.continuous
  have hc2 : Continuous (deriv (deriv halfSlopeCut)) := h1.continuous_deriv le_rfl
  exact (halfSlopeS_contDiff (n := 0)).continuous.mul
    (((continuous_ofReal.comp hc2).mul (halfSlopeU_contDiff (n := 0) t).continuous).add
      ((continuous_const.mul (continuous_ofReal.comp hc1)).mul (halfSlopeU1_continuous t)))

end Involution
