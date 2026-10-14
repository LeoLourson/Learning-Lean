module

public import Involution.Estimates.RampSpectrum
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Липшицев коэффициент `a(x) = max(x, 0)`: нет базиса Рисса из собственных функций.
Квазимоды с носителем в `[0,1]` дают `‖(L_a - ω²) y‖ ≤ (A + B ω) ‖y‖` для вещественных `ω`,
базис Рисса из собственных функций дал бы собственное значение на расстоянии `O(ω)` от `ω²`,
а `ramp_eigenvalue_bound` запрещает такие собственные значения при больших `ω`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Involution

/-- Вещественный профиль квазимоды: нуль при `x ≤ 0` и в точке `1`. -/
def quasiProfile : ℝ → ℝ := fun x => Real.smoothTransition x * (1 - x)

theorem quasiProfile_contDiff : ContDiff ℝ 2 quasiProfile :=
  Real.smoothTransition.contDiff.mul (contDiff_const.sub contDiff_id)

theorem quasiProfile_of_nonpos {x : ℝ} (hx : x ≤ 0) : quasiProfile x = 0 := by
  change Real.smoothTransition x * (1 - x) = 0
  rw [Real.smoothTransition.zero_of_nonpos hx, zero_mul]

def quasiPhase (ω : ℝ) : ℝ → ℂ := fun x => Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)

theorem quasiPhase_norm (ω x : ℝ) : ‖quasiPhase ω x‖ = 1 := by
  change ‖Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)‖ = 1
  rw [← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

def quasiMode (ω : ℝ) : ℝ → ℂ := fun x => (quasiProfile x : ℂ) * quasiPhase ω x

theorem quasiPhase_contDiff (ω : ℝ) : ContDiff ℝ 2 (quasiPhase ω) :=
  ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp

theorem quasiMode_contDiff (ω : ℝ) : ContDiff ℝ 2 (quasiMode ω) :=
  (Complex.ofRealCLM.contDiff.comp quasiProfile_contDiff).mul (quasiPhase_contDiff ω)

theorem quasiPhase_hasDerivAt (ω x : ℝ) :
    HasDerivAt (quasiPhase ω) (quasiPhase ω x * ((ω : ℂ) * 1 * Complex.I)) x := by
  have dx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  exact ((dx.const_mul (ω : ℂ)).mul_const Complex.I).cexp

theorem quasiMode_second_deriv (ω x : ℝ) :
    -deriv (deriv (quasiMode ω)) x - (ω : ℂ) ^ 2 * quasiMode ω x =
      -(((deriv (deriv quasiProfile) x : ℝ) : ℂ) +
        2 * Complex.I * (ω : ℂ) * ((deriv quasiProfile x : ℝ) : ℂ)) * quasiPhase ω x := by
  have h1 : ContDiff ℝ 1 (deriv quasiProfile) := ContDiff.deriv' quasiProfile_contDiff
  have dψ : ∀ y, HasDerivAt (fun t : ℝ => (quasiProfile t : ℂ))
      ((deriv quasiProfile y : ℝ) : ℂ) y :=
    fun y => ((quasiProfile_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
      ).ofReal_comp
  have dψ' : HasDerivAt (fun t : ℝ => ((deriv quasiProfile t : ℝ) : ℂ))
      ((deriv (deriv quasiProfile) x : ℝ) : ℂ) x :=
    ((h1.differentiable (by norm_num)).differentiableAt.hasDerivAt).ofReal_comp
  let f1 : ℝ → ℂ := fun y => ((deriv quasiProfile y : ℝ) : ℂ) * quasiPhase ω y +
    (quasiProfile y : ℂ) * (quasiPhase ω y * ((ω : ℂ) * 1 * Complex.I))
  have hfirst : deriv (quasiMode ω) = f1 := by
    funext y
    exact ((dψ y).mul (quasiPhase_hasDerivAt ω y)).deriv
  have hsecond : HasDerivAt f1
      ((((deriv (deriv quasiProfile) x : ℝ) : ℂ) * quasiPhase ω x +
        ((deriv quasiProfile x : ℝ) : ℂ) * (quasiPhase ω x * ((ω : ℂ) * 1 * Complex.I))) +
        (((deriv quasiProfile x : ℝ) : ℂ) * (quasiPhase ω x * ((ω : ℂ) * 1 * Complex.I)) +
          (quasiProfile x : ℂ) *
            (quasiPhase ω x * ((ω : ℂ) * 1 * Complex.I) * ((ω : ℂ) * 1 * Complex.I)))) x :=
    (dψ'.mul (quasiPhase_hasDerivAt ω x)).add
      ((dψ x).mul ((quasiPhase_hasDerivAt ω x).mul_const _))
  rw [hfirst, hsecond.deriv]
  change _ - (ω : ℂ) ^ 2 * ((quasiProfile x : ℂ) * quasiPhase ω x) = _
  linear_combination (-(quasiProfile x : ℂ) * quasiPhase ω x * (ω : ℂ) ^ 2) * Complex.I_sq

def quasiModeL2 (ω : ℝ) : IntervalL2 :=
  (continuous_memLp_interval (quasiMode ω) (quasiMode_contDiff ω).continuous).toLp (quasiMode ω)

theorem quasiModeL2_ae (ω : ℝ) : quasiModeL2 ω =ᵐ[intervalMeasure] quasiMode ω :=
  MemLp.coeFn_toLp _

theorem quasiModeL2_memDirichletH2 (ω : ℝ) : MemDirichletH2 (quasiModeL2 ω) := by
  refine ⟨memIntervalH2_of_contDiff _ (quasiMode_contDiff ω), quasiMode ω,
    ⟨(quasiMode_contDiff ω).continuous.continuousOn, (quasiModeL2_ae ω).symm⟩, ?_, ?_⟩
  · change (quasiProfile (-1) : ℂ) * quasiPhase ω (-1) = 0
    rw [quasiProfile_of_nonpos (by norm_num)]
    simp
  · change ((Real.smoothTransition 1 * (1 - 1) : ℝ) : ℂ) * quasiPhase ω 1 = 0
    simp

theorem quasiMode_norm (ω x : ℝ) : ‖quasiMode ω x‖ = ‖quasiMode 0 x‖ := by
  change ‖(quasiProfile x : ℂ) * quasiPhase ω x‖ = ‖(quasiProfile x : ℂ) * quasiPhase 0 x‖
  rw [norm_mul, norm_mul, quasiPhase_norm, quasiPhase_norm]

theorem quasiModeL2_norm (ω : ℝ) : ‖quasiModeL2 ω‖ = ‖quasiModeL2 0‖ := by
  rw [quasiModeL2, quasiModeL2, Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (quasiMode_contDiff ω).continuous.aestronglyMeasurable
    (quasiMode_contDiff 0).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => quasiMode_norm ω x)

theorem quasiModeL2_zero_ne : quasiModeL2 0 ≠ 0 := by
  intro hz
  have hrep : HasIntervalRepresentative (quasiModeL2 0) (quasiMode 0) :=
    ⟨(quasiMode_contDiff 0).continuous.continuousOn, (quasiModeL2_ae 0).symm⟩
  have hzero : HasIntervalRepresentative (quasiModeL2 0) (fun _ => 0) := by
    rw [hz]
    exact ⟨continuous_const.continuousOn, (Lp.coeFn_zero ℂ 2 intervalMeasure).symm⟩
  have hx := hrep.unique hzero (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (-1) 1)
  have hpos : 0 < quasiProfile (1 / 2) :=
    mul_pos (Real.smoothTransition.pos_of_pos (by norm_num)) (by norm_num)
  have hn : ‖quasiMode 0 (1 / 2)‖ = quasiProfile (1 / 2) := by
    change ‖(quasiProfile (1 / 2) : ℂ) * quasiPhase 0 (1 / 2)‖ = _
    rw [norm_mul, quasiPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
  rw [hx, norm_zero] at hn
  linarith

/-- Квазимоды: `‖(L_a - ω²) y_ω‖ ≤ A + B ω`, а `‖y_ω‖` не зависит от `ω`. -/
theorem ramp_quasimodes : ∃ c₀ A B : ℝ, 0 < c₀ ∧ 0 ≤ A ∧ 0 ≤ B ∧ ∀ ω : ℝ, 0 ≤ ω →
    ∃ (y : IntervalL2) (hy : MemDirichletH2 y), ‖y‖ = c₀ ∧
      ‖variableSobolevOperator rampClass y hy.1 - ((ω : ℂ) ^ 2) • y‖ ≤ A + B * ω := by
  have h1 : ContDiff ℝ 1 (deriv quasiProfile) := ContDiff.deriv' quasiProfile_contDiff
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h1.continuous.continuousOn (s := Icc (-1 : ℝ) 1))
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h1.continuous_deriv_one.continuousOn (s := Icc (-1 : ℝ) 1))
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0 (by norm_num))
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0 (by norm_num))
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1))
    infer_instance
  let m₀ : ℝ := (measureUnivNNReal intervalMeasure : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hm₀ : 0 ≤ m₀ := by positivity
  refine ⟨‖quasiModeL2 0‖, m₀ * M₂, m₀ * (2 * M₁), norm_pos_iff.mpr quasiModeL2_zero_ne,
    mul_nonneg hm₀ hM₂0, mul_nonneg hm₀ (by positivity), ?_⟩
  intro ω hω
  refine ⟨quasiModeL2 ω, quasiModeL2_memDirichletH2 ω, quasiModeL2_norm ω, ?_⟩
  have hD : secondWeakDeriv (quasiModeL2 ω) (quasiModeL2_memDirichletH2 ω).1
      =ᵐ[intervalMeasure] deriv (deriv (quasiMode ω)) :=
    secondWeakDeriv_smooth_ae (quasiMode ω) (quasiMode_contDiff ω)
  have hDn : ∀ᵐ x ∂intervalMeasure,
      secondWeakDeriv (quasiModeL2 ω) (quasiModeL2_memDirichletH2 ω).1 (-x) =
        deriv (deriv (quasiMode ω)) (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hD] with x hx
    exact hx
  have hvanish : ∀ x : ℝ, (rampCoefficient x : ℂ) * deriv (deriv (quasiMode ω)) (-x) = 0 := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · rw [rampCoefficient_of_nonpos hx]
      simp
    · have hev : quasiMode ω =ᶠ[𝓝 (-x)] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds (neg_neg_of_pos hx)] with y hy
        change (quasiProfile y : ℂ) * quasiPhase ω y = 0
        rw [quasiProfile_of_nonpos (le_of_lt hy)]
        simp
      have hd : deriv (deriv (quasiMode ω)) (-x) = 0 := by
        rw [hev.deriv.deriv_eq]
        simp
      rw [hd, mul_zero]
  have hbound : ∀ᵐ x ∂intervalMeasure,
      ‖(variableSobolevOperator rampClass (quasiModeL2 ω) (quasiModeL2_memDirichletH2 ω).1 -
        ((ω : ℂ) ^ 2) • quasiModeL2 ω) x‖ ≤ M₂ + 2 * M₁ * ω := by
    filter_upwards [Lp.coeFn_sub
        (variableSobolevOperator rampClass (quasiModeL2 ω) (quasiModeL2_memDirichletH2 ω).1)
        (((ω : ℂ) ^ 2) • quasiModeL2 ω),
      Lp.coeFn_smul ((ω : ℂ) ^ 2) (quasiModeL2 ω),
      variableSobolevOperator_ae rampClass (quasiModeL2 ω) (quasiModeL2_memDirichletH2 ω).1,
      hD, hDn, quasiModeL2_ae ω,
      realIntervalCoefficient_ae rampCoefficient rampCoefficient_memLp,
      ae_restrict_mem measurableSet_Ioo] with x hsub hsm hop hDx hDnx hq ha hx
    have ha' : rampClass x = (rampCoefficient x : ℂ) := ha
    rw [hsub, Pi.sub_apply, hsm, Pi.smul_apply, hop, hDx, hDnx, ha', hvanish x, sub_zero, hq,
      smul_eq_mul, quasiMode_second_deriv, norm_mul, quasiPhase_norm, mul_one, norm_neg]
    have hxI : x ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hx
    calc
      _ ≤ ‖((deriv (deriv quasiProfile) x : ℝ) : ℂ)‖ +
          ‖2 * Complex.I * (ω : ℂ) * ((deriv quasiProfile x : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖deriv (deriv quasiProfile) x‖ + 2 * ω * ‖deriv quasiProfile x‖ := by
        rw [Complex.norm_real, norm_mul, norm_mul, norm_mul, Complex.norm_real,
          Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg hω]
        simp
      _ ≤ M₂ + 2 * ω * M₁ :=
        add_le_add (hM₂ x hxI) (mul_le_mul_of_nonneg_left (hM₁ x hxI) (by positivity))
      _ = M₂ + 2 * M₁ * ω := by ring
  have hnorm := Lp.norm_le_of_ae_bound (by positivity : (0 : ℝ) ≤ M₂ + 2 * M₁ * ω) hbound
  calc
    _ ≤ m₀ * (M₂ + 2 * M₁ * ω) := hnorm
    _ = m₀ * M₂ + m₀ * (2 * M₁) * ω := by ring

open Classical in
/-- Базис Рисса из собственных векторов даёт нижнюю оценку `‖(L - μ) y‖ ≥ d ‖y‖ / C`,
где `d` — расстояние от `μ` до собственных значений. -/
theorem rieszEigenbasis_lower_bound (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1)
    {ι : Type} (b : RieszBasis ι IntervalL2) (lam : ι → ℂ)
    (hb : ∀ i, ∃ hf : MemDirichletH2 (b.vector i),
      variableSobolevOperator a (b.vector i) hf.1 = lam i • b.vector i)
    (y : IntervalL2) (hy : MemDirichletH2 y) (mu : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdist : ∀ i, δ ≤ ‖lam i - mu‖) :
    δ * ‖y‖ ≤ (‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr.toContinuousLinearMap‖) *
      ‖variableSobolevOperator a y hy.1 - mu • y‖ := by
  let K := variableGreen a d
  have hvne : ∀ i, b.vector i ≠ 0 := by
    intro i hz
    have h := b.repr_vector i
    rw [hz, map_zero] at h
    have h1 := congrArg (fun v : lp (fun _ : ι => ℂ) 2 => v i) h
    simp at h1
  have hlam : ∀ i, lam i ≠ 0 := fun i => by
    obtain ⟨hf, he⟩ := hb i
    exact variableOperator_eigenvalue_ne_zero a d hd _ hf (hvne i) _ he
  have hK : ∀ i, K (b.vector i) = (lam i)⁻¹ • b.vector i := fun i =>
    (variableOperator_eigen_iff a d hd _ _ (hlam i)).mp (hb i)
  let φ : ι → IntervalL2 →L[ℂ] ℂ := fun i =>
    (innerSL ℂ (lp.single 2 i (1 : ℂ))).comp b.repr.toContinuousLinearMap
  have hφ : ∀ i v, φ i v = b.repr v i := by
    intro i v
    change inner ℂ (lp.single 2 i (1 : ℂ)) (b.repr v) = b.repr v i
    rw [lp.inner_single_left]
    simp
  have hφK : ∀ i w, φ i (K w) = (lam i)⁻¹ * φ i w := by
    intro i
    let Ψ : IntervalL2 →L[ℂ] ℂ := (φ i).comp K - (lam i)⁻¹ • φ i
    have hspan : Submodule.span ℂ (Set.range b.vector) ≤ LinearMap.ker Ψ.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change (φ i) (K (b.vector j)) - (lam i)⁻¹ • φ i (b.vector j) = 0
      rw [hK j, map_smul, hφ, b.repr_vector j, smul_eq_mul, smul_eq_mul]
      by_cases hij : j = i
      · rw [hij, sub_self]
      · rw [lp.single_apply_ne _ _ _ (Ne.symm hij)]
        simp
    have hclosed : IsClosed (LinearMap.ker Ψ.toLinearMap : Set IntervalL2) := Ψ.isClosed_ker
    have htop := Submodule.topologicalClosure_minimal _ hspan hclosed
    rw [b.dense_span] at htop
    intro w
    have hw : Ψ w = 0 := htop (Submodule.mem_top : w ∈ ⊤)
    change (φ i) (K w) - (lam i)⁻¹ • φ i w = 0 at hw
    rw [smul_eq_mul] at hw
    exact sub_eq_zero.mp hw
  let Ly := variableSobolevOperator a y hy.1
  have hφL : ∀ i, φ i Ly = lam i * φ i y := by
    intro i
    have h := hφK i Ly
    rw [variableGreen_left_inverse a d hd y hy] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (hlam i), one_mul]
  let x := b.repr y
  let z := b.repr (Ly - mu • y)
  have hz : ∀ i, z i = (lam i - mu) * x i := by
    intro i
    rw [← hφ, map_sub, map_smul, hφL, hφ, smul_eq_mul]
    ring
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hxz : ‖((δ : ℂ) • x)‖ ≤ ‖z‖ := by
    apply lp.norm_le_of_forall_sum_le hp (norm_nonneg z)
    intro s
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (lp.sum_rpow_le_norm_rpow hp z s)
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, hz, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_right (hdist i) (norm_nonneg _)
  have hyx : ‖y‖ ≤ ‖b.repr.symm.toContinuousLinearMap‖ * ‖x‖ := by
    have h := b.repr.symm.toContinuousLinearMap.le_opNorm x
    simpa only [ContinuousLinearEquiv.coe_coe, x, ContinuousLinearEquiv.symm_apply_apply] using h
  have hzL : ‖z‖ ≤ ‖b.repr.toContinuousLinearMap‖ * ‖Ly - mu • y‖ :=
    b.repr.toContinuousLinearMap.le_opNorm _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ] at hxz
  calc
    δ * ‖y‖ ≤ δ * (‖b.repr.symm.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left hyx hδ
    _ = ‖b.repr.symm.toContinuousLinearMap‖ * (δ * ‖x‖) := by ring
    _ ≤ ‖b.repr.symm.toContinuousLinearMap‖ *
        (‖b.repr.toContinuousLinearMap‖ * ‖Ly - mu • y‖) :=
      mul_le_mul_of_nonneg_left (hxz.trans hzL) (norm_nonneg _)
    _ = _ := by ring

theorem rampClass_product :
    ∀ᵐ x ∂intervalMeasure, |rampCoefficient x * rampCoefficient (-x)| ≤ 0 :=
  Filter.Eventually.of_forall fun x => by rw [rampCoefficient_product, abs_zero]

/-- Для липшицева коэффициента `a(x) = max(x, 0)` (класс `W¹∞`, `a(x) a(-x) = 0`)
не существует базиса Рисса пространства `L₂(-1,1)`, состоящего из собственных функций `L_a`. -/
theorem ramp_no_riesz_eigenbasis :
    ¬ ∃ (ι : Type) (b : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemDirichletH2 (b.vector i), ∃ lam : ℂ,
        variableSobolevOperator rampClass (b.vector i) hf.1 = lam • b.vector i := by
  classical
  rintro ⟨ι, b, hb⟩
  choose hf lam he using hb
  let dinv := determinantInverse rampCoefficient rampCoefficient_memLp 0 (by norm_num)
    rampClass_product
  have hd := determinantInverse_identity rampCoefficient rampCoefficient_memLp 0 (by norm_num)
    rampClass_product
  let C := ‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr.toContinuousLinearMap‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨c₀, A, B, hc₀, hA, hB, hq⟩ := ramp_quasimodes
  have hvne : ∀ i, b.vector i ≠ 0 := by
    intro i hz
    have h := b.repr_vector i
    rw [hz, map_zero] at h
    have h1 := congrArg (fun v : lp (fun _ : ι => ℂ) 2 => v i) h
    simp at h1
  let D₀ := C * A / c₀ + 1
  let D₁ := C * B / c₀
  let D := D₀ + D₁
  have hD₀ : 1 ≤ D₀ := by
    have : 0 ≤ C * A / c₀ := div_nonneg (mul_nonneg hC hA) hc₀.le
    change 1 ≤ C * A / c₀ + 1
    linarith
  have hD₁ : 0 ≤ D₁ := div_nonneg (mul_nonneg hC hB) hc₀.le
  have hD : 1 ≤ D := by
    change 1 ≤ D₀ + D₁
    linarith
  let Λ := 32 * Real.exp (2 * (4 * D))
  have hΛ : 0 < Λ := by positivity
  let ω := 2 * D + 2 * Λ + 2
  have hω1 : 1 ≤ ω := by
    change 1 ≤ 2 * D + 2 * Λ + 2
    linarith
  have hω0 : 0 ≤ ω := by linarith
  let δ := D₀ + D₁ * ω
  have hδ0 : 0 ≤ δ := by
    change 0 ≤ D₀ + D₁ * ω
    nlinarith
  have hδω : δ ≤ D * ω := by
    change D₀ + D₁ * ω ≤ (D₀ + D₁) * ω
    nlinarith
  obtain ⟨y, hy, hyn, hyq⟩ := hq ω hω0
  have hexists : ∃ i, ‖lam i - (ω : ℂ) ^ 2‖ < δ := by
    by_contra hnone
    have hall : ∀ i, δ ≤ ‖lam i - (ω : ℂ) ^ 2‖ := fun i => le_of_not_gt fun h => hnone ⟨i, h⟩
    have hlow := rieszEigenbasis_lower_bound rampClass dinv hd b lam
      (fun i => ⟨hf i, he i⟩) y hy ((ω : ℂ) ^ 2) δ hδ0 hall
    rw [hyn] at hlow
    have hup : δ * c₀ ≤ C * (A + B * ω) := hlow.trans (mul_le_mul_of_nonneg_left hyq hC)
    have hδc : δ * c₀ = C * (A + B * ω) + c₀ := by
      change (C * A / c₀ + 1 + C * B / c₀ * ω) * c₀ = C * (A + B * ω) + c₀
      field_simp
      ring
    linarith
  obtain ⟨i, hi⟩ := hexists
  have hω2 : ‖((ω : ℂ) ^ 2)‖ = ω ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hω0]
  have hnormdiff : |‖lam i‖ - ω ^ 2| ≤ ‖lam i - (ω : ℂ) ^ 2‖ := by
    rw [← hω2]
    exact abs_norm_sub_norm_le _ _
  have hDω : D ≤ ω / 2 := by
    change D ≤ (2 * D + 2 * Λ + 2) / 2
    linarith
  have hδhalf : δ ≤ ω ^ 2 / 2 := by nlinarith
  have hlamlow : ω ^ 2 / 2 ≤ ‖lam i‖ := by
    have := (abs_le.mp (hnormdiff.trans hi.le)).1
    linarith
  have hsqrt : ω / 2 ≤ Real.sqrt ‖lam i‖ := by
    have hsq : (ω / 2) ^ 2 ≤ ‖lam i‖ := by nlinarith
    exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have hκ : ‖((‖lam i‖ : ℝ) : ℂ) - lam i‖ ≤ 4 * D * Real.sqrt ‖lam i‖ := by
    have h1 : ‖((‖lam i‖ : ℝ) : ℂ) - lam i‖ ≤
        ‖((‖lam i‖ : ℝ) : ℂ) - (ω : ℂ) ^ 2‖ + ‖(ω : ℂ) ^ 2 - lam i‖ := by
      have := norm_add_le (((‖lam i‖ : ℝ) : ℂ) - (ω : ℂ) ^ 2) ((ω : ℂ) ^ 2 - lam i)
      rwa [sub_add_sub_cancel] at this
    have h2 : ‖((‖lam i‖ : ℝ) : ℂ) - (ω : ℂ) ^ 2‖ = |‖lam i‖ - ω ^ 2| := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h3 : ‖(ω : ℂ) ^ 2 - lam i‖ = ‖lam i - (ω : ℂ) ^ 2‖ := norm_sub_rev _ _
    rw [h2, h3] at h1
    have h4 : ‖((‖lam i‖ : ℝ) : ℂ) - lam i‖ ≤ 2 * δ := by linarith [hnormdiff.trans hi.le]
    calc
      _ ≤ 2 * δ := h4
      _ ≤ 2 * (D * ω) := by linarith
      _ = 4 * D * (ω / 2) := by ring
      _ ≤ 4 * D * Real.sqrt ‖lam i‖ := mul_le_mul_of_nonneg_left hsqrt (by linarith)
  have hbound := ramp_eigenvalue_bound (b.vector i) (hf i) (hvne i) (lam i) (he i) (4 * D)
    (by linarith) hκ (by nlinarith)
  have hΛω : Λ < ω ^ 2 / 2 := by
    change Λ < (2 * D + 2 * Λ + 2) ^ 2 / 2
    nlinarith
  change ‖lam i‖ ≤ Λ at hbound
  linarith

end Involution
