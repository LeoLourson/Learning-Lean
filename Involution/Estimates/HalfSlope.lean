module

public import Involution.Estimates.OddCoefficient
public import Involution.Estimates.RampNoBasis
public import Involution.Model.EigenvalueCounting
public import Involution.Estimates.RieszEigenCount
public import Involution.Estimates.HalfSlopeProfile

/-! Нечётный коэффициент `a(x) = x / 2`: нет базиса Рисса из собственных функций.
Функция `s^{1/4} exp(-4 t √s)`, `s = 1 + i x / 2`, точно решает уравнение
`(1 + i a)(-u'') - t² u = -(3 / (64 s)) u`; после срезки она даёт квазимоды
`‖(L_a - t²) y‖ ≤ C ‖y‖` при всех `t ≥ 0`. Базис Рисса из собственных функций дал бы
собственное значение на ограниченном расстоянии от каждой точки `t²`, а счётная функция
собственных значений растёт как `√r`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Involution

/-- Нечётный коэффициент `a(x) = x / 2`. -/
def halfSlopeCoefficient : ℝ → ℝ := fun x => x / 2

theorem halfSlopeCoefficient_memLp : MemLp halfSlopeCoefficient ∞ intervalMeasure := by
  apply memLp_top_of_bound (measurable_id.div_const 2).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change ‖x / 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

def halfSlopeClass : IntervalLInfinity :=
  realIntervalCoefficient halfSlopeCoefficient halfSlopeCoefficient_memLp

theorem halfSlopeClass_product :
    ∀ᵐ x ∂intervalMeasure, |halfSlopeCoefficient x * halfSlopeCoefficient (-x)| ≤ 1 / 4 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change |x / 2 * (-x / 2)| ≤ 1 / 4
  have h : 0 < (1 - x) * (1 + x) := mul_pos (by linarith [hx.2]) (by linarith [hx.1])
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x]

theorem halfSlopeClass_odd :
    ∀ᵐ x ∂intervalMeasure, halfSlopeClass (-x) = -halfSlopeClass x := by
  have hn : ∀ᵐ x ∂intervalMeasure,
      halfSlopeClass (-x) = ((halfSlopeCoefficient (-x) : ℝ) : ℂ) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (realIntervalCoefficient_ae halfSlopeCoefficient halfSlopeCoefficient_memLp)] with x hx
    exact hx
  filter_upwards [realIntervalCoefficient_ae halfSlopeCoefficient halfSlopeCoefficient_memLp, hn]
    with x hx hnx
  have hx' : halfSlopeClass x = ((halfSlopeCoefficient x : ℝ) : ℂ) := hx
  rw [hnx, hx']
  change (((-x / 2 : ℝ)) : ℂ) = -((x / 2 : ℝ) : ℂ)
  push_cast
  ring

/-- `L₂`-класс срезанного решения `Z_t`. -/
def halfSlopeZL (t : ℝ) : IntervalL2 :=
  (continuous_memLp_interval (halfSlopeZ t) (halfSlopeZ_contDiff t).continuous).toLp
    (halfSlopeZ t)

theorem halfSlopeZL_ae (t : ℝ) : halfSlopeZL t =ᵐ[intervalMeasure] halfSlopeZ t :=
  MemLp.coeFn_toLp _

theorem halfSlopeZL_memDirichletH2 (t : ℝ) : MemDirichletH2 (halfSlopeZL t) :=
  ⟨memIntervalH2_of_contDiff _ (halfSlopeZ_contDiff t), halfSlopeZ t,
    ⟨(halfSlopeZ_contDiff t).continuous.continuousOn, (halfSlopeZL_ae t).symm⟩,
    halfSlopeZ_neg_one t, halfSlopeZ_one t⟩

/-- Нижняя оценка нормы: `‖Z_t‖ ≥ c₀ exp(-4 t (1 + 1/512))`. -/
theorem halfSlopeZL_norm_ge : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, 0 ≤ t →
    c₀ * Real.exp (-4 * t * (1 + 1 / 512)) ≤ ‖halfSlopeZL t‖ := by
  have hs : MeasurableSet (Icc (-(1 / 4) : ℝ) (1 / 4)) := measurableSet_Icc
  have hμ : intervalMeasure (Icc (-(1 / 4) : ℝ) (1 / 4)) = ENNReal.ofReal (1 / 2) := by
    change volume.restrict (Ioo (-1 : ℝ) 1) _ = _
    rw [Measure.restrict_apply hs, Set.inter_eq_left.2, Real.volume_Icc]
    · norm_num
    · intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hμs : intervalMeasure (Icc (-(1 / 4) : ℝ) (1 / 4)) ≠ ⊤ := by
    rw [hμ]
    exact ENNReal.ofReal_ne_top
  have hreal : intervalMeasure.real (Icc (-(1 / 4) : ℝ) (1 / 4)) = 1 / 2 := by
    rw [measureReal_def, hμ, ENNReal.toReal_ofReal (by norm_num)]
  refine ⟨(1 / 2 : ℝ) ^ (1 / (2 : ℝ≥0∞).toReal), by positivity, fun t ht => ?_⟩
  set e := Real.exp (-4 * t * (1 + 1 / 512)) with he
  have he0 : 0 < e := Real.exp_pos _
  let ind : IntervalL2 := indicatorConstLp 2 hs hμs (e : ℂ)
  have hind : ‖ind‖ = e * (1 / 2 : ℝ) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), hreal, Complex.norm_real,
      Real.norm_of_nonneg he0.le]
  have hle : ∀ᵐ x ∂intervalMeasure, ‖ind x‖ ≤ 1 * ‖halfSlopeZL t x‖ := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (e : ℂ)),
      halfSlopeZL_ae t] with x hx hz
    rw [hx, hz, one_mul]
    by_cases hxs : x ∈ Icc (-(1 / 4) : ℝ) (1 / 4)
    · rw [Set.indicator_of_mem hxs, Complex.norm_real, Real.norm_of_nonneg he0.le]
      exact halfSlopeZ_norm_ge ht (abs_le.2 hxs)
    · rw [Set.indicator_of_notMem hxs, norm_zero]
      exact norm_nonneg _
  have := Lp.norm_le_mul_norm_of_ae_le_mul hle
  rw [hind, one_mul] at this
  linarith

theorem secondWeakDeriv_congr_eq {f g : IntervalL2} (hfg : f = g) (hf : MemIntervalH2 f)
    (hg : MemIntervalH2 g) : secondWeakDeriv f hf = secondWeakDeriv g hg := by
  subst hfg
  rfl

/-- После поворота по чётности невязка квазимоды равна `-(3/64) Z_t / s - R_t`. -/
theorem halfSlope_rotated_residual (t : ℝ)
    (hy : MemIntervalH2 (parityRotationInv (halfSlopeZL t))) :
    parityRotation (variableSobolevOperator halfSlopeClass (parityRotationInv (halfSlopeZL t)) hy -
      ((t : ℂ) ^ 2) • parityRotationInv (halfSlopeZL t)) =ᵐ[intervalMeasure]
      fun x => -(3 / 64) * halfSlopeZ t x / halfSlopeS x - halfSlopeR t x := by
  have hUy : parityRotation (parityRotationInv (halfSlopeZL t)) = halfSlopeZL t :=
    parityRotation_parityRotationInv _
  rw [map_sub, map_smul, hUy, oddCoefficient_unitary_multiplication halfSlopeClass
    halfSlopeClass_odd _ hy]
  rw [secondWeakDeriv_congr_eq hUy _ (halfSlopeZL_memDirichletH2 t).1]
  set D := secondWeakDeriv (halfSlopeZL t) (halfSlopeZL_memDirichletH2 t).1 with hD
  have hDae : D =ᵐ[intervalMeasure] deriv (deriv (halfSlopeZ t)) :=
    secondWeakDeriv_smooth_ae (halfSlopeZ t) (halfSlopeZ_contDiff t)
  filter_upwards [Lp.coeFn_sub (-D + Complex.I • boundedMultiplier halfSlopeClass (-D))
      (((t : ℂ) ^ 2) • halfSlopeZL t),
    Lp.coeFn_add (-D) (Complex.I • boundedMultiplier halfSlopeClass (-D)),
    Lp.coeFn_neg D, Lp.coeFn_smul Complex.I (boundedMultiplier halfSlopeClass (-D)),
    boundedMultiplier_ae halfSlopeClass (-D), Lp.coeFn_neg D,
    Lp.coeFn_smul ((t : ℂ) ^ 2) (halfSlopeZL t), hDae, halfSlopeZL_ae t,
    realIntervalCoefficient_ae halfSlopeCoefficient halfSlopeCoefficient_memLp]
    with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have ha : halfSlopeClass x = ((x / 2 : ℝ) : ℂ) := h10
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.neg_apply, h4, Pi.smul_apply, h5, h6,
    Pi.neg_apply, h7, Pi.smul_apply, h8, h9, ha, smul_eq_mul, smul_eq_mul,
    ← halfSlopeZ_equation]
  simp only [halfSlopeS]
  push_cast
  ring

/-- Квазимоды на положительной полуоси: `‖(L_a - t²) y‖ ≤ C ‖y‖` с постоянной `C`,
не зависящей от `t`. -/
theorem halfSlope_quasimodes : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    ∃ (y : IntervalL2) (hy : MemDirichletH2 y), y ≠ 0 ∧
      ‖variableSobolevOperator halfSlopeClass y hy.1 - ((t : ℂ) ^ 2) • y‖ ≤ C * ‖y‖ := by
  have h1 : ContDiff ℝ 1 (deriv halfSlopeCut) := ContDiff.deriv' halfSlopeCut_contDiff_two
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
  obtain ⟨c₀, hc₀, hlow⟩ := halfSlopeZL_norm_ge
  set γ : ℝ := 1 / 200 - 1 / 512 with hγ
  have hγ0 : 0 < γ := by norm_num [hγ]
  set B : ℝ := 1 + 1 / (4 * γ) with hB
  set K : ℝ := 4 * M₂ + 16 * M₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨3 / 64 + m₀ * K * B / c₀, fun t ht => ?_⟩
  set Z := halfSlopeZL t
  have hZ := halfSlopeZL_memDirichletH2 t
  set y := parityRotationInv Z with hydef
  have hy : MemDirichletH2 y := by
    rw [hydef, parityRotationInv_eq]
    exact (hZ.smul _).add (hZ.reflect.smul _)
  have hUy : parityRotation y = Z := parityRotation_parityRotationInv _
  have hyn : ‖y‖ = ‖Z‖ := by rw [← parityRotation_norm y, hUy]
  set e := Real.exp (-4 * t * (1 + 1 / 512)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hZlow := hlow t ht
  have hZpos : 0 < ‖Z‖ := lt_of_lt_of_le (mul_pos hc₀ he0) hZlow
  refine ⟨y, hy, fun h0 => by rw [h0, norm_zero] at hyn; linarith, ?_⟩
  have hres := halfSlope_rotated_residual t hy.1
  set F := parityRotation (variableSobolevOperator halfSlopeClass y hy.1 - ((t : ℂ) ^ 2) • y)
    with hF
  have hFn : ‖variableSobolevOperator halfSlopeClass y hy.1 - ((t : ℂ) ^ 2) • y‖ = ‖F‖ :=
    (parityRotation_norm _).symm
  have hAm : MemLp (fun x => -(3 / 64) * halfSlopeZ t x / halfSlopeS x) 2 intervalMeasure :=
    continuous_memLp_interval _ ((continuous_const.mul (halfSlopeZ_contDiff t).continuous).div
      (halfSlopeS_contDiff (n := 0)).continuous halfSlopeS_ne_zero)
  have hBm : MemLp (fun x => -halfSlopeR t x) 2 intervalMeasure :=
    continuous_memLp_interval _ (halfSlopeR_continuous t).neg
  set A : IntervalL2 := hAm.toLp _
  set Bv : IntervalL2 := hBm.toLp _
  have hFAB : F = A + Bv := by
    apply Lp.ext
    filter_upwards [hres, Lp.coeFn_add A Bv, hAm.coeFn_toLp, hBm.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    ring
  have hA : ‖A‖ ≤ 3 / 64 * ‖Z‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hAm.coeFn_toLp, halfSlopeZL_ae t] with x h1 h2
    rw [h1, h2, mul_div_assoc, norm_mul]
    have : ‖(-(3 / 64) : ℂ)‖ = 3 / 64 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (halfSlopeZ_div_norm_le t x) (by norm_num)
  have hBv : ‖Bv‖ ≤ m₀ * (K * (1 + t) * Real.exp (-4 * t * (1 + 1 / 200))) := by
    apply Lp.norm_le_of_ae_bound (by positivity)
    filter_upwards [hBm.coeFn_toLp, ae_restrict_mem measurableSet_Ioo] with x h1 hx
    rw [h1, norm_neg]
    have hxI : x ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hx
    exact halfSlopeR_norm_le ht (abs_le.2 hxI) (hM₁ x hxI) (hM₂ x hxI)
  have hexp : (1 + t) * Real.exp (-4 * t * (1 + 1 / 200)) ≤ B * e := by
    have hsplit : Real.exp (-4 * t * (1 + 1 / 200)) = Real.exp (-(4 * γ * t)) * e := by
      rw [he, ← Real.exp_add]
      congr 1
      rw [hγ]
      ring
    have hlin : 1 + 4 * γ * t ≤ Real.exp (4 * γ * t) := by
      have := Real.add_one_le_exp (4 * γ * t)
      linarith
    have hB1 : 1 + t ≤ B * (1 + 4 * γ * t) := by
      rw [hB]
      have : 1 / (4 * γ) * (4 * γ * t) = t := by field_simp
      nlinarith
    have hinv : (1 + 4 * γ * t) * Real.exp (-(4 * γ * t)) ≤ 1 := by
      rw [Real.exp_neg]
      rw [mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
      exact hlin
    rw [hsplit]
    have hB0 : 0 ≤ B := by positivity
    calc (1 + t) * (Real.exp (-(4 * γ * t)) * e)
        ≤ (B * (1 + 4 * γ * t)) * (Real.exp (-(4 * γ * t)) * e) :=
          mul_le_mul_of_nonneg_right hB1 (by positivity)
      _ = B * ((1 + 4 * γ * t) * Real.exp (-(4 * γ * t))) * e := by ring
      _ ≤ B * 1 * e := by gcongr
      _ = B * e := by ring
  have he_le : e ≤ ‖Z‖ / c₀ := by
    rw [le_div_iff₀ hc₀, mul_comm]
    exact hZlow
  have hBv' : ‖Bv‖ ≤ m₀ * K * B / c₀ * ‖Z‖ := by
    calc ‖Bv‖ ≤ m₀ * (K * (1 + t) * Real.exp (-4 * t * (1 + 1 / 200))) := hBv
      _ = m₀ * K * ((1 + t) * Real.exp (-4 * t * (1 + 1 / 200))) := by ring
      _ ≤ m₀ * K * (B * e) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ m₀ * K * (B * (‖Z‖ / c₀)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left he_le (by positivity)
      _ = m₀ * K * B / c₀ * ‖Z‖ := by ring
  rw [hFn, hFAB, hyn]
  calc ‖A + Bv‖ ≤ ‖A‖ + ‖Bv‖ := norm_add_le _ _
    _ ≤ 3 / 64 * ‖Z‖ + m₀ * K * B / c₀ * ‖Z‖ := add_le_add hA hBv'
    _ = (3 / 64 + m₀ * K * B / c₀) * ‖Z‖ := by ring

/-- Счётная функция собственных значений при наличии базиса Рисса из собственных векторов:
индексов с `‖λ_i‖ ≤ r` не больше `c √r + 2`. -/
theorem rieszEigenbasis_count (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1)
    {ι : Type} (b : RieszBasis ι IntervalL2) (lam : ι → ℂ)
    (hb : ∀ i, ∃ hf : MemDirichletH2 (b.vector i),
      variableSobolevOperator a (b.vector i) hf.1 = lam i • b.vector i) :
    ∃ c : ℝ, ∀ r : ℝ, 0 ≤ r → ∀ s : Finset ι, (∀ i ∈ s, ‖lam i‖ ≤ r) →
      (s.card : ℝ) ≤ c * Real.sqrt r + 2 := by
  have hvne : ∀ i, b.vector i ≠ 0 := by
    intro i hz
    have h := b.repr_vector i
    rw [hz, map_zero] at h
    have h1 := congrArg (fun v : lp (fun _ : ι => ℂ) 2 => v i) h
    simp at h1
  have hlam : ∀ i, lam i ≠ 0 := fun i => by
    obtain ⟨hf, he⟩ := hb i
    exact variableOperator_eigenvalue_ne_zero a d hd _ hf (hvne i) _ he
  have hK : ∀ i, variableGreen a d (b.vector i) = (lam i)⁻¹ • b.vector i := fun i =>
    (variableOperator_eigen_iff a d hd _ _ (hlam i)).mp (hb i)
  set Cb := ‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr.toContinuousLinearMap‖ with hCb
  set T := principalOperatorInverse a d with hT
  set A := Cb * ‖T‖ + 1 with hA
  have hCb0 : 0 ≤ Cb := by positivity
  have hA0 : 0 < A := by positivity
  have hpi := Real.pi_pos
  refine ⟨2 * Real.sqrt A / Real.pi, fun r hr s hs => ?_⟩
  rcases hr.eq_or_lt with hr0 | hr0
  · have hempty : s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      have h := hs i hi
      rw [← hr0] at h
      exact hlam i (norm_le_zero_iff.mp h)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  set N := ⌊Real.sqrt (A * r) / Real.pi⌋₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNlt : Real.sqrt (A * r) / Real.pi < N := by
    rw [hNdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hNle : (N : ℝ) ≤ Real.sqrt (A * r) / Real.pi + 1 := by
    rw [hNdef]
    push_cast
    have := Nat.floor_le (a := Real.sqrt (A * r) / Real.pi) (by positivity)
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set F₀ := diagOp constantModelHilbertBasis (greenHeadSymbol N) with hF₀
  set E₀ := diagOp constantModelHilbertBasis (greenTailSymbol N) with hE₀
  have hsplit : spectralGreen = F₀ + E₀ := spectralGreen_head_add_tail N hN1
  set P := Submodule.span ℂ (Set.range fun j : ↥(modeHead N) => constantModelHilbertBasis j)
    with hP
  have hfdP : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hrankP : Module.finrank ℂ P ≤ 2 * N := by
    calc
      Module.finrank ℂ P ≤ Fintype.card ↥(modeHead N) :=
        finrank_range_le_card fun j : ↥(modeHead N) => constantModelHilbertBasis j
      _ = (modeHead N).card := Fintype.card_coe _
      _ = 2 * N := card_modeHead N
  have hE₀norm : ‖E₀‖ ≤ (((N : ℝ) * Real.pi) ^ 2)⁻¹ :=
    diagOp_norm_le constantModelHilbertBasis (greenTailSymbol N) _ (by positivity)
      (greenTailSymbol_norm_le N hN1)
  have hNpi : 0 < (N : ℝ) * Real.pi := by positivity
  have hsq : A * r < ((N : ℝ) * Real.pi) ^ 2 := by
    have hlt : Real.sqrt (A * r) < (N : ℝ) * Real.pi := by
      rwa [div_lt_iff₀ hpi] at hNlt
    have h0 : 0 ≤ Real.sqrt (A * r) := Real.sqrt_nonneg _
    have h1 := Real.sq_sqrt (by positivity : 0 ≤ A * r)
    nlinarith
  have hG : Cb * ‖E₀ ∘L T‖ < r⁻¹ := by
    have h1 : Cb * ‖E₀ ∘L T‖ ≤ Cb * ((((N : ℝ) * Real.pi) ^ 2)⁻¹ * ‖T‖) :=
      mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hE₀norm (norm_nonneg _))) hCb0
    refine lt_of_le_of_lt h1 ?_
    rw [show Cb * ((((N : ℝ) * Real.pi) ^ 2)⁻¹ * ‖T‖) =
        (Cb * ‖T‖) / (((N : ℝ) * Real.pi) ^ 2) by ring, div_lt_iff₀ (by positivity),
      show r⁻¹ * (((N : ℝ) * Real.pi) ^ 2) = (((N : ℝ) * Real.pi) ^ 2) / r by ring,
      lt_div_iff₀ hr0]
    have hAr : A * r = Cb * ‖T‖ * r + r := by rw [hA]; ring
    linarith
  have hcard : s.card ≤ 2 * N := by
    refine b.card_le_of_finiteRank_approx (variableGreen a d) (F₀ ∘L T) (E₀ ∘L T) ?_ P (2 * N)
      hrankP ?_ (fun i => (lam i)⁻¹) hK r⁻¹ hG s ?_
    · change spectralGreen ∘L T = _
      rw [hsplit, ContinuousLinearMap.add_comp]
    · intro x
      exact greenHead_range N (T x)
    · intro i hi
      rw [norm_inv]
      exact inv_anti₀ (norm_pos_iff.mpr (hlam i)) (hs i hi)
  have hcardR : (s.card : ℝ) ≤ 2 * N := by exact_mod_cast hcard
  have hsqrt : Real.sqrt (A * r) = Real.sqrt A * Real.sqrt r := Real.sqrt_mul hA0.le r
  calc
    (s.card : ℝ) ≤ 2 * N := hcardR
    _ ≤ 2 * (Real.sqrt (A * r) / Real.pi + 1) := by linarith
    _ = 2 * Real.sqrt A / Real.pi * Real.sqrt r + 2 := by rw [hsqrt]; ring

/-- Для нечётного коэффициента `a(x) = x / 2` (класс `W¹∞`, `|a(x) a(-x)| ≤ 1/4`)
не существует базиса Рисса пространства `L₂(-1,1)`, состоящего из собственных функций `L_a`. -/
theorem halfSlope_no_riesz_eigenbasis :
    ¬ ∃ (ι : Type) (b : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemDirichletH2 (b.vector i), ∃ lam : ℂ,
        variableSobolevOperator halfSlopeClass (b.vector i) hf.1 = lam • b.vector i := by
  classical
  rintro ⟨ι, b, hb⟩
  choose hf lam he using hb
  let dinv := determinantInverse halfSlopeCoefficient halfSlopeCoefficient_memLp (1 / 4)
    (by norm_num) halfSlopeClass_product
  have hd := determinantInverse_identity halfSlopeCoefficient halfSlopeCoefficient_memLp (1 / 4)
    (by norm_num) halfSlopeClass_product
  let Cb := ‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr.toContinuousLinearMap‖
  have hCb : 0 ≤ Cb := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨C, hq⟩ := halfSlope_quasimodes
  set D := Cb * max C 0 + 1 with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ Cb * max C 0 := mul_nonneg hCb (le_max_right _ _)
    linarith
  have hD0 : 0 < D := by linarith
  have hnear : ∀ t : ℝ, 0 ≤ t → ∃ i, ‖lam i - (t : ℂ) ^ 2‖ < D := by
    intro t ht
    obtain ⟨y, hy, hy0, hyq⟩ := hq t ht
    by_contra hnone
    have hall : ∀ i, D ≤ ‖lam i - (t : ℂ) ^ 2‖ := fun i => le_of_not_gt fun h => hnone ⟨i, h⟩
    have hlow := rieszEigenbasis_lower_bound halfSlopeClass dinv hd b lam
      (fun i => ⟨hf i, he i⟩) y hy ((t : ℂ) ^ 2) D hD0.le hall
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have h2 : Cb * ‖variableSobolevOperator halfSlopeClass y hy.1 - ((t : ℂ) ^ 2) • y‖ ≤
        Cb * (max C 0 * ‖y‖) :=
      mul_le_mul_of_nonneg_left (hyq.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hCb
    have h3 : D * ‖y‖ = Cb * (max C 0 * ‖y‖) + ‖y‖ := by rw [hDdef]; ring
    linarith
  have hpt : ∀ k : ℕ, ∃ i, ‖lam i - ((3 * D * ((k : ℝ) + 1) : ℝ) : ℂ)‖ < D := by
    intro k
    have hx : 0 ≤ 3 * D * ((k : ℝ) + 1) := by positivity
    obtain ⟨i, hi⟩ := hnear (Real.sqrt (3 * D * ((k : ℝ) + 1))) (Real.sqrt_nonneg _)
    refine ⟨i, ?_⟩
    rwa [← Complex.ofReal_pow, Real.sq_sqrt hx] at hi
  choose f hf' using hpt
  obtain ⟨c, hc⟩ := rieszEigenbasis_count halfSlopeClass dinv hd b lam (fun i => ⟨hf i, he i⟩)
  set B := |c| * Real.sqrt (4 * D) + 2 with hB
  have hB2 : 2 ≤ B := by
    have : 0 ≤ |c| * Real.sqrt (4 * D) := by positivity
    linarith
  set n := ⌈B ^ 2⌉₊ + 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈B ^ 2⌉₊]
  have hnB : B ^ 2 + 1 ≤ (n : ℝ) := by
    rw [hn]; push_cast; linarith [Nat.le_ceil (B ^ 2)]
  have hinj : Set.InjOn f (Finset.range n : Set ℕ) := by
    intro p _ q _ hpq
    have h1 := hf' p
    have h2 := hf' q
    rw [hpq] at h1
    have h3 : ‖((3 * D * ((p : ℝ) + 1) : ℝ) : ℂ) - ((3 * D * ((q : ℝ) + 1) : ℝ) : ℂ)‖ < 2 * D := by
      have := norm_sub_le (lam (f q) - ((3 * D * ((q : ℝ) + 1) : ℝ) : ℂ))
        (lam (f q) - ((3 * D * ((p : ℝ) + 1) : ℝ) : ℂ))
      rw [sub_sub_sub_cancel_left] at this
      linarith
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at h3
    have h4 : ((p : ℝ) - q) < 1 := by nlinarith
    have h5 : ((q : ℝ) - p) < 1 := by nlinarith
    have h4' : ((p : ℤ) - q) < 1 := by exact_mod_cast h4
    have h5' : ((q : ℤ) - p) < 1 := by exact_mod_cast h5
    omega
  have hbound : ∀ i ∈ (Finset.range n).image f, ‖lam i‖ ≤ 4 * D * n := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
    have h1 := norm_le_norm_add_norm_sub' (lam (f k)) ((3 * D * ((k : ℝ) + 1) : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
    have := hf' k
    nlinarith
  have hcount := hc (4 * D * n) (by positivity) _ hbound
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcount
  have hsq : Real.sqrt (4 * D * n) = Real.sqrt (4 * D) * Real.sqrt n :=
    Real.sqrt_mul (by positivity) _
  set m := Real.sqrt n with hm
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hmm : m * m = n := Real.mul_self_sqrt (by positivity)
  have hmB : B < m := by
    rw [hm]
    apply Real.lt_sqrt_of_sq_lt
    linarith
  have hcm : c * Real.sqrt (4 * D * n) ≤ |c| * Real.sqrt (4 * D) * m := by
    rw [hsq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c)
      (Real.sqrt_nonneg _)) hm0
  have hBm : (n : ℝ) ≤ (B - 2) * m + 2 := by
    rw [hB]; linarith
  nlinarith

end Involution
