module

public import Involution.Setup.ACDomain
public import Involution.Setup.ComplexAC

/-! Узел S-DOMAIN: слабая область Дирихле совпадает с `H² ∩ H₀¹`, где `H₀¹` — замыкание
гладких функций с компактным носителем в `(-1, 1)` по норме `H¹`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Involution

/-- Гладкая функция с носителем в `(-1, 1)` и её производная как элементы `L₂`. -/
def IsTestPair (φ φ' : IntervalL2) : Prop :=
  ∃ u : ℝ → ℂ, ContDiff ℝ ∞ u ∧ tsupport u ⊆ Ioo (-1) 1 ∧
    u =ᵐ[intervalMeasure] φ ∧ deriv u =ᵐ[intervalMeasure] φ'

/-- `H₀¹(-1, 1)`: замыкание пробных функций по норме `H¹`. -/
def MemIntervalH01 (f : IntervalL2) : Prop :=
  ∃ g : IntervalL2, HasL2WeakDeriv f g ∧
    ∀ ε > 0, ∃ φ φ' : IntervalL2, IsTestPair φ φ' ∧ ‖f - φ‖ < ε ∧ ‖g - φ'‖ < ε

/-- Формула интегрирования по частям в терминах скалярных произведений `L₂`. -/
theorem inner_add_inner_eq_boundary {a b f g : IntervalL2} {A B F G : ℝ → ℂ}
    (hA : A =ᵐ[intervalMeasure] fun x => star (a x))
    (hB : B =ᵐ[intervalMeasure] fun x => star (b x))
    (hBac : AbsolutelyContinuousOnInterval B (-1) 1)
    (hdB : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt B (A x) x)
    (hF : F =ᵐ[intervalMeasure] f) (hG : G =ᵐ[intervalMeasure] g)
    (hFac : AbsolutelyContinuousOnInterval F (-1) 1)
    (hdF : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (G x) x) :
    inner ℂ a f + inner ℂ b g = B 1 * F 1 - B (-1) * F (-1) := by
  have hAi : IntervalIntegrable A volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr
      ((show Integrable (fun x => star (a x)) intervalMeasure from
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (intervalL2_integrable a)).congr hA.symm)
  have hGi : IntervalIntegrable G volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr
      ((intervalL2_integrable g).congr hG.symm)
  have key := complex_ac_integral_product_derivative hBac hFac hAi hGi
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdB)
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdF)
  rw [← key, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    ← integral_add (L2.integrable_inner a f) (L2.integrable_inner b g),
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  change _ = ∫ x, _ ∂intervalMeasure
  apply integral_congr_ae
  filter_upwards [hA, hB, hF, hG] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, RCLike.inner_apply, Complex.star_def]
  ring

/-- Пространство пар `(f, g)` с нормой `L₂ × L₂`. -/
abbrev IntervalH1Pair := WithLp 2 (IntervalL2 × IntervalL2)

theorem IsTestPair.zero : IsTestPair 0 0 := by
  refine ⟨0, contDiff_const, by simp, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_zero ℂ 2 intervalMeasure] with x hx
    rw [hx]
  · filter_upwards [Lp.coeFn_zero ℂ 2 intervalMeasure] with x hx
    rw [hx]
    simp

theorem IsTestPair.add {φ φ' ψ ψ' : IntervalL2} (h₁ : IsTestPair φ φ')
    (h₂ : IsTestPair ψ ψ') : IsTestPair (φ + ψ) (φ' + ψ') := by
  obtain ⟨u, hu, hus, hu1, hu2⟩ := h₁
  obtain ⟨v, hv, hvs, hv1, hv2⟩ := h₂
  refine ⟨u + v, hu.add hv, (tsupport_add u v).trans (union_subset hus hvs), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add φ ψ, hu1, hv1] with x hx h1 h2
    rw [hx, Pi.add_apply, Pi.add_apply, h1, h2]
  · have hd : deriv (u + v) = deriv u + deriv v := by
      funext x
      exact deriv_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)
    filter_upwards [Lp.coeFn_add φ' ψ', hu2, hv2] with x hx h1 h2
    rw [hd, hx, Pi.add_apply, Pi.add_apply, h1, h2]

theorem IsTestPair.smul {φ φ' : IntervalL2} (c : ℂ) (h : IsTestPair φ φ') :
    IsTestPair (c • φ) (c • φ') := by
  obtain ⟨u, hu, hus, hu1, hu2⟩ := h
  refine ⟨c • u, hu.const_smul c, (tsupport_smul_subset_right (fun _ => c) u).trans hus, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c φ, hu1] with x hx h1
    rw [hx, Pi.smul_apply, Pi.smul_apply, h1]
  · have hd : deriv (c • u) = c • deriv u := by
      funext x
      exact deriv_const_smul c (hu.differentiable (by simp) x)
    filter_upwards [Lp.coeFn_smul c φ', hu2] with x hx h1
    rw [hd, hx, Pi.smul_apply, Pi.smul_apply, h1]

/-- Подпространство пробных пар `(u, u')`. -/
def testPairSubmodule : Submodule ℂ IntervalH1Pair where
  carrier := {p | IsTestPair (WithLp.ofLp p).1 (WithLp.ofLp p).2}
  zero_mem' := by simpa using IsTestPair.zero
  add_mem' := by
    intro p q hp hq
    simpa using hp.add hq
  smul_mem' := by
    intro c p hp
    simpa using hp.smul c

theorem approx_iff_mem_closure (f g : IntervalL2) :
    (∀ ε > 0, ∃ φ φ' : IntervalL2, IsTestPair φ φ' ∧ ‖f - φ‖ < ε ∧ ‖g - φ'‖ < ε) ↔
      WithLp.toLp 2 (f, g) ∈ testPairSubmodule.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨φ, φ', hφ, h1, h2⟩ := h (ε / 2) (by positivity)
    refine ⟨WithLp.toLp 2 (φ, φ'), hφ, ?_⟩
    rw [dist_eq_norm, ← WithLp.toLp_sub, WithLp.prod_norm_eq_of_L2]
    simp only [Prod.fst_sub, Prod.snd_sub, WithLp.toLp_fst, WithLp.toLp_snd]
    rw [Real.sqrt_lt' hε]
    have := norm_nonneg (f - φ)
    have := norm_nonneg (g - φ')
    nlinarith
  · intro h ε hε
    obtain ⟨p, hp, hd⟩ := h ε hε
    have key := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (f, g) - p)
    rw [← dist_eq_norm] at key
    have h1 : (WithLp.toLp 2 (f, g) - p).fst = f - (WithLp.ofLp p).1 := rfl
    have h2 : (WithLp.toLp 2 (f, g) - p).snd = g - (WithLp.ofLp p).2 := rfl
    rw [h1, h2] at key
    have := norm_nonneg (f - (WithLp.ofLp p).1)
    have := norm_nonneg (g - (WithLp.ofLp p).2)
    have := dist_nonneg (x := WithLp.toLp 2 (f, g)) (y := p)
    refine ⟨(WithLp.ofLp p).1, (WithLp.ofLp p).2, hp, ?_, ?_⟩
    · nlinarith
    · nlinarith

theorem mem_orthogonal_of_boundary {q : IntervalH1Pair} {A B : ℝ → ℂ}
    (hA : A =ᵐ[intervalMeasure] fun x => star ((WithLp.ofLp q).1 x))
    (hB : B =ᵐ[intervalMeasure] fun x => star ((WithLp.ofLp q).2 x))
    (hBac : AbsolutelyContinuousOnInterval B (-1) 1)
    (hdB : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt B (A x) x) :
    q ∈ testPairSubmoduleᗮ := by
  rw [Submodule.mem_orthogonal']
  intro p hp
  obtain ⟨u, hu, hus, hu1, hu2⟩ := hp
  have hu0 : ∀ x ∉ Ioo (-1 : ℝ) 1, u x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hus h))
  have hu1' : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast le_top)
  rw [WithLp.prod_inner_apply, inner_add_inner_eq_boundary hA hB hBac hdB hu1 hu2
    hu1'.contDiffOn.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall fun x _ => (hu.differentiable (by simp) x).hasDerivAt),
    hu0 1 (by simp), hu0 (-1) (by simp)]
  simp

theorem hasIntervalWeakDeriv_of_mem_orthogonal {q : IntervalH1Pair}
    (hq : q ∈ testPairSubmoduleᗮ) :
    HasIntervalWeakDeriv (fun x => star ((WithLp.ofLp q).2 x))
      (fun x => star ((WithLp.ofLp q).1 x)) := by
  have hint : ∀ a : IntervalL2, Integrable (fun x => star (a x)) intervalMeasure := fun a =>
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (intervalL2_integrable a)
  refine ⟨hint _, hint _, ?_⟩
  intro φ hφ
  set u : ℝ → ℂ := fun x => (φ x : ℂ) with hu_def
  have hd : ∀ x, HasDerivAt u ((deriv φ x : ℝ) : ℂ) x := fun x =>
    ((hφ.1.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have hderiv : deriv u = fun x => ((deriv φ x : ℝ) : ℂ) := funext fun x => (hd x).deriv
  have hu : ContDiff ℝ ∞ u := Complex.ofRealCLM.contDiff.comp hφ.1
  have hu' : Continuous (deriv u) := by
    rw [hderiv]
    exact Complex.continuous_ofReal.comp hφ.deriv.1.continuous
  set U := (continuous_memLp_interval u hu.continuous).toLp u
  set U' := (continuous_memLp_interval (deriv u) hu').toLp (deriv u)
  have hp : WithLp.toLp 2 (U, U') ∈ testPairSubmodule := by
    change IsTestPair U U'
    exact ⟨u, hu, (tsupport_comp_subset Complex.ofReal_zero φ).trans hφ.2.2,
      (MemLp.coeFn_toLp _).symm, (MemLp.coeFn_toLp _).symm⟩
  have h0 := (Submodule.mem_orthogonal' _ _).1 hq _ hp
  rw [WithLp.prod_inner_apply, L2.inner_def, L2.inner_def] at h0
  have e1 : (∫ x, inner ℂ ((WithLp.ofLp q).1 x) ((WithLp.ofLp (WithLp.toLp 2 (U, U'))).1 x)
      ∂intervalMeasure) = ∫ x in Ioo (-1) 1, φ x • star ((WithLp.ofLp q).1 x) := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (continuous_memLp_interval u hu.continuous)] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, hu_def, Complex.real_smul, Complex.star_def]
  have e2 : (∫ x, inner ℂ ((WithLp.ofLp q).2 x) ((WithLp.ofLp (WithLp.toLp 2 (U, U'))).2 x)
      ∂intervalMeasure) = ∫ x in Ioo (-1) 1, deriv φ x • star ((WithLp.ofLp q).2 x) := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (continuous_memLp_interval (deriv u) hu')] with x hx
    rw [hx, hderiv]
    simp only [RCLike.inner_apply, Complex.real_smul, Complex.star_def]
  rw [e1, e2] at h0
  linear_combination h0

theorem boundary_combination_eq_zero_of_mem_closure {f g : IntervalL2} {F : ℝ → ℂ}
    (hmem : WithLp.toLp 2 (f, g) ∈ testPairSubmodule.topologicalClosure)
    (hF : F =ᵐ[intervalMeasure] f) (hFac : AbsolutelyContinuousOnInterval F (-1) 1)
    (hdF : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (g x) x)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (ψ 1 : ℂ) * F 1 - (ψ (-1) : ℂ) * F (-1) = 0 := by
  set B : ℝ → ℂ := fun x => (ψ x : ℂ) with hB_def
  set A : ℝ → ℂ := fun x => ((deriv ψ x : ℝ) : ℂ) with hA_def
  have hBd : ContDiff ℝ 1 B := Complex.ofRealCLM.contDiff.comp hψ
  have hAc : Continuous A := Complex.continuous_ofReal.comp (hψ.continuous_deriv le_rfl)
  have hdB : ∀ x, HasDerivAt B (A x) x := fun x =>
    ((hψ.differentiable one_ne_zero x).hasDerivAt).ofReal_comp
  set a := (continuous_memLp_interval A hAc).toLp A
  set b := (continuous_memLp_interval B hBd.continuous).toLp B
  have hA : A =ᵐ[intervalMeasure] fun x => star ((WithLp.ofLp (WithLp.toLp 2 (a, b))).1 x) := by
    filter_upwards [MemLp.coeFn_toLp (continuous_memLp_interval A hAc)] with x hx
    rw [hx]
    simp [hA_def]
  have hB : B =ᵐ[intervalMeasure] fun x => star ((WithLp.ofLp (WithLp.toLp 2 (a, b))).2 x) := by
    filter_upwards [MemLp.coeFn_toLp (continuous_memLp_interval B hBd.continuous)] with x hx
    rw [hx]
    simp [hB_def]
  have hBac : AbsolutelyContinuousOnInterval B (-1) 1 :=
    hBd.contDiffOn.absolutelyContinuousOnInterval
  have hdB' : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt B (A x) x :=
    Filter.Eventually.of_forall fun x _ => hdB x
  have hq := mem_orthogonal_of_boundary hA hB hBac hdB'
  rw [← Submodule.orthogonal_orthogonal_eq_closure] at hmem
  have h0 := (Submodule.mem_orthogonal _ _).1 hmem _ hq
  rw [WithLp.prod_inner_apply, inner_add_inner_eq_boundary hA hB hBac hdB' hF
    Filter.EventuallyEq.rfl hFac hdF] at h0
  exact h0

theorem memIntervalH01_iff_trace (f : IntervalL2) :
    MemIntervalH01 f ↔ (∃ g : IntervalL2, HasL2WeakDeriv f g) ∧ HasDirichletTrace f := by
  constructor
  · rintro ⟨g, hfg, happrox⟩
    have hmem := (approx_iff_mem_closure f g).1 happrox
    obtain ⟨F, hF, hFac, hdF⟩ := hfg.exists_ac_representative
    have h1 := boundary_combination_eq_zero_of_mem_closure hmem hF.2 hFac hdF
      (fun x => x + 1) (by fun_prop)
    have h2 := boundary_combination_eq_zero_of_mem_closure hmem hF.2 hFac hdF
      (fun x => x - 1) (by fun_prop)
    norm_num at h1 h2
    exact ⟨⟨g, hfg⟩, F, hF, h2, h1⟩
  · rintro ⟨⟨g, hfg⟩, htr⟩
    refine ⟨g, hfg, (approx_iff_mem_closure f g).2 ?_⟩
    obtain ⟨F, hF, hFac, hdF⟩ := hfg.exists_ac_representative
    obtain ⟨hl, hr⟩ := htr.boundary hF
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro q hq
    obtain ⟨B, hBac, hBeq, hdB⟩ := HasWeakDerivOn.exists_ac_representative
      (by norm_num : (-1 : ℝ) < 1) (hasIntervalWeakDeriv_of_mem_orthogonal hq)
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hdB
    rw [WithLp.prod_inner_apply, inner_add_inner_eq_boundary Filter.EventuallyEq.rfl hBeq hBac
      hdB hF.2 Filter.EventuallyEq.rfl hFac hdF, hl, hr]
    simp

theorem memDirichletH2_iff_h2_and_h01 (f : IntervalL2) :
    MemDirichletH2 f ↔ MemIntervalH2 f ∧ MemIntervalH01 f := by
  constructor
  · rintro ⟨hH2, htr⟩
    obtain ⟨g, _, hfg, _⟩ := hH2
    exact ⟨⟨g, _, hfg, ‹_›⟩, (memIntervalH01_iff_trace f).2 ⟨⟨g, hfg⟩, htr⟩⟩
  · rintro ⟨hH2, hH01⟩
    exact ⟨hH2, ((memIntervalH01_iff_trace f).1 hH01).2⟩

end Involution
