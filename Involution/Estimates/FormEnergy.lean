module

public import Involution.Estimates.SobolevClosure
public import Involution.Estimates.FormMarkusMatsaev
public import Involution.Model.GaugeOperators

/-! Энергетическое пространство диагонализованной модели `T = V (-D²) V`.

Пусть `W` — симметричный ограниченный оператор с обратным `V`, и `W G W eᵢ = λᵢ⁻¹ eᵢ` в
ортонормированном базисе `e`, где `G` — обратный оператор Дирихле. Тогда
`x ∈ formDomain e λ` равносильно `V x ∈ H₀¹`, производная `(V x)'` равна сумме ряда
`Φ x = ∑ ⟨eᵢ, x⟩ (V eᵢ)'`, и `⟨(V y)', (V x)'⟩ = formPairing e λ y x`.
Пара `(f, g)` с `f ∈ H₀¹`, `f' = g` — `IsH01Pair f g`; множество таких пар замкнуто
в `L₂ × L₂`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace Involution

/-! ### Замкнутость пар `(f, f')` в `H₀¹` -/

theorem setIntegral_real_smul_eq_inner (φ : ℝ → ℝ) (hφ : Continuous φ) (f : IntervalL2) :
    (∫ x in Ioo (-1 : ℝ) 1, φ x • f x) =
      inner ℂ ((continuous_memLp_interval (fun x => (φ x : ℂ))
        (Complex.continuous_ofReal.comp hφ)).toLp _) f := by
  rw [l2_inner_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (continuous_memLp_interval (fun x => (φ x : ℂ))
    (Complex.continuous_ofReal.comp hφ))] with x hx
  rw [hx]
  simp [Complex.real_smul]

theorem isClosed_weakDerivPairs :
    IsClosed {q : IntervalL2 × IntervalL2 | HasL2WeakDeriv q.1 q.2} := by
  have hset : {q : IntervalL2 × IntervalL2 | HasL2WeakDeriv q.1 q.2} =
      ⋂ φ ∈ {φ : ℝ → ℝ | IsSmoothTestOn (Ioo (-1) 1) φ},
        {q : IntervalL2 × IntervalL2 |
          (∫ x in Ioo (-1 : ℝ) 1, deriv φ x • q.1 x) = -(∫ x in Ioo (-1 : ℝ) 1, φ x • q.2 x)} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h φ hφ
      exact h.2.2 φ hφ
    · intro h
      exact ⟨intervalL2_integrable q.1, intervalL2_integrable q.2, h⟩
  rw [hset]
  refine isClosed_biInter fun φ hφ => ?_
  have hd : Continuous (deriv φ) := hφ.deriv.1.continuous
  have hc : Continuous φ := hφ.1.continuous
  simp only [setIntegral_real_smul_eq_inner _ hd, setIntegral_real_smul_eq_inner _ hc]
  exact isClosed_eq (continuous_const.inner continuous_fst)
    (continuous_const.inner continuous_snd).neg

/-- Пара `(f, g)`: `f ∈ H₀¹` и `g = f'`. -/
def IsH01Pair (f g : IntervalL2) : Prop := HasL2WeakDeriv f g ∧ HasDirichletTrace f

theorem isH01Pair_iff (f g : IntervalL2) :
    IsH01Pair f g ↔
      HasL2WeakDeriv f g ∧ WithLp.toLp 2 (f, g) ∈ testPairSubmodule.topologicalClosure := by
  constructor
  · rintro ⟨hfg, htr⟩
    obtain ⟨g', hfg', happ⟩ := (memIntervalH01_iff_trace f).2 ⟨⟨g, hfg⟩, htr⟩
    have hgg : g' = g := hfg'.unique hfg
    subst hgg
    exact ⟨hfg, (approx_iff_mem_closure f g').1 happ⟩
  · rintro ⟨hfg, hmem⟩
    exact ⟨hfg, ((memIntervalH01_iff_trace f).1
      ⟨g, hfg, (approx_iff_mem_closure f g).2 hmem⟩).2⟩

theorem isClosed_h01Pairs : IsClosed {q : IntervalL2 × IntervalL2 | IsH01Pair q.1 q.2} := by
  have hset : {q : IntervalL2 × IntervalL2 | IsH01Pair q.1 q.2} =
      {q : IntervalL2 × IntervalL2 | HasL2WeakDeriv q.1 q.2} ∩
        (fun q : IntervalL2 × IntervalL2 => WithLp.toLp 2 q) ⁻¹'
          (testPairSubmodule.topologicalClosure : Set IntervalH1Pair) := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, SetLike.mem_coe]
    exact isH01Pair_iff q.1 q.2
  rw [hset]
  exact isClosed_weakDerivPairs.inter
    ((Submodule.isClosed_topologicalClosure _).preimage (WithLp.prod_continuous_toLp 2 _ _))

theorem HasDirichletTrace.add_trace {f g : IntervalL2} (hf : HasDirichletTrace f)
    (hg : HasDirichletTrace g) : HasDirichletTrace (f + g) := by
  obtain ⟨F, hF, hF1, hF2⟩ := hf
  obtain ⟨G, hG, hG1, hG2⟩ := hg
  refine ⟨F + G, ⟨hF.1.add hG.1, (hF.2.add hG.2).trans (Lp.coeFn_add f g).symm⟩, ?_, ?_⟩
  · simp [hF1, hG1]
  · simp [hF2, hG2]

theorem HasDirichletTrace.smul_trace {f : IntervalL2} (hf : HasDirichletTrace f) (c : ℂ) :
    HasDirichletTrace (c • f) := by
  obtain ⟨F, hF, hF1, hF2⟩ := hf
  refine ⟨fun x => c * F x, ⟨continuousOn_const.mul hF.1, ?_⟩, ?_, ?_⟩
  · filter_upwards [hF.2, Lp.coeFn_smul c f] with x h1 h2
    rw [h2, Pi.smul_apply, h1, smul_eq_mul]
  · simp [hF1]
  · simp [hF2]

theorem IsH01Pair.add {f g f₁ g₁ : IntervalL2} (h : IsH01Pair f g) (h₁ : IsH01Pair f₁ g₁) :
    IsH01Pair (f + f₁) (g + g₁) := ⟨h.1.add h₁.1, h.2.add_trace h₁.2⟩

theorem IsH01Pair.smul {f g : IntervalL2} (h : IsH01Pair f g) (c : ℂ) :
    IsH01Pair (c • f) (c • g) := ⟨h.1.smul c, h.2.smul_trace c⟩

theorem IsH01Pair.zero : IsH01Pair 0 0 := by
  have hG := spectralGreen_memDirichletH2 0
  have h : IsH01Pair (spectralGreen 0) (firstWeakDeriv (spectralGreen 0) hG.1) :=
    ⟨firstWeakDeriv_spec _ hG.1, hG.2⟩
  simpa using h.smul 0

/-- Интегрирование по частям: `⟨u, v''⟩ = -⟨u', v'⟩` для `u ∈ H₀¹` и `v' ∈ H¹`. -/
theorem IsH01Pair.inner_second {u g v' v'' : IntervalL2} (hu : IsH01Pair u g)
    (hv' : HasL2WeakDeriv v' v'') :
    inner ℂ u v'' = -inner ℂ g v' := by
  obtain ⟨F, hF, hFac, hdF⟩ := hu.1.exists_ac_representative
  obtain ⟨V, hV, hVac, hdV⟩ := hv'.exists_ac_representative
  have hgi : IntervalIntegrable g volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr hu.1.2.1
  have hhi : IntervalIntegrable v'' volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr hv'.2.1
  have hparts := complex_ac_green_identity hFac hVac hgi hhi
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdF)
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdV)
  obtain ⟨hleft, hright⟩ := hu.2.boundary hF
  simp only [hleft, hright, star_zero, zero_mul, sub_self, zero_sub] at hparts
  rw [l2_inner_integral, l2_inner_integral]
  calc
    _ = ∫ x, star (F x) * v'' x ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [hF.2] with x hx
      rw [hx]
    _ = -(∫ x, star (g x) * V x ∂intervalMeasure) := by
      rw [integral_complex_intervalMeasure, integral_complex_intervalMeasure]
      exact hparts
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hV.2] with x hx
      rw [hx]

/-! ### Диагонализованная модель -/

section Model

variable (Wm Vm : IntervalL2 →L[ℂ] IntervalL2) {ι : Type*}
  (e : HilbertBasis ι ℂ IntervalL2) (lam : ι → ℝ)

/-- Производная собственной функции `(V eᵢ)' = λᵢ (G W eᵢ)'`. -/
def modeDeriv (i : ι) : IntervalL2 := (lam i : ℂ) • greenDeriv (Wm (e i))

/-- Ряд `Φ x = ∑ ⟨eᵢ, x⟩ (V eᵢ)'` — производная `V x` на области формы. -/
def formDeriv (x : IntervalL2) : IntervalL2 := ∑' i, e.repr x i • modeDeriv Wm e lam i

variable {Wm Vm e lam}

theorem green_isH01Pair (h : IntervalL2) : IsH01Pair (spectralGreen h) (greenDeriv h) :=
  ⟨firstWeakDeriv_spec _ (spectralGreen_memDirichletH2 h).1,
    (spectralGreen_memDirichletH2 h).2⟩

theorem greenDeriv_hasDeriv (h : IntervalL2) : HasL2WeakDeriv (greenDeriv h) (-h) := by
  have h2 := secondWeakDeriv_spec _ (spectralGreen_memDirichletH2 h).1
  have h3 : -h = secondWeakDeriv (spectralGreen h) (spectralGreen_memDirichletH2 h).1 :=
    neg_eq_iff_eq_neg.2 (spectralGreen_right_inverse h).symm
  rw [h3]
  exact h2

theorem mode_eq (hlam : ∀ i, 0 < lam i) (hVW : ∀ z, Vm (Wm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i) (i : ι) :
    Vm (e i) = (lam i : ℂ) • spectralGreen (Wm (e i)) := by
  have h := congrArg Vm (hK i)
  rw [hVW, map_smul] at h
  rw [h, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (hlam i).ne', Complex.ofReal_one,
    one_smul]

theorem mode_isH01Pair (hlam : ∀ i, 0 < lam i) (hVW : ∀ z, Vm (Wm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i) (i : ι) :
    IsH01Pair (Vm (e i)) (modeDeriv Wm e lam i) := by
  rw [mode_eq hlam hVW hK i]
  exact (green_isH01Pair _).smul _

theorem modeDeriv_hasDeriv (i : ι) :
    HasL2WeakDeriv (modeDeriv Wm e lam i) (-((lam i : ℂ) • Wm (e i))) := by
  rw [← smul_neg]
  exact (greenDeriv_hasDeriv _).smul _

/-- `⟨(V eᵢ)', u'⟩ = λᵢ ⟨eᵢ, W u⟩` для `u ∈ H₀¹`. -/
theorem inner_modeDeriv (hWsym : Wm.IsSymmetric) {u g : IntervalL2} (hu : IsH01Pair u g)
    (i : ι) : inner ℂ (modeDeriv Wm e lam i) g = (lam i : ℂ) * inner ℂ (e i) (Wm u) := by
  have h := hu.inner_second (modeDeriv_hasDeriv (Wm := Wm) (e := e) (lam := lam) i)
  rw [inner_neg_right, inner_smul_right, neg_inj] at h
  rw [← inner_conj_symm, ← h, map_mul, Complex.conj_ofReal, inner_conj_symm]
  congr 1
  exact hWsym (e i) u

theorem inner_modeDeriv_modeDeriv (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i) (i j : ι) :
    inner ℂ (modeDeriv Wm e lam i) (modeDeriv Wm e lam j) =
      (lam i : ℂ) * inner ℂ (e i) (e j) := by
  rw [inner_modeDeriv hWsym (mode_isH01Pair hlam hVW hK j), hWV]

/-- Нормированные производные собственных функций ортонормированы. -/
theorem modeDeriv_orthonormal (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i) :
    Orthonormal ℂ fun i => (((Real.sqrt (lam i))⁻¹ : ℝ) : ℂ) • modeDeriv Wm e lam i := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, inner_modeDeriv_modeDeriv hlam hWsym hVW hWV hK,
    (orthonormal_iff_ite.mp e.orthonormal) i j]
  split_ifs with hij
  · subst hij
    rw [Complex.conj_ofReal, mul_one, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : (Real.sqrt (lam i))⁻¹ * ((Real.sqrt (lam i))⁻¹ * lam i) = 1 := by
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (hlam i).le, inv_mul_cancel₀ (hlam i).ne']
    rw [this, Complex.ofReal_one]
  · simp

theorem formDeriv_summable (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i)
    {x : IntervalL2} (hx : x ∈ formDomain e lam) :
    Summable fun i => e.repr x i • modeDeriv Wm e lam i := by
  have ho := modeDeriv_orthonormal hlam hWsym hVW hWV hK
  have hs := (ho.orthogonalFamily.summable_iff_norm_sq_summable
    (fun i => e.repr x i * (Real.sqrt (lam i) : ℂ))).2 ?_
  · convert hs using 1
    funext i
    simp only [LinearIsometry.toSpanSingleton_apply, smul_smul]
    congr 1
    rw [mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hlam i)).ne',
      Complex.ofReal_one, mul_one]
  · have hx' : Summable fun i => lam i * ‖e.repr x i‖ ^ 2 := hx
    convert hx' using 1
    funext i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hlam i).le, mul_comm]

theorem isH01Pair_of_hasSum {κ : Type*} {a b : κ → IntervalL2} {A B : IntervalL2}
    (ha : HasSum a A) (hb : HasSum b B) (h : ∀ i, IsH01Pair (a i) (b i)) : IsH01Pair A B := by
  classical
  have hp := ha.prodMk hb
  refine isClosed_h01Pairs.mem_of_tendsto hp (Filter.Eventually.of_forall fun s => ?_)
  change IsH01Pair (∑ i ∈ s, (a i, b i)).1 (∑ i ∈ s, (a i, b i)).2
  rw [Prod.fst_sum, Prod.snd_sum]
  induction s using Finset.induction_on with
  | empty => simpa using IsH01Pair.zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j).add ih

/-- На области формы `V x ∈ H₀¹` и `(V x)' = Φ x`. -/
theorem formDeriv_isH01Pair (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i)
    {x : IntervalL2} (hx : x ∈ formDomain e lam) :
    IsH01Pair (Vm x) (formDeriv Wm e lam x) := by
  have h1 : HasSum (fun i => e.repr x i • Vm (e i)) (Vm x) := by
    have := (e.hasSum_repr x).mapL Vm
    simpa only [map_smul] using this
  exact isH01Pair_of_hasSum h1 (formDeriv_summable hlam hWsym hVW hWV hK hx).hasSum
    fun i => (mode_isH01Pair hlam hVW hK i).smul _

/-- Обратно: если `V x ∈ H₀¹`, то `x` лежит в области формы. -/
theorem mem_formDomain_of_isH01Pair (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i)
    {x g : IntervalL2} (hx : IsH01Pair (Vm x) g) : x ∈ formDomain e lam := by
  have ho := modeDeriv_orthonormal hlam hWsym hVW hWV hK
  have hb := ho.inner_products_summable (x := g)
  change Summable fun i => lam i * ‖e.repr x i‖ ^ 2
  convert hb using 1
  funext i
  rw [inner_smul_left, inner_modeDeriv hWsym hx, hWV, ← e.repr_apply_apply, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  have : ((Real.sqrt (lam i))⁻¹ * lam i) ^ 2 = lam i := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (hlam i).le, sq, ← mul_assoc, inv_mul_cancel₀ (hlam i).ne',
      one_mul]
  rw [this]

theorem inner_modeDeriv_formDeriv (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i)
    {x : IntervalL2} (hx : x ∈ formDomain e lam) (i : ι) :
    inner ℂ (modeDeriv Wm e lam i) (formDeriv Wm e lam x) = (lam i : ℂ) * e.repr x i := by
  rw [inner_modeDeriv hWsym (formDeriv_isH01Pair hlam hWsym hVW hWV hK hx), hWV,
    e.repr_apply_apply]

/-- `⟨(V y)', (V x)'⟩ = formPairing e λ y x` на области формы. -/
theorem inner_formDeriv (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i)
    {x y : IntervalL2} (hx : x ∈ formDomain e lam) (hy : y ∈ formDomain e lam) :
    inner ℂ (formDeriv Wm e lam y) (formDeriv Wm e lam x) = formPairing e lam y x := by
  have hs := formDeriv_summable hlam hWsym hVW hWV hK hy
  rw [← inner_conj_symm]
  change conj ((innerSL ℂ (formDeriv Wm e lam x)) (∑' i, e.repr y i • modeDeriv Wm e lam i)) = _
  rw [(innerSL ℂ (formDeriv Wm e lam x)).map_tsum hs, Complex.conj_tsum]
  unfold formPairing
  congr 1
  funext i
  rw [innerSL_apply_apply, inner_smul_right, map_mul, inner_conj_symm,
    inner_modeDeriv_formDeriv hlam hWsym hVW hWV hK hx]
  ring

theorem formEnergy_eq (hlam : ∀ i, 0 < lam i) (hWsym : Wm.IsSymmetric)
    (hVW : ∀ z, Vm (Wm z) = z) (hWV : ∀ z, Wm (Vm z) = z)
    (hK : ∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i)
    {x : IntervalL2} (hx : x ∈ formDomain e lam) :
    formEnergy e lam x = ‖formDeriv Wm e lam x‖ ^ 2 := by
  have h := inner_formDeriv hlam hWsym hVW hWV hK hx hx
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((formEnergy e lam x : ℝ) : ℂ) = formPairing e lam x x := by
    unfold formEnergy formPairing
    rw [Complex.ofReal_tsum]
    congr 1
    funext i
    rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]
  exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h2.trans h.symm)

end Model

end Involution
