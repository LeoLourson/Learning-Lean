module

public import Involution.Model.SubordinatePerturbation
public import Involution.Model.EigenvalueCounting
public import Involution.Model.GaugeOperators
public import Involution.Model.EvenCoefficient

/-! Базис Рисса со скобками для знакопостоянного коэффициента с малой производной.
Условия: вещественный `a ∈ W²∞`, `0 < m ≤ |a| ≤ M`, `|a(x) a(-x)| ≤ κ < 1` и
`|a'| ≤ ε` почти всюду, где `320 (1 + √κ) ε < π (1 - √κ) m`. Чётность не требуется.
Вывод: существует последовательность конечномерных подпространств слабой области
Дирихле, инвариантных относительно `L_a`, образующая базис Рисса со скобками.
Доказательство: калибровка `r = √|a|`, диагонализация чётной модели `L_b` и
абстрактная теорема `exists_bracket_basis_of_subordinate`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

section Transfer

variable {J : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Перенос базиса Рисса со скобками ограниченным обратимым оператором. -/
def RieszBasisWithBrackets.map {V : J → Submodule ℂ E} (B : RieszBasisWithBrackets V)
    (T : E ≃L[ℂ] F) :
    RieszBasisWithBrackets (fun j => (V j).map (T : E →L[ℂ] F).toLinearMap) where
  lower := B.lower * ((1 + ‖(T : E →L[ℂ] F)‖) ^ 2 * (1 + ‖(T.symm : F →L[ℂ] E)‖) ^ 2)⁻¹
  upper := B.upper * ((1 + ‖(T : E →L[ℂ] F)‖) ^ 2 * (1 + ‖(T.symm : F →L[ℂ] E)‖) ^ 2)
  lower_pos := mul_pos B.lower_pos (by positivity)
  upper_pos := mul_pos B.upper_pos (by positivity)
  finite := fun j => by
    have := B.finite j
    infer_instance
  total := by
    rw [eq_top_iff]
    intro y _
    have hy : T.symm y ∈ ((⨆ j, V j).topologicalClosure : Set E) := by
      rw [B.total]
      trivial
    have hmap : Set.MapsTo T ((⨆ j, V j : Submodule ℂ E) : Set E)
        ((⨆ j, (V j).map (T : E →L[ℂ] F).toLinearMap : Submodule ℂ F) : Set F) := by
      intro z hz
      have hz' : T z ∈ (⨆ j, V j).map (T : E →L[ℂ] F).toLinearMap := ⟨z, hz, rfl⟩
      rwa [Submodule.map_iSup] at hz'
    have h := map_mem_closure T.continuous hy hmap
    rwa [ContinuousLinearEquiv.apply_symm_apply] at h
  bounds := by
    intro t v
    set cU := 1 + ‖(T : E →L[ℂ] F)‖ with hcU
    set cV := 1 + ‖(T.symm : F →L[ℂ] E)‖ with hcV
    have hcU0 : 0 < cU := by positivity
    have hcV0 : 0 < cV := by positivity
    have hU : ∀ x : E, ‖T x‖ ≤ cU * ‖x‖ := fun x =>
      ((T : E →L[ℂ] F).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
    have hV : ∀ x : F, ‖T.symm x‖ ≤ cV * ‖x‖ := fun x =>
      ((T.symm : F →L[ℂ] E).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
    have hmem : ∀ j, T.symm (v j : F) ∈ V j := by
      intro j
      obtain ⟨x, hx, hxv⟩ := (v j).property
      have he : T.symm (v j : F) = x := by
        rw [← hxv]
        exact T.symm_apply_apply x
      rw [he]
      exact hx
    let h : ∀ j, V j := fun j => ⟨T.symm (v j : F), hmem j⟩
    have hTh : ∀ j, T (h j : E) = (v j : F) := fun j => T.apply_symm_apply _
    have hsum : (∑ j ∈ t, (v j : F)) = T (∑ j ∈ t, (h j : E)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (hTh j).symm
    obtain ⟨hlow, hup⟩ := B.bounds t h
    have hA : (∑ j ∈ t, ‖v j‖ ^ 2) ≤ cU ^ 2 * ∑ j ∈ t, ‖h j‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hj := hU (h j : E)
      rw [hTh j] at hj
      rw [← Submodule.norm_coe, ← Submodule.norm_coe (h j), ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hj 2
    have hB : (∑ j ∈ t, ‖h j‖ ^ 2) ≤ cV ^ 2 * ∑ j ∈ t, ‖v j‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hj := hV (v j : F)
      rw [← Submodule.norm_coe, ← Submodule.norm_coe (v j), ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hj 2
    have hN : ‖∑ j ∈ t, (v j : F)‖ ^ 2 ≤ cU ^ 2 * ‖∑ j ∈ t, (h j : E)‖ ^ 2 := by
      rw [hsum, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hU _) 2
    have hS : ‖∑ j ∈ t, (h j : E)‖ ^ 2 ≤ cV ^ 2 * ‖∑ j ∈ t, (v j : F)‖ ^ 2 := by
      have hs : (∑ j ∈ t, (h j : E)) = T.symm (∑ j ∈ t, (v j : F)) := by
        rw [hsum]
        exact (T.symm_apply_apply _).symm
      rw [hs, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hV _) 2
    have hc : 0 < cU ^ 2 * cV ^ 2 := by positivity
    have hl0 := B.lower_pos
    have hu0 := B.upper_pos
    constructor
    · have key : B.lower * (∑ j ∈ t, ‖v j‖ ^ 2) ≤
          cU ^ 2 * cV ^ 2 * ‖∑ j ∈ t, (v j : F)‖ ^ 2 := by
        calc
          B.lower * (∑ j ∈ t, ‖v j‖ ^ 2) ≤ B.lower * (cU ^ 2 * ∑ j ∈ t, ‖h j‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hA hl0.le
          _ = cU ^ 2 * (B.lower * ∑ j ∈ t, ‖h j‖ ^ 2) := by ring
          _ ≤ cU ^ 2 * ‖∑ j ∈ t, (h j : E)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
          _ ≤ cU ^ 2 * (cV ^ 2 * ‖∑ j ∈ t, (v j : F)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hS (by positivity)
          _ = _ := by ring
      calc
        B.lower * (cU ^ 2 * cV ^ 2)⁻¹ * (∑ j ∈ t, ‖v j‖ ^ 2) =
            (cU ^ 2 * cV ^ 2)⁻¹ * (B.lower * ∑ j ∈ t, ‖v j‖ ^ 2) := by ring
        _ ≤ (cU ^ 2 * cV ^ 2)⁻¹ * (cU ^ 2 * cV ^ 2 * ‖∑ j ∈ t, (v j : F)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
        _ = _ := inv_mul_cancel_left₀ hc.ne' _
    · calc
        ‖∑ j ∈ t, (v j : F)‖ ^ 2 ≤ cU ^ 2 * ‖∑ j ∈ t, (h j : E)‖ ^ 2 := hN
        _ ≤ cU ^ 2 * (B.upper * ∑ j ∈ t, ‖h j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
        _ ≤ cU ^ 2 * (B.upper * (cV ^ 2 * ∑ j ∈ t, ‖v j‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hu0.le) (by positivity)
        _ = _ := by ring

end Transfer

/-- Веса каналов чётного коэффициента вместе с равномерными оценками. -/
theorem evenCoefficient_channel_weights_bounded (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (t : ℝ) (ht : |t| = 1) :
    ∃ v w : IntervalLInfinity,
      (∀ᵐ x ∂intervalMeasure, v (-x) = v x) ∧
      (∀ᵐ x ∂intervalMeasure, w (-x) = w x) ∧
      (∀ᵐ x ∂intervalMeasure, star (w x) = w x) ∧
      (∀ᵐ x ∂intervalMeasure, v x * w x = 1) ∧
      (∀ᵐ x ∂intervalMeasure, (1 + (t : ℂ) * realIntervalCoefficient a ha x) *
        (w x * w x) = 1) ∧
      (∀ᵐ x ∂intervalMeasure, ‖w x‖ ≤ (Real.sqrt (1 - Real.sqrt kappa))⁻¹) ∧
      (∀ᵐ x ∂intervalMeasure, ‖v x‖ ≤ Real.sqrt (1 + Real.sqrt kappa)) := by
  let p : ℝ → ℝ := fun x => 1 + t * a x
  have hp : MemLp p ∞ intervalMeasure := channelCoefficient_memLp a ha t
  have hm : 0 < 1 - Real.sqrt kappa := by
    have hs : Real.sqrt kappa < 1 := by
      exact (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
    linarith
  have hb := evenCoefficient_channel_bounds a kappa hkappa heven hproduct t ht
  have hl : ∀ᵐ x ∂intervalMeasure, 1 - Real.sqrt kappa ≤ p x := hb.mono fun _ h => h.1
  have hu : ∀ᵐ x ∂intervalMeasure, p x ≤ 1 + Real.sqrt kappa := hb.mono fun _ h => h.2
  have hep : ∀ᵐ x ∂intervalMeasure, p (-x) = p x := heven.mono fun x hx => by
    dsimp [p]
    rw [hx]
  have hc : ∀ᵐ x ∂intervalMeasure, (p x : ℂ) =
      1 + (t : ℂ) * realIntervalCoefficient a ha x := by
    filter_upwards [realIntervalCoefficient_ae a ha] with x hx
    rw [hx]
    simp only [p, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  refine ⟨sqrtWeight p hp (1 + Real.sqrt kappa) hu,
    inverseSqrtWeight p hp (1 - Real.sqrt kappa) hm hl,
    sqrtWeight_even p hp _ hu hep, inverseSqrtWeight_even p hp _ hm hl hep,
    inverseSqrtWeight_real p hp _ hm hl, sqrtWeight_inverseSqrtWeight p hp _ _ hm hl hu,
    inverseSqrtWeight_channel_identity (realIntervalCoefficient a ha) (t : ℂ) p hp _ hm hl hc,
    ?_, ?_⟩
  · filter_upwards [inverseSqrtWeight_ae p hp _ hm hl, hl] with x hx hlx
    have hpos : 0 < p x := lt_of_lt_of_le hm hlx
    rw [hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hpos))]
    exact inv_anti₀ (Real.sqrt_pos.mpr hm) (Real.sqrt_le_sqrt hlx)
  · filter_upwards [sqrtWeight_ae p hp _ hu, hu] with x hx hux
    rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hux

/-- Данные калибровки `r = √|a|` с явной оценкой производной веса. -/
theorem signDefinite_gauge_data (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa ε : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'')
    (hε : ∀ᵐ x ∂intervalMeasure, ‖a' x‖ ≤ ε) :
    ∃ (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (r wg r' r'' : IntervalLInfinity),
      (∀ x, b (-x) = b x) ∧
      (∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa) ∧
      (∀ᵐ x ∂intervalMeasure, r x * wg x = 1) ∧
      HasACMultiplierDerivative r r' ∧ HasACMultiplierDerivative r' r'' ∧
      (∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x =
        realIntervalCoefficient a ha x * r (-x)) ∧
      (∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f) ∧
      (∀ᵐ x ∂intervalMeasure, ‖wg x‖ ≤ (Real.sqrt m)⁻¹) ∧
      (∀ᵐ x ∂intervalMeasure, ‖r' x‖ ≤ ε * (Real.sqrt m)⁻¹ / 2) := by
  have hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha) := ⟨a', a'', h0, h1⟩
  obtain ⟨σ, hσ, hsign⟩ := real_coefficient_constant_sign a ha m hm hlower hreg
  have hσabs : |σ| = 1 := by
    have h : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  let b : ℝ → ℝ := fun x => σ * Real.sqrt |a x * a (-x)|
  have hbeven : ∀ x, b (-x) = b x := by
    intro x
    change σ * Real.sqrt |a (-x) * a (- -x)| = σ * Real.sqrt |a x * a (-x)|
    rw [neg_neg, mul_comm (a (-x))]
  have hbsq : ∀ x, b x * b x = |a x * a (-x)| := by
    intro x
    change σ * Real.sqrt |a x * a (-x)| * (σ * Real.sqrt |a x * a (-x)|) = |a x * a (-x)|
    calc
      _ = (σ * σ) * (Real.sqrt |a x * a (-x)| * Real.sqrt |a x * a (-x)|) := by ring
      _ = _ := by rw [hσ, one_mul, Real.mul_self_sqrt (abs_nonneg _)]
  have hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa := by
    filter_upwards [hproduct] with x hx
    rw [hbeven x, hbsq x, abs_abs]
    exact hx
  have hb : MemLp b ∞ intervalMeasure := by
    have hmeas : AEMeasurable a intervalMeasure := ha.aestronglyMeasurable.aemeasurable
    have hn : AEMeasurable (fun x => a (-x)) intervalMeasure :=
      hmeas.comp_quasiMeasurePreserving interval_neg_measurePreserving.quasiMeasurePreserving
    have hbm : AEMeasurable b intervalMeasure :=
      (continuous_abs.measurable.comp_aemeasurable (hmeas.mul hn)).sqrt.const_mul σ
    apply memLp_top_of_bound hbm.aestronglyMeasurable (Real.sqrt kappa)
    filter_upwards [hproduct] with x hx
    have hsq : ‖b x‖ ^ 2 ≤ kappa := by
      rw [Real.norm_eq_abs, sq_abs, sq, hbsq x]
      exact hx
    exact (Real.sqrt_sq (norm_nonneg _)).symm.le.trans (Real.sqrt_le_sqrt hsq)
  let r := sqrtWeight (fun x => |a x|) (real_abs_memLp a ha) M hupper
  let wg := inverseSqrtWeight (fun x => |a x|) (real_abs_memLp a ha) m hm hlower
  have hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1 :=
    sqrtWeight_inverseSqrtWeight (fun x => |a x|) (real_abs_memLp a ha) m M hm hlower hupper
  -- производная коэффициента `|a|`
  have habs : realIntervalCoefficient (fun x => |a x|) (real_abs_memLp a ha) =
      (σ : ℂ) • realIntervalCoefficient a ha := by
    apply Lp.ext
    filter_upwards [realIntervalCoefficient_ae (fun x => |a x|) (real_abs_memLp a ha),
      realIntervalCoefficient_ae a ha, hsign,
      Lp.coeFn_smul (σ : ℂ) (realIntervalCoefficient a ha)] with x hab hax hs hc
    rw [hab, hc]
    change ((|a x| : ℝ) : ℂ) = (σ : ℂ) * realIntervalCoefficient a ha x
    rw [hax, ← Complex.ofReal_mul]
    congr 1
    calc
      |a x| = (σ * σ) * |a x| := by rw [hσ, one_mul]
      _ = σ * (σ * |a x|) := by ring
      _ = σ * a x := by rw [← hs]
  have hAabs : HasACMultiplierDerivative
      (realIntervalCoefficient (fun x => |a x|) (real_abs_memLp a ha)) ((σ : ℂ) • a') := by
    rw [habs]
    exact (HasACMultiplierDerivative.of_weak h0).coeff_smul (σ : ℂ)
  let r' := sqrtCoefficientDeriv ((σ : ℂ) • a') wg
  have hr : HasACMultiplierDerivative r r' :=
    sqrtWeight_hasACDerivative (fun x => |a x|) (real_abs_memLp a ha) m M hm hlower hupper
      ((σ : ℂ) • a') hAabs
  obtain ⟨⟨r₁', r'', hr0, hr1⟩, _⟩ :=
    sqrt_abs_weights_memW2Infinity a ha m M hm hlower hupper hreg
  have heq : r₁' = r' := Lp.ext (HasWeakDerivOn.unique isOpen_Ioo hr0 hr.to_weak)
  rw [heq] at hr1
  have hr' : HasACMultiplierDerivative r' r'' := HasACMultiplierDerivative.of_weak hr1
  let A := realIntervalCoefficient a ha
  let Bc := realIntervalCoefficient b hb
  have hrn : ∀ᵐ x ∂intervalMeasure, r (-x) = ((Real.sqrt |a (-x)| : ℝ) : ℂ) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (sqrtWeight_ae (fun x => |a x|) (real_abs_memLp a ha) M hupper)] with x hx
    exact hx
  have hg : ∀ᵐ x ∂intervalMeasure, Bc x * r x = A x * r (-x) := by
    filter_upwards [realIntervalCoefficient_ae b hb, realIntervalCoefficient_ae a ha,
      sqrtWeight_ae (fun x => |a x|) (real_abs_memLp a ha) M hupper, hrn, hsign]
      with x hbx hax hrx hrnx hs
    have hbx' : Bc x = (b x : ℂ) := hbx
    have hax' : A x = (a x : ℂ) := hax
    have hrx' : r x = ((Real.sqrt |a x| : ℝ) : ℂ) := hrx
    rw [hbx', hax', hrx', hrnx]
    have hreal : b x * Real.sqrt |a x| = a x * Real.sqrt |a (-x)| := by
      change σ * Real.sqrt |a x * a (-x)| * Real.sqrt |a x| = a x * Real.sqrt |a (-x)|
      rw [abs_mul, Real.sqrt_mul (abs_nonneg _)]
      calc
        _ = σ * (Real.sqrt |a x| * Real.sqrt |a x|) * Real.sqrt |a (-x)| := by ring
        _ = σ * |a x| * Real.sqrt |a (-x)| := by rw [Real.mul_self_sqrt (abs_nonneg _)]
        _ = _ := by rw [← hs]
    exact_mod_cast hreal
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hwgb : ∀ᵐ x ∂intervalMeasure, ‖wg x‖ ≤ (Real.sqrt m)⁻¹ := by
    filter_upwards [inverseSqrtWeight_ae (fun x => |a x|) (real_abs_memLp a ha) m hm hlower,
      hlower] with x hx hlx
    have hpos : 0 < |a x| := lt_of_lt_of_le hm hlx
    change ‖wg x‖ ≤ _
    rw [hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hpos))]
    exact inv_anti₀ hsm (Real.sqrt_le_sqrt hlx)
  have hr'b : ∀ᵐ x ∂intervalMeasure, ‖r' x‖ ≤ ε * (Real.sqrt m)⁻¹ / 2 := by
    filter_upwards [sqrtCoefficientDeriv_ae ((σ : ℂ) • a') wg, hwgb, hε,
      Lp.coeFn_smul (σ : ℂ) a'] with x hx hwx hεx hc
    rw [hx, hc]
    change ‖(1 / 2 : ℂ) * ((((σ : ℂ) * a' x).re : ℝ) : ℂ) * wg x‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    have hre : |((σ : ℂ) * a' x).re| ≤ ε := by
      calc
        |((σ : ℂ) * a' x).re| ≤ ‖(σ : ℂ) * a' x‖ := Complex.abs_re_le_norm _
        _ = ‖a' x‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hσabs, one_mul]
        _ ≤ ε := hεx
    rw [hhalf]
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans hεx
    calc
      1 / 2 * |((σ : ℂ) * a' x).re| * ‖wg x‖ ≤ 1 / 2 * ε * (Real.sqrt m)⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hre (by norm_num)) hwx (norm_nonneg _)
          (by positivity)
      _ = _ := by ring
  exact ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, hr, hr', hg,
    fun f => sqrt_abs_dirichlet_iff a ha m M hm hlower hupper hreg f, hwgb, hr'b⟩

/-- Собственное значение оператора `W G W` равно энергии и потому положительно. -/
theorem sandwich_eigenvalue_eq_energy (Wm : IntervalL2 →L[ℂ] IntervalL2)
    (hsym : Wm.IsSymmetric) (u : IntervalL2) (hu : ‖u‖ = 1) (mu : ℂ)
    (he : Wm (spectralGreen (Wm u)) = mu • u) :
    mu = ((‖greenDeriv (Wm u)‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : inner ℂ (Wm (spectralGreen (Wm u))) u =
      inner ℂ (greenDeriv (Wm u)) (greenDeriv (Wm u)) := by
    rw [← greenDeriv_inner]
    exact hsym _ _
  rw [he, inner_smul_left, inner_self_eq_norm_sq_to_K, hu, inner_self_eq_norm_sq_to_K] at h1
  have h2 : (starRingEnd ℂ) mu = ((‖greenDeriv (Wm u)‖ ^ 2 : ℝ) : ℂ) := by
    simpa using h1
  have h3 := congrArg (starRingEnd ℂ) h2
  rwa [Complex.conj_conj, Complex.conj_ofReal] at h3

/-- Редукция к абстрактной теореме о возмущениях. Калибровка к чётному коэффициенту
приводит `L_A` к виду `G + S` с диагональным `G`, счётной функцией частот
`≤ (2ν/π) t + 2` и оценкой `‖S u‖ ≤ b₁ ⟨G u, u⟩^{1/2} + b₀ ‖u‖`, где
`ν = (1 - √κ)^{-1/2}`, `b₁ = ν (1 + √κ) · 2c`. Гипотеза `habs` — любая теорема, дающая
для таких данных базис со скобками из инвариантных блоков. -/
theorem bracket_basis_of_gauge_core (A : IntervalLInfinity) (b : ℝ → ℝ)
    (hb : MemLp b ∞ intervalMeasure) (kappa c : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hc : 0 ≤ c) (heven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x)
    (hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa)
    (r wg r' r'' : IntervalLInfinity)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1)
    (hr : HasACMultiplierDerivative r r') (hr' : HasACMultiplierDerivative r' r'')
    (hg : ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x = A x * r (-x))
    (hdom : ∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f)
    (hlog : ∀ᵐ x ∂intervalMeasure, ‖wg x * r' x‖ ≤ c)
    (habs : ∀ {ι : Type} (bH : HilbertBasis ι ℂ IntervalL2) (lam : ι → ℝ),
      (∀ i, 0 < lam i) → ∀ K₀ B : IntervalL2 →L[ℂ] IntervalL2,
      (∀ i, K₀ (bH i) = (((lam i)⁻¹ : ℝ) : ℂ) • bH i) → ∀ b₀ : ℝ, 0 ≤ b₀ →
      (∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t ^ 2) →
        (s.card : ℝ) ≤ 2 * (Real.sqrt (1 - Real.sqrt kappa))⁻¹ / Real.pi * t + 2) →
      (∀ g : IntervalL2, ‖B g‖ ≤
        (Real.sqrt (1 - Real.sqrt kappa))⁻¹ * (1 + Real.sqrt kappa) * (2 * c) *
          Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) + b₀ * ‖K₀ g‖) →
      ∃ V : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets V) ∧
        ∀ k, ∀ v ∈ V k, ∃ g : IntervalL2, K₀ g = v ∧ g + B g ∈ V k) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f, variableSobolevOperator A f hf.1 ∈ W k := by
  obtain ⟨ve, we, hve, hwe, hree, hive, hpe, hweb, hveb⟩ :=
    evenCoefficient_channel_weights_bounded b hb kappa hkappa hkappa1 heven hbprod 1
      (by norm_num)
  obtain ⟨vo, wo, hvo, hwo, hreo, hivo, hpo, hwob, hvob⟩ :=
    evenCoefficient_channel_weights_bounded b hb kappa hkappa hkappa1 heven hbprod (-1)
      (by norm_num)
  simp only [Complex.ofReal_one] at hpe
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hpo
  set Bc := realIntervalCoefficient b hb with hBc
  -- постоянные
  have hsk : Real.sqrt kappa < 1 :=
    (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
  have hsk0 : 0 ≤ Real.sqrt kappa := Real.sqrt_nonneg _
  have hq : 0 < 1 - Real.sqrt kappa := by linarith
  set ν := (Real.sqrt (1 - Real.sqrt kappa))⁻¹ with hν
  have hν0 : 0 < ν := inv_pos.mpr (Real.sqrt_pos.mpr hq)
  have hν2 : ν * ν = (1 - Real.sqrt kappa)⁻¹ := by
    rw [hν, ← mul_inv, Real.mul_self_sqrt hq.le]
  -- операторы
  let Wm : IntervalL2 →L[ℂ] IntervalL2 := parityMultiplierSum we wo
  let Vm : IntervalL2 →L[ℂ] IntervalL2 := parityMultiplierSum ve vo
  let T : IntervalL2 →L[ℂ] IntervalL2 := principalOperator Bc
  let Kt : IntervalL2 →L[ℂ] IntervalL2 := Wm ∘L spectralGreen ∘L Wm
  let Bt : IntervalL2 →L[ℂ] IntervalL2 := Wm ∘L T ∘L gaugeLowerOp wg r' r'' ∘L Wm
  have hWnorm : ‖Wm‖ ≤ ν := parityMultiplierSum_norm_le we wo ν hν0.le hwe hwo hweb hwob
  have hVnorm : ‖Vm‖ ≤ Real.sqrt (1 + Real.sqrt kappa) :=
    parityMultiplierSum_norm_le ve vo _ (Real.sqrt_nonneg _) hve hvo hveb hvob
  have hWsym : Wm.IsSymmetric := parityMultiplierSum_symmetric we wo hwe hwo hree hreo
  have hVW : ∀ z : IntervalL2, Vm (Wm z) = z :=
    parityMultiplierSum_inverse we wo ve vo hwe hwo hive hivo
  have hbabs : ∀ᵐ x ∂intervalMeasure, ‖Bc x‖ ≤ Real.sqrt kappa := by
    filter_upwards [evenCoefficient_abs_bound b kappa hkappa heven hbprod,
      realIntervalCoefficient_ae b hb] with x hx hbx
    change ‖realIntervalCoefficient b hb x‖ ≤ _
    rw [hbx, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hTnorm : ‖T‖ ≤ 1 + Real.sqrt kappa := principalOperator_norm_le Bc _ hsk0 hbabs
  have hTW : ∀ g : IntervalL2, T (Wm g) = Vm g := by
    intro g
    change principalOperator Bc (boundedMultiplier we (l2EvenPart g) +
      boundedMultiplier wo (l2OddPart g)) =
        boundedMultiplier ve (l2EvenPart g) + boundedMultiplier vo (l2OddPart g)
    rw [map_add,
      principalOperator_weight Bc ve we 1 hwe hive hpe (l2EvenPart g)
        (by rw [l2EvenPart_fixed, one_smul]),
      principalOperator_weight Bc vo wo (-1) hwo hivo hpo (l2OddPart g)
        (by rw [l2OddPart_neg, neg_one_smul])]
  -- собственный базис
  let be := weightedChannelEigenbasis we hwe hree 1
  let bo := weightedChannelEigenbasis wo hwo hreo (-1)
  let bH := parityHilbertBasis be bo
  have hKe : ∀ i, Kt (bH (Sum.inl i)) = i.1 • bH (Sum.inl i) := by
    intro i
    have hbi : bH (Sum.inl i) = (be i : IntervalL2) := parityHilbertBasis_apply be bo _
    rw [hbi]
    have hz : spectralGreen (boundedMultiplier we (be i : IntervalL2)) ∈ parityL2Submodule 1 :=
      spectralGreen_parity_invariant 1 _
        (boundedMultiplier_parity_invariant we hwe 1 _ (be i).property)
    change Wm (spectralGreen (Wm (be i : IntervalL2))) = _
    rw [show Wm (be i : IntervalL2) = boundedMultiplier we (be i : IntervalL2) from
      parityMultiplierSum_even we wo (be i)]
    rw [show Wm (spectralGreen (boundedMultiplier we (be i : IntervalL2))) =
      boundedMultiplier we (spectralGreen (boundedMultiplier we (be i : IntervalL2))) from
      parityMultiplierSum_even we wo ⟨_, hz⟩]
    exact congrArg Subtype.val (weightedChannelEigenbasis_equation we hwe hree 1 i)
  have hKo : ∀ i, Kt (bH (Sum.inr i)) = i.1 • bH (Sum.inr i) := by
    intro i
    have hbi : bH (Sum.inr i) = (bo i : IntervalL2) := parityHilbertBasis_apply be bo _
    rw [hbi]
    have hz : spectralGreen (boundedMultiplier wo (bo i : IntervalL2)) ∈
        parityL2Submodule (-1) :=
      spectralGreen_parity_invariant (-1) _
        (boundedMultiplier_parity_invariant wo hwo (-1) _ (bo i).property)
    change Wm (spectralGreen (Wm (bo i : IntervalL2))) = _
    rw [show Wm (bo i : IntervalL2) = boundedMultiplier wo (bo i : IntervalL2) from
      parityMultiplierSum_odd we wo (bo i)]
    rw [show Wm (spectralGreen (boundedMultiplier wo (bo i : IntervalL2))) =
      boundedMultiplier wo (spectralGreen (boundedMultiplier wo (bo i : IntervalL2))) from
      parityMultiplierSum_odd we wo ⟨_, hz⟩]
    exact congrArg Subtype.val (weightedChannelEigenbasis_equation wo hwo hreo (-1) i)
  let mu : CompactEigenbasisIndex (weightedParityGreen we hwe 1) ⊕
      CompactEigenbasisIndex (weightedParityGreen wo hwo (-1)) → ℂ :=
    Sum.elim (fun i => i.1) (fun i => i.1)
  have hKmu : ∀ i, Kt (bH i) = mu i • bH i := by
    intro i
    cases i with
    | inl i => exact hKe i
    | inr i => exact hKo i
  have hmu0 : ∀ i, mu i ≠ 0 := by
    intro i
    cases i with
    | inl i => exact weightedChannelEigenvalue_ne_zero ve we hwe hree hive 1 i
    | inr i => exact weightedChannelEigenvalue_ne_zero vo wo hwo hreo hivo (-1) i
  have hmuE : ∀ i, mu i = ((‖greenDeriv (Wm (bH i))‖ ^ 2 : ℝ) : ℂ) := fun i =>
    sandwich_eigenvalue_eq_energy Wm hWsym (bH i) (bH.orthonormal.norm_eq_one i) (mu i)
      (hKmu i)
  let lam := fun i => (‖greenDeriv (Wm (bH i))‖ ^ 2)⁻¹
  have hEpos : ∀ i, 0 < ‖greenDeriv (Wm (bH i))‖ ^ 2 := by
    intro i
    refine lt_of_le_of_ne (sq_nonneg _) fun h0 => hmu0 i ?_
    rw [hmuE i, ← h0, Complex.ofReal_zero]
  have hlam : ∀ i, 0 < lam i := fun i => inv_pos.mpr (hEpos i)
  have hK₀ : ∀ i, Kt (bH i) = (((lam i)⁻¹ : ℝ) : ℂ) • bH i := by
    intro i
    rw [hKmu i, hmuE i]
    change _ = ((((‖greenDeriv (Wm (bH i))‖ ^ 2)⁻¹)⁻¹ : ℝ) : ℂ) • bH i
    rw [inv_inv]
  -- оценка счётной функции
  have hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset _, (∀ i ∈ s, lam i ≤ t ^ 2) →
      (s.card : ℝ) ≤ 2 * ν / Real.pi * t + 2 := fun t ht s hs =>
    green_sandwich_eigen_count Wm Wm ν hν0 hWnorm hWnorm bH bH.orthonormal lam hlam hK₀ t ht
      s hs
  -- оценка возмущения
  set b₁ := ν * (1 + Real.sqrt kappa) * (2 * c) with hb₁
  set b₀ := ν * (1 + Real.sqrt kappa) * (‖wg‖ * ‖r''‖ *
    Real.sqrt (1 + Real.sqrt kappa)) with hb₀
  have hb₁0 : 0 ≤ b₁ := by positivity
  have hb₀0 : 0 ≤ b₀ := by positivity
  have hB : ∀ g : IntervalL2, ‖Bt g‖ ≤
      b₁ * Real.sqrt (RCLike.re (inner ℂ (Kt g) g)) + b₀ * ‖Kt g‖ := by
    intro g
    set h := Wm g with hh
    have hD : ‖greenDeriv h‖ = Real.sqrt (RCLike.re (inner ℂ (Kt g) g)) := by
      have h1 : inner ℂ (Kt g) g = inner ℂ (spectralGreen h) h := hWsym _ _
      rw [h1, ← greenDeriv_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have hG : ‖spectralGreen h‖ ≤ Real.sqrt (1 + Real.sqrt kappa) * ‖Kt g‖ := by
      have h1 : spectralGreen h = Vm (Kt g) := (hVW _).symm
      rw [h1]
      exact (Vm.le_opNorm _).trans (mul_le_mul_of_nonneg_right hVnorm (norm_nonneg _))
    have hL := gaugeLowerOp_norm_le wg r' r'' c (‖wg‖ * ‖r''‖)
      (boundedMultiplier_comp_norm_le_of_ae wg r' c hc hlog)
      (fun f => (boundedMultiplier_norm_le wg _).trans
        ((mul_le_mul_of_nonneg_left (boundedMultiplier_norm_le r'' f) (norm_nonneg wg)).trans
          (mul_assoc _ _ _).ge)) h
    have hL' : ‖gaugeLowerOp wg r' r'' h‖ ≤
        2 * c * Real.sqrt (RCLike.re (inner ℂ (Kt g) g)) +
          ‖wg‖ * ‖r''‖ * (Real.sqrt (1 + Real.sqrt kappa) * ‖Kt g‖) := by
      rw [hD] at hL
      exact hL.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hG (by positivity)))
    have hWT : ‖Bt g‖ ≤ ν * ((1 + Real.sqrt kappa) * ‖gaugeLowerOp wg r' r'' h‖) := by
      change ‖Wm (T (gaugeLowerOp wg r' r'' h))‖ ≤ _
      calc
        _ ≤ ‖Wm‖ * ‖T (gaugeLowerOp wg r' r'' h)‖ := Wm.le_opNorm _
        _ ≤ ν * ((1 + Real.sqrt kappa) * ‖gaugeLowerOp wg r' r'' h‖) :=
          mul_le_mul hWnorm ((T.le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _))) (norm_nonneg _) hν0.le
    calc
      ‖Bt g‖ ≤ ν * ((1 + Real.sqrt kappa) * ‖gaugeLowerOp wg r' r'' h‖) := hWT
      _ ≤ ν * ((1 + Real.sqrt kappa) *
          (2 * c * Real.sqrt (RCLike.re (inner ℂ (Kt g) g)) +
            ‖wg‖ * ‖r''‖ * (Real.sqrt (1 + Real.sqrt kappa) * ‖Kt g‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL' (by positivity)) hν0.le
      _ = _ := by
        rw [hb₁, hb₀]
        ring
  obtain ⟨V, hV, hinv⟩ := habs bH lam hlam Kt Bt hK₀ b₀ hb₀0 hcount hB
  -- перенос на исходный оператор
  let Φ : IntervalL2 ≃L[ℂ] IntervalL2 :=
    (parityMultiplierEquiv ve vo we wo hve hvo hwe hwo hive hivo).trans
      (multiplicationEquiv r wg hrw)
  have hΦ : ∀ z : IntervalL2, Φ z = boundedMultiplier r (Vm z) := fun z => rfl
  obtain ⟨BV⟩ := hV
  refine ⟨fun k => (V k).map (Φ : IntervalL2 →L[ℂ] IntervalL2).toLinearMap, ⟨BV.map Φ⟩, ?_⟩
  rintro k _ ⟨v, hv, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := hinv k v hv
  set h := Wm g with hh
  set y := spectralGreen h with hy
  have hyD : MemDirichletH2 y := spectralGreen_memDirichletH2 h
  have hVv : Vm v = y := by
    rw [← hg1]
    exact hVW y
  have hΦv : (Φ : IntervalL2 →L[ℂ] IntervalL2).toLinearMap v = boundedMultiplier r y := by
    change Φ v = _
    rw [hΦ, hVv]
  rw [hΦv]
  have hf : MemDirichletH2 (boundedMultiplier r y) := (hdom y).mpr hyD
  refine ⟨hf, ?_⟩
  have hsim := gauge_similarity A Bc r wg r' r'' hr hr' hrw hg y hyD.1 hf.1
  have hLb : variableSobolevOperator Bc y hyD.1 = Vm g := by
    rw [variableSobolevOperator_eq_principal, spectralGreen_right_inverse h]
    exact hTW g
  have hLow : principalOperator Bc (gaugeLowerOrder wg r' r'' y hyD.1) = Vm (Bt g) := by
    change T (gaugeLowerOp wg r' r'' h) = Vm (Wm (T (gaugeLowerOp wg r' r'' h)))
    rw [hVW]
  rw [hsim, hLb, hLow, ← map_add]
  exact ⟨g + Bt g, hg2, (hΦ _)⟩

/-- **Базис Рисса со скобками при калибровке к чётному коэффициенту.**
Пусть вес `r` класса `W²∞` с ограниченным обратным `wg` переводит коэффициент `A`
в вещественный чётный `b`: `b(x) r(x) = A(x) r(-x)`, причём `|b(x) b(-x)| ≤ κ < 1`.
Если логарифмическая производная веса мала, `|r'/r| ≤ c` с
`640 (1 + √κ) c < π (1 - √κ)`, то существует базис Рисса со скобками из конечномерных
подпространств слабой области Дирихле, инвариантных относительно `L_A`. -/
theorem bracket_basis_of_gauge (A : IntervalLInfinity) (b : ℝ → ℝ)
    (hb : MemLp b ∞ intervalMeasure) (kappa c : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hc : 0 ≤ c) (heven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x)
    (hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa)
    (r wg r' r'' : IntervalLInfinity)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1)
    (hr : HasACMultiplierDerivative r r') (hr' : HasACMultiplierDerivative r' r'')
    (hg : ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x = A x * r (-x))
    (hdom : ∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f)
    (hlog : ∀ᵐ x ∂intervalMeasure, ‖wg x * r' x‖ ≤ c)
    (hsmall : 640 * (1 + Real.sqrt kappa) * c < Real.pi * (1 - Real.sqrt kappa)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f, variableSobolevOperator A f hf.1 ∈ W k := by
  have hsk : Real.sqrt kappa < 1 :=
    (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
  have hsk0 : 0 ≤ Real.sqrt kappa := Real.sqrt_nonneg _
  have hq : 0 < 1 - Real.sqrt kappa := by linarith
  set ν := (Real.sqrt (1 - Real.sqrt kappa))⁻¹ with hν
  have hν0 : 0 < ν := inv_pos.mpr (Real.sqrt_pos.mpr hq)
  have hν2 : ν * ν = (1 - Real.sqrt kappa)⁻¹ := by
    rw [hν, ← mul_inv, Real.mul_self_sqrt hq.le]
  have hpi := Real.pi_pos
  have hsmall' : 160 * (ν * (1 + Real.sqrt kappa) * (2 * c)) * (2 * ν / Real.pi) < 1 := by
    have e : 160 * (ν * (1 + Real.sqrt kappa) * (2 * c)) * (2 * ν / Real.pi) =
        640 * (1 + Real.sqrt kappa) * c / (Real.pi * (1 - Real.sqrt kappa)) := by
      have : 160 * (ν * (1 + Real.sqrt kappa) * (2 * c)) * (2 * ν / Real.pi) =
          640 * (1 + Real.sqrt kappa) * c * (ν * ν) / Real.pi := by
        field_simp
        ring
      rw [this, hν2]
      field_simp
    rw [e, div_lt_one (by positivity)]
    exact hsmall
  exact bracket_basis_of_gauge_core A b hb kappa c hkappa hkappa1 hc heven hbprod r wg r' r''
    hrw hr hr' hg hdom hlog
    (fun bH lam hlam K₀ B hK₀ b₀ hb₀ hcount hB =>
      exists_bracket_basis_of_subordinate bH lam hlam K₀ B hK₀ (2 * ν / Real.pi) 2
        (ν * (1 + Real.sqrt kappa) * (2 * c)) b₀ (by positivity) (by norm_num)
        (by positivity) hb₀ hcount hB hsmall')

/-- **Базис Рисса со скобками для знакопостоянного коэффициента с малой производной.**
Чётность `a` не предполагается. Подпространства `W k` конечномерны, лежат в слабой
области Дирихле и инвариантны относительно `L_a`, поэтому состоят из корневых функций. -/
theorem signDefinite_bracket_basis (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa ε : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'') (hε0 : 0 ≤ ε)
    (hε : ∀ᵐ x ∂intervalMeasure, ‖a' x‖ ≤ ε)
    (hsmall : 320 * (1 + Real.sqrt kappa) * ε < Real.pi * (1 - Real.sqrt kappa) * m) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k := by
  obtain ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, hr, hr', hg, hdom, hwgb, hr'b⟩ :=
    signDefinite_gauge_data a ha m M kappa ε hm hlower hupper hproduct a' a'' h0 h1 hε
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsm2 : (Real.sqrt m)⁻¹ * (Real.sqrt m)⁻¹ = m⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hm.le]
  have hlog : ∀ᵐ x ∂intervalMeasure, ‖wg x * r' x‖ ≤ ε * m⁻¹ / 2 := by
    filter_upwards [hwgb, hr'b] with x hw hx
    rw [norm_mul]
    calc
      ‖wg x‖ * ‖r' x‖ ≤ (Real.sqrt m)⁻¹ * (ε * (Real.sqrt m)⁻¹ / 2) :=
        mul_le_mul hw hx (norm_nonneg _) (by positivity)
      _ = ε * ((Real.sqrt m)⁻¹ * (Real.sqrt m)⁻¹) / 2 := by ring
      _ = _ := by rw [hsm2]
  refine bracket_basis_of_gauge (realIntervalCoefficient a ha) b hb kappa (ε * m⁻¹ / 2) hkappa
    hkappa1 (by positivity) (Filter.Eventually.of_forall hbeven) hbprod r wg r' r'' hrw hr hr'
    hg hdom hlog ?_
  have hpos : 0 < Real.pi * (1 - Real.sqrt kappa) := by
    have hsk : Real.sqrt kappa < 1 :=
      (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
    exact mul_pos Real.pi_pos (by linarith)
  have e : 640 * (1 + Real.sqrt kappa) * (ε * m⁻¹ / 2) =
      320 * (1 + Real.sqrt kappa) * ε / m := by
    field_simp
    ring
  rw [e, div_lt_iff₀ hm]
  exact hsmall

end Involution
