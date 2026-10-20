module

public import Involution.Estimates.GeneralBrackets
public import Involution.Estimates.NearlyEvenBrackets

/-! Положительное отношение `a(x)/a(-x)` класса `W²∞` (утверждение C20).

Условия: вещественный `a ∈ L∞`, `|a(x) a(-x)| ≤ κ < 1` почти всюду и вещественная
`q ∈ W²∞`, `q ≥ q₀ > 0`, с `a(x) = q(x) a(-x)` почти всюду. Гладкость `a` не требуется.
Калибровка `r = ρ^(1/8)`, `ρ(x) = q(x)/q(-x)`, переводит `a` в чётный коэффициент
`b = a · r(-·)/r`; далее работает `bracket_basis_of_gauge_general`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Отношение `ρ(x) = q(x)/q(-x)` положительного коэффициента `q ∈ W²∞` лежит в `W²∞`. -/
theorem positiveRatio_memW2Infinity (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hρ : MemLp (fun x => q x / q (-x)) ∞ intervalMeasure) :
    MemIntervalW2Infinity (realIntervalCoefficient (fun x => q x / q (-x)) hρ) := by
  obtain ⟨a', a'', h0, h1⟩ := hreg
  let Q := realIntervalCoefficient q hq
  have hA0 := HasACMultiplierDerivative.of_weak h0
  have hA1 := HasACMultiplierDerivative.of_weak h1
  let R := reflectCoefficient Q
  have hR0 : HasACMultiplierDerivative R (-reflectCoefficient a') := hA0.reflect
  have hR1 := hA1.reflect.coeff_neg
  have hlown : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q (-x) :=
    interval_neg_measurePreserving.quasiMeasurePreserving.ae hlow
  have hRae : ∀ᵐ x ∂intervalMeasure, R x = ((q (-x) : ℝ) : ℂ) := by
    filter_upwards [reflectCoefficient_ae Q,
      interval_neg_measurePreserving.quasiMeasurePreserving.ae
        (realIntervalCoefficient_ae q hq)] with x h1 h2
    rw [h1]
    exact h2
  have hRlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ ‖R x‖ := by
    filter_upwards [hRae, hlown] with x h1 h2
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hq₀ h2)]
    exact h2
  let Ri := inverseCoefficient R q₀ hq₀ hRlow
  have hRi0 := hR0.coeff_inv q₀ hq₀ hRlow
  have hRi1 := ((hR1.coeff_mul hRi0).coeff_mul hRi0).coeff_neg
  have hQ0 := hA0.coeff_mul hRi0
  have hQ1 := (hA1.coeff_mul hRi0).coeff_add (hA0.coeff_mul hRi1)
  have hQeq : realIntervalCoefficient (fun x => q x / q (-x)) hρ = coefficientProduct Q Ri := by
    apply Lp.ext
    filter_upwards [realIntervalCoefficient_ae _ hρ, coefficientProduct_ae Q Ri,
      realIntervalCoefficient_ae q hq, inverseCoefficient_ae R q₀ hq₀ hRlow, hRae]
      with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
    push_cast
    rw [div_eq_mul_inv]
  rw [hQeq]
  exact ⟨_, _, hQ0.to_weak, hQ1.to_weak⟩

/-- Алгебраическое тождество калибровки в точке. -/
theorem positiveRatio_gauge_point (q q' α β t t' : ℝ) (hq : 0 < q)
    (ht : 0 < t) (ht' : 0 < t') (h8 : t ^ 8 = q / q') (h8' : t' ^ 8 = q' / q)
    (hα : α = q * β) (hβ : β = q' * α) :
    α * t' / t = β * t / t' := by
  rw [div_eq_div_iff ht.ne' ht'.ne']
  rcases eq_or_ne β 0 with h0 | h0
  · simp [h0, hα]
  have hqq : q * q' = 1 := by
    have : β = (q' * q) * β := by rw [mul_assoc, ← hα]; exact hβ
    have := mul_right_cancel₀ h0 (this.symm.trans (one_mul β).symm)
    linarith [mul_comm q q']
  rw [hα]
  have key : q * t' ^ 2 = t ^ 2 := by
    have hp : 0 ≤ q * t' ^ 2 := by positivity
    have hp' : 0 ≤ t ^ 2 := by positivity
    refine (pow_left_inj₀ hp hp' (by norm_num : (8 : ℕ) ≠ 0)).mp ?_
    have e1 : (q * t' ^ 2) ^ 8 = q ^ 8 * (t' ^ 8) ^ 2 := by ring
    have e2 : (t ^ 2) ^ 8 = (t ^ 8) ^ 2 := by ring
    rw [e1, e2, h8, h8']
    have hq'e : q' = q⁻¹ := eq_inv_of_mul_eq_one_right hqq
    rw [hq'e]
    field_simp
  linear_combination β * key

theorem sqrt_sqrt_sqrt_pow_eight (y : ℝ) (hy : 0 ≤ y) :
    Real.sqrt (Real.sqrt (Real.sqrt y)) ^ 8 = y := by
  have e : Real.sqrt (Real.sqrt (Real.sqrt y)) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt y)) ^ 2) ^ 2) ^ 2 := by ring
  rw [e, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt hy]

/-- Данные калибровки `r = (q(x)/q(-x))^(1/8)` для гипотез `bracket_basis_of_gauge_general`. -/
theorem positiveRatio_gauge_data (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hratio : ∀ᵐ x ∂intervalMeasure, a x = q x * a (-x)) (kappa : ℝ)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (r wg r' r'' : IntervalLInfinity),
      (∀ᵐ x ∂intervalMeasure, b (-x) = b x) ∧
      (∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa) ∧
      (∀ᵐ x ∂intervalMeasure, r x * wg x = 1) ∧
      HasACMultiplierDerivative r r' ∧ HasACMultiplierDerivative r' r'' ∧
      (∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x =
        realIntervalCoefficient a ha x * r (-x)) ∧
      (∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f) := by
  have hneg := interval_neg_measurePreserving.quasiMeasurePreserving
  -- верхняя граница `q`
  set Mq := ‖realIntervalCoefficient q hq‖ + q₀ with hMqdef
  have hMq : 0 < Mq := by positivity
  have hup : ∀ᵐ x ∂intervalMeasure, q x ≤ Mq := by
    filter_upwards [intervalLInfinity_ae_norm_le (realIntervalCoefficient q hq),
      realIntervalCoefficient_ae q hq] with x h1 h2
    rw [h2, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [le_abs_self (q x)]
  have hlown : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q (-x) := hneg.ae hlow
  have hupn : ∀ᵐ x ∂intervalMeasure, q (-x) ≤ Mq := hneg.ae hup
  have hration : ∀ᵐ x ∂intervalMeasure, a (-x) = q (-x) * a (- -x) := hneg.ae hratio
  -- отношение `ρ`
  let ρ : ℝ → ℝ := fun x => q x / q (-x)
  have hqm : AEMeasurable q intervalMeasure := hq.aestronglyMeasurable.aemeasurable
  have hqmn : AEMeasurable (fun x => q (-x)) intervalMeasure :=
    hqm.comp_quasiMeasurePreserving hneg
  have hρm : AEMeasurable ρ intervalMeasure := hqm.div hqmn
  have hρlow : ∀ᵐ x ∂intervalMeasure, q₀ / Mq ≤ ρ x := by
    filter_upwards [hlow, hupn, hlown] with x h1 h2 h3
    exact div_le_div₀ (lt_of_lt_of_le hq₀ h1).le h1 (lt_of_lt_of_le hq₀ h3) h2
  have hρup : ∀ᵐ x ∂intervalMeasure, ρ x ≤ Mq / q₀ := by
    filter_upwards [hup, hlown] with x h1 h2
    exact div_le_div₀ hMq.le h1 hq₀ h2
  have hm1 : 0 < q₀ / Mq := div_pos hq₀ hMq
  have hρ : MemLp ρ ∞ intervalMeasure := by
    apply memLp_top_of_bound hρm.aestronglyMeasurable (Mq / q₀)
    filter_upwards [hρup, hρlow] with x h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (hm1.le.trans h2)]
    exact h1
  have hρW : MemIntervalW2Infinity (realIntervalCoefficient ρ hρ) :=
    positiveRatio_memW2Infinity q hq hreg q₀ hq₀ hlow hρ
  -- первый корень
  let s1 : ℝ → ℝ := fun x => Real.sqrt (ρ x)
  have hs1 : MemLp s1 ∞ intervalMeasure := sqrt_memLp_of_upper_bound ρ hρ _ hρup
  have hs1W : MemIntervalW2Infinity (realIntervalCoefficient s1 hs1) :=
    sqrtWeight_memW2Infinity ρ hρ _ _ hm1 hρlow hρup hρW
  have hs1low : ∀ᵐ x ∂intervalMeasure, Real.sqrt (q₀ / Mq) ≤ s1 x :=
    hρlow.mono fun x hx => Real.sqrt_le_sqrt hx
  have hs1up : ∀ᵐ x ∂intervalMeasure, s1 x ≤ Real.sqrt (Mq / q₀) :=
    hρup.mono fun x hx => Real.sqrt_le_sqrt hx
  have hm2 : 0 < Real.sqrt (q₀ / Mq) := Real.sqrt_pos.mpr hm1
  -- второй корень
  let s2 : ℝ → ℝ := fun x => Real.sqrt (s1 x)
  have hs2 : MemLp s2 ∞ intervalMeasure := sqrt_memLp_of_upper_bound s1 hs1 _ hs1up
  have hs2W : MemIntervalW2Infinity (realIntervalCoefficient s2 hs2) :=
    sqrtWeight_memW2Infinity s1 hs1 _ _ hm2 hs1low hs1up hs1W
  have hs2low : ∀ᵐ x ∂intervalMeasure, Real.sqrt (Real.sqrt (q₀ / Mq)) ≤ s2 x :=
    hs1low.mono fun x hx => Real.sqrt_le_sqrt hx
  have hs2up : ∀ᵐ x ∂intervalMeasure, s2 x ≤ Real.sqrt (Real.sqrt (Mq / q₀)) :=
    hs1up.mono fun x hx => Real.sqrt_le_sqrt hx
  have hm3 : 0 < Real.sqrt (Real.sqrt (q₀ / Mq)) := Real.sqrt_pos.mpr hm2
  -- вес `r = √s2`
  let r := sqrtWeight s2 hs2 _ hs2up
  let wg := inverseSqrtWeight s2 hs2 _ hm3 hs2low
  have hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1 :=
    sqrtWeight_inverseSqrtWeight s2 hs2 _ _ hm3 hs2low hs2up
  obtain ⟨r', r'', hr0, hr1⟩ := sqrtWeight_memW2Infinity s2 hs2 _ _ hm3 hs2low hs2up hs2W
  let t : ℝ → ℝ := fun x => Real.sqrt (s2 x)
  -- точечные свойства `t`
  have ht : ∀ᵐ x ∂intervalMeasure, 0 < t x ∧ t x ^ 8 = q x / q (-x) := by
    filter_upwards [hρlow] with x hx
    have hρx : 0 ≤ ρ x := hm1.le.trans hx
    exact ⟨Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le hm1 hx))),
      sqrt_sqrt_sqrt_pow_eight _ hρx⟩
  have htn : ∀ᵐ x ∂intervalMeasure, 0 < t (-x) ∧ t (-x) ^ 8 = q (-x) / q x := by
    filter_upwards [hneg.ae ht] with x hx
    simpa only [neg_neg] using hx
  -- чётный коэффициент
  let b : ℝ → ℝ := fun x => a x * t (-x) / t x
  have hbeven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x := by
    filter_upwards [ht, htn, hlow, hlown, hratio, hration] with x h1 h2 h3 h4 h5 h6
    rw [neg_neg] at h6
    have := positiveRatio_gauge_point (q x) (q (-x)) (a x) (a (-x)) (t x) (t (-x))
      (lt_of_lt_of_le hq₀ h3) h1.1 h2.1 h1.2 h2.2 h5 h6
    change a (-x) * t (- -x) / t (-x) = a x * t (-x) / t x
    rw [neg_neg, this]
  have hbmul : ∀ᵐ x ∂intervalMeasure, b x * b (-x) = a x * a (-x) := by
    filter_upwards [ht, htn] with x h1 h2
    change a x * t (-x) / t x * (a (-x) * t (- -x) / t (-x)) = _
    rw [neg_neg]
    field_simp [h1.1.ne', h2.1.ne']
  have hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa := by
    filter_upwards [hbmul, hproduct] with x h1 h2
    rwa [h1]
  have hb : MemLp b ∞ intervalMeasure := by
    have ham : AEMeasurable a intervalMeasure := ha.aestronglyMeasurable.aemeasurable
    have htm : AEMeasurable t intervalMeasure := hρm.sqrt.sqrt.sqrt
    have htmn : AEMeasurable (fun x => t (-x)) intervalMeasure :=
      htm.comp_quasiMeasurePreserving hneg
    apply memLp_top_of_bound ((ham.mul htmn).div htm).aestronglyMeasurable (Real.sqrt kappa)
    filter_upwards [hbeven, hbprod] with x h1 h2
    rw [h1, abs_mul_self] at h2
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by rw [sq]; exact h2)
  refine ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, HasACMultiplierDerivative.of_weak hr0,
    HasACMultiplierDerivative.of_weak hr1, ?_,
    fun f => sqrtWeight_dirichlet_iff s2 hs2 _ _ hm3 hs2low hs2up hs2W f⟩
  have hrn : ∀ᵐ x ∂intervalMeasure, r (-x) = ((t (-x) : ℝ) : ℂ) :=
    hneg.ae (sqrtWeight_ae s2 hs2 _ hs2up)
  filter_upwards [realIntervalCoefficient_ae b hb, realIntervalCoefficient_ae a ha,
    sqrtWeight_ae s2 hs2 _ hs2up, hrn, ht] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4]
  change ((a x * t (-x) / t x : ℝ) : ℂ) * ((t x : ℝ) : ℂ) = _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, div_mul_cancel₀ _ h5.1.ne']

/-- **Положительное отношение `a(x)/a(-x)` класса `W²∞`: базис Рисса со скобками (C20).**
Условия: вещественный `a ∈ L∞`, `|a(x) a(-x)| ≤ κ < 1` почти всюду; вещественная
`q ∈ W²∞`, `q ≥ q₀ > 0` почти всюду, `a(x) = q(x) a(-x)` почти всюду. Существует
последовательность конечномерных подпространств слабой области Дирихле, инвариантных
относительно `L_a` и образующих базис Рисса со скобками. -/
theorem bracketBasis_of_positiveRatio (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hratio : ∀ᵐ x ∂intervalMeasure, a x = q x * a (-x))
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k := by
  obtain ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, hr, hr', hg, hdom⟩ :=
    positiveRatio_gauge_data a ha q hq hreg q₀ hq₀ hlow hratio kappa hproduct
  exact bracket_basis_of_gauge_general markusMatsaevStatement (realIntervalCoefficient a ha)
    b hb kappa hkappa hkappa1 hbeven hbprod r wg r' r'' hrw hr hr' hg hdom

/-- Блоки базиса со скобками из `bracketBasis_of_positiveRatio` порождены корневыми
векторами `L_a`. -/
theorem bracketRootVectors_of_positiveRatio (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hratio : ∀ᵐ x ∂intervalMeasure, a x = q x * a (-x))
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ := by
  obtain ⟨W, ⟨B⟩, hW⟩ := bracketBasis_of_positiveRatio a ha q hq hreg q₀ hq₀ hlow hratio
    kappa hkappa hkappa1 hproduct
  refine ⟨W, ⟨B⟩, fun k => ?_⟩
  have := B.finite k
  exact invariant_block_rootVectors (realIntervalCoefficient a ha) (W k) (hW k)

end Involution
