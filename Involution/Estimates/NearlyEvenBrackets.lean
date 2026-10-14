module

public import Involution.Estimates.BracketCorollaries

/-! Базис Рисса со скобками для коэффициента, близкого к чётному.
Знакопостоянный `a ∈ W²∞` записывается как `a = s e^φ` с чётной `s` и нечётной `φ`.
Калибровка `r = e^(φ/2) = (|a(x)| / |a(-x)|)^(1/4)` переводит `a` в чётный
`b = σ √(a(x) a(-x))`, а её логарифмическая производная равна
`(a'(x)/a(x) + a'(-x)/a(-x)) / 4`. Эта величина обращается в нуль для чётного `a`,
поэтому условие малости измеряет отклонение от чётности. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem uIoc_neg_disjoint {a b c d : ℝ} (h : Disjoint (Set.uIoc a b) (Set.uIoc c d)) :
    Disjoint (Set.uIoc (-a) (-b)) (Set.uIoc (-c) (-d)) := by
  simp only [Set.uIoc, Set.Ioc_disjoint_Ioc] at h ⊢
  rw [max_neg_neg, max_neg_neg, min_neg_neg, min_neg_neg, min_neg_neg, max_neg_neg]
  exact neg_le_neg h

theorem absolutelyContinuousOnInterval_comp_neg {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} (hf : AbsolutelyContinuousOnInterval f (-1) 1) :
    AbsolutelyContinuousOnInterval (fun x => f (-x)) (-1) 1 := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hmem : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, -x ∈ Set.uIcc (-1 : ℝ) 1 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx ⊢
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hE' : ((E.1, fun i => (-(E.2 i).1, -(E.2 i).2)) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (-1) 1 := by
    refine ⟨fun i hi => ⟨hmem _ (hE.1 i hi).1, hmem _ (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    exact uIoc_neg_disjoint (hE.2 hi hj hij)
  have := h _ hE' (by simpa [dist_neg_neg] using hlen)
  simpa using this

/-- Отражение `x ↦ -x` класса `L∞`. -/
def reflectCoefficient (u : IntervalLInfinity) : IntervalLInfinity :=
  Lp.compMeasurePreserving (fun x : ℝ => -x) interval_neg_measurePreserving u

theorem reflectCoefficient_ae (u : IntervalLInfinity) :
    reflectCoefficient u =ᵐ[intervalMeasure] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u interval_neg_measurePreserving

theorem HasACMultiplierDerivative.reflect {u u' : IntervalLInfinity}
    (h : HasACMultiplierDerivative u u') :
    HasACMultiplierDerivative (reflectCoefficient u) (-reflectCoefficient u') := by
  obtain ⟨A, hAac, hA, hdA⟩ := h
  refine ⟨fun x => A (-x), absolutelyContinuousOnInterval_comp_neg hAac, ?_, ?_⟩
  · filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hA,
      reflectCoefficient_ae u] with x hx hr
    rw [hr]
    exact hx
  · have hneg : ∀ᵐ x ∂intervalMeasure, (-reflectCoefficient u') x = -(u' (-x)) := by
      filter_upwards [Lp.coeFn_neg (reflectCoefficient u'), reflectCoefficient_ae u']
        with x hn hr
      rw [hn]
      change -(reflectCoefficient u' x) = _
      rw [hr]
    filter_upwards [(Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      hdA, interval_ae_closed hneg] with x hx he hxI
    rw [he hxI]
    have hxI' : -x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hxI.2], by linarith [hxI.1]⟩
    have := (hx hxI').scomp x (hasDerivAt_neg x)
    rw [neg_one_smul] at this
    exact this

theorem HasACMultiplierDerivative.coeff_add {a a' b b' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (hb : HasACMultiplierDerivative b b') :
    HasACMultiplierDerivative (a + b) (a' + b') := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  obtain ⟨B, hBac, hB, hdB⟩ := hb
  refine ⟨fun x => A x + B x, hAac.add hBac, ?_, ?_⟩
  · filter_upwards [hA, hB, Lp.coeFn_add a b] with x ha hb hc
    rw [hc]
    change A x + B x = a x + b x
    rw [ha, hb]
  · filter_upwards [hdA, hdB, interval_ae_closed (Lp.coeFn_add a' b')] with x ha hb hc hx
    rw [hc hx]
    exact (ha hx).add (hb hx)

theorem nearlyEven_gauge_real_identity (σ α β : ℝ) (hσ : α = σ * |α|) (hα : 0 < |α|)
    (hβ : 0 < |β|) :
    σ * Real.sqrt |α * β| * Real.sqrt (Real.sqrt (|α| / |β|)) =
      α * Real.sqrt (Real.sqrt (|β| / |α|)) := by
  set u := Real.sqrt (Real.sqrt |α|) with hu
  set v := Real.sqrt (Real.sqrt |β|) with hv
  have hu0 : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hα)
  have hv0 : 0 < v := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hsa : Real.sqrt |α| = u * u := (Real.mul_self_sqrt (Real.sqrt_nonneg _)).symm
  have hsb : Real.sqrt |β| = v * v := (Real.mul_self_sqrt (Real.sqrt_nonneg _)).symm
  have ha : |α| = (u * u) * (u * u) := by rw [← hsa, Real.mul_self_sqrt (abs_nonneg _)]
  have hb : |β| = (v * v) * (v * v) := by rw [← hsb, Real.mul_self_sqrt (abs_nonneg _)]
  have h1 : Real.sqrt (Real.sqrt (|α| / |β|)) = u / v := by
    rw [Real.sqrt_div (abs_nonneg _), Real.sqrt_div (Real.sqrt_nonneg _)]
  have h2 : Real.sqrt (Real.sqrt (|β| / |α|)) = v / u := by
    rw [Real.sqrt_div (abs_nonneg _), Real.sqrt_div (Real.sqrt_nonneg _)]
  have h3 : Real.sqrt |α * β| = (u * u) * (v * v) := by
    rw [abs_mul, Real.sqrt_mul (abs_nonneg _), hsa, hsb]
  rw [h1, h2, h3]
  conv_rhs => rw [hσ, ha]
  field_simp

theorem nearlyEven_log_bound (σ α β η : ℝ) (z1 z2 : ℂ) (hσ : σ * σ = 1)
    (hα : α = σ * |α|) (hβ : β = σ * |β|) (hα0 : 0 < |α|) (hβ0 : 0 < |β|)
    (hη : ‖z1 * (β : ℂ) + z2 * (α : ℂ)‖ ≤ η * |α * β|) :
    ‖(((Real.sqrt (Real.sqrt (|α| / |β|)))⁻¹ : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * ((((1 / 2 : ℂ) * ((((σ : ℂ) * z1 * ((|β|⁻¹ : ℝ) : ℂ) +
        ((|α| : ℝ) : ℂ) * -(-((σ : ℂ) * z2) * ((|β|⁻¹ : ℝ) : ℂ) * ((|β|⁻¹ : ℝ) : ℂ))).re : ℝ) : ℂ)
        * (((Real.sqrt (|α| / |β|))⁻¹ : ℝ) : ℂ)).re : ℝ) : ℂ) *
        (((Real.sqrt (Real.sqrt (|α| / |β|)))⁻¹ : ℝ) : ℂ))‖ ≤ η / 4 := by
  set t := Real.sqrt (|α| / |β|) with ht
  set w := Real.sqrt t with hw
  have hq0 : 0 < |α| / |β| := div_pos hα0 hβ0
  have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
  have hw0 : 0 < w := Real.sqrt_pos.mpr ht0
  have htt : t * t = |α| / |β| := Real.mul_self_sqrt hq0.le
  have hww : w * w = t := Real.mul_self_sqrt ht0.le
  set u := z1.re
  set v := z2.re
  have hQ : ((σ : ℂ) * z1 * ((|β|⁻¹ : ℝ) : ℂ) +
        ((|α| : ℝ) : ℂ) * -(-((σ : ℂ) * z2) * ((|β|⁻¹ : ℝ) : ℂ) * ((|β|⁻¹ : ℝ) : ℂ))).re =
      σ * u * |β|⁻¹ + |α| * (σ * v * |β|⁻¹ * |β|⁻¹) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_im, Complex.mul_im, u, v]
    ring
  rw [hQ]
  have hre : ((1 / 2 : ℂ) * (((σ * u * |β|⁻¹ + |α| * (σ * v * |β|⁻¹ * |β|⁻¹)) : ℝ) : ℂ)
        * ((t⁻¹ : ℝ) : ℂ)).re = 1 / 2 * (σ * u * |β|⁻¹ + |α| * (σ * v * |β|⁻¹ * |β|⁻¹)) * t⁻¹ := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  have key : w⁻¹ * (1 / 2 * (1 / 2 * (σ * u * |β|⁻¹ + |α| * (σ * v * |β|⁻¹ * |β|⁻¹)) * t⁻¹) *
      w⁻¹) = (u * β + v * α) / (4 * (α * β)) := by
    have hα1 : α ≠ 0 := fun h => by simp [h] at hα0
    have hβ1 : β ≠ 0 := fun h => by simp [h] at hβ0
    have e1 : w⁻¹ * w⁻¹ = t⁻¹ := by rw [← mul_inv, hww]
    have e2 : t⁻¹ * t⁻¹ = |β| / |α| := by rw [← mul_inv, htt, inv_div]
    calc _ = 1 / 4 * (σ * u * |β|⁻¹ + |α| * (σ * v * |β|⁻¹ * |β|⁻¹)) * (t⁻¹ * t⁻¹) := by
            rw [← e1]; ring
      _ = _ := by
        rw [e2]
        conv_rhs => rw [hα, hβ]
        have hσ0 : σ ≠ 0 := fun h => by simp [h] at hσ
        field_simp
        linear_combination (u * |β| + |α| * v) * hσ
  have hcast : ((w⁻¹ : ℝ) : ℂ) * ((1 / 2 : ℂ) * (((1 / 2 * (σ * u * |β|⁻¹ + |α| *
      (σ * v * |β|⁻¹ * |β|⁻¹)) * t⁻¹ : ℝ) : ℂ)) * ((w⁻¹ : ℝ) : ℂ)) =
      (((u * β + v * α) / (4 * (α * β)) : ℝ) : ℂ) := by
    rw [← key]; push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 4)]
  have hab : 0 < |α * β| := by rw [abs_mul]; positivity
  have hnum : |u * β + v * α| ≤ η * |α * β| := by
    refine le_trans ?_ hη
    have : (z1 * (β : ℂ) + z2 * (α : ℂ)).re = u * β + v * α := by simp [u, v]
    rw [← this]
    exact Complex.abs_re_le_norm _
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Данные калибровки `r = (|a(x)| / |a(-x)|)^(1/4)`. -/
theorem nearlyEven_gauge_data (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa η : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'')
    (hη : ∀ᵐ x ∂intervalMeasure,
      ‖a' x * (a (-x) : ℂ) + a' (-x) * (a x : ℂ)‖ ≤ η * |a x * a (-x)|) :
    ∃ (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (r wg r' r'' : IntervalLInfinity),
      (∀ x, b (-x) = b x) ∧
      (∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa) ∧
      (∀ᵐ x ∂intervalMeasure, r x * wg x = 1) ∧
      HasACMultiplierDerivative r r' ∧ HasACMultiplierDerivative r' r'' ∧
      (∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x =
        realIntervalCoefficient a ha x * r (-x)) ∧
      (∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f) ∧
      (∀ᵐ x ∂intervalMeasure, ‖wg x * r' x‖ ≤ η / 4) := by
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
  have hmeas : AEMeasurable a intervalMeasure := ha.aestronglyMeasurable.aemeasurable
  have hmeasn : AEMeasurable (fun x => a (-x)) intervalMeasure :=
    hmeas.comp_quasiMeasurePreserving interval_neg_measurePreserving.quasiMeasurePreserving
  have hb : MemLp b ∞ intervalMeasure := by
    have hbm : AEMeasurable b intervalMeasure :=
      (continuous_abs.measurable.comp_aemeasurable (hmeas.mul hmeasn)).sqrt.const_mul σ
    apply memLp_top_of_bound hbm.aestronglyMeasurable (Real.sqrt kappa)
    filter_upwards [hproduct] with x hx
    have hsq : ‖b x‖ ^ 2 ≤ kappa := by
      rw [Real.norm_eq_abs, sq_abs, sq, hbsq x]
      exact hx
    exact (Real.sqrt_sq (norm_nonneg _)).symm.le.trans (Real.sqrt_le_sqrt hsq)
  -- отражённые оценки
  have hlowern : ∀ᵐ x ∂intervalMeasure, m ≤ |a (-x)| :=
    interval_neg_measurePreserving.quasiMeasurePreserving.ae hlower
  have huppern : ∀ᵐ x ∂intervalMeasure, |a (-x)| ≤ M :=
    interval_neg_measurePreserving.quasiMeasurePreserving.ae hupper
  have hsignn : ∀ᵐ x ∂intervalMeasure, a (-x) = σ * |a (-x)| :=
    interval_neg_measurePreserving.quasiMeasurePreserving.ae hsign
  have hne : intervalMeasure ≠ 0 := by
    intro h
    have h2 := congrArg (fun μ : Measure ℝ => μ Set.univ) h
    simp [intervalMeasure] at h2
    norm_num at h2
  have := ae_neBot.mpr hne
  have hmM : m ≤ M := by
    obtain ⟨x, hx1, hx2⟩ := (hlower.and hupper).exists
    exact hx1.trans hx2
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  -- коэффициент `|a|` и его производные
  let Aabs := realIntervalCoefficient (fun x => |a x|) (real_abs_memLp a ha)
  have habs : Aabs = (σ : ℂ) • realIntervalCoefficient a ha := by
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
  let D1 := (σ : ℂ) • a'
  let D2 := (σ : ℂ) • a''
  have hA0 : HasACMultiplierDerivative Aabs D1 := by
    rw [habs]
    exact (HasACMultiplierDerivative.of_weak h0).coeff_smul (σ : ℂ)
  have hA1 : HasACMultiplierDerivative D1 D2 :=
    (HasACMultiplierDerivative.of_weak h1).coeff_smul (σ : ℂ)
  -- отражение и обратный коэффициент
  let R := reflectCoefficient Aabs
  have hR0 : HasACMultiplierDerivative R (-reflectCoefficient D1) := hA0.reflect
  have hR1 : HasACMultiplierDerivative (-reflectCoefficient D1) (-(-reflectCoefficient D2)) :=
    hA1.reflect.coeff_neg
  have hRae : ∀ᵐ x ∂intervalMeasure, R x = ((|a (-x)| : ℝ) : ℂ) := by
    filter_upwards [reflectCoefficient_ae Aabs,
      interval_neg_measurePreserving.quasiMeasurePreserving.ae
        (realIntervalCoefficient_ae (fun x => |a x|) (real_abs_memLp a ha))] with x h1 h2
    rw [h1]
    exact h2
  have hRlow : ∀ᵐ x ∂intervalMeasure, m ≤ ‖R x‖ := by
    filter_upwards [hRae, hlowern] with x h1 h2
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact h2
  let Ri := inverseCoefficient R m hm hRlow
  let Ri' := inverseCoefficientDeriv (-reflectCoefficient D1) Ri
  have hRi0 : HasACMultiplierDerivative Ri Ri' := hR0.coeff_inv m hm hRlow
  have hRi1 := ((hR1.coeff_mul hRi0).coeff_mul hRi0).coeff_neg
  -- произведение `q = |a(x)| / |a(-x)|`
  let Qc := coefficientProduct Aabs Ri
  let Q' := coefficientProduct D1 Ri + coefficientProduct Aabs Ri'
  have hQ0 : HasACMultiplierDerivative Qc Q' := hA0.coeff_mul hRi0
  have hQ1 := (hA1.coeff_mul hRi0).coeff_add (hA0.coeff_mul hRi1)
  have hQW : MemIntervalW2Infinity Qc := ⟨Q', _, hQ0.to_weak, hQ1.to_weak⟩
  let q : ℝ → ℝ := fun x => |a x| / |a (-x)|
  have hqlow : ∀ᵐ x ∂intervalMeasure, m / M ≤ q x := by
    filter_upwards [hlower, huppern, hlowern] with x h1 h2 h3
    exact div_le_div₀ (abs_nonneg _) h1 (lt_of_lt_of_le hm h3) h2
  have hqup : ∀ᵐ x ∂intervalMeasure, q x ≤ M / m := by
    filter_upwards [hupper, hlowern] with x h1 h2
    exact div_le_div₀ hM.le h1 hm h2
  have hq : MemLp q ∞ intervalMeasure := by
    have hqm : AEMeasurable q intervalMeasure :=
      (continuous_abs.measurable.comp_aemeasurable hmeas).div
        (continuous_abs.measurable.comp_aemeasurable hmeasn)
    apply memLp_top_of_bound hqm.aestronglyMeasurable (M / m)
    filter_upwards [hqup, hqlow] with x h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg ((div_pos hm hM).le.trans h2)]
    exact h1
  have hQeq : realIntervalCoefficient q hq = Qc := by
    apply Lp.ext
    filter_upwards [realIntervalCoefficient_ae q hq, coefficientProduct_ae Aabs Ri,
      realIntervalCoefficient_ae (fun x => |a x|) (real_abs_memLp a ha),
      inverseCoefficient_ae R m hm hRlow, hRae] with x h1 h2 h3 h4 h5
    rw [h1, h2]
    rw [h3, h4, h5]
    change ((|a x| / |a (-x)| : ℝ) : ℂ) = _
    push_cast
    rw [div_eq_mul_inv]
  have hQW' : MemIntervalW2Infinity (realIntervalCoefficient q hq) := hQeq ▸ hQW
  have hQ0' : HasACMultiplierDerivative (realIntervalCoefficient q hq) Q' := hQeq ▸ hQ0
  have hmMpos : 0 < m / M := div_pos hm hM
  let W := inverseSqrtWeight q hq (m / M) hmMpos hqlow
  let S' := sqrtCoefficientDeriv Q' W
  have hS0 : HasACMultiplierDerivative (sqrtWeight q hq (M / m) hqup) S' :=
    sqrtWeight_hasACDerivative q hq (m / M) (M / m) hmMpos hqlow hqup Q' hQ0'
  have hSW : MemIntervalW2Infinity (sqrtWeight q hq (M / m) hqup) :=
    sqrtWeight_memW2Infinity q hq (m / M) (M / m) hmMpos hqlow hqup hQW'
  -- вес `r = √(√q)`
  let s : ℝ → ℝ := fun x => Real.sqrt (q x)
  have hs : MemLp s ∞ intervalMeasure := sqrt_memLp_of_upper_bound q hq (M / m) hqup
  have hslow : ∀ᵐ x ∂intervalMeasure, Real.sqrt (m / M) ≤ s x := by
    filter_upwards [hqlow] with x hx
    exact Real.sqrt_le_sqrt hx
  have hsup : ∀ᵐ x ∂intervalMeasure, s x ≤ Real.sqrt (M / m) := by
    filter_upwards [hqup] with x hx
    exact Real.sqrt_le_sqrt hx
  have hsm : 0 < Real.sqrt (m / M) := Real.sqrt_pos.mpr hmMpos
  have hSW' : MemIntervalW2Infinity (realIntervalCoefficient s hs) := hSW
  let r := sqrtWeight s hs (Real.sqrt (M / m)) hsup
  let wg := inverseSqrtWeight s hs (Real.sqrt (m / M)) hsm hslow
  let r' := sqrtCoefficientDeriv S' wg
  have hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1 :=
    sqrtWeight_inverseSqrtWeight s hs _ _ hsm hslow hsup
  have hr : HasACMultiplierDerivative r r' :=
    sqrtWeight_hasACDerivative s hs _ _ hsm hslow hsup S' hS0
  obtain ⟨r₁', r'', hr0, hr1⟩ := sqrtWeight_memW2Infinity s hs _ _ hsm hslow hsup hSW'
  have heq : r₁' = r' := Lp.ext (HasWeakDerivOn.unique isOpen_Ioo hr0 hr.to_weak)
  rw [heq] at hr1
  have hr' : HasACMultiplierDerivative r' r'' := HasACMultiplierDerivative.of_weak hr1
  refine ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, hr, hr', ?_,
    fun f => sqrtWeight_dirichlet_iff s hs _ _ hsm hslow hsup hSW' f, ?_⟩
  · have hrn : ∀ᵐ x ∂intervalMeasure, r (-x) = ((Real.sqrt (s (-x)) : ℝ) : ℂ) :=
      interval_neg_measurePreserving.quasiMeasurePreserving.ae (sqrtWeight_ae s hs _ hsup)
    filter_upwards [realIntervalCoefficient_ae b hb, realIntervalCoefficient_ae a ha,
      sqrtWeight_ae s hs _ hsup, hrn, hsign, hlower, hlowern] with x hbx hax hrx hrnx hsx hl hln
    rw [hbx, hax, hrx, hrnx]
    have hreal := nearlyEven_gauge_real_identity σ (a x) (a (-x)) hsx (lt_of_lt_of_le hm hl)
      (lt_of_lt_of_le hm hln)
    change ((σ * Real.sqrt |a x * a (-x)| : ℝ) : ℂ) * ((Real.sqrt (Real.sqrt
      (|a x| / |a (-x)|)) : ℝ) : ℂ) = ((a x : ℝ) : ℂ) * ((Real.sqrt (Real.sqrt
      (|a (-x)| / |a (- -x)|)) : ℝ) : ℂ)
    rw [neg_neg]
    exact_mod_cast hreal
  · have hD1n : ∀ᵐ x ∂intervalMeasure, D1 (-x) = (σ : ℂ) • a' (-x) :=
      interval_neg_measurePreserving.quasiMeasurePreserving.ae (Lp.coeFn_smul (σ : ℂ) a')
    filter_upwards [inverseSqrtWeight_ae s hs _ hsm hslow, sqrtCoefficientDeriv_ae S' wg,
      sqrtCoefficientDeriv_ae Q' W, inverseSqrtWeight_ae q hq _ hmMpos hqlow,
      Lp.coeFn_add (coefficientProduct D1 Ri) (coefficientProduct Aabs Ri'),
      coefficientProduct_ae D1 Ri, coefficientProduct_ae Aabs Ri', Lp.coeFn_smul (σ : ℂ) a',
      inverseCoefficient_ae R m hm hRlow, hRae,
      realIntervalCoefficient_ae (fun x => |a x|) (real_abs_memLp a ha),
      inverseCoefficientDeriv_ae (-reflectCoefficient D1) Ri,
      Lp.coeFn_neg (reflectCoefficient D1), reflectCoefficient_ae D1, hD1n,
      hsign, hsignn, hlower, hlowern, hη]
      with x hwg hr'x hS'x hWx hQx hp1 hp2 hD1 hRi hRx hAx hRi' hnegD hrefl hD1nx
        hsx hsxn hl hln hηx
    have hQval : Q' x = (σ : ℂ) * a' x * ((|a (-x)|⁻¹ : ℝ) : ℂ) + ((|a x| : ℝ) : ℂ) *
        -(-((σ : ℂ) * a' (-x)) * ((|a (-x)|⁻¹ : ℝ) : ℂ) * ((|a (-x)|⁻¹ : ℝ) : ℂ)) := by
      rw [hQx, Pi.add_apply, hp1, hp2, hD1, hRi', hnegD, Pi.neg_apply, hrefl, hD1nx, hAx, hRi,
        hRx, Complex.ofReal_inv, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    rw [hr'x, hwg, hS'x, hWx, hQval]
    have hb := nearlyEven_log_bound σ (a x) (a (-x)) η (a' x) (a' (-x)) hσ hsx hsxn
      (lt_of_lt_of_le hm hl) (lt_of_lt_of_le hm hln) hηx
    simp only [Complex.ofReal_inv] at hb ⊢
    exact hb

/-- **Базис Рисса со скобками для коэффициента, близкого к чётному.**
Условия: вещественный `a ∈ W²∞`, `0 < m ≤ |a| ≤ M`, `|a(x) a(-x)| ≤ κ < 1` и
`|a'(x)/a(x) + a'(-x)/a(-x)| ≤ η` почти всюду, где `160 (1 + √κ) η < π (1 - √κ)`.
Для чётного `a` левая часть условия малости равна нулю. -/
theorem nearlyEven_bracket_basis (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa η : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'') (hη0 : 0 ≤ η)
    (hη : ∀ᵐ x ∂intervalMeasure,
      ‖a' x * (a (-x) : ℂ) + a' (-x) * (a x : ℂ)‖ ≤ η * |a x * a (-x)|)
    (hsmall : 160 * (1 + Real.sqrt kappa) * η < Real.pi * (1 - Real.sqrt kappa)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k := by
  obtain ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, hr, hr', hg, hdom, hlog⟩ :=
    nearlyEven_gauge_data a ha m M kappa η hm hlower hupper hproduct a' a'' h0 h1 hη
  refine bracket_basis_of_gauge (realIntervalCoefficient a ha) b hb kappa (η / 4) hkappa
    hkappa1 (by positivity) (Filter.Eventually.of_forall hbeven) hbprod r wg r' r'' hrw hr hr'
    hg hdom hlog ?_
  have e : 640 * (1 + Real.sqrt kappa) * (η / 4) = 160 * (1 + Real.sqrt kappa) * η := by ring
  rw [e]
  exact hsmall

/-- Для коэффициента, близкого к чётному, блоки базиса со скобками порождены
корневыми векторами `L_a`. -/
theorem nearlyEven_bracket_rootVectors (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa η : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'') (hη0 : 0 ≤ η)
    (hη : ∀ᵐ x ∂intervalMeasure,
      ‖a' x * (a (-x) : ℂ) + a' (-x) * (a x : ℂ)‖ ≤ η * |a x * a (-x)|)
    (hsmall : 160 * (1 + Real.sqrt kappa) * η < Real.pi * (1 - Real.sqrt kappa)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ := by
  obtain ⟨W, ⟨B⟩, hW⟩ := nearlyEven_bracket_basis a ha m M kappa η hm hlower hupper hkappa
    hkappa1 hproduct a' a'' h0 h1 hη0 hη hsmall
  refine ⟨W, ⟨B⟩, fun k => ?_⟩
  have := B.finite k
  exact invariant_block_rootVectors (realIntervalCoefficient a ha) (W k) (hW k)

/-- Для чётного коэффициента слабая производная нечётна, поэтому мера отклонения
от чётности `a'(x) a(-x) + a'(-x) a(x)` равна нулю почти всюду. -/
theorem even_coefficient_deviation_zero (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (a' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) :
    ∀ᵐ x ∂intervalMeasure, a' x * (a (-x) : ℂ) + a' (-x) * (a x : ℂ) = 0 := by
  have hAneg : ∀ᵐ x ∂intervalMeasure,
      realIntervalCoefficient a ha (-x) = ((a (-x) : ℝ) : ℂ) :=
    interval_neg_measurePreserving.quasiMeasurePreserving.ae (realIntervalCoefficient_ae a ha)
  have hrefl : (Involution.reflect (realIntervalCoefficient a ha : ℝ → ℂ))
      =ᵐ[intervalMeasure] (realIntervalCoefficient a ha : ℝ → ℂ) := by
    filter_upwards [hAneg, realIntervalCoefficient_ae a ha, heven] with x hn hx he
    change realIntervalCoefficient a ha (-x) = realIntervalCoefficient a ha x
    rw [hn, hx, he]
  have h1 : HasIntervalWeakDeriv (realIntervalCoefficient a ha : ℝ → ℂ)
      (-Involution.reflect (a' : ℝ → ℂ)) := h0.reflect.congr hrefl Filter.EventuallyEq.rfl
  have huniq := HasWeakDerivOn.unique isOpen_Ioo h0 h1
  filter_upwards [huniq, heven] with x hx he
  have hneg : a' (-x) = -a' x := by
    have : a' x = -a' (-x) := hx
    rw [this, neg_neg]
  rw [hneg, he]
  ring

/-- Согласованность с чётным случаем: чётный знакопостоянный коэффициент класса `W²∞`
удовлетворяет условию близости к чётному с `η = 0`. Вывод слабее, чем в
`evenCoefficient_riesz_eigenbasis`, где получен обычный базис Рисса. -/
theorem evenSignDefinite_bracket_basis (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'')
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k := by
  refine nearlyEven_bracket_basis a ha m M kappa 0 hm hlower hupper hkappa hkappa1 hproduct
    a' a'' h0 h1 le_rfl ?_ ?_
  · filter_upwards [even_coefficient_deviation_zero a ha a' h0 heven] with x hx
    rw [hx, norm_zero, zero_mul]
  · have hsk : Real.sqrt kappa < 1 :=
      (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
    rw [mul_zero]
    exact mul_pos Real.pi_pos (by linarith)

end Involution
