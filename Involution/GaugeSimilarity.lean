module

public import Involution.CompactInverse
public import Involution.CoefficientSqrt

/-! Калибровочное подобие для случая C6.
Умножение на регулярный вес `r` переводит `L_a` в `L_b + B`, где
`b(x) r(x) = a(x) r(-x)` почти всюду, а `B` — оператор первого порядка.
Для знакопостоянного `a` класса `W²∞` выбор `r = sqrt |a|` даёт чётный `b`,
и `B` подчинён `L_b` с показателем `1/2`. Базис со скобками выводится отсюда в
`GeneralBrackets.lean` теоремой о подчинённых возмущениях из `MarkusMatsaev.lean`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem principalOperator_gauge (a b r : IntervalLInfinity)
    (hg : ∀ᵐ x ∂intervalMeasure, b x * r x = a x * r (-x)) (g : IntervalL2) :
    principalOperator a (boundedMultiplier r g) =
      boundedMultiplier r (principalOperator b g) := by
  apply Lp.ext
  have hmn : ∀ᵐ x ∂intervalMeasure, boundedMultiplier r g (-x) = r (-x) * g (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (boundedMultiplier_ae r g)] with x hx
    exact hx
  filter_upwards [principalOperator_ae a (boundedMultiplier r g), boundedMultiplier_ae r g, hmn,
    boundedMultiplier_ae r (principalOperator b g), principalOperator_ae b g, hg]
    with x hp hm hmx hb hq hx
  rw [hp, hm, hmx, hb, hq]
  calc
    r x * g x + a x * (r (-x) * g (-x)) = r x * g x + (a x * r (-x)) * g (-x) := by ring
    _ = r x * g x + (b x * r x) * g (-x) := by rw [hx]
    _ = _ := by ring

/-- Младшие члены `-(2 w r' f' + w r'' f)` после калибровки весом `r`, `w = 1 / r`. -/
def gaugeLowerOrder (w r' r'' : IntervalLInfinity) (f : IntervalL2) (hf : MemIntervalH2 f) :
    IntervalL2 :=
  -((2 : ℂ) • boundedMultiplier w (boundedMultiplier r' (firstWeakDeriv f hf)) +
    boundedMultiplier w (boundedMultiplier r'' f))

theorem secondWeakDeriv_gauge (r w r' r'' : IntervalLInfinity)
    (hr : HasACMultiplierDerivative r r') (hr' : HasACMultiplierDerivative r' r'')
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1) (f : IntervalL2) (hf : MemIntervalH2 f)
    (hrf : MemIntervalH2 (boundedMultiplier r f)) :
    -secondWeakDeriv (boundedMultiplier r f) hrf =
      boundedMultiplier r (-secondWeakDeriv f hf + gaugeLowerOrder w r' r'' f hf) := by
  rw [secondWeakDeriv_mul_coefficient hr hr' f hf hrf]
  simp only [gaugeLowerOrder, map_add, map_neg, map_smul, boundedMultiplier_inverse r w hrw]
  module

/-- Калибровочное подобие: `L_a (r f) = r (L_b f + (I + b R) B₀ f)`. -/
theorem gauge_similarity (a b r w r' r'' : IntervalLInfinity)
    (hr : HasACMultiplierDerivative r r') (hr' : HasACMultiplierDerivative r' r'')
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1)
    (hg : ∀ᵐ x ∂intervalMeasure, b x * r x = a x * r (-x))
    (f : IntervalL2) (hf : MemIntervalH2 f) (hrf : MemIntervalH2 (boundedMultiplier r f)) :
    variableSobolevOperator a (boundedMultiplier r f) hrf =
      boundedMultiplier r (variableSobolevOperator b f hf +
        principalOperator b (gaugeLowerOrder w r' r'' f hf)) := by
  rw [variableSobolevOperator_eq_principal, variableSobolevOperator_eq_principal,
    ← (principalOperator b).map_add, ← principalOperator_gauge a b r hg,
    secondWeakDeriv_gauge r w r' r'' hr hr' hrw f hf hrf]

theorem firstWeakDeriv_norm_sq_le (f : IntervalL2) (hf : MemDirichletH2 f) :
    ‖firstWeakDeriv f hf.1‖ ^ 2 ≤ ‖f‖ * ‖secondWeakDeriv f hf.1‖ := by
  have he := negativeSecondWeakDeriv_energy f f hf hf.1
  calc
    ‖firstWeakDeriv f hf.1‖ ^ 2 =
        RCLike.re (inner ℂ (firstWeakDeriv f hf.1) (firstWeakDeriv f hf.1)) :=
      (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (inner ℂ f (-secondWeakDeriv f hf.1)) := by rw [he]
    _ ≤ ‖f‖ * ‖-secondWeakDeriv f hf.1‖ := re_inner_le_norm _ _
    _ = _ := by rw [norm_neg]

theorem dirichlet_norm_le (f : IntervalL2) (hf : MemDirichletH2 f) :
    ‖f‖ ≤ ‖spectralGreen‖ * ‖secondWeakDeriv f hf.1‖ := by
  have h := spectralGreen.le_opNorm (-secondWeakDeriv f hf.1)
  rwa [spectralGreen_left_inverse f hf, norm_neg] at h

/-- Оценка младших членов через `‖f‖^(1/2) ‖f''‖^(1/2)`. -/
theorem gaugeLowerOrder_norm_le (w r' r'' : IntervalLInfinity) (f : IntervalL2)
    (hf : MemDirichletH2 f) :
    ‖gaugeLowerOrder w r' r'' f hf.1‖ ≤
      (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) *
        Real.sqrt (‖f‖ * ‖secondWeakDeriv f hf.1‖) := by
  let q := Real.sqrt (‖f‖ * ‖secondWeakDeriv f hf.1‖)
  have hd : ‖firstWeakDeriv f hf.1‖ ≤ q :=
    (Real.sqrt_sq (norm_nonneg _)).symm.le.trans
      (Real.sqrt_le_sqrt (firstWeakDeriv_norm_sq_le f hf))
  have hn : ‖f‖ ≤ Real.sqrt ‖spectralGreen‖ * q := by
    calc
      ‖f‖ = Real.sqrt (‖f‖ * ‖f‖) := (Real.sqrt_mul_self (norm_nonneg f)).symm
      _ ≤ Real.sqrt (‖spectralGreen‖ * (‖f‖ * ‖secondWeakDeriv f hf.1‖)) := by
        apply Real.sqrt_le_sqrt
        calc
          ‖f‖ * ‖f‖ ≤ ‖f‖ * (‖spectralGreen‖ * ‖secondWeakDeriv f hf.1‖) :=
            mul_le_mul_of_nonneg_left (dirichlet_norm_le f hf) (norm_nonneg f)
          _ = _ := by ring
      _ = _ := Real.sqrt_mul (norm_nonneg _) _
  have h1 : ‖boundedMultiplier w (boundedMultiplier r' (firstWeakDeriv f hf.1))‖ ≤
      ‖w‖ * (‖r'‖ * q) :=
    (boundedMultiplier_norm_le w _).trans (mul_le_mul_of_nonneg_left
      ((boundedMultiplier_norm_le r' _).trans
        (mul_le_mul_of_nonneg_left hd (norm_nonneg r'))) (norm_nonneg w))
  have h2 : ‖boundedMultiplier w (boundedMultiplier r'' f)‖ ≤
      ‖w‖ * (‖r''‖ * (Real.sqrt ‖spectralGreen‖ * q)) :=
    (boundedMultiplier_norm_le w _).trans (mul_le_mul_of_nonneg_left
      ((boundedMultiplier_norm_le r'' _).trans
        (mul_le_mul_of_nonneg_left hn (norm_nonneg r''))) (norm_nonneg w))
  have htwo : ‖(2 : ℂ)‖ = 2 := by simp
  calc
    ‖gaugeLowerOrder w r' r'' f hf.1‖ =
        ‖(2 : ℂ) • boundedMultiplier w (boundedMultiplier r' (firstWeakDeriv f hf.1)) +
          boundedMultiplier w (boundedMultiplier r'' f)‖ := norm_neg _
    _ ≤ ‖(2 : ℂ) • boundedMultiplier w (boundedMultiplier r' (firstWeakDeriv f hf.1))‖ +
          ‖boundedMultiplier w (boundedMultiplier r'' f)‖ := norm_add_le _ _
    _ ≤ 2 * (‖w‖ * (‖r'‖ * q)) + ‖w‖ * (‖r''‖ * (Real.sqrt ‖spectralGreen‖ * q)) := by
      rw [norm_smul, htwo]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
    _ = _ := by ring

/-- Подчинённость порядка `1/2`: калибровочное возмущение оценивается через
`‖f‖^(1/2) ‖L_b f‖^(1/2)` на всей слабой области Дирихле. -/
theorem gaugePerturbation_subordinate (b db w r' r'' : IntervalLInfinity)
    (hdb : ∀ᵐ x ∂intervalMeasure, db x * (1 - b x * b (-x)) = 1)
    (f : IntervalL2) (hf : MemDirichletH2 f) :
    ‖principalOperator b (gaugeLowerOrder w r' r'' f hf.1)‖ ≤
      (‖principalOperator b‖ *
        (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) *
          Real.sqrt ‖principalOperatorInverse b db‖) *
        Real.sqrt (‖f‖ * ‖variableSobolevOperator b f hf.1‖) := by
  let c := 2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖
  have hc : 0 ≤ c := by positivity
  have hinv : principalOperatorInverse b db (variableSobolevOperator b f hf.1) =
      -secondWeakDeriv f hf.1 := by
    rw [variableSobolevOperator_eq_principal, principalOperatorInverse_left b db hdb]
  have hs : ‖secondWeakDeriv f hf.1‖ ≤
      ‖principalOperatorInverse b db‖ * ‖variableSobolevOperator b f hf.1‖ := by
    have h := (principalOperatorInverse b db).le_opNorm (variableSobolevOperator b f hf.1)
    rwa [hinv, norm_neg] at h
  have hq : Real.sqrt (‖f‖ * ‖secondWeakDeriv f hf.1‖) ≤
      Real.sqrt ‖principalOperatorInverse b db‖ *
        Real.sqrt (‖f‖ * ‖variableSobolevOperator b f hf.1‖) := by
    calc
      _ ≤ Real.sqrt (‖principalOperatorInverse b db‖ *
          (‖f‖ * ‖variableSobolevOperator b f hf.1‖)) := by
        apply Real.sqrt_le_sqrt
        calc
          ‖f‖ * ‖secondWeakDeriv f hf.1‖ ≤
              ‖f‖ * (‖principalOperatorInverse b db‖ * ‖variableSobolevOperator b f hf.1‖) :=
            mul_le_mul_of_nonneg_left hs (norm_nonneg f)
          _ = _ := by ring
      _ = _ := Real.sqrt_mul (norm_nonneg _) _
  calc
    _ ≤ ‖principalOperator b‖ * ‖gaugeLowerOrder w r' r'' f hf.1‖ :=
      (principalOperator b).le_opNorm _
    _ ≤ ‖principalOperator b‖ * (c * Real.sqrt (‖f‖ * ‖secondWeakDeriv f hf.1‖)) :=
      mul_le_mul_of_nonneg_left (gaugeLowerOrder_norm_le w r' r'' f hf) (norm_nonneg _)
    _ ≤ ‖principalOperator b‖ * (c * (Real.sqrt ‖principalOperatorInverse b db‖ *
          Real.sqrt (‖f‖ * ‖variableSobolevOperator b f hf.1‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hc) (norm_nonneg _)
    _ = _ := by ring

/-- Коэффициент класса `W²∞`, отделённый от нуля, имеет постоянный знак почти всюду. -/
theorem real_coefficient_constant_sign (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (ε : ℝ) (hε : 0 < ε) (hlower : ∀ᵐ x ∂intervalMeasure, ε ≤ |p x|)
    (ha : MemIntervalW2Infinity (realIntervalCoefficient p hp)) :
    ∃ σ : ℝ, σ * σ = 1 ∧ ∀ᵐ x ∂intervalMeasure, p x = σ * |p x| := by
  obtain ⟨a', a'', h0, _⟩ := ha
  obtain ⟨A, hAac, hA, _⟩ := HasACMultiplierDerivative.of_weak h0
  let P : ℝ → ℝ := fun x => (A x).re
  have hPc : ContinuousOn P (Set.Icc (-1 : ℝ) 1) := by
    have hc := hAac.continuousOn
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hc
    exact Complex.reCLM.continuous.comp_continuousOn hc
  have hP : P =ᵐ[intervalMeasure] p := by
    filter_upwards [hA, realIntervalCoefficient_ae p hp] with x ha hp
    change (A x).re = p x
    rw [ha, hp]
    rfl
  have hcastP : (fun x => (P x : ℂ)) =ᵐ[intervalMeasure] realIntervalCoefficient p hp := by
    filter_upwards [hP, realIntervalCoefficient_ae p hp] with x hp ha
    rw [hp, ha]
  have hbound : ∀ᵐ x ∂intervalMeasure, ε ≤ ‖realIntervalCoefficient p hp x‖ := by
    filter_upwards [hlower, realIntervalCoefficient_ae p hp] with x hx ha
    simpa only [ha, Complex.norm_real, Real.norm_eq_abs] using hx
  have hPlower := continuous_representative_norm_lower
    (Complex.continuous_ofReal.comp_continuousOn hPc) hcastP ε hbound
  have hPnz : ∀ x ∈ Set.Icc (-1 : ℝ) 1, P x ≠ 0 := by
    intro x hx hz
    have h := hPlower x hx
    change ε ≤ ‖(P x : ℂ)‖ at h
    simp only [hz, Complex.ofReal_zero, norm_zero] at h
    linarith
  rcases continuous_nonzero_constant_sign P hPc hPnz with hpos | hneg
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [hP, ae_restrict_mem measurableSet_Ioo] with x hpx hx
    have hxpos := hpos x (Set.Ioo_subset_Icc_self hx)
    rw [hpx] at hxpos
    rw [abs_of_pos hxpos, one_mul]
  · refine ⟨-1, by norm_num, ?_⟩
    filter_upwards [hP, ae_restrict_mem measurableSet_Ioo] with x hpx hx
    have hxneg := hneg x (Set.Ioo_subset_Icc_self hx)
    rw [hpx] at hxneg
    rw [abs_of_neg hxneg]
    ring

/-- Редукция C6. Для вещественного `a ∈ W²∞` с `0 < m ≤ |a| ≤ M` и
`|a(x) a(-x)| ≤ κ < 1` существуют чётный коэффициент `b` с той же оценкой произведения,
взаимно обратные веса `r, w`, сохраняющие слабую область Дирихле, и возмущение `B`,
такие что `L_a (r f) = r (L_b f + B f)` и `‖B f‖ ≤ C ‖f‖^(1/2) ‖L_b f‖^(1/2)`. -/
theorem signDefinite_gauge_reduction (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha)) :
    ∃ (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (r w : IntervalLInfinity)
      (B : ∀ f : IntervalL2, MemDirichletH2 f → IntervalL2) (C : ℝ),
      (∀ x, b (-x) = b x) ∧
      (∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa) ∧
      (∀ᵐ x ∂intervalMeasure, r x * w x = 1) ∧
      (∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f) ∧
      (∀ (f : IntervalL2) (hf : MemDirichletH2 f)
        (hrf : MemDirichletH2 (boundedMultiplier r f)),
        variableSobolevOperator (realIntervalCoefficient a ha) (boundedMultiplier r f) hrf.1 =
          boundedMultiplier r
            (variableSobolevOperator (realIntervalCoefficient b hb) f hf.1 + B f hf)) ∧
      (∀ (f : IntervalL2) (hf : MemDirichletH2 f), ‖B f hf‖ ≤
        C * Real.sqrt (‖f‖ * ‖variableSobolevOperator (realIntervalCoefficient b hb) f hf.1‖)) := by
  obtain ⟨σ, hσ, hsign⟩ := real_coefficient_constant_sign a ha m hm hlower hreg
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
  let w := inverseSqrtWeight (fun x => |a x|) (real_abs_memLp a ha) m hm hlower
  have hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1 :=
    sqrtWeight_inverseSqrtWeight (fun x => |a x|) (real_abs_memLp a ha) m M hm hlower hupper
  obtain ⟨⟨r', r'', hr0, hr1⟩, _⟩ :=
    sqrt_abs_weights_memW2Infinity a ha m M hm hlower hupper hreg
  have hr := HasACMultiplierDerivative.of_weak hr0
  have hr' := HasACMultiplierDerivative.of_weak hr1
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
  let db := determinantInverse b hb kappa hkappa1 hbprod
  have hdb := determinantInverse_identity b hb kappa hkappa1 hbprod
  refine ⟨b, hb, r, w,
    fun f hf => principalOperator Bc (gaugeLowerOrder w r' r'' f hf.1),
    ‖principalOperator Bc‖ *
      (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) *
        Real.sqrt ‖principalOperatorInverse Bc db‖,
    hbeven, hbprod, hrw, ?_, ?_, ?_⟩
  · intro f
    exact sqrt_abs_dirichlet_iff a ha m M hm hlower hupper hreg f
  · intro f hf hrf
    exact gauge_similarity A Bc r w r' r'' hr hr' hrw hg f hf.1 hrf.1
  · intro f hf
    exact gaugePerturbation_subordinate Bc db w r' r'' hdb f hf

end Involution
