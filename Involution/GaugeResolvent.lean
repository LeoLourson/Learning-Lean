module

public import Involution.GaugeOperators
public import Involution.ResolventBound

/-! Утверждение 1 записи C19: оценка резольвенты на луче после калибровки.
Пусть `a`, `b ∈ L∞` вещественны, `r`, `w ∈ W²∞`, `r w = 1`, `b(x) r(x) = a(x) r(-x)` и
`|b(x) + b(-x)| ≤ 2α < 2` почти всюду. Тогда `T_a` ограниченно обратим, а при `s ≥ s₀`
уравнение `(L_a + s) f = h` однозначно разрешимо на слабой области Дирихле и
`‖f‖ ≤ C / s * ‖h‖`.

Доказательство ведётся в переменной `W = -g''`, `f = r g`: по `gauge_similarity`
`(L_a + s)(r g) = r (T_b + s G + T_b B̃) W`, где `B̃ = gaugeLowerOp w r' r''`. Оператор
`T_b + s G` обратим по коэрцитивности, а `‖T_b B̃ W‖ ≤ ‖(T_b + s G) W‖ / 2` при `s ≥ s₀`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Оператор `T_b + s G + T_b B̃`: на слабой области Дирихле
`L_b g + T_b B₀ g + s g = (T_b + s G + T_b B̃)(-g'')`. -/
def gaugeShiftedOperator (B w r' r'' : IntervalLInfinity) (s : ℝ) :
    IntervalL2 →L[ℂ] IntervalL2 :=
  shiftedPrincipalOperator B s + principalOperator B ∘L gaugeLowerOp w r' r''

/-- Главный множитель `T_a` обратим, если калибровка переводит `a` в `b` с `|b_e| ≤ α < 1`. -/
theorem gauge_principalOperator_boundedInverse (a b : ℝ → ℝ)
    (ha : MemLp a ∞ intervalMeasure) (hb : MemLp b ∞ intervalMeasure)
    (r w : IntervalLInfinity)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1)
    (hg : ∀ᵐ x ∂intervalMeasure,
      realIntervalCoefficient b hb x * r x = realIntervalCoefficient a ha x * r (-x))
    (α : ℝ) (hα1 : α < 1) (hα : ∀ᵐ x ∂intervalMeasure, |b x + b (-x)| ≤ 2 * α) :
    ∃ Tinv : IntervalL2 →L[ℂ] IntervalL2,
      Tinv.comp (principalOperator (realIntervalCoefficient a ha)) = 1 ∧
      (principalOperator (realIntervalCoefficient a ha)).comp Tinv = 1 := by
  obtain ⟨Tb, hl, hr, _⟩ := principalOperator_boundedInverse b hb α hα1 hα
  have hleft : ∀ W, Tb (principalOperator (realIntervalCoefficient b hb) W) = W := fun W => by
    simpa using congrArg (fun S : IntervalL2 →L[ℂ] IntervalL2 => S W) hl
  have hright : ∀ W, principalOperator (realIntervalCoefficient b hb) (Tb W) = W := fun W => by
    simpa using congrArg (fun S : IntervalL2 →L[ℂ] IntervalL2 => S W) hr
  have hwr : ∀ᵐ x ∂intervalMeasure, w x * r x = 1 := hrw.mono fun x hx => by rwa [mul_comm]
  have hG := principalOperator_gauge (realIntervalCoefficient a ha)
    (realIntervalCoefficient b hb) r hg
  refine ⟨boundedMultiplier r ∘L Tb ∘L boundedMultiplier w, ?_, ?_⟩
  · ext1 f
    change boundedMultiplier r (Tb (boundedMultiplier w
      (principalOperator (realIntervalCoefficient a ha) f))) = f
    nth_rewrite 1 [← boundedMultiplier_inverse r w hrw f]
    rw [hG, boundedMultiplier_inverse w r hwr, hleft, boundedMultiplier_inverse r w hrw]
  · ext1 f
    change principalOperator (realIntervalCoefficient a ha)
      (boundedMultiplier r (Tb (boundedMultiplier w f))) = f
    rw [hG, hright, boundedMultiplier_inverse r w hrw]

theorem spectralGreen_norm_le_shifted (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1) (hα : ∀ᵐ x ∂intervalMeasure, |b x + b (-x)| ≤ 2 * α)
    (s : ℝ) (hs : 0 < s) (W : IntervalL2) :
    ‖spectralGreen W‖ ≤
      ‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / ((1 - α) ^ 2 * s) *
        ‖shiftedPrincipalOperator (realIntervalCoefficient b hb) s W‖ :=
  resolvent_ray_estimate b hb α hα1 hα s hs _ (spectralGreen W) (spectralGreen_memDirichletH2 W)
    (by rw [variableSobolevOperator_add_smul_eq _ s _ (spectralGreen_memDirichletH2 W),
      spectralGreen_right_inverse])

theorem principalOperator_norm_le_shifted (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1) (hα : ∀ᵐ x ∂intervalMeasure, |b x + b (-x)| ≤ 2 * α)
    (s : ℝ) (hs : 0 < s) (W : IntervalL2) :
    ‖principalOperator (realIntervalCoefficient b hb) W‖ ≤
      (1 + ‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2) *
        ‖shiftedPrincipalOperator (realIntervalCoefficient b hb) s W‖ := by
  have hG := spectralGreen_norm_le_shifted b hb α hα1 hα s hs W
  have hα0 : 0 < 1 - α := by linarith
  set B := realIntervalCoefficient b hb
  have hT : principalOperator B W =
      shiftedPrincipalOperator B s W - (s : ℂ) • spectralGreen W := by
    rw [shiftedPrincipalOperator, add_apply, smul_apply, add_sub_cancel_right]
  have hsG : ‖(s : ℂ) • spectralGreen W‖ ≤
      ‖principalOperator B‖ ^ 2 / (1 - α) ^ 2 * ‖shiftedPrincipalOperator B s W‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    calc
      s * ‖spectralGreen W‖ ≤ s * (‖principalOperator B‖ ^ 2 / ((1 - α) ^ 2 * s) *
          ‖shiftedPrincipalOperator B s W‖) := mul_le_mul_of_nonneg_left hG hs.le
      _ = _ := by field_simp
  rw [hT, add_mul, one_mul]
  exact (norm_sub_le _ _).trans (by linarith)

theorem gaugeLowerOp_norm_sq_le (w r' r'' : IntervalLInfinity) (W : IntervalL2) :
    ‖gaugeLowerOp w r' r'' W‖ ^ 2 ≤
      (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) ^ 2 *
        (‖spectralGreen W‖ * ‖W‖) := by
  have h := gaugeLowerOrder_norm_le w r' r'' (spectralGreen W) (spectralGreen_memDirichletH2 W)
  have hn : ‖secondWeakDeriv (spectralGreen W) (spectralGreen_memDirichletH2 W).1‖ = ‖W‖ := by
    rw [← norm_neg, spectralGreen_right_inverse]
  rw [hn] at h
  rw [gaugeLowerOp_apply]
  calc
    _ ≤ ((2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) *
        Real.sqrt (‖spectralGreen W‖ * ‖W‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]

theorem gaugeLowerOp_neg_secondWeakDeriv (w r' r'' : IntervalLInfinity) (g : IntervalL2)
    (hg : MemDirichletH2 g) :
    gaugeLowerOp w r' r'' (-secondWeakDeriv g hg.1) = gaugeLowerOrder w r' r'' g hg.1 := by
  have key : ∀ (g' : IntervalL2) (hg' : MemDirichletH2 g'), g' = g →
      gaugeLowerOrder w r' r'' g' hg'.1 = gaugeLowerOrder w r' r'' g hg.1 := by
    intro g' hg' h
    subst h
    rfl
  rw [gaugeLowerOp_apply]
  exact key _ (spectralGreen_memDirichletH2 _) (spectralGreen_left_inverse g hg)

/-- Шаг 4 записи C19: при `s ≥ 4 C₂² C₁ (1 + C₁)` калибровочная поправка не больше половины
главной части. -/
theorem gaugeCorrection_norm_le (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1) (hα : ∀ᵐ x ∂intervalMeasure, |b x + b (-x)| ≤ 2 * α)
    (w r' r'' : IntervalLInfinity) (s : ℝ) (hs : 0 < s)
    (hE : 4 * (‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 *
        (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) ^ 2 *
        (‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2 *
          (1 + ‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2)) /
        (1 - α)) ≤ s) (W : IntervalL2) :
    ‖principalOperator (realIntervalCoefficient b hb) (gaugeLowerOp w r' r'' W)‖ ≤
      1 / 2 * ‖shiftedPrincipalOperator (realIntervalCoefficient b hb) s W‖ := by
  have hα0 : 0 < 1 - α := by linarith
  have h1 := spectralGreen_norm_le_shifted b hb α hα1 hα s hs W
  have h2' := principalOperator_norm_le_shifted b hb α hα1 hα s hs W
  have h3 := gaugeLowerOp_norm_sq_le w r' r'' W
  obtain ⟨Tinv, hl, _, hn⟩ := principalOperator_boundedInverse b hb α hα1 hα
  set T := principalOperator (realIntervalCoefficient b hb)
  set c := 2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖ with hc
  set n := ‖shiftedPrincipalOperator (realIntervalCoefficient b hb) s W‖ with hndef
  set C1 := ‖T‖ ^ 2 / (1 - α) ^ 2 with hC1def
  have hn0 : 0 ≤ n := norm_nonneg _
  have hC1 : 0 ≤ C1 := by rw [hC1def]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have h1' : ‖spectralGreen W‖ ≤ C1 / s * n := by
    rwa [hC1def, div_div]
  have h2 : ‖W‖ ≤ (1 - α)⁻¹ * ((1 + C1) * n) := by
    have hW : Tinv (T W) = W := by
      simpa using congrArg (fun S : IntervalL2 →L[ℂ] IntervalL2 => S W) hl
    calc
      ‖W‖ = ‖Tinv (T W)‖ := by rw [hW]
      _ ≤ ‖Tinv‖ * ‖T W‖ := Tinv.le_opNorm _
      _ ≤ (1 - α)⁻¹ * ((1 + C1) * n) := by gcongr
  have hsq : ‖T (gaugeLowerOp w r' r'' W)‖ ^ 2 ≤ (1 / 2 * n) ^ 2 := by
    calc
      ‖T (gaugeLowerOp w r' r'' W)‖ ^ 2 ≤ (‖T‖ * ‖gaugeLowerOp w r' r'' W‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
      _ = ‖T‖ ^ 2 * ‖gaugeLowerOp w r' r'' W‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖T‖ ^ 2 * (c ^ 2 * (C1 / s * n * ((1 - α)⁻¹ * ((1 + C1) * n)))) := by
        gcongr
        exact h3.trans (by gcongr)
      _ = ‖T‖ ^ 2 * c ^ 2 * (C1 * (1 + C1)) / (1 - α) / s * n ^ 2 := by
        field_simp
      _ ≤ 1 / 4 * n ^ 2 :=
        mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ hs]; linarith) (by positivity)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq (by positivity)

/-- Однозначная разрешимость `(T_b + s G + T_b B̃) W = k` и оценка `‖G W‖ ≤ 2 C₁ / s * ‖k‖`. -/
theorem gaugeShiftedOperator_solvable (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1) (hα : ∀ᵐ x ∂intervalMeasure, |b x + b (-x)| ≤ 2 * α)
    (w r' r'' : IntervalLInfinity) (s : ℝ) (hs : 0 < s)
    (hE : 4 * (‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 *
        (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) ^ 2 *
        (‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2 *
          (1 + ‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2)) /
        (1 - α)) ≤ s) (k : IntervalL2) :
    ∃ W : IntervalL2, gaugeShiftedOperator (realIntervalCoefficient b hb) w r' r'' s W = k ∧
      (∀ W' : IntervalL2,
        gaugeShiftedOperator (realIntervalCoefficient b hb) w r' r'' s W' = k → W' = W) ∧
      ‖spectralGreen W‖ ≤
        2 * (‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2 / s) * ‖k‖ := by
  have hhalf := gaugeCorrection_norm_le b hb α hα1 hα w r' r'' s hs hE
  have hgreen := spectralGreen_norm_le_shifted b hb α hα1 hα s hs
  set B := realIntervalCoefficient b hb
  set S0 := shiftedPrincipalOperator B s
  set P : IntervalL2 →L[ℂ] IntervalL2 := principalOperator B ∘L gaugeLowerOp w r' r'' with hP
  have hS : ∀ W, gaugeShiftedOperator B w r' r'' s W = S0 W + P W := fun W => rfl
  obtain ⟨Sinv, hl, hr, _⟩ := exists_inverse_of_coercive S0
    (1 - α) (by linarith) (shiftedPrincipalOperator_re_inner_lower b hb α hα s hs.le)
  have hleft : ∀ W, Sinv (S0 W) = W := fun W => by
    simpa using congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T W) hl
  have hright : ∀ g, S0 (Sinv g) = g := fun g => by
    simpa using congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T g) hr
  have hlow : ∀ W, ‖S0 W‖ ≤ 2 * ‖gaugeShiftedOperator B w r' r'' s W‖ := by
    intro W
    have h1 : ‖S0 W‖ ≤ ‖S0 W + P W‖ + ‖P W‖ := by
      simpa using norm_sub_le (S0 W + P W) (P W)
    have h2 : ‖P W‖ ≤ 1 / 2 * ‖S0 W‖ := hhalf W
    rw [hS]
    linarith
  set K : IntervalL2 →L[ℂ] IntervalL2 := P ∘L Sinv with hK
  have hKn : ‖K‖ ≤ 1 / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => ?_
    have := hhalf (Sinv h)
    rwa [hright] at this
  let U := Units.oneSub (-K) (by rw [norm_neg]; linarith)
  set u : IntervalL2 := (↑U⁻¹ : IntervalL2 →L[ℂ] IntervalL2) k with hu
  have hUu : u + K u = k := by
    have h1 : (↑U : IntervalL2 →L[ℂ] IntervalL2) * ↑U⁻¹ = 1 := U.mul_inv
    have h2 := congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T k) h1
    simpa [U, sub_neg_eq_add] using h2
  refine ⟨Sinv u, ?_, ?_, ?_⟩
  · rw [hS, hright]
    exact hUu
  · intro W' hW'
    have hz : gaugeShiftedOperator B w r' r'' s (W' - Sinv u) = 0 := by
      rw [map_sub, hW', hS, hright]
      change k - (u + K u) = 0
      rw [hUu, sub_self]
    have h0 := hlow (W' - Sinv u)
    rw [hz, norm_zero, mul_zero] at h0
    have h1 : S0 (W' - Sinv u) = 0 := norm_le_zero_iff.mp h0
    have h2 := hleft (W' - Sinv u)
    rw [h1, map_zero] at h2
    exact sub_eq_zero.mp h2.symm
  · have h1 := hgreen (Sinv u)
    have h2 := hlow (Sinv u)
    have h3 : gaugeShiftedOperator B w r' r'' s (Sinv u) = k := by
      rw [hS, hright]
      exact hUu
    rw [h3] at h2
    have hα0 : 0 < 1 - α := by linarith
    calc
      _ ≤ ‖principalOperator B‖ ^ 2 / ((1 - α) ^ 2 * s) * ‖S0 (Sinv u)‖ := h1
      _ ≤ ‖principalOperator B‖ ^ 2 / ((1 - α) ^ 2 * s) * (2 * ‖k‖) := by gcongr
      _ = _ := by rw [div_div]; ring

/-- Формула (7) записи C19 со сдвигом: `(L_a + s)(r g) = r (T_b + s G + T_b B̃)(-g'')`. -/
theorem gauge_shifted_similarity (A B r w r' r'' : IntervalLInfinity)
    (hr : HasACMultiplierDerivative r r') (hr' : HasACMultiplierDerivative r' r'')
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1)
    (hg : ∀ᵐ x ∂intervalMeasure, B x * r x = A x * r (-x)) (s : ℝ)
    (g : IntervalL2) (hgD : MemDirichletH2 g) (hrg : MemDirichletH2 (boundedMultiplier r g)) :
    variableSobolevOperator A (boundedMultiplier r g) hrg.1 + s • boundedMultiplier r g =
      boundedMultiplier r (gaugeShiftedOperator B w r' r'' s (-secondWeakDeriv g hgD.1)) := by
  rw [gauge_similarity A B r w r' r'' hr hr' hrw hg g hgD.1 hrg.1]
  change _ = boundedMultiplier r (shiftedPrincipalOperator B s (-secondWeakDeriv g hgD.1) +
    principalOperator B (gaugeLowerOp w r' r'' (-secondWeakDeriv g hgD.1)))
  rw [← variableSobolevOperator_add_smul_eq B s g hgD,
    gaugeLowerOp_neg_secondWeakDeriv w r' r'' g hgD,
    map_add, map_add, map_add, ContinuousLinearMap.map_smul_of_tower]
  abel

/-- **Утверждение 1 записи C19.** Пусть `a`, `b ∈ L∞` вещественны, веса `r`, `w ∈ W²∞`
взаимно обратны, `b(x) r(x) = a(x) r(-x)` и `|b(x) + b(-x)| ≤ 2α < 2` почти всюду. Тогда
существуют `C > 0` и `s₀ > 0`, для которых при `s ≥ s₀` уравнение `(L_a + s) f = h` имеет
единственное решение на слабой области Дирихле и `‖f‖ ≤ C / s * ‖h‖`. -/
theorem gauge_resolvent_ray_estimate (a b : ℝ → ℝ)
    (ha : MemLp a ∞ intervalMeasure) (hb : MemLp b ∞ intervalMeasure)
    (r w : IntervalLInfinity)
    (hr : MemIntervalW2Infinity r) (hw : MemIntervalW2Infinity w)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1)
    (hg : ∀ᵐ x ∂intervalMeasure,
      realIntervalCoefficient b hb x * r x = realIntervalCoefficient a ha x * r (-x))
    (α : ℝ) (hα1 : α < 1) (hα : ∀ᵐ x ∂intervalMeasure, |b x + b (-x)| ≤ 2 * α) :
    ∃ C s₀ : ℝ, 0 < C ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s → ∀ h : IntervalL2,
      (∃! f : IntervalL2, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 + s • f = h) ∧
      ∀ (f : IntervalL2) (hf : MemDirichletH2 f),
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 + s • f = h →
        ‖f‖ ≤ C / s * ‖h‖ := by
  have hwr : ∀ᵐ x ∂intervalMeasure, w x * r x = 1 := hrw.mono fun x hx => by rwa [mul_comm]
  have hDr : ∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f :=
    memDirichletH2_mul_iff r w hr hw hrw
  have hDw : ∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier w f) ↔ MemDirichletH2 f :=
    memDirichletH2_mul_iff w r hw hr hwr
  obtain ⟨r', r'', hr0, hr1⟩ := hr
  have hr' := HasACMultiplierDerivative.of_weak hr0
  have hr'' := HasACMultiplierDerivative.of_weak hr1
  have hα0 : 0 < 1 - α := by linarith
  set A := realIntervalCoefficient a ha
  set C1 := ‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 / (1 - α) ^ 2 with hC1def
  have hC1 : 0 ≤ C1 := by rw [hC1def]; positivity
  set E := ‖principalOperator (realIntervalCoefficient b hb)‖ ^ 2 *
    (2 * (‖w‖ * ‖r'‖) + ‖w‖ * ‖r''‖ * Real.sqrt ‖spectralGreen‖) ^ 2 * (C1 * (1 + C1)) /
      (1 - α) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  refine ⟨2 * (‖r‖ * ‖w‖ * C1) + 1, 4 * E + 1, by positivity, by positivity, fun s hs h => ?_⟩
  have hs0 : 0 < s := by linarith
  obtain ⟨W, hW, huniq, hbound⟩ := gaugeShiftedOperator_solvable b hb α hα1 hα w r' r'' s hs0
    (by linarith) (boundedMultiplier w h)
  set B := realIntervalCoefficient b hb
  have hsim := gauge_shifted_similarity A B r w r' r'' hr' hr'' hrw hg s
  have key : ∀ (f : IntervalL2) (hf : MemDirichletH2 f),
      variableSobolevOperator A f hf.1 + s • f = h →
      f = boundedMultiplier r (spectralGreen W) := by
    intro f hf heq
    have hgD : MemDirichletH2 (boundedMultiplier w f) := (hDw f).2 hf
    have hfg : boundedMultiplier r (boundedMultiplier w f) = f :=
      boundedMultiplier_inverse r w hrw f
    have htr : ∀ (f' : IntervalL2) (hf' : MemDirichletH2 f'), f' = f →
        variableSobolevOperator A f' hf'.1 + s • f' = h := by
      intro f' hf' hff
      subst hff
      exact heq
    have h1 := htr _ ((hDr _).2 hgD) hfg
    rw [hsim _ hgD ((hDr _).2 hgD)] at h1
    have h2 := congrArg (boundedMultiplier w) h1
    rw [boundedMultiplier_inverse w r hwr] at h2
    have h3 := huniq _ h2
    rw [← hfg, ← h3, spectralGreen_left_inverse _ hgD]
  have hf0 : MemDirichletH2 (boundedMultiplier r (spectralGreen W)) :=
    (hDr _).2 (spectralGreen_memDirichletH2 W)
  refine ⟨⟨boundedMultiplier r (spectralGreen W), ⟨hf0, ?_⟩, ?_⟩, ?_⟩
  · rw [hsim _ (spectralGreen_memDirichletH2 W) hf0, spectralGreen_right_inverse, hW,
      boundedMultiplier_inverse r w hrw]
  · rintro f ⟨hf, heq⟩
    exact key f hf heq
  · intro f hf heq
    rw [key f hf heq]
    have hwh := boundedMultiplier_norm_le w h
    have hC1s : 0 ≤ C1 / s := by positivity
    calc
      ‖boundedMultiplier r (spectralGreen W)‖ ≤ ‖r‖ * ‖spectralGreen W‖ :=
        boundedMultiplier_norm_le r _
      _ ≤ ‖r‖ * (2 * (C1 / s) * (‖w‖ * ‖h‖)) := by
        gcongr
        exact hbound.trans (by gcongr)
      _ = 2 * (‖r‖ * ‖w‖ * C1) / s * ‖h‖ := by ring
      _ ≤ (2 * (‖r‖ * ‖w‖ * C1) + 1) / s * ‖h‖ := by
        gcongr
        linarith

end Involution
