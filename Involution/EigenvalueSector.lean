module

public import Involution.OddCoefficient
public import Involution.RampSpectrum

/-! Сектор собственных значений. Для вещественного `a ∈ L∞` с
`|a(x) + a(-x)| ≤ 2α`, `α < 1`, и `|a(x) - a(-x)| ≤ 2β` каждое собственное значение `L_a`
на слабой области Дирихле удовлетворяет `Re λ > 0` и `(1 - α) |Im λ| ≤ β Re λ`.
Оценка произведения `a(x) a(-x)` и гладкость коэффициента не используются. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Involution

/-- `(a R + R a) g = (a(x) + a(-x)) g(-x)`. -/
theorem reflectedMultiplier_add_adjoint_ae (a : IntervalLInfinity) (g : IntervalL2) :
    reflectedMultiplier a g + l2Reflect (boundedMultiplier a g) =ᵐ[intervalMeasure]
      fun x => (a x + a (-x)) * g (-x) := by
  have hmn : ∀ᵐ x ∂intervalMeasure, boundedMultiplier a g (-x) = a (-x) * g (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (boundedMultiplier_ae a g)] with x hx
    exact hx
  filter_upwards [Lp.coeFn_add (reflectedMultiplier a g) (l2Reflect (boundedMultiplier a g)),
    reflectedMultiplier_ae a g, l2Reflect_ae (boundedMultiplier a g), hmn] with x hadd hr hl hm
  rw [hadd, Pi.add_apply, hr, hl, hm]
  ring

/-- `(a R - R a) g = (a(x) - a(-x)) g(-x)`. -/
theorem reflectedMultiplier_sub_adjoint_ae (a : IntervalLInfinity) (g : IntervalL2) :
    reflectedMultiplier a g - l2Reflect (boundedMultiplier a g) =ᵐ[intervalMeasure]
      fun x => (a x - a (-x)) * g (-x) := by
  have hmn : ∀ᵐ x ∂intervalMeasure, boundedMultiplier a g (-x) = a (-x) * g (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (boundedMultiplier_ae a g)] with x hx
    exact hx
  filter_upwards [Lp.coeFn_sub (reflectedMultiplier a g) (l2Reflect (boundedMultiplier a g)),
    reflectedMultiplier_ae a g, l2Reflect_ae (boundedMultiplier a g), hmn] with x hsub hr hl hm
  rw [hsub, Pi.sub_apply, hr, hl, hm]
  ring

theorem reflectedMultiplier_add_adjoint_norm_le (a : IntervalLInfinity) (c : ℝ)
    (h : ∀ᵐ x ∂intervalMeasure, ‖a x + a (-x)‖ ≤ c) (g : IntervalL2) :
    ‖reflectedMultiplier a g + l2Reflect (boundedMultiplier a g)‖ ≤ c * ‖g‖ := by
  rw [← l2Reflect.norm_map g]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [reflectedMultiplier_add_adjoint_ae a g, l2Reflect_ae g, h] with x hx hr hc
  rw [hx, hr, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem reflectedMultiplier_sub_adjoint_norm_le (a : IntervalLInfinity) (c : ℝ)
    (h : ∀ᵐ x ∂intervalMeasure, ‖a x - a (-x)‖ ≤ c) (g : IntervalL2) :
    ‖reflectedMultiplier a g - l2Reflect (boundedMultiplier a g)‖ ≤ c * ‖g‖ := by
  rw [← l2Reflect.norm_map g]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [reflectedMultiplier_sub_adjoint_ae a g, l2Reflect_ae g, h] with x hx hr hc
  rw [hx, hr, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- Сопряжённый к `a R` при вещественном `a` — оператор `R a`. -/
theorem inner_reflectedMultiplier_left (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, star (a x) = a x) (f g : IntervalL2) :
    ⟪reflectedMultiplier a f, g⟫_ℂ = ⟪f, l2Reflect (boundedMultiplier a g)⟫_ℂ := by
  calc
    ⟪boundedMultiplier a (l2Reflect f), g⟫_ℂ = ⟪l2Reflect f, boundedMultiplier a g⟫_ℂ :=
      boundedMultiplier_symmetric a ha _ _
    _ = ⟪l2Reflect (l2Reflect f), l2Reflect (boundedMultiplier a g)⟫_ℂ :=
      (l2Reflect.inner_map_map _ _).symm
    _ = _ := by rw [l2Reflect_involution]

/-- **Сектор собственных значений.** Если `a` вещественна, `|a(x) + a(-x)| ≤ 2α` с `α < 1`
и `|a(x) - a(-x)| ≤ 2β` почти всюду, то собственное значение `λ` оператора `L_a`
удовлетворяет `Re λ > 0` и `(1 - α) |Im λ| ≤ β Re λ`. -/
theorem eigenvalue_sector (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, star (a x) = a x) (α β : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, ‖a x + a (-x)‖ ≤ 2 * α)
    (hβ : ∀ᵐ x ∂intervalMeasure, ‖a x - a (-x)‖ ≤ 2 * β)
    (f : IntervalL2) (hf : MemDirichletH2 f) (hne : f ≠ 0) (lam : ℂ)
    (he : variableSobolevOperator a f hf.1 = lam • f) :
    0 < lam.re ∧ (1 - α) * |lam.im| ≤ β * lam.re := by
  set W : IntervalL2 := -secondWeakDeriv f hf.1 with hW
  set g : IntervalL2 := firstWeakDeriv f hf.1 with hg
  set X : ℂ := ⟪W, reflectedMultiplier a W⟫_ℂ with hX
  have hL : W + reflectedMultiplier a W = lam • f := by
    rw [← he, variableSobolevOperator_eq_principal]
    rfl
  have hconj : (starRingEnd ℂ) X = ⟪W, l2Reflect (boundedMultiplier a W)⟫_ℂ := by
    rw [hX, inner_conj_symm]
    exact inner_reflectedMultiplier_left a ha W W
  have hre : |X.re| ≤ α * ‖W‖ ^ 2 := by
    have h1 : ‖X + (starRingEnd ℂ) X‖ ≤ ‖W‖ * (2 * α * ‖W‖) := by
      rw [hconj, hX, ← inner_add_right]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (reflectedMultiplier_add_adjoint_norm_le a _ hα W) (norm_nonneg _))
    have h2 : (X + (starRingEnd ℂ) X).re = 2 * X.re := by
      rw [Complex.add_re, Complex.conj_re]
      ring
    have h3 := Complex.abs_re_le_norm (X + (starRingEnd ℂ) X)
    rw [h2, abs_mul, abs_two] at h3
    nlinarith
  have him : |X.im| ≤ β * ‖W‖ ^ 2 := by
    have h1 : ‖X - (starRingEnd ℂ) X‖ ≤ ‖W‖ * (2 * β * ‖W‖) := by
      rw [hconj, hX, ← inner_sub_right]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (reflectedMultiplier_sub_adjoint_norm_le a _ hβ W) (norm_nonneg _))
    have h2 : (X - (starRingEnd ℂ) X).im = 2 * X.im := by
      rw [Complex.sub_im, Complex.conj_im]
      ring
    have h3 := Complex.abs_im_le_norm (X - (starRingEnd ℂ) X)
    rw [h2, abs_mul, abs_two] at h3
    nlinarith
  have hE : ⟪W, f⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hW, negativeSecondWeakDeriv_energy f f hf hf.1,
      inner_self_eq_norm_sq_to_K, ← hg]
    rw [map_pow, RCLike.conj_ofReal]
    norm_cast
  have hmain : ((‖W‖ ^ 2 : ℝ) : ℂ) + X = lam * ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    have h := congrArg (fun u : IntervalL2 => ⟪W, u⟫_ℂ) hL
    simp only [inner_add_right, inner_smul_right, hE, inner_self_eq_norm_sq_to_K] at h
    rw [← h]
    push_cast
    rfl
  have hreq : ‖W‖ ^ 2 + X.re = lam.re * ‖g‖ ^ 2 := by
    have h := congrArg Complex.re hmain
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
      sub_zero] using h
  have himq : X.im = lam.im * ‖g‖ ^ 2 := by
    have h := congrArg Complex.im hmain
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero,
      zero_add, add_zero] using h
  have hgpos : 0 < ‖g‖ ^ 2 := by
    have hg0 : g ≠ 0 := fun h => hne (dirichlet_eq_zero_of_firstWeakDeriv_eq_zero f hf h)
    positivity
  have hWpos : 0 < ‖W‖ ^ 2 := by
    have hW0 : W ≠ 0 := fun h =>
      hne (dirichlet_eq_zero_of_secondWeakDeriv_eq_zero f hf (neg_eq_zero.mp h))
    positivity
  have hlow : (1 - α) * ‖W‖ ^ 2 ≤ lam.re * ‖g‖ ^ 2 := by
    have := (abs_le.mp hre).1
    linarith
  have hrepos : 0 < lam.re * ‖g‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos (by linarith) hWpos) hlow
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    have : β * ‖W‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hWpos
    linarith [abs_nonneg X.im]
  refine ⟨(pos_iff_pos_of_mul_pos hrepos).mpr hgpos, ?_⟩
  apply le_of_mul_le_mul_right _ hgpos
  have habs : |lam.im| * ‖g‖ ^ 2 = |X.im| := by
    rw [himq, abs_mul, abs_of_pos hgpos]
  calc
    (1 - α) * |lam.im| * ‖g‖ ^ 2 = (1 - α) * |X.im| := by rw [mul_assoc, habs]
    _ ≤ (1 - α) * (β * ‖W‖ ^ 2) := mul_le_mul_of_nonneg_left him (by linarith)
    _ = β * ((1 - α) * ‖W‖ ^ 2) := by ring
    _ ≤ β * (lam.re * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_left hlow hβ0
    _ = β * lam.re * ‖g‖ ^ 2 := by ring

/-- Нечётный вещественный коэффициент с `|a| ≤ β`: `Re λ > 0` и `|Im λ| ≤ β Re λ`.
Оценка `|a(x) a(-x)| < 1` не нужна. -/
theorem oddCoefficient_eigenvalue_sector (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, star (a x) = a x)
    (hodd : ∀ᵐ x ∂intervalMeasure, a (-x) = -a x) (β : ℝ)
    (hβ : ∀ᵐ x ∂intervalMeasure, ‖a x‖ ≤ β)
    (f : IntervalL2) (hf : MemDirichletH2 f) (hne : f ≠ 0) (lam : ℂ)
    (he : variableSobolevOperator a f hf.1 = lam • f) :
    0 < lam.re ∧ |lam.im| ≤ β * lam.re := by
  have h := eigenvalue_sector a ha 0 β zero_lt_one
    (by
      filter_upwards [hodd] with x hx
      rw [hx, add_neg_cancel, norm_zero, mul_zero])
    (by
      filter_upwards [hodd, hβ] with x hx hb
      rw [hx, sub_neg_eq_add, ← two_mul, norm_mul, Complex.norm_ofNat]
      linarith)
    f hf hne lam he
  simpa only [sub_zero, one_mul] using h

/-- Чётный вещественный коэффициент с `|a| ≤ α < 1`: собственные значения вещественны и
положительны. -/
theorem evenCoefficient_eigenvalue_real (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, star (a x) = a x)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) (α : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, ‖a x‖ ≤ α)
    (f : IntervalL2) (hf : MemDirichletH2 f) (hne : f ≠ 0) (lam : ℂ)
    (he : variableSobolevOperator a f hf.1 = lam • f) :
    0 < lam.re ∧ lam.im = 0 := by
  have h := eigenvalue_sector a ha α 0 hα1
    (by
      filter_upwards [heven, hα] with x hx hb
      rw [hx, ← two_mul, norm_mul, Complex.norm_ofNat]
      linarith)
    (by
      filter_upwards [heven] with x hx
      rw [hx, sub_self, norm_zero, mul_zero])
    f hf hne lam he
  refine ⟨h.1, ?_⟩
  have h2 : (1 - α) * |lam.im| ≤ 0 := by simpa only [zero_mul] using h.2
  have h3 : |lam.im| ≤ 0 := by
    by_contra hpos
    have := mul_pos (by linarith : 0 < 1 - α) (not_le.mp hpos)
    linarith
  exact abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _))

/-- Коэффициент `a(x) = max(x, 0)` из C12: собственные значения лежат в секторе
`|Im λ| ≤ Re λ`. -/
theorem ramp_eigenvalue_sector (f : IntervalL2) (hf : MemDirichletH2 f) (hne : f ≠ 0)
    (lam : ℂ) (he : variableSobolevOperator rampClass f hf.1 = lam • f) :
    0 < lam.re ∧ |lam.im| ≤ lam.re := by
  have hax := realIntervalCoefficient_ae rampCoefficient rampCoefficient_memLp
  have han : ∀ᵐ x ∂intervalMeasure, rampClass (-x) = ((rampCoefficient (-x) : ℝ) : ℂ) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hax] with x hx
    exact hx
  have hsum : ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
      |rampCoefficient x + rampCoefficient (-x)| ≤ 1 ∧
        |rampCoefficient x - rampCoefficient (-x)| ≤ 1 := by
    intro x hx
    rcases le_total 0 x with h0 | h0
    · rw [rampCoefficient_of_nonneg h0, rampCoefficient_of_nonpos (by linarith : -x ≤ 0),
        add_zero, sub_zero, abs_of_nonneg h0]
      exact ⟨hx.2.le, hx.2.le⟩
    · rw [rampCoefficient_of_nonpos h0, rampCoefficient_of_nonneg (by linarith : 0 ≤ -x),
        zero_add, zero_sub, neg_neg, abs_neg, abs_of_nonpos h0]
      exact ⟨by linarith [hx.1], by linarith [hx.1]⟩
  have h := eigenvalue_sector rampClass
    (realIntervalCoefficient_real rampCoefficient rampCoefficient_memLp) (1 / 2) (1 / 2)
    (by norm_num)
    (by
      filter_upwards [hax, han, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
      have h1' : rampClass x = ((rampCoefficient x : ℝ) : ℂ) := h1
      rw [h1', h2, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
      linarith [(hsum x hx).1])
    (by
      filter_upwards [hax, han, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
      have h1' : rampClass x = ((rampCoefficient x : ℝ) : ℂ) := h1
      rw [h1', h2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      linarith [(hsum x hx).2])
    f hf hne lam he
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  linarith

end Involution
