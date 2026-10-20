module

public import Involution.Estimates.EigenvalueSector

/-! Лемма записи C21 (оценка на лучах). Для вещественного `a ∈ L∞` с
`|a(x) + a(-x)| ≤ 2α`, `α < 1`, и `|a(x) - a(-x)| ≤ 2β` почти всюду, при
`0 < δ ≤ π/2` и `arctan (β / (1 - α)) + δ ≤ |arg λ|` всякое решение `f` из слабой области
Дирихле уравнения `(L_a - λ) f = g` удовлетворяет

`|λ| ‖f‖ ≤ (‖T_a‖ / ((1 - α) sin δ) + 1) ‖g‖`.

Число `arctan (β / (1 - α))` равно `πτ/2` записи C21. При `λ ≠ 0` оценка даёт
единственность решения. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Involution

/-- Если `δ ≤ |χ| ≤ 2π - δ` и `0 ≤ δ ≤ π`, то `cos χ ≤ cos δ`. -/
theorem cos_le_cos_of_abs_mem (χ δ : ℝ) (hδ0 : 0 ≤ δ)
    (h1 : δ ≤ |χ|) (h2 : |χ| ≤ 2 * Real.pi - δ) : Real.cos χ ≤ Real.cos δ := by
  rw [← Real.cos_abs χ]
  rcases le_or_gt |χ| Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 h h1
  · have : Real.cos |χ| = Real.cos (2 * Real.pi - |χ|) := by
      rw [Real.cos_two_pi_sub]
    rw [this]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 (by linarith) (by linarith)

/-- Расстояние от точки `z` до луча `{E λ : E ≥ 0}`: если косинус угла между ними не больше
`cos δ`, то `‖z‖ sin δ ≤ ‖z - E λ‖`. -/
theorem norm_mul_sin_le_norm_sub_ray (z lam : ℂ) (E δ : ℝ) (hE : 0 ≤ E) (hs : 0 ≤ Real.sin δ)
    (hc : Real.cos (lam.arg - z.arg) ≤ Real.cos δ) :
    ‖z‖ * Real.sin δ ≤ ‖z - (E : ℂ) * lam‖ := by
  set ρ := ‖z‖
  set s := E * ‖lam‖
  have hs0 : 0 ≤ s := mul_nonneg hE (norm_nonneg _)
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hre : (z - (E : ℂ) * lam).re = ρ * Real.cos z.arg - s * Real.cos lam.arg := by
    simp only [Complex.sub_re, Complex.re_ofReal_mul, ρ, s, Complex.norm_mul_cos_arg]
    rw [mul_assoc, Complex.norm_mul_cos_arg]
  have him : (z - (E : ℂ) * lam).im = ρ * Real.sin z.arg - s * Real.sin lam.arg := by
    simp only [Complex.sub_im, Complex.im_ofReal_mul, ρ, s, Complex.norm_mul_sin_arg]
    rw [mul_assoc, Complex.norm_mul_sin_arg]
  have hsq : ‖z - (E : ℂ) * lam‖ ^ 2 =
      ρ ^ 2 + s ^ 2 - 2 * ρ * s * Real.cos (lam.arg - z.arg) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← pow_two, ← pow_two, hre, him,
      Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq z.arg, Real.sin_sq_add_cos_sq lam.arg]
  set c := Real.cos (lam.arg - z.arg)
  have hδ : Real.sin δ ^ 2 = 1 - Real.cos δ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq δ]
  have key : (ρ * Real.sin δ) ^ 2 ≤ ‖z - (E : ℂ) * lam‖ ^ 2 := by
    rw [hsq, mul_pow, hδ]
    rcases le_or_gt c 0 with hc0 | hc0
    · nlinarith [mul_nonneg (mul_nonneg hρ hs0) (neg_nonneg.mpr hc0), sq_nonneg (Real.cos δ)]
    · have : c ^ 2 ≤ Real.cos δ ^ 2 := pow_le_pow_left₀ hc0.le hc 2
      nlinarith [sq_nonneg (s - ρ * c), sq_nonneg ρ]
  exact (pow_le_pow_iff_left₀ (mul_nonneg hρ hs) (norm_nonneg _) two_ne_zero).1 key

/-- Аргумент точки сектора `Re z > 0`, `|Im z| ≤ c Re z` не превосходит `arctan c`. -/
theorem abs_arg_le_arctan (z : ℂ) (c : ℝ) (hre : 0 < z.re) (him : |z.im| ≤ c * z.re) :
    |z.arg| ≤ Real.arctan c := by
  have harg : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  have hz : z.arg = Real.arctan (z.im / z.re) := by
    rw [← Complex.tan_arg, Real.arctan_tan (by linarith [neg_abs_le z.arg]) (by
      linarith [le_abs_self z.arg])]
  have ht : |z.im / z.re| ≤ c := by
    rw [abs_div, abs_of_pos hre, div_le_iff₀ hre]
    exact him
  rw [hz, abs_le]
  constructor
  · rw [← Real.arctan_neg]
    exact Real.arctan_strictMono.monotone (neg_le.1 ((neg_abs_le _).trans' (neg_le_neg ht)) |>
      fun h => by linarith [neg_abs_le (z.im / z.re)])
  · exact Real.arctan_strictMono.monotone ((le_abs_self _).trans ht)

/-- **Оценка на лучах (лемма записи C21).** Пусть `a` вещественна, `|a(x) + a(-x)| ≤ 2α`
с `α < 1` и `|a(x) - a(-x)| ≤ 2β` почти всюду, `0 < δ ≤ π/2` и
`arctan (β / (1 - α)) + δ ≤ |arg λ|`. Тогда всякое решение `f` из слабой области Дирихле
уравнения `(L_a - λ) f = g` удовлетворяет `|λ| ‖f‖ ≤ (‖T_a‖ / ((1 - α) sin δ) + 1) ‖g‖`. -/
theorem resolvent_sector_ray_estimate (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, star (a x) = a x) (α β : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, ‖a x + a (-x)‖ ≤ 2 * α)
    (hβ : ∀ᵐ x ∂intervalMeasure, ‖a x - a (-x)‖ ≤ 2 * β)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ Real.pi / 2)
    (lam : ℂ) (hlam : Real.arctan (β / (1 - α)) + δ ≤ |lam.arg|)
    (f g : IntervalL2) (hf : MemDirichletH2 f)
    (heq : variableSobolevOperator a f hf.1 - lam • f = g) :
    ‖lam‖ * ‖f‖ ≤ (‖principalOperator a‖ / ((1 - α) * Real.sin δ) + 1) * ‖g‖ := by
  set W : IntervalL2 := -secondWeakDeriv f hf.1 with hW
  set X : ℂ := ⟪W, reflectedMultiplier a W⟫_ℂ with hX
  have hα0 : 0 < 1 - α := by linarith
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith [Real.pi_pos])
  have hTW : principalOperator a W = W + reflectedMultiplier a W := rfl
  have hL : W + reflectedMultiplier a W - lam • f = g := by
    rw [← heq, variableSobolevOperator_eq_principal, hTW]
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
  set E : ℝ := ‖firstWeakDeriv f hf.1‖ ^ 2 with hEdef
  have hE : ⟪W, f⟫_ℂ = (E : ℂ) := by
    rw [← inner_conj_symm, hW, negativeSecondWeakDeriv_energy f f hf hf.1,
      inner_self_eq_norm_sq_to_K, map_pow, RCLike.conj_ofReal, hEdef]
    norm_cast
  set z : ℂ := ((‖W‖ ^ 2 : ℝ) : ℂ) + X with hz
  have hmain : z - (E : ℂ) * lam = ⟪W, g⟫_ℂ := by
    have h := congrArg (fun u : IntervalL2 => ⟪W, u⟫_ℂ) hL
    simp only [inner_sub_right, inner_add_right, inner_smul_right, hE,
      inner_self_eq_norm_sq_to_K] at h
    rw [← h, hz, hX, Complex.ofReal_pow, mul_comm]
    rfl
  have hzre : z.re = ‖W‖ ^ 2 + X.re := by
    rw [hz, Complex.add_re, Complex.ofReal_re]
  have hzim : z.im = X.im := by
    rw [hz, Complex.add_im, Complex.ofReal_im, zero_add]
  -- `(1 - α) sin δ ‖W‖² ≤ ‖W‖ ‖g‖`
  have hWg : (1 - α) * Real.sin δ * ‖W‖ ^ 2 ≤ ‖W‖ * ‖g‖ := by
    rcases (norm_nonneg W).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    have hN : 0 < ‖W‖ ^ 2 := by positivity
    have hlow : (1 - α) * ‖W‖ ^ 2 ≤ z.re := by
      rw [hzre]
      linarith [neg_abs_le X.re]
    have hzpos : 0 < z.re := lt_of_lt_of_le (by positivity) hlow
    have hβ0 : 0 ≤ β := by
      by_contra hb
      linarith [abs_nonneg X.im, mul_neg_of_neg_of_pos (not_le.1 hb) hN]
    have hzim' : |z.im| ≤ β / (1 - α) * z.re := by
      rw [hzim, div_mul_eq_mul_div, le_div_iff₀ hα0]
      nlinarith
    have harg := abs_arg_le_arctan z _ hzpos hzim'
    have hat := Real.arctan_lt_pi_div_two (β / (1 - α))
    have hcos : Real.cos (lam.arg - z.arg) ≤ Real.cos δ := by
      apply cos_le_cos_of_abs_mem _ _ hδ0.le
      · have := abs_sub_abs_le_abs_sub lam.arg z.arg
        linarith
      · have := abs_sub lam.arg z.arg
        linarith [Complex.abs_arg_le_pi lam]
    have hray := norm_mul_sin_le_norm_sub_ray z lam E δ (by positivity) hsin.le hcos
    rw [hmain] at hray
    have hzn : (1 - α) * ‖W‖ ^ 2 ≤ ‖z‖ := hlow.trans (Complex.re_le_norm z)
    calc (1 - α) * Real.sin δ * ‖W‖ ^ 2 = (1 - α) * ‖W‖ ^ 2 * Real.sin δ := by ring
      _ ≤ ‖z‖ * Real.sin δ := by gcongr
      _ ≤ ‖⟪W, g⟫_ℂ‖ := hray
      _ ≤ ‖W‖ * ‖g‖ := norm_inner_le_norm _ _
  have hk : 0 < (1 - α) * Real.sin δ := mul_pos hα0 hsin
  have hWle : ‖W‖ ≤ ‖g‖ / ((1 - α) * Real.sin δ) := by
    rw [le_div_iff₀ hk]
    rcases (norm_nonneg W).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    nlinarith
  have hlf : lam • f = principalOperator a W - g := by
    rw [hTW, ← hL]
    abel
  calc ‖lam‖ * ‖f‖ = ‖lam • f‖ := (norm_smul lam f).symm
    _ ≤ ‖principalOperator a W‖ + ‖g‖ := by rw [hlf]; exact norm_sub_le _ _
    _ ≤ ‖principalOperator a‖ * (‖g‖ / ((1 - α) * Real.sin δ)) + ‖g‖ := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    _ = (‖principalOperator a‖ / ((1 - α) * Real.sin δ) + 1) * ‖g‖ := by ring

end Involution
