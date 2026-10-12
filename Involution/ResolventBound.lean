module

public import Involution.ResolventAux

/-! Утверждение 2 записи C17: при вещественном коэффициенте `a ∈ L∞` с `|a_e| ≤ α < 1`,
где `a_e(x) = (a(x) + a(-x))/2`, главный множитель `T_a = I + aR` ограниченно обратим,
`‖T_a⁻¹‖ ≤ (1 - α)⁻¹`, а решение уравнения `(L_a + s) f = h`, `s > 0`, на слабой области
Дирихле удовлетворяет оценке

`‖f‖ ≤ ‖T_a‖² / ((1 - α)² s) * ‖h‖`.

Равномерная по `s ≥ 0` оценка `‖f‖ ≤ ‖spectralGreen‖ / (1 - α) * ‖h‖` и однозначная
разрешимость — `resolvent_estimate_corrected` в `ResolventAux`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Главный множитель `T_a = I + aR` ограниченно обратим, `‖T_a⁻¹‖ ≤ (1 - α)⁻¹`. -/
theorem principalOperator_boundedInverse (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α) :
    ∃ Tinv : IntervalL2 →L[ℂ] IntervalL2,
      Tinv.comp (principalOperator (realIntervalCoefficient a ha)) = 1 ∧
      (principalOperator (realIntervalCoefficient a ha)).comp Tinv = 1 ∧
      ‖Tinv‖ ≤ (1 - α)⁻¹ :=
  exists_inverse_of_coercive _ (1 - α) (by linarith) (principalOperator_re_inner_lower a ha α hα)

/-- **Убывание резольвенты на отрицательной полуоси.** Если `(L_a + s) f = h`, `s > 0`, то
`‖f‖ ≤ ‖T_a‖² / ((1 - α)² s) * ‖h‖`. Доказательство: `W + s T_a⁻¹ f = T_a⁻¹ h` при
`W = -f''`, `Re ⟪f, W⟫ ≥ 0`, а `T_a⁻¹` коэрцитивен вместе с `T_a`. -/
theorem resolvent_ray_estimate (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (α : ℝ) (hα1 : α < 1)
    (hα : ∀ᵐ x ∂intervalMeasure, |a x + a (-x)| ≤ 2 * α)
    (s : ℝ) (hs : 0 < s) (h f : IntervalL2) (hf : MemDirichletH2 f)
    (heq : variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 + s • f = h) :
    ‖f‖ ≤ ‖principalOperator (realIntervalCoefficient a ha)‖ ^ 2 / ((1 - α) ^ 2 * s) * ‖h‖ := by
  set T := principalOperator (realIntervalCoefficient a ha) with hT
  obtain ⟨Tinv, hl, hr, hn⟩ := principalOperator_boundedInverse a ha α hα1 hα
  have hleft : ∀ W, Tinv (T W) = W := fun W => by
    simpa using congrArg (fun S : IntervalL2 →L[ℂ] IntervalL2 => S W) hl
  have hright : ∀ g, T (Tinv g) = g := fun g => by
    simpa using congrArg (fun S : IntervalL2 →L[ℂ] IntervalL2 => S g) hr
  have hα0 : 0 < 1 - α := by linarith
  set W := -secondWeakDeriv f hf.1 with hW
  set u := Tinv f with hu
  -- `W + s u = T⁻¹ h`
  have h1 : W + (s : ℂ) • u = Tinv h := by
    rw [← heq, variableSobolevOperator_eq_principal, RCLike.real_smul_eq_coe_smul (K := ℂ),
      map_add, hleft, map_smul]
    rfl
  -- `Re ⟪f, W⟫ ≥ 0`
  have hfW : 0 ≤ (inner ℂ f W).re := by
    rw [hW, negativeSecondWeakDeriv_energy f f hf hf.1]
    exact inner_self_nonneg (𝕜 := ℂ)
  -- `(1 - α) ‖u‖² ≤ Re ⟪f, u⟫`
  have hfu : (1 - α) * ‖u‖ ^ 2 ≤ (inner ℂ f u).re := by
    have := principalOperator_re_inner_lower a ha α hα u
    rw [← hT, hu, hright, ← hu, ← inner_conj_symm, Complex.conj_re] at this
    exact this
  have hsum : (inner ℂ f W).re + s * (inner ℂ f u).re = (inner ℂ f (Tinv h)).re := by
    rw [← h1, inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have hup : (inner ℂ f (Tinv h)).re ≤ ‖f‖ * ((1 - α)⁻¹ * ‖h‖) :=
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((Tinv.le_opNorm h).trans (by gcongr)) (norm_nonneg _)))
  have hfT : ‖f‖ ≤ ‖T‖ * ‖u‖ := by
    have := T.le_opNorm u
    rwa [hu, hright] at this
  -- `s (1 - α) ‖u‖² ≤ ‖f‖ ‖h‖ / (1 - α)`
  have hmain : s * ((1 - α) * ‖u‖ ^ 2) ≤ ‖f‖ * ((1 - α)⁻¹ * ‖h‖) := by nlinarith
  rcases (norm_nonneg f).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  have hsq : ‖f‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖u‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg f) hfT 2
  have hden : 0 < (1 - α) ^ 2 * s := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  have hkey : ‖f‖ ^ 2 * ((1 - α) ^ 2 * s) ≤ ‖T‖ ^ 2 * ‖h‖ * ‖f‖ := by
    calc ‖f‖ ^ 2 * ((1 - α) ^ 2 * s)
        ≤ ‖T‖ ^ 2 * ‖u‖ ^ 2 * ((1 - α) ^ 2 * s) := by gcongr
      _ = ‖T‖ ^ 2 * (1 - α) * (s * ((1 - α) * ‖u‖ ^ 2)) := by ring
      _ ≤ ‖T‖ ^ 2 * (1 - α) * (‖f‖ * ((1 - α)⁻¹ * ‖h‖)) := by gcongr
      _ = ‖T‖ ^ 2 * ‖h‖ * ‖f‖ := by field_simp
  exact le_of_mul_le_mul_right (by nlinarith) hpos

end Involution
