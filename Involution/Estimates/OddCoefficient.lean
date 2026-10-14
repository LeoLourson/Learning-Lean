module

public import Involution.Model.ParityDomain
public import Involution.Model.CompactInverse

/-! Нечётный коэффициент: поворот по чётности `U = P₊ + i P₋` унитарен и переводит
`L_a` в `(1 + i a) (-D²)`. Оценка произведения `a(x) a(-x)` здесь не используется. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Involution

/-- Поворот по чётности `U = P₊ + i P₋`. -/
def parityRotation : IntervalL2 →L[ℂ] IntervalL2 :=
  evenProjection + Complex.I • oddProjection

/-- Обратный поворот `P₊ - i P₋`. -/
def parityRotationInv : IntervalL2 →L[ℂ] IntervalL2 :=
  evenProjection - Complex.I • oddProjection

theorem parityRotation_apply (f : IntervalL2) :
    parityRotation f = l2EvenPart f + Complex.I • l2OddPart f := rfl

theorem parityRotationInv_apply (f : IntervalL2) :
    parityRotationInv f = l2EvenPart f - Complex.I • l2OddPart f := rfl

theorem parityRotation_eq (f : IntervalL2) :
    parityRotation f =
      ((1 + Complex.I) / 2) • f + ((1 - Complex.I) / 2) • l2Reflect f := by
  rw [parityRotation_apply, l2EvenPart, l2OddPart]
  module

theorem parityRotationInv_eq (f : IntervalL2) :
    parityRotationInv f =
      ((1 - Complex.I) / 2) • f + ((1 + Complex.I) / 2) • l2Reflect f := by
  rw [parityRotationInv_apply, l2EvenPart, l2OddPart]
  module

private theorem rotation_coeff_mul :
    (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1 / 2 := by
  linear_combination (-1 / 4 : ℂ) * Complex.I_mul_I

private theorem rotation_coeff_sq_add :
    (1 + Complex.I) / 2 * ((1 + Complex.I) / 2) +
      (1 - Complex.I) / 2 * ((1 - Complex.I) / 2) = 0 := by
  linear_combination (1 / 2 : ℂ) * Complex.I_mul_I

theorem parityRotationInv_parityRotation (f : IntervalL2) :
    parityRotationInv (parityRotation f) = f := by
  have h1 := rotation_coeff_mul
  have h2 := rotation_coeff_sq_add
  simp only [parityRotation_eq, parityRotationInv_eq, map_add, map_smul, l2Reflect_involution]
  match_scalars
  · linear_combination 2 * h1
  · linear_combination h2

theorem parityRotation_parityRotationInv (f : IntervalL2) :
    parityRotation (parityRotationInv f) = f := by
  have h1 := rotation_coeff_mul
  have h2 := rotation_coeff_sq_add
  simp only [parityRotation_eq, parityRotationInv_eq, map_add, map_smul, l2Reflect_involution]
  match_scalars
  · linear_combination 2 * h1
  · linear_combination h2

theorem parityRotation_injective : Function.Injective parityRotation :=
  Function.LeftInverse.injective parityRotationInv_parityRotation

/-- Поворот по чётности сохраняет норму `L₂`. -/
theorem parityRotation_norm (f : IntervalL2) : ‖parityRotation f‖ = ‖f‖ := by
  have ho : ⟪l2EvenPart f, Complex.I • l2OddPart f⟫_ℂ = 0 := by
    rw [inner_smul_right, l2EvenPart_orthogonal_l2OddPart, mul_zero]
  have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (l2EvenPart_orthogonal_l2OddPart f f)
  rw [l2EvenPart_add_l2OddPart] at h2
  rw [← parityRotation_apply, norm_smul, Complex.norm_I, one_mul, ← h2] at h1
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h1

/-- Умножение на нечётный коэффициент антикоммутирует с отражением. -/
theorem boundedMultiplier_reflect_odd (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = -w x) (f : IntervalL2) :
    boundedMultiplier w (l2Reflect f) = -l2Reflect (boundedMultiplier w f) := by
  apply Lp.ext
  have hm := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (boundedMultiplier_ae w f)
  filter_upwards [boundedMultiplier_ae w (l2Reflect f), l2Reflect_ae f,
    l2Reflect_ae (boundedMultiplier w f), hm, hw,
    Lp.coeFn_neg (l2Reflect (boundedMultiplier w f))] with x hmf hrf hrm hmneg hx hneg
  change boundedMultiplier w f (-x) = w (-x) * f (-x) at hmneg
  rw [hneg, Pi.neg_apply, hmf, hrf, hrm, hmneg, hx, neg_mul, neg_neg]

/-- `U (I + a R) = (1 + i a) U` для нечётного `a`. -/
theorem parityRotation_principalOperator (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, a (-x) = -a x) (g : IntervalL2) :
    parityRotation (principalOperator a g) =
      parityRotation g + Complex.I • boundedMultiplier a (parityRotation g) := by
  have hR : l2Reflect (boundedMultiplier a (l2Reflect g)) = -boundedMultiplier a g := by
    have h := boundedMultiplier_reflect_odd a ha (l2Reflect g)
    rw [l2Reflect_involution] at h
    rw [h, neg_neg]
  have h1 : Complex.I * ((1 + Complex.I) / 2) = -((1 - Complex.I) / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
  have h2 : Complex.I * ((1 - Complex.I) / 2) = (1 + Complex.I) / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  have hP : principalOperator a g = g + boundedMultiplier a (l2Reflect g) := rfl
  simp only [parityRotation_eq, hP, map_add, map_smul, hR, smul_add, smul_smul, h1, h2]
  module

theorem memIntervalH2_parityRotation {f : IntervalL2} (hf : MemIntervalH2 f) :
    MemIntervalH2 (parityRotation f) := by
  rw [parityRotation_eq]
  have h1 := firstWeakDeriv_spec f hf
  have h2 := secondWeakDeriv_spec f hf
  have h2r : HasL2WeakDeriv (-l2Reflect (firstWeakDeriv f hf))
      (l2Reflect (secondWeakDeriv f hf)) := by
    simpa only [neg_neg] using h2.reflect.neg
  exact ⟨_, _, (h1.smul _).add (h1.reflect.smul _), (h2.smul _).add (h2r.smul _)⟩

theorem memDirichletH2_parityRotation {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemDirichletH2 (parityRotation f) := by
  rw [parityRotation_eq]
  exact (hf.smul _).add (hf.reflect.smul _)

/-- Поворот по чётности коммутирует со второй слабой производной. -/
theorem secondWeakDeriv_parityRotation (f : IntervalL2) (hf : MemIntervalH2 f) :
    secondWeakDeriv (parityRotation f) (memIntervalH2_parityRotation hf) =
      parityRotation (secondWeakDeriv f hf) := by
  have h1 := firstWeakDeriv_spec f hf
  have h2 := secondWeakDeriv_spec f hf
  have h2r : HasL2WeakDeriv (-l2Reflect (firstWeakDeriv f hf))
      (l2Reflect (secondWeakDeriv f hf)) := by
    simpa only [neg_neg] using h2.reflect.neg
  have key : ∀ (u : IntervalL2) (hu : MemIntervalH2 u),
      u = ((1 + Complex.I) / 2) • f + ((1 - Complex.I) / 2) • l2Reflect f →
      secondWeakDeriv u hu = ((1 + Complex.I) / 2) • secondWeakDeriv f hf +
        ((1 - Complex.I) / 2) • l2Reflect (secondWeakDeriv f hf) := by
    rintro u hu rfl
    exact (weakDerivatives_eq _ hu ((h1.smul _).add (h1.reflect.smul _))
      ((h2.smul _).add (h2r.smul _))).2
  rw [key _ _ (parityRotation_eq f), parityRotation_eq]

/-- **Нечётный коэффициент.** `U L_a f = (1 + i a) (-(U f)'')`. -/
theorem oddCoefficient_unitary_multiplication (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, a (-x) = -a x) (f : IntervalL2) (hf : MemIntervalH2 f) :
    parityRotation (variableSobolevOperator a f hf) =
      -secondWeakDeriv (parityRotation f) (memIntervalH2_parityRotation hf) +
        Complex.I • boundedMultiplier a
          (-secondWeakDeriv (parityRotation f) (memIntervalH2_parityRotation hf)) := by
  rw [variableSobolevOperator_eq_principal, parityRotation_principalOperator a ha,
    secondWeakDeriv_parityRotation, map_neg]

/-- Уравнение `L_a f = λ f` равносильно уравнению `(1 + i a) (-Z'') = λ Z` для `Z = U f`. -/
theorem oddCoefficient_eigen_iff (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, a (-x) = -a x) (f : IntervalL2) (hf : MemIntervalH2 f)
    (lam : ℂ) :
    variableSobolevOperator a f hf = lam • f ↔
      -secondWeakDeriv (parityRotation f) (memIntervalH2_parityRotation hf) +
        Complex.I • boundedMultiplier a
          (-secondWeakDeriv (parityRotation f) (memIntervalH2_parityRotation hf)) =
        lam • parityRotation f := by
  rw [← oddCoefficient_unitary_multiplication a ha f hf, ← map_smul]
  exact parityRotation_injective.eq_iff.symm

end Involution
