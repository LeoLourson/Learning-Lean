module

public import Involution.Model.ParityBasis

/-! Разные ограниченные веса в двух каналах отражения.
Прямой и обратный операторы задаются на всём L₂ через ограниченные проекции. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

def evenProjection : IntervalL2 →L[ℂ] IntervalL2 :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ IntervalL2 + l2Reflect.toContinuousLinearMap)

def oddProjection : IntervalL2 →L[ℂ] IntervalL2 :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ IntervalL2 - l2Reflect.toContinuousLinearMap)

theorem evenProjection_apply (f : IntervalL2) : evenProjection f = l2EvenPart f := rfl
theorem oddProjection_apply (f : IntervalL2) : oddProjection f = l2OddPart f := rfl

def parityMultiplierSum (ve vo : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  (boundedMultiplier ve).comp evenProjection + (boundedMultiplier vo).comp oddProjection

theorem parityMultiplierSum_apply (ve vo : IntervalLInfinity) (f : IntervalL2) :
    parityMultiplierSum ve vo f = boundedMultiplier ve (l2EvenPart f) +
      boundedMultiplier vo (l2OddPart f) := rfl

theorem parityMultiplierSum_parts (ve vo : IntervalLInfinity)
    (he : ∀ᵐ x ∂intervalMeasure, ve (-x) = ve x)
    (ho : ∀ᵐ x ∂intervalMeasure, vo (-x) = vo x) (f : IntervalL2) :
    l2EvenPart (parityMultiplierSum ve vo f) = boundedMultiplier ve (l2EvenPart f) ∧
    l2OddPart (parityMultiplierSum ve vo f) = boundedMultiplier vo (l2OddPart f) := by
  have h := l2Parity_unique (parityMultiplierSum ve vo f)
    (boundedMultiplier ve (l2EvenPart f)) (boundedMultiplier vo (l2OddPart f))
    (by rw [← boundedMultiplier_reflect ve he, l2EvenPart_fixed])
    (by rw [← boundedMultiplier_reflect vo ho, l2OddPart_neg, map_neg])
    (parityMultiplierSum_apply ve vo f)
  exact ⟨h.1.symm, h.2.symm⟩

theorem parityMultiplierSum_inverse (ve vo we wo : IntervalLInfinity)
    (he : ∀ᵐ x ∂intervalMeasure, ve (-x) = ve x)
    (ho : ∀ᵐ x ∂intervalMeasure, vo (-x) = vo x)
    (hre : ∀ᵐ x ∂intervalMeasure, we x * ve x = 1)
    (hro : ∀ᵐ x ∂intervalMeasure, wo x * vo x = 1) (f : IntervalL2) :
    parityMultiplierSum we wo (parityMultiplierSum ve vo f) = f := by
  rw [parityMultiplierSum_apply, (parityMultiplierSum_parts ve vo he ho f).1,
    (parityMultiplierSum_parts ve vo he ho f).2,
    boundedMultiplier_inverse we ve hre, boundedMultiplier_inverse wo vo hro,
    l2EvenPart_add_l2OddPart]

def parityMultiplierEquiv (ve vo we wo : IntervalLInfinity)
    (he : ∀ᵐ x ∂intervalMeasure, ve (-x) = ve x)
    (ho : ∀ᵐ x ∂intervalMeasure, vo (-x) = vo x)
    (hwe : ∀ᵐ x ∂intervalMeasure, we (-x) = we x)
    (hwo : ∀ᵐ x ∂intervalMeasure, wo (-x) = wo x)
    (hre : ∀ᵐ x ∂intervalMeasure, ve x * we x = 1)
    (hro : ∀ᵐ x ∂intervalMeasure, vo x * wo x = 1) : IntervalL2 ≃L[ℂ] IntervalL2 :=
  ContinuousLinearEquiv.equivOfInverse (parityMultiplierSum ve vo) (parityMultiplierSum we wo)
    (parityMultiplierSum_inverse ve vo we wo he ho
      (hre.mono fun _ hx => by rwa [mul_comm]) (hro.mono fun _ hx => by rwa [mul_comm]))
    (parityMultiplierSum_inverse we wo ve vo hwe hwo hre hro)

theorem l2EvenPart_of_even (f : IntervalL2) (hf : l2Reflect f = f) :
    l2EvenPart f = f ∧ l2OddPart f = 0 := by
  have h := l2Parity_unique f f 0 hf (by simp) (by simp)
  exact ⟨h.1.symm, h.2.symm⟩

theorem l2OddPart_of_odd (f : IntervalL2) (hf : l2Reflect f = -f) :
    l2EvenPart f = 0 ∧ l2OddPart f = f := by
  have h := l2Parity_unique f 0 f (by simp) hf (by simp)
  exact ⟨h.1.symm, h.2.symm⟩

theorem parityMultiplierSum_even (ve vo : IntervalLInfinity) (f : ParityL2 1) :
    parityMultiplierSum ve vo (f : IntervalL2) = boundedMultiplier ve f := by
  rw [parityMultiplierSum_apply, (l2EvenPart_of_even f (parityL2_even f)).1,
    (l2EvenPart_of_even f (parityL2_even f)).2, map_zero, add_zero]

theorem parityMultiplierSum_odd (ve vo : IntervalLInfinity) (f : ParityL2 (-1)) :
    parityMultiplierSum ve vo (f : IntervalL2) = boundedMultiplier vo f := by
  rw [parityMultiplierSum_apply, (l2OddPart_of_odd f (parityL2_odd f)).1,
    (l2OddPart_of_odd f (parityL2_odd f)).2, map_zero, zero_add]

end Involution
