module

public import Involution.Model.ParityMultiplier
public import Involution.Model.ScalarDomain

/-! Проекции чётности сохраняют слабую область Дирихле.
При чётном коэффициенте они коммутируют с исходным оператором на этой области. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

theorem MemDirichletH2.evenPart {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemDirichletH2 (l2EvenPart f) := (hf.add hf.reflect).smul (2 : ℂ)⁻¹

theorem MemDirichletH2.oddPart {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemDirichletH2 (l2OddPart f) := (hf.sub hf.reflect).smul (2 : ℂ)⁻¹

theorem variableSobolevOperator_reflect (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) (f : IntervalL2) (hf : MemIntervalH2 f) :
    variableSobolevOperator a (l2Reflect f) hf.reflect =
      l2Reflect (variableSobolevOperator a f hf) := by
  simp only [variableSobolevOperator, secondWeakDeriv_reflect f hf, map_sub, map_neg,
    ← boundedMultiplier_reflect a ha, l2Reflect_involution]

theorem variableSobolevOperator_evenPart (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) (f : IntervalL2) (hf : MemDirichletH2 f) :
    variableSobolevOperator a (l2EvenPart f) hf.evenPart.1 =
      l2EvenPart (variableSobolevOperator a f hf.1) := by
  calc
    _ = (2 : ℂ)⁻¹ • variableSobolevOperator a (f + l2Reflect f) (hf.add hf.reflect).1 :=
      variableSobolevOperator_smul a _ _ _ _
    _ = (2 : ℂ)⁻¹ • (variableSobolevOperator a f hf.1 +
        variableSobolevOperator a (l2Reflect f) hf.reflect.1) :=
      congrArg (fun z => (2 : ℂ)⁻¹ • z) (variableSobolevOperator_add a _ _ _ _ _)
    _ = (2 : ℂ)⁻¹ • (variableSobolevOperator a f hf.1 +
        l2Reflect (variableSobolevOperator a f hf.1)) :=
      congrArg (fun z => (2 : ℂ)⁻¹ • (variableSobolevOperator a f hf.1 + z))
        (variableSobolevOperator_reflect a ha f hf.1)
    _ = _ := rfl

theorem variableSobolevOperator_oddPart (a : IntervalLInfinity)
    (ha : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) (f : IntervalL2) (hf : MemDirichletH2 f) :
    variableSobolevOperator a (l2OddPart f) hf.oddPart.1 =
      l2OddPart (variableSobolevOperator a f hf.1) := by
  have hsub : variableSobolevOperator a (f - l2Reflect f) (hf.sub hf.reflect).1 =
      variableSobolevOperator a f hf.1 -
        variableSobolevOperator a (l2Reflect f) hf.reflect.1 := by
    simp only [variableSobolevOperator, secondWeakDeriv_sub f (l2Reflect f) hf.1 hf.reflect.1,
      map_sub, neg_sub]
    abel
  calc
    _ = (2 : ℂ)⁻¹ • variableSobolevOperator a (f - l2Reflect f) (hf.sub hf.reflect).1 :=
      variableSobolevOperator_smul a _ _ _ _
    _ = (2 : ℂ)⁻¹ • (variableSobolevOperator a f hf.1 -
        variableSobolevOperator a (l2Reflect f) hf.reflect.1) :=
      congrArg (fun z => (2 : ℂ)⁻¹ • z) hsub
    _ = (2 : ℂ)⁻¹ • (variableSobolevOperator a f hf.1 -
        l2Reflect (variableSobolevOperator a f hf.1)) :=
      congrArg (fun z => (2 : ℂ)⁻¹ • (variableSobolevOperator a f hf.1 - z))
        (variableSobolevOperator_reflect a ha f hf.1)
    _ = _ := rfl

end Involution
