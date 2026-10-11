module

public import Involution.ACDomain
public import Involution.EvenNoJordan

/-! Спектральные результаты чётного случая на области абсолютно непрерывных
представителей. Утверждения переносятся через доказанную эквивалентность областей. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem evenCoefficient_AC_riesz_eigenbasis (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ (ι : Type) (b : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemACDirichletH2 (b.vector i), ∃ lam : ℂ,
        variableSobolevOperator (realIntervalCoefficient a ha) (b.vector i) hf.weakRealization.1 =
          lam • b.vector i := by
  obtain ⟨ι, b, hb⟩ := evenCoefficient_riesz_eigenbasis a ha kappa hkappa hkappa1 heven hproduct
  refine ⟨ι, b, ?_⟩
  intro i
  obtain ⟨hf, lam, he⟩ := hb i
  exact ⟨hf.acRealization, lam, he⟩

theorem evenCoefficient_AC_noJordan (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (f g : IntervalL2) (hf : MemACDirichletH2 f) (hg : MemACDirichletH2 g) (lam : ℂ)
    (he : variableSobolevOperator (realIntervalCoefficient a ha) f hf.weakRealization.1 = lam • f)
    (hj : variableSobolevOperator (realIntervalCoefficient a ha) g hg.weakRealization.1 =
      lam • g + f) : f = 0 :=
  evenCoefficient_noJordan a ha kappa hkappa hkappa1 heven hproduct
    f g hf.weakRealization hg.weakRealization lam he hj

end Involution
