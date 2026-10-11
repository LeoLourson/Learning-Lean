module

public import Involution.EvenEigenbasis
public import Involution.WeightedSymmetry
public import Involution.ParityDomain

/-! Исключение нетривиальных жордановых цепочек для чётного коэффициента.
Если (L-λ)f=0 и (L-λ)g=f на слабой области Дирихле, то f=0. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem realIntervalCoefficient_even (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x) :
    ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient a ha (-x) = realIntervalCoefficient a ha x := by
  have href := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (realIntervalCoefficient_ae a ha)
  filter_upwards [realIntervalCoefficient_ae a ha, href, heven] with x hx hr he
  change realIntervalCoefficient a ha (-x) = (a (-x) : ℂ) at hr
  rw [hr, hx, he]

theorem evenCoefficient_noJordan (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (f g : IntervalL2) (hf : MemDirichletH2 f) (hg : MemDirichletH2 g) (lam : ℂ)
    (he : variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 = lam • f)
    (hj : variableSobolevOperator (realIntervalCoefficient a ha) g hg.1 = lam • g + f) : f = 0 := by
  let A := realIntervalCoefficient a ha
  have hA := realIntervalCoefficient_even a ha heven
  have heE : variableSobolevOperator A (l2EvenPart f) hf.evenPart.1 = lam • l2EvenPart f := by
    calc
      _ = evenProjection (variableSobolevOperator A f hf.1) :=
        variableSobolevOperator_evenPart A hA f hf
      _ = _ := by rw [he, map_smul, evenProjection_apply]
  have hjE : variableSobolevOperator A (l2EvenPart g) hg.evenPart.1 =
      lam • l2EvenPart g + l2EvenPart f := by
    calc
      _ = evenProjection (variableSobolevOperator A g hg.1) :=
        variableSobolevOperator_evenPart A hA g hg
      _ = _ := by rw [hj, map_add, map_smul, evenProjection_apply, evenProjection_apply]
  have heO : variableSobolevOperator A (l2OddPart f) hf.oddPart.1 = lam • l2OddPart f := by
    calc
      _ = oddProjection (variableSobolevOperator A f hf.1) :=
        variableSobolevOperator_oddPart A hA f hf
      _ = _ := by rw [he, map_smul, oddProjection_apply]
  have hjO : variableSobolevOperator A (l2OddPart g) hg.oddPart.1 =
      lam • l2OddPart g + l2OddPart f := by
    calc
      _ = oddProjection (variableSobolevOperator A g hg.1) :=
        variableSobolevOperator_oddPart A hA g hg
      _ = _ := by rw [hj, map_add, map_smul, oddProjection_apply, oddProjection_apply]
  obtain ⟨ve, we, _, _, hre, hive, hpe⟩ :=
    evenCoefficient_channel_weights a ha kappa hkappa hkappa1 heven hproduct 1 (by norm_num)
  obtain ⟨vo, wo, _, _, hro, hivo, hpo⟩ :=
    evenCoefficient_channel_weights a ha kappa hkappa hkappa1 heven hproduct (-1) (by norm_num)
  simp only [Complex.ofReal_one] at hpe
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hpo
  have hfe : l2EvenPart f = 0 := weighted_channel_noJordan A we 1 lam hre hpe
    (reciprocalWeight_nonzero ve we hive) _ _ hf.evenPart hg.evenPart
    (by simpa only [one_smul] using l2EvenPart_fixed f)
    (by simpa only [one_smul] using l2EvenPart_fixed g) heE hjE
  have hfo : l2OddPart f = 0 := weighted_channel_noJordan A wo (-1) lam hro hpo
    (reciprocalWeight_nonzero vo wo hivo) _ _ hf.oddPart hg.oddPart
    (by simpa only [neg_one_smul] using l2OddPart_neg f)
    (by simpa only [neg_one_smul] using l2OddPart_neg g) heO hjO
  calc
    f = l2EvenPart f + l2OddPart f := (l2EvenPart_add_l2OddPart f).symm
    _ = 0 := by rw [hfe, hfo, add_zero]

end Involution
