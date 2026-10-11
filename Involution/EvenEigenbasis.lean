module

public import Involution.EvenCoefficient
public import Involution.ParityMultiplier

/-! Базис Рисса собственных функций на всём L₂ для чётного коэффициента.
Два канала объединяются обратимым ограниченным отображением; совпадения
собственных значений каналов не требуют скобок. Область — слабая область проекта. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem evenCoefficient_riesz_eigenbasis (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ (ι : Type) (b : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemDirichletH2 (b.vector i), ∃ lam : ℂ,
        variableSobolevOperator (realIntervalCoefficient a ha) (b.vector i) hf.1 =
          lam • b.vector i := by
  obtain ⟨ve, we, hve, hwe, hre, hive, hpe⟩ :=
    evenCoefficient_channel_weights a ha kappa hkappa hkappa1 heven hproduct 1 (by norm_num)
  obtain ⟨vo, wo, hvo, hwo, hro, hivo, hpo⟩ :=
    evenCoefficient_channel_weights a ha kappa hkappa hkappa1 heven hproduct (-1) (by norm_num)
  simp only [Complex.ofReal_one] at hpe
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hpo
  let be := weightedChannelEigenbasis we hwe hre 1
  let bo := weightedChannelEigenbasis wo hwo hro (-1)
  let T := parityMultiplierEquiv ve vo we wo hve hvo hwe hwo hive hivo
  let b := rieszBasisOfHilbertBasis (parityHilbertBasis be bo) T
  refine ⟨CompactEigenbasisIndex (weightedParityGreen we hwe 1) ⊕
    CompactEigenbasisIndex (weightedParityGreen wo hwo (-1)), b, ?_⟩
  intro i
  cases i with
  | inl i =>
    have hbi : b.vector (Sum.inl i) = boundedMultiplier ve (be i) := by
      rw [rieszBasisOfHilbertBasis_vector, parityHilbertBasis_apply]
      exact parityMultiplierSum_even ve vo (be i)
    rw [hbi]
    exact ⟨weightedSpectralRieszBasis_memDirichletH2 ve we hve hwe hre hive 1 i, i.1⁻¹,
      weightedSpectralRieszBasis_eigen_equation (realIntervalCoefficient a ha)
        ve we hve hwe hre hive 1 hpe i⟩
  | inr i =>
    have hbi : b.vector (Sum.inr i) = boundedMultiplier vo (bo i) := by
      rw [rieszBasisOfHilbertBasis_vector, parityHilbertBasis_apply]
      exact parityMultiplierSum_odd ve vo (bo i)
    rw [hbi]
    exact ⟨weightedSpectralRieszBasis_memDirichletH2 vo wo hvo hwo hro hivo (-1) i, i.1⁻¹,
      weightedSpectralRieszBasis_eigen_equation (realIntervalCoefficient a ha)
        vo wo hvo hwo hro hivo (-1) hpo i⟩

end Involution
