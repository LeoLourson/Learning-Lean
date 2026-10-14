module

public import Involution.Model.WeightedEigenbasis

/-! Положительные веса каналов из исходной оценки произведения и чётности.
Соболевская гладкость a здесь не нужна: достаточно вещественного класса L∞. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem evenCoefficient_abs_bound (a : ℝ → ℝ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∀ᵐ x ∂intervalMeasure, |a x| ≤ Real.sqrt kappa := by
  filter_upwards [heven, hproduct] with x he hp
  rw [he, ← sq, abs_sq] at hp
  apply (Real.le_sqrt (abs_nonneg _) hkappa).mpr
  simpa only [sq_abs] using hp

theorem evenCoefficient_channel_bounds (a : ℝ → ℝ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (t : ℝ) (ht : |t| = 1) :
    ∀ᵐ x ∂intervalMeasure, 1 - Real.sqrt kappa ≤ 1 + t * a x ∧
      1 + t * a x ≤ 1 + Real.sqrt kappa := by
  filter_upwards [evenCoefficient_abs_bound a kappa hkappa heven hproduct] with x hx
  have hta : |t * a x| ≤ Real.sqrt kappa := by simpa only [abs_mul, ht, one_mul] using hx
  obtain ⟨hl, hr⟩ := abs_le.mp hta
  constructor <;> linarith

theorem channelCoefficient_memLp (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure) (t : ℝ) :
    MemLp (fun x => 1 + t * a x) ∞ intervalMeasure := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1))
    infer_instance
  exact (memLp_const (1 : ℝ)).add (ha.const_mul t)

theorem evenCoefficient_channel_weights (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (t : ℝ) (ht : |t| = 1) :
    ∃ v w : IntervalLInfinity,
      (∀ᵐ x ∂intervalMeasure, v (-x) = v x) ∧
      (∀ᵐ x ∂intervalMeasure, w (-x) = w x) ∧
      (∀ᵐ x ∂intervalMeasure, star (w x) = w x) ∧
      (∀ᵐ x ∂intervalMeasure, v x * w x = 1) ∧
      (∀ᵐ x ∂intervalMeasure, (1 + (t : ℂ) * realIntervalCoefficient a ha x) *
        (w x * w x) = 1) := by
  let p : ℝ → ℝ := fun x => 1 + t * a x
  have hp : MemLp p ∞ intervalMeasure := channelCoefficient_memLp a ha t
  have hm : 0 < 1 - Real.sqrt kappa := by
    have hs : Real.sqrt kappa < 1 := by
      exact (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
    linarith
  have hb := evenCoefficient_channel_bounds a kappa hkappa heven hproduct t ht
  have hl : ∀ᵐ x ∂intervalMeasure, 1 - Real.sqrt kappa ≤ p x := hb.mono fun _ h => h.1
  have hu : ∀ᵐ x ∂intervalMeasure, p x ≤ 1 + Real.sqrt kappa := hb.mono fun _ h => h.2
  have hep : ∀ᵐ x ∂intervalMeasure, p (-x) = p x := heven.mono fun x hx => by
    dsimp [p]
    rw [hx]
  have hc : ∀ᵐ x ∂intervalMeasure, (p x : ℂ) =
      1 + (t : ℂ) * realIntervalCoefficient a ha x := by
    filter_upwards [realIntervalCoefficient_ae a ha] with x hx
    rw [hx]
    simp only [p, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  refine ⟨sqrtWeight p hp (1 + Real.sqrt kappa) hu,
    inverseSqrtWeight p hp (1 - Real.sqrt kappa) hm hl,
    sqrtWeight_even p hp _ hu hep, inverseSqrtWeight_even p hp _ hm hl hep,
    inverseSqrtWeight_real p hp _ hm hl, sqrtWeight_inverseSqrtWeight p hp _ _ hm hl hu, ?_⟩
  exact inverseSqrtWeight_channel_identity (realIntervalCoefficient a ha) (t : ℂ) p hp _ hm hl hc

theorem evenCoefficient_channel_riesz_eigenbasis (a : ℝ → ℝ)
    (ha : MemLp a ∞ intervalMeasure) (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (t : ℝ) (ht : |t| = 1) :
    ∃ (ι : Type) (b : RieszBasis ι (ParityL2 (t : ℂ))), ∀ i : ι,
      ∃ hf : MemDirichletH2 (b.vector i : IntervalL2), ∃ lam : ℂ,
        variableSobolevOperator (realIntervalCoefficient a ha) (b.vector i : IntervalL2) hf.1 =
          lam • (b.vector i : IntervalL2) := by
  obtain ⟨v, w, hv, hw, hr, hvw, hinv⟩ :=
    evenCoefficient_channel_weights a ha kappa hkappa hkappa1 heven hproduct t ht
  refine ⟨CompactEigenbasisIndex (weightedParityGreen w hw (t : ℂ)),
    weightedSpectralRieszBasis v w hv hw hr hvw (t : ℂ), ?_⟩
  intro i
  exact ⟨weightedSpectralRieszBasis_memDirichletH2 v w hv hw hr hvw (t : ℂ) i, i.1⁻¹,
    weightedSpectralRieszBasis_eigen_equation (realIntervalCoefficient a ha)
      v w hv hw hr hvw (t : ℂ) hinv i⟩

end Involution
