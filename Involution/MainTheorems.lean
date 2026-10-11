module

public import Involution.ACSpectral
public import Involution.GaugeSimilarity
public import Involution.SobolevModes

/-! Сводка условий на коэффициент.
* Весь класс `|a(x) a(-x)| ≤ κ < 1`: компактный обратный и альтернатива Фредгольма
  (`productBound_compact_inverse`, `productBound_fredholm`).
* Чётный `a`: обычный базис Рисса собственных функций без присоединённых
  (`evenCoefficient_riesz_eigenbasis`, `evenCoefficient_noJordan`).
* Знакопостоянный `a ∈ W²∞`: подобие оператору `L_b + B` с чётным `b` и возмущением,
  подчинённым с показателем `1/2` (ниже). Базис со скобками при малой производной
  коэффициента доказан в `SignDefiniteBrackets.lean` (`signDefinite_bracket_basis`),
  при близости к чётному — в `NearlyEvenBrackets.lean` (`nearlyEven_bracket_basis`).
  Без условия малости вывод получен из теоремы Маркуса–Мацаева в
  `GeneralBrackets.lean` (`signDefinite_bracket_basis_W2`). -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Модель случая C6: `L_a` подобен `L_b + B`, где `L_b` имеет базис Рисса собственных
функций без присоединённых, а `B` подчинён `L_b` с показателем `1/2`. -/
theorem signDefinite_perturbed_riesz_model (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha)) :
    ∃ (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (r w : IntervalLInfinity)
      (B : ∀ f : IntervalL2, MemDirichletH2 f → IntervalL2) (C : ℝ),
      (∀ᵐ x ∂intervalMeasure, r x * w x = 1) ∧
      (∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f) ∧
      (∀ (f : IntervalL2) (hf : MemDirichletH2 f)
        (hrf : MemDirichletH2 (boundedMultiplier r f)),
        variableSobolevOperator (realIntervalCoefficient a ha) (boundedMultiplier r f) hrf.1 =
          boundedMultiplier r
            (variableSobolevOperator (realIntervalCoefficient b hb) f hf.1 + B f hf)) ∧
      (∀ (f : IntervalL2) (hf : MemDirichletH2 f), ‖B f hf‖ ≤
        C * Real.sqrt (‖f‖ * ‖variableSobolevOperator (realIntervalCoefficient b hb) f hf.1‖)) ∧
      (∃ (ι : Type) (e : RieszBasis ι IntervalL2), ∀ i : ι,
        ∃ hf : MemDirichletH2 (e.vector i), ∃ lam : ℂ,
          variableSobolevOperator (realIntervalCoefficient b hb) (e.vector i) hf.1 =
            lam • e.vector i) ∧
      (∀ (f g : IntervalL2) (hf : MemDirichletH2 f) (hg : MemDirichletH2 g) (lam : ℂ),
        variableSobolevOperator (realIntervalCoefficient b hb) f hf.1 = lam • f →
        variableSobolevOperator (realIntervalCoefficient b hb) g hg.1 = lam • g + f → f = 0) := by
  obtain ⟨b, hb, r, w, B, C, hbeven, hbprod, hrw, hdom, hsim, hsub⟩ :=
    signDefinite_gauge_reduction a ha m M kappa hm hlower hupper hkappa1 hproduct hreg
  have heven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x := Filter.Eventually.of_forall hbeven
  exact ⟨b, hb, r, w, B, C, hrw, hdom, hsim, hsub,
    evenCoefficient_riesz_eigenbasis b hb kappa hkappa hkappa1 heven hbprod,
    fun f g hf hg lam he hj =>
      evenCoefficient_noJordan b hb kappa hkappa hkappa1 heven hbprod f g hf hg lam he hj⟩

/-- Граница условия `κ < 1`: при `a ≡ 1` каждая синусная мода лежит в ядре, так что
ядро бесконечномерно. Обратного оператора из `productBound_compact_inverse` при `κ = 1`
нет, и собственное подпространство нуля не конечномерно. Базисность этим не опровергается. -/
theorem unit_coefficient_sine_kernel (n : ℕ) (hn : 0 < n) :
    MemDirichletH2 (sineWaveL2 ((n : ℝ) * Real.pi)) ∧ sineWaveL2 ((n : ℝ) * Real.pi) ≠ 0 ∧
      constantSobolevOperator 1 (sineWaveL2 ((n : ℝ) * Real.pi))
        (sineWave_memIntervalH2 ((n : ℝ) * Real.pi)) = 0 := by
  refine ⟨sineMode_memDirichletH2 n, sineModeL2_ne_zero n hn, ?_⟩
  rw [sineWaveL2_eigen_equation 1 ((n : ℝ) * Real.pi)]
  simp

end Involution
