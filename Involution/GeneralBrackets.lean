module

public import Involution.BracketCorollaries
public import Involution.MarkusMatsaev

/-! Знакопостоянный коэффициент класса `W²∞` без условия малости (утверждение C6).

`MarkusMatsaevStatement` — формулировка теоремы о возмущениях порядка `1/2` без
условия малости (Wyss, arXiv:0906.2631v1, теорема 6.1, в диагональной форме). От
`exists_bracket_basis_of_subordinate` она отличается только отсутствием условия
`160 b₁ c₂ < 1`. Редукция `signDefinite_bracket_basis_general` принимает её как явную
гипотезу; сама теорема доказана в `MarkusMatsaev.lean` и модулях `MM*`
(`markusMatsaevStatement`), что даёт безусловные теоремы
`signDefinite_bracket_basis_W2` и `signDefinite_bracket_rootVectors_W2`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Формулировка теоремы Маркуса–Мацаева для возмущений порядка `1/2` диагонального
оператора с линейной оценкой счётной функции частот. Доказательство —
`markusMatsaevStatement`. -/
def MarkusMatsaevStatement : Prop :=
  ∀ (ι H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (lam : ι → ℝ), (∀ i, 0 < lam i) →
    ∀ K₀ B : H →L[ℂ] H, (∀ i, K₀ (b i) = (((lam i)⁻¹ : ℝ) : ℂ) • b i) →
    ∀ c₂ C₀ b₁ b₀ : ℝ, 0 < c₂ → 0 ≤ C₀ → 0 ≤ b₁ → 0 ≤ b₀ →
    (∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t ^ 2) →
      (s.card : ℝ) ≤ c₂ * t + C₀) →
    (∀ g : H, ‖B g‖ ≤ b₁ * Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) + b₀ * ‖K₀ g‖) →
    ∃ V : ℕ → Submodule ℂ H, Nonempty (RieszBasisWithBrackets V) ∧
      ∀ k, ∀ v ∈ V k, ∃ g : H, K₀ g = v ∧ g + B g ∈ V k

theorem intervalLInfinity_ae_norm_le (f : IntervalLInfinity) :
    ∀ᵐ x ∂intervalMeasure, ‖f x‖ ≤ ‖f‖ := by
  have hfin : eLpNorm f ∞ intervalMeasure ≠ ∞ := (Lp.eLpNorm_lt_top f).ne
  filter_upwards [ae_le_eLpNormEssSup (f := (f : ℝ → ℂ)) (μ := intervalMeasure)] with x hx
  rw [Lp.norm_def, ← toReal_enorm]
  exact ENNReal.toReal_mono hfin (by rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)])

/-- Калибровка к чётному коэффициенту без условия малости, при гипотезе
`MarkusMatsaevStatement`. -/
theorem bracket_basis_of_gauge_general (hMM : MarkusMatsaevStatement)
    (A : IntervalLInfinity) (b : ℝ → ℝ)
    (hb : MemLp b ∞ intervalMeasure) (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x)
    (hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa)
    (r wg r' r'' : IntervalLInfinity)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1)
    (hr : HasACMultiplierDerivative r r') (hr' : HasACMultiplierDerivative r' r'')
    (hg : ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x = A x * r (-x))
    (hdom : ∀ f : IntervalL2, MemDirichletH2 (boundedMultiplier r f) ↔ MemDirichletH2 f) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f, variableSobolevOperator A f hf.1 ∈ W k := by
  have hsk : Real.sqrt kappa < 1 :=
    (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
  have hq : 0 < 1 - Real.sqrt kappa := by linarith
  have hν0 : 0 < (Real.sqrt (1 - Real.sqrt kappa))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hq)
  have hpi := Real.pi_pos
  have hlog : ∀ᵐ x ∂intervalMeasure, ‖wg x * r' x‖ ≤ ‖wg‖ * ‖r'‖ := by
    filter_upwards [intervalLInfinity_ae_norm_le wg, intervalLInfinity_ae_norm_le r']
      with x h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  exact bracket_basis_of_gauge_core A b hb kappa (‖wg‖ * ‖r'‖) hkappa hkappa1 (by positivity)
    heven hbprod r wg r' r'' hrw hr hr' hg hdom hlog
    (fun {ι} bH lam hlam K₀ B hK₀ b₀ hb₀ hcount hB =>
      hMM ι IntervalL2 bH lam hlam K₀ B hK₀
        (2 * (Real.sqrt (1 - Real.sqrt kappa))⁻¹ / Real.pi) 2
        ((Real.sqrt (1 - Real.sqrt kappa))⁻¹ * (1 + Real.sqrt kappa) * (2 * (‖wg‖ * ‖r'‖))) b₀
        (by positivity) (by norm_num) (by positivity) hb₀ hcount hB)

/-- **Знакопостоянный коэффициент класса `W²∞`: редукция к теореме Маркуса–Мацаева.**
Условия: вещественный `a ∈ W²∞`, `0 < m ≤ |a| ≤ M`, `|a(x) a(-x)| ≤ κ < 1`.
Ни чётность, ни малость производной не требуются; вместо них используется гипотеза
`MarkusMatsaevStatement`. -/
theorem signDefinite_bracket_basis_general (hMM : MarkusMatsaevStatement)
    (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k := by
  obtain ⟨a', a'', h0, h1⟩ := hreg
  obtain ⟨b, hb, r, wg, r', r'', hbeven, hbprod, hrw, hr, hr', hg, hdom, -, -⟩ :=
    signDefinite_gauge_data a ha m M kappa ‖a'‖ hm hlower hupper hproduct a' a'' h0 h1
      (intervalLInfinity_ae_norm_le a')
  exact bracket_basis_of_gauge_general hMM (realIntervalCoefficient a ha) b hb kappa hkappa
    hkappa1
    (Filter.Eventually.of_forall hbeven) hbprod r wg r' r'' hrw hr hr' hg hdom

/-- Блоки базиса со скобками порождены корневыми векторами `L_a`. -/
theorem signDefinite_bracket_rootVectors_general (hMM : MarkusMatsaevStatement)
    (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure) (m M kappa : ℝ) (hm : 0 < m)
    (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|) (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M)
    (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ := by
  obtain ⟨W, ⟨B⟩, hW⟩ := signDefinite_bracket_basis_general hMM a ha m M kappa hm hlower
    hupper hkappa hkappa1 hproduct hreg
  refine ⟨W, ⟨B⟩, fun k => ?_⟩
  have := B.finite k
  exact invariant_block_rootVectors (realIntervalCoefficient a ha) (W k) (hW k)

/-- Теорема Маркуса–Мацаева для возмущений порядка `1/2` доказана:
`exists_bracket_basis_of_subordinate_general`. -/
theorem markusMatsaevStatement : MarkusMatsaevStatement :=
  fun _ _ _ _ _ b lam hlam K₀ B hK₀ c₂ C₀ b₁ b₀ hc₂ hC₀ hb₁ hb₀ hcount hB =>
    exists_bracket_basis_of_subordinate_general b lam hlam K₀ B hK₀ c₂ C₀ b₁ b₀ hc₂ hC₀ hb₁
      hb₀ hcount hB

/-- **Знакопостоянный коэффициент класса `W²∞`: базис Рисса со скобками.**
Условия: вещественный `a ∈ W²∞`, `0 < m ≤ |a| ≤ M`, `|a(x) a(-x)| ≤ κ < 1`.
Ни чётность, ни малость производной не требуются. Существует последовательность
конечномерных подпространств слабой области Дирихле, инвариантных относительно `L_a`
и образующих базис Рисса со скобками. -/
theorem signDefinite_bracket_basis_W2 (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k :=
  signDefinite_bracket_basis_general markusMatsaevStatement a ha m M kappa hm hlower hupper
    hkappa hkappa1 hproduct hreg

/-- Блоки базиса со скобками порождены корневыми векторами `L_a`. -/
theorem signDefinite_bracket_rootVectors_W2 (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (hreg : MemIntervalW2Infinity (realIntervalCoefficient a ha)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ :=
  signDefinite_bracket_rootVectors_general markusMatsaevStatement a ha m M kappa hm hlower
    hupper hkappa hkappa1 hproduct hreg

end Involution
