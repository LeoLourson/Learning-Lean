module

public import Involution.Theorems.MainTheorems
public import Involution.Estimates.NearlyEvenBrackets
public import Involution.Estimates.GeneralBrackets

/-! Сводка: достаточные условия двух видов базисности в зависимости от коэффициента.

Оператор `L_a y = -y''(x) - a(x) y''(-x)` на слабой области Дирихле, `a` веществен,
`|a(x) a(-x)| ≤ κ < 1` почти всюду.

* `rieszBasis_of_even`: `a ∈ L∞`, `a(-x) = a(x)`. Вывод: обычный базис Рисса из
  собственных функций, присоединённых функций нет.
* `bracketBasis_of_signDefinite`: `a ∈ W²∞`, `0 < m ≤ |a| ≤ M`. Вывод: базис Рисса со
  скобками из конечномерных инвариантных блоков, порождённых корневыми функциями.
  Доказательство опирается на теорему Маркуса–Мацаева, формализованную в модулях `MM*`.
* `bracketBasis_of_nearlyEven`: тот же вывод при дополнительном условии близости к
  чётному `|a'(x)/a(x) + a'(-x)/a(-x)| ≤ η`, `160 (1 + √κ) η < π (1 - √κ)`; доказан
  независимо, методом подобных операторов, без контурных интегралов.

Отрицательные примеры: `oneSided_no_bracket_basis`, `ramp_no_riesz_eigenbasis`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- **Обычный базис Рисса.** Для чётного коэффициента существует базис Рисса из
собственных функций `L_a`, и нетривиальных жордановых цепочек нет. -/
theorem rieszBasis_of_even (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, a (-x) = a x)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    (∃ (ι : Type) (e : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemDirichletH2 (e.vector i), ∃ lam : ℂ,
        variableSobolevOperator (realIntervalCoefficient a ha) (e.vector i) hf.1 =
          lam • e.vector i) ∧
    (∀ (f g : IntervalL2) (hf : MemDirichletH2 f) (hg : MemDirichletH2 g) (lam : ℂ),
      variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 = lam • f →
      variableSobolevOperator (realIntervalCoefficient a ha) g hg.1 = lam • g + f → f = 0) :=
  ⟨evenCoefficient_riesz_eigenbasis a ha kappa hkappa hkappa1 heven hproduct,
    fun f g hf hg lam he hj =>
      evenCoefficient_noJordan a ha kappa hkappa hkappa1 heven hproduct f g hf hg lam he hj⟩

/-- **Базис Рисса со скобками.** Для знакопостоянного коэффициента класса `W²∞`,
близкого к чётному, существует базис Рисса со скобками из конечномерных подпространств
области, на каждом из которых `L_a` действует как эндоморфизм `N`, а корневые
подпространства `N` порождают блок. -/
theorem bracketBasis_of_nearlyEven (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa η : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'') (hη0 : 0 ≤ η)
    (hη : ∀ᵐ x ∂intervalMeasure,
      ‖a' x * (a (-x) : ℂ) + a' (-x) * (a x : ℂ)‖ ≤ η * |a x * a (-x)|)
    (hsmall : 160 * (1 + Real.sqrt kappa) * η < Real.pi * (1 - Real.sqrt kappa)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ :=
  nearlyEven_bracket_rootVectors a ha m M kappa η hm hlower hupper hkappa hkappa1 hproduct
    a' a'' h0 h1 hη0 hη hsmall

/-- **Базис Рисса со скобками, общий знакопостоянный случай.** Вещественный `a ∈ W²∞`,
отделённый от нуля, без условий чётности и малости. -/
theorem bracketBasis_of_signDefinite (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
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
  signDefinite_bracket_rootVectors_W2 a ha m M kappa hm hlower hupper hkappa hkappa1 hproduct
    hreg

/-- Пример без чётности и без малости: `a(x) = 1/2 + x/4` (пример из C6). -/
def steepCoefficient (x : ℝ) : ℝ := 1 / 2 + x / 4

theorem steepCoefficient_not_even (x : ℝ) (hx : x ≠ 0) :
    steepCoefficient (-x) ≠ steepCoefficient x := by
  unfold steepCoefficient
  intro h
  apply hx
  linarith

theorem steepCoefficient_bounds (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    1 / 4 ≤ |steepCoefficient x| ∧ |steepCoefficient x| ≤ 3 / 4 ∧
      |steepCoefficient x * steepCoefficient (-x)| ≤ 1 / 4 := by
  obtain ⟨h1, h2⟩ := hx
  have hpos : 0 < steepCoefficient x := by
    unfold steepCoefficient
    linarith
  have hprod : steepCoefficient x * steepCoefficient (-x) = 1 / 4 - x ^ 2 / 16 := by
    unfold steepCoefficient
    ring
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos hpos]
    unfold steepCoefficient
    linarith
  · rw [abs_of_pos hpos]
    unfold steepCoefficient
    linarith
  · rw [hprod, abs_of_nonneg (by nlinarith [sq_nonneg x])]
    nlinarith [sq_nonneg x]

theorem steepCoefficient_memLp : MemLp steepCoefficient ∞ intervalMeasure := by
  have hc : Continuous steepCoefficient := by
    unfold steepCoefficient
    fun_prop
  apply memLp_top_of_bound hc.aestronglyMeasurable (3 / 4)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  exact (steepCoefficient_bounds x hx).2.1

theorem steepCoefficient_memW2Infinity :
    MemIntervalW2Infinity (realIntervalCoefficient steepCoefficient steepCoefficient_memLp) := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1))
    infer_instance
  have hmem : ∀ c : ℝ, MemLp (fun _ : ℝ => c) ∞ intervalMeasure := fun c => memLp_const c
  let g : ℝ → ℂ := fun x => (1 / 2 : ℂ) + (x : ℂ) / 4
  have hg : ∀ x : ℝ, HasDerivAt g (1 / 4 : ℂ) x := fun x =>
    (((Complex.ofRealCLM.hasDerivAt (x := x)).div_const (4 : ℂ)).const_add
      (1 / 2 : ℂ)).congr_deriv (by simp)
  have hgc : ContDiff ℝ 1 g := contDiff_const.add (Complex.ofRealCLM.contDiff.div_const _)
  have hderiv : deriv g = fun _ => (1 / 4 : ℂ) := funext fun x => (hg x).deriv
  refine ⟨realIntervalCoefficient (fun _ => 1 / 4) (hmem _),
    realIntervalCoefficient (fun _ => 0) (hmem _), ?_, ?_⟩
  · refine (hasIntervalWeakDeriv_of_contDiff hgc).congr ?_ ?_
    · filter_upwards [realIntervalCoefficient_ae steepCoefficient steepCoefficient_memLp]
        with x hx
      rw [hx]
      simp [g, steepCoefficient]
    · filter_upwards [realIntervalCoefficient_ae (fun _ => (1 / 4 : ℝ)) (hmem _)] with x hx
      rw [hderiv, hx]
      simp
  · have hc : ContDiff ℝ 1 (fun _ : ℝ => (1 / 4 : ℂ)) := contDiff_const
    refine (hasIntervalWeakDeriv_of_contDiff hc).congr ?_ ?_
    · filter_upwards [realIntervalCoefficient_ae (fun _ => (1 / 4 : ℝ)) (hmem _)] with x hx
      rw [hx]
      simp
    · filter_upwards [realIntervalCoefficient_ae (fun _ => (0 : ℝ)) (hmem _)] with x hx
      rw [hx]
      simp

/-- Для `a(x) = 1/2 + x/4` существует базис Рисса со скобками из конечномерных
инвариантных подпространств `L_a`. Условие малости C14–C15 здесь не выполнено, так что
результат получен из общей теоремы. -/
theorem steepCoefficient_bracket_basis :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator
          (realIntervalCoefficient steepCoefficient steepCoefficient_memLp) f hf.1 ∈ W k := by
  have hbounds := ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1))
  refine signDefinite_bracket_basis_W2 steepCoefficient steepCoefficient_memLp (1 / 4) (3 / 4)
    (1 / 4) (by norm_num) ?_ ?_ (by norm_num) (by norm_num) ?_ steepCoefficient_memW2Infinity
  · filter_upwards [hbounds] with x hx
    exact (steepCoefficient_bounds x hx).1
  · filter_upwards [hbounds] with x hx
    exact (steepCoefficient_bounds x hx).2.1
  · filter_upwards [hbounds] with x hx
    exact (steepCoefficient_bounds x hx).2.2

end Involution
