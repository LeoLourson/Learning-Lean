module

public import Involution.SignDefiniteBrackets
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Следствия теоремы о базисе со скобками.
* Конечномерный инвариантный блок порождён корневыми векторами ограничения `L_a`.
* Пример `a(x) = 1/2 + x/1000`: условия теоремы выполнены, коэффициент не чётен. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- На конечномерном инвариантном подпространстве области оператор `L_a` задаёт
линейный эндоморфизм, и корневые подпространства этого эндоморфизма порождают блок. -/
theorem invariant_block_rootVectors (A : IntervalLInfinity) (W : Submodule ℂ IntervalL2)
    [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∃ hf : MemDirichletH2 f, variableSobolevOperator A f hf.1 ∈ W) :
    ∃ N : Module.End ℂ W,
      (∀ f : W, ∃ hf : MemDirichletH2 (f : IntervalL2),
        ((N f : W) : IntervalL2) = variableSobolevOperator A f hf.1) ∧
      ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ := by
  let N : Module.End ℂ W :=
    { toFun := fun f => ⟨variableSobolevOperator A f (hW f f.2).choose.1, (hW f f.2).choose_spec⟩
      map_add' := fun f g => Subtype.ext
        (variableSobolevOperator_add A f g (hW f f.2).choose.1 (hW g g.2).choose.1 _)
      map_smul' := fun c f => Subtype.ext
        (variableSobolevOperator_smul A c f (hW f f.2).choose.1 _) }
  exact ⟨N, fun f => ⟨(hW f f.2).choose, rfl⟩, Module.End.iSup_maxGenEigenspace_eq_top N⟩

/-- Базис Рисса со скобками из блоков, порождённых корневыми векторами `L_a`. -/
theorem signDefinite_bracket_rootVectors (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (m M kappa ε : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ |a x|)
    (hupper : ∀ᵐ x ∂intervalMeasure, |a x| ≤ M) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa)
    (a' a'' : IntervalLInfinity)
    (h0 : HasIntervalWeakDeriv (realIntervalCoefficient a ha) a')
    (h1 : HasIntervalWeakDeriv a' a'') (hε0 : 0 ≤ ε)
    (hε : ∀ᵐ x ∂intervalMeasure, ‖a' x‖ ≤ ε)
    (hsmall : 320 * (1 + Real.sqrt kappa) * ε < Real.pi * (1 - Real.sqrt kappa) * m) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ := by
  obtain ⟨W, ⟨B⟩, hW⟩ := signDefinite_bracket_basis a ha m M kappa ε hm hlower hupper hkappa
    hkappa1 hproduct a' a'' h0 h1 hε0 hε hsmall
  refine ⟨W, ⟨B⟩, fun k => ?_⟩
  have := B.finite k
  exact invariant_block_rootVectors (realIntervalCoefficient a ha) (W k) (hW k)

/-- Нечётно возмущённый постоянный коэффициент. -/
def tiltedCoefficient (x : ℝ) : ℝ := 1 / 2 + x / 1000

theorem tiltedCoefficient_not_even (x : ℝ) (hx : x ≠ 0) :
    tiltedCoefficient (-x) ≠ tiltedCoefficient x := by
  unfold tiltedCoefficient
  intro h
  apply hx
  linarith

theorem tiltedCoefficient_bounds (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    499 / 1000 ≤ |tiltedCoefficient x| ∧ |tiltedCoefficient x| ≤ 501 / 1000 ∧
      |tiltedCoefficient x * tiltedCoefficient (-x)| ≤ 1 / 4 := by
  obtain ⟨h1, h2⟩ := hx
  have hpos : 0 < tiltedCoefficient x := by
    unfold tiltedCoefficient
    linarith
  have hprod : tiltedCoefficient x * tiltedCoefficient (-x) = 1 / 4 - x ^ 2 / 1000000 := by
    unfold tiltedCoefficient
    ring
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos hpos]
    unfold tiltedCoefficient
    linarith
  · rw [abs_of_pos hpos]
    unfold tiltedCoefficient
    linarith
  · rw [hprod, abs_of_nonneg (by nlinarith [sq_nonneg x])]
    nlinarith [sq_nonneg x]

theorem tiltedCoefficient_memLp : MemLp tiltedCoefficient ∞ intervalMeasure := by
  have hc : Continuous tiltedCoefficient := by
    unfold tiltedCoefficient
    fun_prop
  apply memLp_top_of_bound hc.aestronglyMeasurable (501 / 1000)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  exact (tiltedCoefficient_bounds x hx).2.1

/-- Гладкий представитель коэффициента. -/
def tiltedCoefficientComplex (x : ℝ) : ℂ := (1 / 2 : ℂ) + (x : ℂ) / 1000

theorem tiltedCoefficientComplex_hasDerivAt (x : ℝ) :
    HasDerivAt tiltedCoefficientComplex (1 / 1000 : ℂ) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).div_const (1000 : ℂ)).const_add
    (1 / 2 : ℂ)
  exact h.congr_deriv (by simp)

theorem tiltedCoefficientComplex_contDiff : ContDiff ℝ 1 tiltedCoefficientComplex := by
  unfold tiltedCoefficientComplex
  exact contDiff_const.add (Complex.ofRealCLM.contDiff.div_const _)

/-- Пример: для `a(x) = 1/2 + x/1000` существует базис Рисса со скобками из
конечномерных инвариантных подпространств `L_a`. Коэффициент не является чётным. -/
theorem tiltedCoefficient_bracket_basis :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator
          (realIntervalCoefficient tiltedCoefficient tiltedCoefficient_memLp) f hf.1 ∈ W k := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1))
    infer_instance
  have hmem : ∀ c : ℝ, MemLp (fun _ : ℝ => c) ∞ intervalMeasure := fun c => memLp_const c
  let a' : IntervalLInfinity := realIntervalCoefficient (fun _ => 1 / 1000) (hmem _)
  let a'' : IntervalLInfinity := realIntervalCoefficient (fun _ => 0) (hmem _)
  have hbounds := ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1))
  have hderiv : deriv tiltedCoefficientComplex = fun _ => (1 / 1000 : ℂ) :=
    funext fun x => (tiltedCoefficientComplex_hasDerivAt x).deriv
  have h0 : HasIntervalWeakDeriv
      (realIntervalCoefficient tiltedCoefficient tiltedCoefficient_memLp) a' := by
    refine (hasIntervalWeakDeriv_of_contDiff tiltedCoefficientComplex_contDiff).congr ?_ ?_
    · filter_upwards [realIntervalCoefficient_ae tiltedCoefficient tiltedCoefficient_memLp]
        with x hx
      rw [hx]
      simp [tiltedCoefficientComplex, tiltedCoefficient]
    · filter_upwards [realIntervalCoefficient_ae (fun _ => (1 / 1000 : ℝ)) (hmem _)] with x hx
      rw [hderiv]
      change _ = realIntervalCoefficient (fun _ => (1 / 1000 : ℝ)) (hmem _) x
      rw [hx]
      simp
  have h1 : HasIntervalWeakDeriv a' a'' := by
    have hc : ContDiff ℝ 1 (fun _ : ℝ => (1 / 1000 : ℂ)) := contDiff_const
    refine (hasIntervalWeakDeriv_of_contDiff hc).congr ?_ ?_
    · filter_upwards [realIntervalCoefficient_ae (fun _ => (1 / 1000 : ℝ)) (hmem _)] with x hx
      change _ = realIntervalCoefficient (fun _ => (1 / 1000 : ℝ)) (hmem _) x
      rw [hx]
      simp
    · filter_upwards [realIntervalCoefficient_ae (fun _ => (0 : ℝ)) (hmem _)] with x hx
      change _ = realIntervalCoefficient (fun _ => (0 : ℝ)) (hmem _) x
      rw [hx]
      simp
  have hε : ∀ᵐ x ∂intervalMeasure, ‖a' x‖ ≤ 1 / 1000 := by
    filter_upwards [realIntervalCoefficient_ae (fun _ => (1 / 1000 : ℝ)) (hmem _)] with x hx
    change ‖realIntervalCoefficient (fun _ => (1 / 1000 : ℝ)) (hmem _) x‖ ≤ _
    rw [hx]
    simp
  have hsqrt : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine signDefinite_bracket_basis tiltedCoefficient tiltedCoefficient_memLp (499 / 1000)
    (501 / 1000) (1 / 4) (1 / 1000) (by norm_num) ?_ ?_ (by norm_num) (by norm_num) ?_ a' a''
    h0 h1 (by norm_num) hε ?_
  · filter_upwards [hbounds] with x hx
    exact (tiltedCoefficient_bounds x hx).1
  · filter_upwards [hbounds] with x hx
    exact (tiltedCoefficient_bounds x hx).2.1
  · filter_upwards [hbounds] with x hx
    exact (tiltedCoefficient_bounds x hx).2.2
  · rw [hsqrt]
    have hpi := Real.pi_gt_three
    nlinarith

end Involution
