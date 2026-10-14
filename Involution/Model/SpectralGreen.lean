module

public import Involution.Model.DirichletGreen
public import Involution.Model.ModelEigenbasis
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Спектральный ряд обратного оператора Дирихле.
Ряд операторов ранга один сходится в операторной норме. Компактность
следует из замкнутости пространства компактных операторов Mathlib. -/

@[expose] public noncomputable section

open MeasureTheory InnerProductSpace
open scoped BigOperators

namespace Involution

theorem modelDirichletEigenvalue_pos (i : ℕ ⊕ ℕ) : 0 < constantModelEigenvalue 0 i := by
  cases i <;> simp only [constantModelEigenvalue, Sum.elim_inl, Sum.elim_inr,
    add_zero, sub_zero, one_mul] <;> positivity

def modelGreenWeight (i : ℕ ⊕ ℕ) : ℂ := ((constantModelEigenvalue 0 i)⁻¹ : ℝ)

theorem modelGreenWeight_norm (i : ℕ ⊕ ℕ) :
    ‖modelGreenWeight i‖ = (constantModelEigenvalue 0 i)⁻¹ := by
  simp only [modelGreenWeight, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (inv_pos.mpr (modelDirichletEigenvalue_pos i))

theorem shiftedFrequency_inverse_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => ((((n : ℝ) + a) * Real.pi) ^ 2)⁻¹) := by
  have hs := (Real.summable_one_div_nat_add_rpow a 2).mpr (by norm_num)
  convert hs.mul_right ((Real.pi ^ 2)⁻¹) using 1
  funext n
  rw [abs_of_pos (by positivity : 0 < (n : ℝ) + a)]
  simp only [Real.rpow_two, mul_pow, mul_inv_rev, one_div]
  ring

theorem modelGreenWeight_norm_summable : Summable (fun i => ‖modelGreenWeight i‖) := by
  apply Summable.sum (fun i => ‖modelGreenWeight i‖)
  · simpa only [Function.comp_def, modelGreenWeight_norm, constantModelEigenvalue,
      Sum.elim_inl, add_zero, one_mul] using
      shiftedFrequency_inverse_summable (1 / 2) (by norm_num)
  · simpa only [Function.comp_def, modelGreenWeight_norm, constantModelEigenvalue,
      Sum.elim_inr, sub_zero, one_mul] using shiftedFrequency_inverse_summable 1 (by norm_num)

def modelGreenTerm (i : ℕ ⊕ ℕ) : IntervalL2 →L[ℂ] IntervalL2 :=
  modelGreenWeight i • rankOne ℂ (constantModelVector i) (constantModelVector i)

theorem modelGreenTerm_summable : Summable modelGreenTerm := by
  apply Summable.of_norm
  convert modelGreenWeight_norm_summable using 1
  funext i
  rw [modelGreenTerm, norm_smul, norm_rankOne, constantModel_orthonormal.norm_eq_one,
    mul_one, mul_one]

def spectralGreen : IntervalL2 →L[ℂ] IntervalL2 := ∑' i, modelGreenTerm i

theorem modelGreenTerm_compact (i : ℕ ⊕ ℕ) : IsCompactOperator (modelGreenTerm i) := by
  have hc : IsCompactOperator (rankOne ℂ (constantModelVector i) (constantModelVector i)) := by
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_dom
      (innerSL ℂ (constantModelVector i))).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ (constantModelVector i))
  exact hc.smul (modelGreenWeight i)

theorem spectralGreen_compact : IsCompactOperator spectralGreen := by
  apply isCompactOperator_of_tendsto modelGreenTerm_summable.hasSum
  exact Filter.Eventually.of_forall fun s =>
    (compactOperator (RingHom.id ℂ) IntervalL2 IntervalL2).sum_mem
      (fun i _ => modelGreenTerm_compact i)

theorem spectralGreen_coefficient (x : IntervalL2) (j : ℕ ⊕ ℕ) :
    inner ℂ (constantModelVector j) (spectralGreen x) =
      modelGreenWeight j * inner ℂ (constantModelVector j) x := by
  have hs := (ContinuousLinearMap.apply ℂ IntervalL2 x).hasSum modelGreenTerm_summable.hasSum
  have hc := (innerSL ℂ (constantModelVector j)).hasSum hs
  change HasSum (fun i => inner ℂ (constantModelVector j) (modelGreenTerm i x))
    (inner ℂ (constantModelVector j) (spectralGreen x)) at hc
  rw [← hc.tsum_eq, tsum_eq_single j]
  · have hself : inner ℂ (constantModelVector j) (constantModelVector j) = 1 := by
      simpa using (orthonormal_iff_ite.mp constantModel_orthonormal j j)
    simp only [modelGreenTerm, smul_apply, rankOne_apply, inner_smul_right, hself, mul_one]
  · intro i hij
    have hzero : inner ℂ (constantModelVector j) (constantModelVector i) = 0 :=
      constantModel_orthonormal.inner_eq_zero (Ne.symm hij)
    simp only [modelGreenTerm, smul_apply, rankOne_apply,
      inner_smul_right, hzero, mul_zero]

theorem dirichlet_solution_coefficient (x y : IntervalL2) (hy : MemDirichletH2 y)
    (hxy : -secondWeakDeriv y hy.1 = x) (i : ℕ ⊕ ℕ) :
    inner ℂ (constantModelVector i) y =
      modelGreenWeight i * inner ℂ (constantModelVector i) x := by
  have hm := constantModel_eigen_equation 0 i
  simp only [constantSobolevOperator, Complex.ofReal_zero, zero_smul, sub_zero] at hm
  have hsym := negativeSecondWeakDeriv_symmetric (constantModelVector i) y
    (constantModelVector_memDirichletH2 i) hy
  rw [hm, hxy, inner_smul_left] at hsym
  have hreal : starRingEnd ℂ ((constantModelEigenvalue 0 i : ℝ) : ℂ) =
      ((constantModelEigenvalue 0 i : ℝ) : ℂ) := by simp
  rw [hreal] at hsym
  have hne : ((constantModelEigenvalue 0 i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (modelDirichletEigenvalue_pos i))
  rw [modelGreenWeight, Complex.ofReal_inv]
  rw [← hsym, inv_mul_cancel_left₀ hne]

theorem spectralGreen_eq_solution (x y : IntervalL2) (hy : MemDirichletH2 y)
    (hxy : -secondWeakDeriv y hy.1 = x) : spectralGreen x = y := by
  apply constantModelHilbertBasis.repr.injective
  ext i
  rw [constantModelHilbertBasis.repr_apply_apply, constantModelHilbertBasis.repr_apply_apply,
    constantModelHilbertBasis_coe, spectralGreen_coefficient,
    dirichlet_solution_coefficient x y hy hxy i]

theorem spectralGreen_memDirichletH2 (x : IntervalL2) : MemDirichletH2 (spectralGreen x) := by
  obtain ⟨y, hy, hxy⟩ := negativeSecondWeakDeriv_surjective x
  exact (spectralGreen_eq_solution x y hy hxy).symm ▸ hy

theorem spectralGreen_right_inverse (x : IntervalL2) :
    -secondWeakDeriv (spectralGreen x) (spectralGreen_memDirichletH2 x).1 = x := by
  obtain ⟨y, hy, hxy⟩ := negativeSecondWeakDeriv_surjective x
  have heq := spectralGreen_eq_solution x y hy hxy
  subst y
  exact hxy

theorem spectralGreen_left_inverse (y : IntervalL2) (hy : MemDirichletH2 y) :
    spectralGreen (-secondWeakDeriv y hy.1) = y :=
  spectralGreen_eq_solution _ y hy rfl

theorem spectralGreen_symmetric : spectralGreen.IsSymmetric := by
  intro f g
  have hsym := negativeSecondWeakDeriv_symmetric (spectralGreen f) (spectralGreen g)
    (spectralGreen_memDirichletH2 f) (spectralGreen_memDirichletH2 g)
  rw [spectralGreen_right_inverse f, spectralGreen_right_inverse g] at hsym
  exact hsym.symm

theorem spectralGreen_eigenspaces_orthogonalComplement :
    (⨆ mu : ℂ, Module.End.eigenspace spectralGreen.toLinearMap mu)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    spectralGreen_compact spectralGreen_symmetric

theorem spectralGreen_eigenspaces_dense :
    (⨆ mu : ℂ, Module.End.eigenspace spectralGreen.toLinearMap mu).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr spectralGreen_eigenspaces_orthogonalComplement

theorem spectralGreen_finiteDimensional_eigenspace (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace spectralGreen.toLinearMap mu) :=
  ContinuousLinearMap.finite_dimensional_eigenspace spectralGreen_compact mu hmu

theorem spectralGreen_eq_zero_imp (f : IntervalL2) (hf : spectralGreen f = 0) : f = 0 := by
  have hinner (i : ℕ ⊕ ℕ) : inner ℂ (constantModelVector i) f = 0 := by
    have hcoef := spectralGreen_coefficient f i
    rw [hf, inner_zero_right] at hcoef
    have hne : modelGreenWeight i ≠ 0 := by
      unfold modelGreenWeight
      exact_mod_cast inv_ne_zero (ne_of_gt (modelDirichletEigenvalue_pos i))
    exact (mul_eq_zero.mp hcoef.symm).resolve_left hne
  apply constantModelHilbertBasis.repr.injective
  rw [map_zero]
  ext i
  rw [constantModelHilbertBasis.repr_apply_apply, constantModelHilbertBasis_coe]
  exact hinner i

theorem spectralGreen_injective : Function.Injective spectralGreen := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply spectralGreen_eq_zero_imp
  rw [map_sub, hfg, sub_self]

theorem spectralGreen_reflect (f : IntervalL2) :
    spectralGreen (l2Reflect f) = l2Reflect (spectralGreen f) := by
  have hy := spectralGreen_memDirichletH2 f
  have hsol : -secondWeakDeriv (l2Reflect (spectralGreen f)) hy.reflect.1 = l2Reflect f := by
    rw [secondWeakDeriv_reflect (spectralGreen f) hy.1,
      ← map_neg, spectralGreen_right_inverse f]
  exact spectralGreen_eq_solution (l2Reflect f) (l2Reflect (spectralGreen f)) hy.reflect hsol

end Involution
