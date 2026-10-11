module

public import Involution.MultiplicationEquiv
public import Involution.ScalarDomain

/-! Собственные уравнения базиса Рисса взвешенного канала.
Принадлежность области получается из обратного Дирихле и скалярной
замкнутости области; гладкость множителя для этого не требуется. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

theorem reciprocalWeight_nonzero (v w : IntervalLInfinity)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) :
    ∀ᵐ x ∂intervalMeasure, w x ≠ 0 := by
  filter_upwards [hvw] with x hx
  intro hz
  rw [hz, mul_zero] at hx
  exact zero_ne_one hx

theorem weightedParityGreen_injective (v w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (s : ℂ) :
    Function.Injective (weightedParityGreen w hw s) := by
  intro f g hfg
  apply Subtype.ext
  exact weightedGreen_injective w
    (boundedMultiplier_injective w (reciprocalWeight_nonzero v w hvw))
      (congrArg Subtype.val hfg)

theorem weightedChannelEigenvalue_ne_zero (v w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (s : ℂ)
    (i : CompactEigenbasisIndex (weightedParityGreen w hw s)) : i.1 ≠ 0 :=
  compactEigenbasis_eigenvalue_ne_zero _ (weightedParityGreen_compact w hw s)
    (weightedParityGreen_symmetric w hw hr s) (weightedParityGreen_injective v w hw hvw s) i

theorem weightedEigenvector_eq_green (v w : IntervalLInfinity)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1)
    (u : IntervalL2) (mu : ℂ) (hmu : mu ≠ 0) (he : weightedGreen w u = mu • u) :
    boundedMultiplier v u = mu⁻¹ • spectralGreen (boundedMultiplier w u) := by
  have he' := congrArg (boundedMultiplier v) he
  change boundedMultiplier v (boundedMultiplier w
    (spectralGreen (boundedMultiplier w u))) = boundedMultiplier v (mu • u) at he'
  rw [boundedMultiplier_inverse v w hvw, map_smul] at he'
  calc
    _ = mu⁻¹ • (mu • boundedMultiplier v u) := by
      rw [smul_smul, inv_mul_cancel₀ hmu, one_smul]
    _ = _ := congrArg (fun f => mu⁻¹ • f) he'.symm

theorem weightedEigenvector_memDirichletH2 (v w : IntervalLInfinity)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1)
    (u : IntervalL2) (mu : ℂ) (hmu : mu ≠ 0) (he : weightedGreen w u = mu • u) :
    MemDirichletH2 (boundedMultiplier v u) := by
  rw [weightedEigenvector_eq_green v w hvw u mu hmu he]
  exact (spectralGreen_memDirichletH2 (boundedMultiplier w u)).smul mu⁻¹

theorem weightedEigenvector_equation (a v w : IntervalLInfinity) (s mu : ℂ)
    (hmu : mu ≠ 0) (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (u : IntervalL2) (hu : l2Reflect u = s • u) (he : weightedGreen w u = mu • u) :
    variableSobolevOperator a (boundedMultiplier v u)
      (weightedEigenvector_memDirichletH2 v w hvw u mu hmu he).1 =
        mu⁻¹ • boundedMultiplier v u := by
  have heq := weightedEigenvector_eq_green v w hvw u mu hmu he
  have hgreen := weightedGreen_eigenfunction a w s mu hmu hw hinv u hu he
  have hy := spectralGreen_memDirichletH2 (boundedMultiplier w u)
  calc
    _ = variableSobolevOperator a (mu⁻¹ • spectralGreen (boundedMultiplier w u))
        (hy.smul mu⁻¹).1 := variableSobolevOperator_congr a _ _ _ _ heq
    _ = mu⁻¹ • variableSobolevOperator a (spectralGreen (boundedMultiplier w u)) hy.1 :=
      variableSobolevOperator_smul a _ _ _ _
    _ = mu⁻¹ • (mu⁻¹ • spectralGreen (boundedMultiplier w u)) := congrArg _ hgreen
    _ = _ := congrArg (fun f => mu⁻¹ • f) heq.symm

theorem weightedSpectralRieszBasis_memDirichletH2 (v w : IntervalLInfinity)
    (hv : ∀ᵐ x ∂intervalMeasure, v (-x) = v x)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (s : ℂ)
    (i : CompactEigenbasisIndex (weightedParityGreen w hw s)) :
    MemDirichletH2 ((weightedSpectralRieszBasis v w hv hw hr hvw s).vector i : IntervalL2) := by
  change MemDirichletH2 (boundedMultiplier v (weightedChannelEigenbasis w hw hr s i))
  exact weightedEigenvector_memDirichletH2 v w hvw _ i.1
    (weightedChannelEigenvalue_ne_zero v w hw hr hvw s i)
    (congrArg Subtype.val (weightedChannelEigenbasis_equation w hw hr s i))

theorem weightedSpectralRieszBasis_eigen_equation (a v w : IntervalLInfinity)
    (hv : ∀ᵐ x ∂intervalMeasure, v (-x) = v x)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (s : ℂ)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (i : CompactEigenbasisIndex (weightedParityGreen w hw s)) :
    variableSobolevOperator a
      ((weightedSpectralRieszBasis v w hv hw hr hvw s).vector i : IntervalL2)
      (weightedSpectralRieszBasis_memDirichletH2 v w hv hw hr hvw s i).1 =
        i.1⁻¹ • ((weightedSpectralRieszBasis v w hv hw hr hvw s).vector i : IntervalL2) := by
  apply weightedEigenvector_equation a v w s i.1
    (weightedChannelEigenvalue_ne_zero v w hw hr hvw s i) hw hvw hinv
  · exact Module.End.mem_eigenspace_iff.mp (weightedChannelEigenbasis w hw hr s i).property
  · exact congrArg Subtype.val (weightedChannelEigenbasis_equation w hw hr s i)

end Involution
