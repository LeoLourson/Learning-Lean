module

public import Involution.Model.PositiveWeight
public import Involution.Model.CompactEigenbasis

/-! Ограниченно обратимое умножение на взаимно обратные веса и его
ограничение на каналы отражения. Оно переносит спектральный Hilbert-базис в базис Рисса. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

theorem boundedMultiplier_inverse (v w : IntervalLInfinity)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (f : IntervalL2) :
    boundedMultiplier v (boundedMultiplier w f) = f := by
  apply Lp.ext
  filter_upwards [boundedMultiplier_ae v (boundedMultiplier w f),
    boundedMultiplier_ae w f, hvw] with x hv hw hx
  rw [hv, hw, ← mul_assoc, hx, one_mul]

def multiplicationEquiv (v w : IntervalLInfinity)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) : IntervalL2 ≃L[ℂ] IntervalL2 :=
  ContinuousLinearEquiv.equivOfInverse (boundedMultiplier v) (boundedMultiplier w)
    (boundedMultiplier_inverse w v (hvw.mono fun x hx => by rwa [mul_comm]))
    (boundedMultiplier_inverse v w hvw)

theorem multiplicationEquiv_apply (v w : IntervalLInfinity)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (f : IntervalL2) :
    multiplicationEquiv v w hvw f = boundedMultiplier v f := rfl

theorem boundedMultiplier_parity_invariant (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (s : ℂ) :
    ∀ f ∈ parityL2Submodule s, boundedMultiplier w f ∈ parityL2Submodule s := by
  intro f hf
  rw [parityL2Submodule, Module.End.mem_eigenspace_iff] at hf ⊢
  change l2Reflect f = s • f at hf
  change l2Reflect (boundedMultiplier w f) = s • boundedMultiplier w f
  rw [← boundedMultiplier_reflect w hw, hf, map_smul]

def parityMultiplier (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (s : ℂ) : ParityL2 s →L[ℂ] ParityL2 s :=
  (boundedMultiplier w).restrict (boundedMultiplier_parity_invariant w hw s)

def parityMultiplicationEquiv (v w : IntervalLInfinity)
    (hv : ∀ᵐ x ∂intervalMeasure, v (-x) = v x)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (s : ℂ) : ParityL2 s ≃L[ℂ] ParityL2 s :=
  ContinuousLinearEquiv.equivOfInverse (parityMultiplier v hv s) (parityMultiplier w hw s)
    (fun f => Subtype.ext (boundedMultiplier_inverse w v
      (hvw.mono fun x hx => by rwa [mul_comm]) f))
    (fun f => Subtype.ext (boundedMultiplier_inverse v w hvw f))

def weightedChannelRieszBasis {ι : Type*} (b : HilbertBasis ι ℂ (ParityL2 s))
    (v w : IntervalLInfinity)
    (hv : ∀ᵐ x ∂intervalMeasure, v (-x) = v x)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) : RieszBasis ι (ParityL2 s) :=
  rieszBasisOfHilbertBasis b (parityMultiplicationEquiv v w hv hw hvw s)

theorem weightedChannelRieszBasis_vector {ι : Type*} (b : HilbertBasis ι ℂ (ParityL2 s))
    (v w : IntervalLInfinity)
    (hv : ∀ᵐ x ∂intervalMeasure, v (-x) = v x)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (i : ι) :
    ((weightedChannelRieszBasis b v w hv hw hvw).vector i : IntervalL2) =
      boundedMultiplier v (b i) := rfl

def weightedChannelEigenbasis (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) (s : ℂ) :=
  compactEigenbasis (weightedParityGreen w hw s) (weightedParityGreen_compact w hw s)
    (weightedParityGreen_symmetric w hw hr s)

def weightedSpectralRieszBasis (v w : IntervalLInfinity)
    (hv : ∀ᵐ x ∂intervalMeasure, v (-x) = v x)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1) (s : ℂ) :
    RieszBasis (CompactEigenbasisIndex (weightedParityGreen w hw s)) (ParityL2 s) :=
  weightedChannelRieszBasis (weightedChannelEigenbasis w hw hr s) v w hv hw hvw

theorem weightedChannelEigenbasis_equation (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) (s : ℂ)
    (i : CompactEigenbasisIndex (weightedParityGreen w hw s)) :
    weightedParityGreen w hw s (weightedChannelEigenbasis w hw hr s i) =
      i.1 • weightedChannelEigenbasis w hw hr s i :=
  compactEigenbasis_equation _ _ _ i

end Involution
