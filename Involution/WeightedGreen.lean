module

public import Involution.ParityGreen
public import Involution.VariableOperator

/-! Симметричный компактный обратный после ограниченного умножения.
Реальность и чётность веса сформулированы почти всюду. На этом операторе основан
случай C5; вес строится в `PositiveWeight.lean`. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

theorem boundedMultiplier_symmetric (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) :
    (boundedMultiplier w).IsSymmetric := by
  intro f g
  rw [l2_inner_integral, l2_inner_integral]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_ae w f, boundedMultiplier_ae w g, hw] with x hf hg hx
  change star ((boundedMultiplier w f) x) * g x = star (f x) * (boundedMultiplier w g) x
  rw [hf, hg, star_mul, hx]
  ring

theorem boundedMultiplier_reflect (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (f : IntervalL2) :
    boundedMultiplier w (l2Reflect f) = l2Reflect (boundedMultiplier w f) := by
  apply Lp.ext
  have hm := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (boundedMultiplier_ae w f)
  filter_upwards [boundedMultiplier_ae w (l2Reflect f), l2Reflect_ae f,
    l2Reflect_ae (boundedMultiplier w f), hm, hw] with x hmf hrf hrm hmneg hx
  change boundedMultiplier w f (-x) = w (-x) * f (-x) at hmneg
  rw [hmf, hrf, hrm, hmneg, hx]

theorem boundedMultiplier_injective (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w x ≠ 0) : Function.Injective (boundedMultiplier w) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [boundedMultiplier_ae w f, boundedMultiplier_ae w g, hw] with x hf hg hx
  have he : w x * f x = w x * g x := by rw [← hf, ← hg, hfg]
  exact mul_left_cancel₀ hx he

def channelPrincipal (a : IntervalLInfinity) (s : ℂ) : IntervalL2 →L[ℂ] IntervalL2 :=
  ContinuousLinearMap.id ℂ IntervalL2 + s • boundedMultiplier a

theorem channelPrincipal_weight_inverse (a w : IntervalLInfinity) (s : ℂ)
    (hw : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1) (f : IntervalL2) :
    channelPrincipal a s (boundedMultiplier w (boundedMultiplier w f)) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (boundedMultiplier w (boundedMultiplier w f))
      (s • boundedMultiplier a (boundedMultiplier w (boundedMultiplier w f))),
    Lp.coeFn_smul s (boundedMultiplier a (boundedMultiplier w (boundedMultiplier w f))),
    boundedMultiplier_ae a (boundedMultiplier w (boundedMultiplier w f)),
    boundedMultiplier_ae w (boundedMultiplier w f), boundedMultiplier_ae w f, hw]
      with x hadd hsmul ha hww hwf hx
  change (boundedMultiplier w (boundedMultiplier w f) +
    s • boundedMultiplier a (boundedMultiplier w (boundedMultiplier w f))) x = f x
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hadd, hsmul, ha, hww, hwf]
  calc
    _ = ((1 + s * a x) * (w x * w x)) * f x := by ring
    _ = _ := by rw [hx, one_mul]

def weightedGreen (w : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  (boundedMultiplier w).comp (spectralGreen.comp (boundedMultiplier w))

theorem weightedGreen_compact (w : IntervalLInfinity) : IsCompactOperator (weightedGreen w) :=
  (spectralGreen_compact.comp_clm (boundedMultiplier w)).clm_comp (boundedMultiplier w)

theorem weightedGreen_symmetric (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) : (weightedGreen w).IsSymmetric := by
  intro f g
  change inner ℂ (boundedMultiplier w (spectralGreen (boundedMultiplier w f))) g =
    inner ℂ f (boundedMultiplier w (spectralGreen (boundedMultiplier w g)))
  calc
    _ = inner ℂ (spectralGreen (boundedMultiplier w f)) (boundedMultiplier w g) :=
      boundedMultiplier_symmetric w hw _ _
    _ = inner ℂ (boundedMultiplier w f) (spectralGreen (boundedMultiplier w g)) :=
      spectralGreen_symmetric _ _
    _ = _ := boundedMultiplier_symmetric w hw _ _

theorem weightedGreen_injective (w : IntervalLInfinity)
    (hw : Function.Injective (boundedMultiplier w)) : Function.Injective (weightedGreen w) := by
  intro f g hfg
  exact hw (spectralGreen_injective (hw hfg))

theorem weightedGreen_eigenspaces_dense (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) :
    (⨆ mu : ℂ, Module.End.eigenspace (weightedGreen w).toLinearMap mu).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (weightedGreen_compact w) (weightedGreen_symmetric w hw))

theorem weightedGreen_reflect (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (f : IntervalL2) :
    weightedGreen w (l2Reflect f) = l2Reflect (weightedGreen w f) := by
  change boundedMultiplier w (spectralGreen (boundedMultiplier w (l2Reflect f))) = _
  rw [boundedMultiplier_reflect w hw, spectralGreen_reflect, boundedMultiplier_reflect w hw]
  rfl

theorem weightedGreen_parity_invariant (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (s : ℂ) :
    ∀ f ∈ parityL2Submodule s, weightedGreen w f ∈ parityL2Submodule s := by
  intro f hf
  rw [parityL2Submodule, Module.End.mem_eigenspace_iff] at hf ⊢
  change l2Reflect f = s • f at hf
  change l2Reflect (weightedGreen w f) = s • weightedGreen w f
  rw [← weightedGreen_reflect w hw, hf, map_smul]

def weightedParityGreen (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (s : ℂ) : ParityL2 s →L[ℂ] ParityL2 s :=
  (weightedGreen w).restrict (weightedGreen_parity_invariant w hw s)

theorem weightedParityGreen_compact (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x) (s : ℂ) :
    IsCompactOperator (weightedParityGreen w hw s) :=
  (weightedGreen_compact w).restrict' (weightedGreen_parity_invariant w hw s)

theorem weightedParityGreen_symmetric (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) (s : ℂ) :
    (weightedParityGreen w hw s).IsSymmetric :=
  (weightedGreen_symmetric w hr).restrict_invariant (weightedGreen_parity_invariant w hw s)

theorem weightedParityGreen_eigenspaces_dense (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x) (s : ℂ) :
    (⨆ mu : ℂ, Module.End.eigenspace (weightedParityGreen w hw s).toLinearMap mu).topologicalClosure
      = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (weightedParityGreen_compact w hw s) (weightedParityGreen_symmetric w hw hr s))

theorem weightedGreen_eigenfunction_equation (a w : IntervalLInfinity) (s mu : ℂ)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (u : IntervalL2) (hu : l2Reflect u = s • u)
    (heigen : weightedGreen w u = mu • u) :
    mu • variableSobolevOperator a (spectralGreen (boundedMultiplier w u))
      (spectralGreen_memDirichletH2 (boundedMultiplier w u)).1 =
        spectralGreen (boundedMultiplier w u) := by
  let z := boundedMultiplier w u
  let y := spectralGreen z
  have hpar : l2Reflect z = s • z := by
    dsimp [z]
    rw [← boundedMultiplier_reflect w hw, hu, map_smul]
  have hinverse : -secondWeakDeriv y (spectralGreen_memDirichletH2 z).1 = z :=
    spectralGreen_right_inverse z
  have hop : variableSobolevOperator a y (spectralGreen_memDirichletH2 z).1 =
      channelPrincipal a s z := by
    have hd : secondWeakDeriv y (spectralGreen_memDirichletH2 z).1 = -z := by
      exact neg_eq_iff_eq_neg.mp hinverse
    simp only [variableSobolevOperator, hd, map_neg, hpar, map_smul,
      sub_neg_eq_add, neg_neg, channelPrincipal, add_apply,
      ContinuousLinearMap.id_apply, smul_apply]
  have he : boundedMultiplier w y = mu • u := heigen
  have hh := congrArg (fun f => channelPrincipal a s (boundedMultiplier w f)) he
  rw [channelPrincipal_weight_inverse a w s hinv y, map_smul, map_smul] at hh
  change mu • variableSobolevOperator a y (spectralGreen_memDirichletH2 z).1 = y
  rw [hop]
  exact hh.symm

theorem weightedGreen_eigenfunction_nonzero (w : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, w x ≠ 0) (u : IntervalL2) (hu : u ≠ 0) :
    spectralGreen (boundedMultiplier w u) ≠ 0 := by
  intro hz
  apply hu
  apply boundedMultiplier_injective w hw
  apply spectralGreen_injective
  simpa only [map_zero] using hz

theorem weightedGreen_eigenfunction (a w : IntervalLInfinity) (s mu : ℂ) (hmu : mu ≠ 0)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (u : IntervalL2) (hu : l2Reflect u = s • u)
    (heigen : weightedGreen w u = mu • u) :
    variableSobolevOperator a (spectralGreen (boundedMultiplier w u))
      (spectralGreen_memDirichletH2 (boundedMultiplier w u)).1 =
        mu⁻¹ • spectralGreen (boundedMultiplier w u) := by
  have he := weightedGreen_eigenfunction_equation a w s mu hw hinv u hu heigen
  calc
    _ = mu⁻¹ • (mu • variableSobolevOperator a (spectralGreen (boundedMultiplier w u))
      (spectralGreen_memDirichletH2 (boundedMultiplier w u)).1) := by
        rw [smul_smul, inv_mul_cancel₀ hmu, one_smul]
    _ = _ := congrArg (fun f => mu⁻¹ • f) he

end Involution
