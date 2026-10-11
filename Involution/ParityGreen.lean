module

public import Involution.SpectralGreen
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-! Ограничение невзвешенного обратного оператора на замкнутые каналы отражения.
При s = 1 и s = -1 это чётный и нечётный каналы. Веса переменного `a` —
в `WeightedGreen.lean`. -/

@[expose] public noncomputable section

namespace Involution

def parityL2Submodule (s : ℂ) : Submodule ℂ IntervalL2 :=
  Module.End.eigenspace l2Reflect.toLinearMap s

abbrev ParityL2 (s : ℂ) := parityL2Submodule s

instance parityL2_completeSpace (s : ℂ) : CompleteSpace (ParityL2 s) :=
  (ContinuousLinearMap.isClosed_eigenspace l2Reflect.toContinuousLinearMap s).completeSpace_coe

theorem spectralGreen_parity_invariant (s : ℂ) :
    ∀ f ∈ parityL2Submodule s, spectralGreen f ∈ parityL2Submodule s := by
  intro f hf
  rw [parityL2Submodule, Module.End.mem_eigenspace_iff] at hf ⊢
  change l2Reflect f = s • f at hf
  change l2Reflect (spectralGreen f) = s • spectralGreen f
  rw [← spectralGreen_reflect, hf, map_smul]

def parityGreen (s : ℂ) : ParityL2 s →L[ℂ] ParityL2 s :=
  spectralGreen.restrict (spectralGreen_parity_invariant s)

theorem parityGreen_compact (s : ℂ) : IsCompactOperator (parityGreen s) :=
  spectralGreen_compact.restrict' (spectralGreen_parity_invariant s)

theorem parityGreen_symmetric (s : ℂ) : (parityGreen s).IsSymmetric :=
  spectralGreen_symmetric.restrict_invariant (spectralGreen_parity_invariant s)

theorem parityGreen_eigenspaces_dense (s : ℂ) :
    (⨆ mu : ℂ, Module.End.eigenspace (parityGreen s).toLinearMap mu).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (parityGreen_compact s) (parityGreen_symmetric s))

theorem parityGreen_injective (s : ℂ) : Function.Injective (parityGreen s) := by
  intro f g hfg
  apply Subtype.ext
  exact spectralGreen_injective (congrArg Subtype.val hfg)

end Involution
