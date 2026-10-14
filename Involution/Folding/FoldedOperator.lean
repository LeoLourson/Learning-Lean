module

public import Involution.Folding.FoldedSobolev
public import Involution.Folding.VariableOperator

/-! Переменный двухкомпонентный оператор на собственной слабой области.
Вторая производная определяется по данным каждой компоненты и не зависит
от выбора представителей. Унитарная редукция доказана на всей слабой области. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

def FoldedDirichletData.secondDeriv {U : FoldedL2} (d : FoldedDirichletData U) : FoldedL2 :=
  WithLp.toLp 2 (d.hu₂.toLp d.u₂, d.hv₂.toLp d.v₂)

theorem FoldedDirichletData.secondDeriv_eq {U : FoldedL2}
    (d e : FoldedDirichletData U) : d.secondDeriv = e.secondDeriv := by
  obtain ⟨_, _, hu, hv⟩ := d.derivatives_unique e
  apply WithLp.ofLp_injective 2
  exact Prod.ext (MemLp.toLp_congr d.hu₂ e.hu₂ hu) (MemLp.toLp_congr d.hv₂ e.hv₂ hv)

def foldedSecondWeakDeriv (U : FoldedL2) (hU : MemFoldedDirichletH2 U) : FoldedL2 :=
  hU.some.secondDeriv

theorem foldedSecondWeakDeriv_eq_data {U : FoldedL2} (hU : MemFoldedDirichletH2 U)
    (d : FoldedDirichletData U) : foldedSecondWeakDeriv U hU = d.secondDeriv :=
  hU.some.secondDeriv_eq d

theorem foldedSecondWeakDeriv_fold (f : IntervalL2) (hf : MemDirichletH2 f)
    (hU : MemFoldedDirichletH2 (l2Fold f)) :
    foldedSecondWeakDeriv (l2Fold f) hU = l2Fold (secondWeakDeriv f hf.1) := by
  let d := hU.some
  let G := firstWeakDeriv f hf.1
  let D := secondWeakDeriv f hf.1
  have hFG := firstWeakDeriv_spec f hf.1
  have hGD := secondWeakDeriv_spec f hf.1
  have hpos : Ioo (0 : ℝ) 1 ⊆ Ioo (-1) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hdu : d.u =ᵐ[halfIntervalMeasure] f := d.hu_rep.trans (l2Fold_fst_ae f)
  have hdv : d.v =ᵐ[halfIntervalMeasure] reflect f := d.hv_rep.trans (l2Fold_snd_ae f)
  have hu₁ : d.u₁ =ᵐ[halfIntervalMeasure] G := HasWeakDerivOn.unique isOpen_Ioo
    (d.hu.congr hdu Filter.EventuallyEq.rfl) (hFG.restrict hpos)
  have hu₂ : d.u₂ =ᵐ[halfIntervalMeasure] D := HasWeakDerivOn.unique isOpen_Ioo
    (d.hu₁.congr hu₁ Filter.EventuallyEq.rfl) (hGD.restrict hpos)
  have hv₁ : d.v₁ =ᵐ[halfIntervalMeasure] -reflect G := HasWeakDerivOn.unique isOpen_Ioo
    (d.hv.congr hdv Filter.EventuallyEq.rfl) (HasWeakDerivOn.reflect hFG |>.restrict hpos)
  have hR : HasWeakDerivOn (Ioo 0 1) (-reflect G) (reflect D) := by
    simpa only [neg_neg] using (HasWeakDerivOn.reflect hGD).neg.restrict hpos
  have hv₂ : d.v₂ =ᵐ[halfIntervalMeasure] reflect D := HasWeakDerivOn.unique isOpen_Ioo
    (d.hv₁.congr hv₁ Filter.EventuallyEq.rfl) hR
  change d.secondDeriv = l2Fold D
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply Lp.ext
    exact (d.hu₂.coeFn_toLp.trans hu₂).trans (l2Fold_fst_ae D).symm
  · apply Lp.ext
    exact (d.hv₂.coeFn_toLp.trans hv₂).trans (l2Fold_snd_ae D).symm

def foldedSobolevOperator (a : IntervalLInfinity) (U : FoldedL2)
    (hU : MemFoldedDirichletH2 U) : FoldedL2 :=
  -foldedPrincipal a (foldedSecondWeakDeriv U hU)

theorem variableSobolevOperator_unitary_reduction (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemDirichletH2 f) :
    l2Fold (variableSobolevOperator a f hf.1) =
      foldedSobolevOperator a (l2Fold f) hf.fold := by
  rw [foldedSobolevOperator, foldedSecondWeakDeriv_fold f hf hf.fold]
  exact variableSobolevOperator_fold a f hf.1

theorem variableSobolevOperator_shift_reduction (a : IntervalLInfinity) (f g : IntervalL2)
    (hf : MemDirichletH2 f) (lam : ℂ) :
    variableSobolevOperator a f hf.1 = lam • f + g ↔
      foldedSobolevOperator a (l2Fold f) hf.fold = lam • l2Fold f + l2Fold g := by
  have hmap : l2Fold (lam • f + g) = lam • l2Fold f + l2Fold g := by
    rw [map_add, map_smul]
  rw [← variableSobolevOperator_unitary_reduction a f hf, ← hmap]
  exact l2Fold.injective.eq_iff.symm

theorem variableSobolevOperator_eigen_reduction (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemDirichletH2 f) (lam : ℂ) :
    variableSobolevOperator a f hf.1 = lam • f ↔
      foldedSobolevOperator a (l2Fold f) hf.fold = lam • l2Fold f := by
  simpa only [map_zero, add_zero] using variableSobolevOperator_shift_reduction a f 0 hf lam

end Involution
