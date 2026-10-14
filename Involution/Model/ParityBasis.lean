module

public import Involution.Model.MultiplicationEquiv
public import Involution.Setup.L2Parity

/-! Объединение Hilbert-базисов чётного и нечётного каналов в Hilbert-базис L₂.
Индексы двух каналов сохраняются раздельно, без группировки собственных значений. -/

@[expose] public noncomputable section

open InnerProductSpace

namespace Involution

variable {ι κ : Type*}

theorem parityL2_even (f : ParityL2 1) : l2Reflect (f : IntervalL2) = f := by
  have hf := Module.End.mem_eigenspace_iff.mp f.property
  change l2Reflect (f : IntervalL2) = (1 : ℂ) • (f : IntervalL2) at hf
  simpa only [one_smul] using hf

theorem parityL2_odd (f : ParityL2 (-1)) : l2Reflect (f : IntervalL2) = -(f : IntervalL2) := by
  have hf := Module.End.mem_eigenspace_iff.mp f.property
  change l2Reflect (f : IntervalL2) = (-1 : ℂ) • (f : IntervalL2) at hf
  simpa only [neg_one_smul] using hf

def parityBasisVector (be : HilbertBasis ι ℂ (ParityL2 1))
    (bo : HilbertBasis κ ℂ (ParityL2 (-1))) : ι ⊕ κ → IntervalL2 :=
  Sum.elim (fun i => be i) (fun j => bo j)

theorem parityBasisVector_orthonormal (be : HilbertBasis ι ℂ (ParityL2 1))
    (bo : HilbertBasis κ ℂ (ParityL2 (-1))) : Orthonormal ℂ (parityBasisVector be bo) := by
  constructor
  · intro i
    cases i with
    | inl i => exact be.orthonormal.norm_eq_one i
    | inr i => exact bo.orthonormal.norm_eq_one i
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact be.orthonormal.inner_eq_zero (fun h => hij (congrArg Sum.inl h))
      | inr j => exact l2Parity_orthogonal _ _ (parityL2_even (be i)) (parityL2_odd (bo j))
    | inr i =>
      cases j with
      | inl j =>
        exact inner_eq_zero_symm.mp
          (l2Parity_orthogonal _ _ (parityL2_even (be j)) (parityL2_odd (bo i)))
      | inr j => exact bo.orthonormal.inner_eq_zero (fun h => hij (congrArg Sum.inr h))

theorem parityBasisVector_orthogonal_eq_bot (be : HilbertBasis ι ℂ (ParityL2 1))
    (bo : HilbertBasis κ ℂ (ParityL2 (-1))) :
    (Submodule.span ℂ (Set.range (parityBasisVector be bo)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have he (i : ι) : inner ℂ (be i : IntervalL2) x = 0 :=
    hx _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  have ho (j : κ) : inner ℂ (bo j : IntervalL2) x = 0 :=
    hx _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have heall (v : ParityL2 1) : inner ℂ x (v : IntervalL2) = 0 := by
    let F : ParityL2 1 →L[ℂ] ℂ := (innerSL ℂ x).comp (parityL2Submodule 1).subtypeL
    have hs := F.hasSum (be.hasSum_repr v)
    have hz (i : ι) : F (be.repr v i • be i) = 0 := by
      rw [map_smul]
      change be.repr v i • inner ℂ x (be i : IntervalL2) = 0
      rw [inner_eq_zero_symm.mp (he i), smul_zero]
    have hzero : F v = 0 := by rw [← hs.tsum_eq]; simp only [hz, tsum_zero]
    exact hzero
  have hoall (v : ParityL2 (-1)) : inner ℂ x (v : IntervalL2) = 0 := by
    let F : ParityL2 (-1) →L[ℂ] ℂ := (innerSL ℂ x).comp (parityL2Submodule (-1)).subtypeL
    have hs := F.hasSum (bo.hasSum_repr v)
    have hz (j : κ) : F (bo.repr v j • bo j) = 0 := by
      rw [map_smul]
      change bo.repr v j • inner ℂ x (bo j : IntervalL2) = 0
      rw [inner_eq_zero_symm.mp (ho j), smul_zero]
    have hzero : F v = 0 := by rw [← hs.tsum_eq]; simp only [hz, tsum_zero]
    exact hzero
  let e : ParityL2 1 := ⟨l2EvenPart x, Module.End.mem_eigenspace_iff.mpr
    (by change l2Reflect (l2EvenPart x) = (1 : ℂ) • l2EvenPart x
        simpa only [one_smul] using l2EvenPart_fixed x)⟩
  let o : ParityL2 (-1) := ⟨l2OddPart x, Module.End.mem_eigenspace_iff.mpr
    (by change l2Reflect (l2OddPart x) = (-1 : ℂ) • l2OddPart x
        simpa only [neg_one_smul] using l2OddPart_neg x)⟩
  have hezero : inner ℂ x (l2EvenPart x) = 0 := heall e
  have hozero : inner ℂ x (l2OddPart x) = 0 := hoall o
  have hself : inner ℂ x x = 0 := by
    calc
      _ = inner ℂ x (l2EvenPart x + l2OddPart x) :=
        congrArg (inner ℂ x) (l2EvenPart_add_l2OddPart x).symm
      _ = 0 := by rw [inner_add_right, hezero, hozero, add_zero]
  change x = 0
  exact inner_self_eq_zero.mp hself

def parityHilbertBasis (be : HilbertBasis ι ℂ (ParityL2 1))
    (bo : HilbertBasis κ ℂ (ParityL2 (-1))) : HilbertBasis (ι ⊕ κ) ℂ IntervalL2 :=
  HilbertBasis.mkOfOrthogonalEqBot (parityBasisVector_orthonormal be bo)
    (parityBasisVector_orthogonal_eq_bot be bo)

theorem parityHilbertBasis_apply (be : HilbertBasis ι ℂ (ParityL2 1))
    (bo : HilbertBasis κ ℂ (ParityL2 (-1))) (i : ι ⊕ κ) :
    parityHilbertBasis be bo i = parityBasisVector be bo i :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

end Involution
