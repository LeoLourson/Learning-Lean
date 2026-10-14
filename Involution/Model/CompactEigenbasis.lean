module

public import Involution.Model.ParityGreen
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Hilbert-базис из собственных векторов компактного симметричного оператора.
Строится объединением Hilbert-базисов замкнутых собственных подпространств;
полнота следует из спектральной теоремы Mathlib. -/

@[expose] public noncomputable section

open InnerProductSpace

namespace Involution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance eigenspace_complete (T : E →L[ℂ] E) (mu : ℂ) :
    CompleteSpace (Module.End.eigenspace T.toLinearMap mu) :=
  (ContinuousLinearMap.isClosed_eigenspace T mu).completeSpace_coe

def compactEigenbasisIndex (T : E →L[ℂ] E) (mu : ℂ) :
    Set (Module.End.eigenspace T.toLinearMap mu) :=
  Classical.choose (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap mu))

def eigenspaceHilbertBasis (T : E →L[ℂ] E) (mu : ℂ) :
    HilbertBasis (compactEigenbasisIndex T mu) ℂ (Module.End.eigenspace T.toLinearMap mu) :=
  Classical.choose (Classical.choose_spec
    (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap mu)))

abbrev CompactEigenbasisIndex (T : E →L[ℂ] E) := Σ mu : ℂ, compactEigenbasisIndex T mu

def compactEigenvector (T : E →L[ℂ] E) (i : CompactEigenbasisIndex T) : E :=
  eigenspaceHilbertBasis T i.1 i.2

theorem compactEigenvector_equation (T : E →L[ℂ] E) (i : CompactEigenbasisIndex T) :
    T (compactEigenvector T i) = i.1 • compactEigenvector T i :=
  Module.End.mem_eigenspace_iff.mp (eigenspaceHilbertBasis T i.1 i.2).property

theorem compactEigenvector_orthonormal (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    Orthonormal ℂ (compactEigenvector T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun mu => (eigenspaceHilbertBasis T mu).orthonormal)

theorem compactEigenvector_orthogonal_eq_bot (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    (Submodule.span ℂ (Set.range (compactEigenvector T)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have heig : x ∈ (⨆ mu : ℂ, Module.End.eigenspace T.toLinearMap mu)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    simp only [Submodule.mem_iInf]
    intro mu v hv
    let v' : Module.End.eigenspace T.toLinearMap mu := ⟨v, hv⟩
    let F : Module.End.eigenspace T.toLinearMap mu →L[ℂ] ℂ :=
      (innerSL ℂ x).comp (Module.End.eigenspace T.toLinearMap mu).subtypeL
    have hs := F.hasSum ((eigenspaceHilbertBasis T mu).hasSum_repr v')
    have hz (j : compactEigenbasisIndex T mu) :
        F ((eigenspaceHilbertBasis T mu).repr v' j • eigenspaceHilbertBasis T mu j) = 0 := by
      rw [map_smul]
      have hmem : compactEigenvector T ⟨mu, j⟩ ∈
          Submodule.span ℂ (Set.range (compactEigenvector T)) :=
        Submodule.subset_span ⟨⟨mu, j⟩, rfl⟩
      have hi' : inner ℂ (compactEigenvector T ⟨mu, j⟩) x = 0 := hx _ hmem
      have hi : inner ℂ x (compactEigenvector T ⟨mu, j⟩) = 0 := inner_eq_zero_symm.mp hi'
      change (eigenspaceHilbertBasis T mu).repr v' j •
        inner ℂ x (compactEigenvector T ⟨mu, j⟩) = 0
      rw [hi, smul_zero]
    have hzero : F v' = 0 := by
      rw [← hs.tsum_eq]
      simp only [hz, tsum_zero]
    change inner ℂ x v = 0 at hzero
    exact inner_eq_zero_symm.mp hzero
  rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hT] at heig
  exact heig

def compactEigenbasis (T : E →L[ℂ] E) (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    HilbertBasis (CompactEigenbasisIndex T) ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (compactEigenvector_orthonormal T hT)
    (compactEigenvector_orthogonal_eq_bot T hc hT)

theorem compactEigenbasis_apply (T : E →L[ℂ] E) (hc : IsCompactOperator T)
    (hT : T.IsSymmetric) (i : CompactEigenbasisIndex T) :
    compactEigenbasis T hc hT i = compactEigenvector T i :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

theorem compactEigenbasis_equation (T : E →L[ℂ] E) (hc : IsCompactOperator T)
    (hT : T.IsSymmetric) (i : CompactEigenbasisIndex T) :
    T (compactEigenbasis T hc hT i) = i.1 • compactEigenbasis T hc hT i := by
  rw [compactEigenbasis_apply]
  exact compactEigenvector_equation T i

theorem compactEigenbasis_eigenvalue_ne_zero (T : E →L[ℂ] E) (hc : IsCompactOperator T)
    (hT : T.IsSymmetric) (hinj : Function.Injective T) (i : CompactEigenbasisIndex T) :
    i.1 ≠ 0 := by
  intro hi
  have he := compactEigenbasis_equation T hc hT i
  rw [hi, zero_smul] at he
  have hzero : compactEigenbasis T hc hT i = 0 := hinj (by simpa only [map_zero] using he)
  have hn := (compactEigenbasis T hc hT).orthonormal.norm_eq_one i
  rw [hzero, norm_zero] at hn
  exact zero_ne_one hn

end Involution
