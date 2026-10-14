module

public import Involution.Model.BlockPerturbation
public import Involution.Model.BracketBounds
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Инвариантные подпространства возмущённого оператора и базис Рисса со скобками.
Образы блочных подпространств при подобии `U` конечномерны, инвариантны и образуют
базис Рисса подпространств. Инвариантность записана через ограниченные операторы:
для `v ∈ V k` найдётся `g` с `R² g = v` и `g + Ŝ R g ∈ V k`, то есть `v` лежит в
области и `(G + S) v ∈ V k`. -/

@[expose] public noncomputable section

namespace Involution

section Orthogonal

variable {J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sq_sum_of_orthogonal (t : Finset J) (h : J → E)
    (horth : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → inner ℂ (h j) (h k) = 0) :
    ‖∑ j ∈ t, h j‖ ^ 2 = ∑ j ∈ t, ‖h j‖ ^ 2 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → inner ℂ (h j) (h k) = 0 := fun j hj k hk hjk =>
      horth j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hzero : inner ℂ (h a) (∑ j ∈ s, h j) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      exact horth a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
        (fun haj => ha (haj ▸ hj))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih hs, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hzero

/-- Образ полной ортогональной системы конечномерных подпространств при ограниченном
обратимом операторе есть базис Рисса подпространств. -/
def rieszBracketsOfOrthogonal (W : J → Submodule ℂ E)
    (hfin : ∀ j, FiniteDimensional ℂ (W j))
    (horth : ∀ j k, j ≠ k → ∀ x ∈ W j, ∀ y ∈ W k, inner ℂ x y = 0)
    (htotal : (⨆ j, W j).topologicalClosure = ⊤) (U : E ≃L[ℂ] E) :
    RieszBasisWithBrackets (fun j => (W j).map (U : E →L[ℂ] E).toLinearMap) where
  lower := ((1 + ‖(U : E →L[ℂ] E)‖) ^ 2 * (1 + ‖(U.symm : E →L[ℂ] E)‖) ^ 2)⁻¹
  upper := (1 + ‖(U : E →L[ℂ] E)‖) ^ 2 * (1 + ‖(U.symm : E →L[ℂ] E)‖) ^ 2
  lower_pos := by positivity
  upper_pos := by positivity
  finite := fun j => by
    have := hfin j
    infer_instance
  total := by
    rw [eq_top_iff]
    intro y _
    have hy : U.symm y ∈ ((⨆ j, W j).topologicalClosure : Set E) := by
      rw [htotal]
      trivial
    have hmap : Set.MapsTo U ((⨆ j, W j : Submodule ℂ E) : Set E)
        ((⨆ j, (W j).map (U : E →L[ℂ] E).toLinearMap : Submodule ℂ E) : Set E) := by
      intro z hz
      have hz' : U z ∈ (⨆ j, W j).map (U : E →L[ℂ] E).toLinearMap := ⟨z, hz, rfl⟩
      rwa [Submodule.map_iSup] at hz'
    have h := map_mem_closure U.continuous hy hmap
    rwa [ContinuousLinearEquiv.apply_symm_apply] at h
  bounds := by
    intro t v
    set cU := 1 + ‖(U : E →L[ℂ] E)‖ with hcU
    set cV := 1 + ‖(U.symm : E →L[ℂ] E)‖ with hcV
    have hcU0 : 0 < cU := by positivity
    have hcV0 : 0 < cV := by positivity
    have hU : ∀ x : E, ‖U x‖ ≤ cU * ‖x‖ := fun x =>
      ((U : E →L[ℂ] E).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
    have hV : ∀ x : E, ‖U.symm x‖ ≤ cV * ‖x‖ := fun x =>
      ((U.symm : E →L[ℂ] E).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
    let h : J → E := fun j => U.symm (v j : E)
    have hmem : ∀ j, h j ∈ W j := by
      intro j
      obtain ⟨x, hx, hxv⟩ := (v j).property
      have he : h j = x := by
        change U.symm (v j : E) = x
        rw [← hxv]
        exact U.symm_apply_apply x
      rw [he]
      exact hx
    have hUh : ∀ j, U (h j) = (v j : E) := fun j => U.apply_symm_apply _
    have hsum : (∑ j ∈ t, (v j : E)) = U (∑ j ∈ t, h j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (hUh j).symm
    have hpyth : ‖∑ j ∈ t, h j‖ ^ 2 = ∑ j ∈ t, ‖h j‖ ^ 2 :=
      norm_sq_sum_of_orthogonal t h fun j _ k _ hjk => horth j k hjk _ (hmem j) _ (hmem k)
    have hA : (∑ j ∈ t, ‖v j‖ ^ 2) ≤ cU ^ 2 * ∑ j ∈ t, ‖h j‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hj := hU (h j)
      rw [hUh j] at hj
      rw [← Submodule.norm_coe, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hj 2
    have hB : (∑ j ∈ t, ‖h j‖ ^ 2) ≤ cV ^ 2 * ∑ j ∈ t, ‖v j‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hj := hV (v j : E)
      rw [← Submodule.norm_coe, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hj 2
    have hN : ‖∑ j ∈ t, (v j : E)‖ ^ 2 ≤ cU ^ 2 * ∑ j ∈ t, ‖h j‖ ^ 2 := by
      rw [hsum, ← hpyth, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hU _) 2
    have hS : (∑ j ∈ t, ‖h j‖ ^ 2) ≤ cV ^ 2 * ‖∑ j ∈ t, (v j : E)‖ ^ 2 := by
      have hs : (∑ j ∈ t, h j) = U.symm (∑ j ∈ t, (v j : E)) := by
        rw [hsum]
        exact (U.symm_apply_apply _).symm
      rw [← hpyth, hs, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hV _) 2
    have hc : 0 < cU ^ 2 * cV ^ 2 := by positivity
    constructor
    · rw [inv_mul_le_iff₀ hc]
      calc
        (∑ j ∈ t, ‖v j‖ ^ 2) ≤ cU ^ 2 * ∑ j ∈ t, ‖h j‖ ^ 2 := hA
        _ ≤ cU ^ 2 * (cV ^ 2 * ‖∑ j ∈ t, (v j : E)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
        _ = _ := by ring
    · calc
        ‖∑ j ∈ t, (v j : E)‖ ^ 2 ≤ cU ^ 2 * ∑ j ∈ t, ‖h j‖ ^ 2 := hN
        _ ≤ cU ^ 2 * (cV ^ 2 * ∑ j ∈ t, ‖v j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
        _ = _ := by ring

end Orthogonal

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Подпространство, натянутое на базисные векторы одного блока. -/
def blockSpace (b : HilbertBasis ι ℂ H) (blk : ι → ℕ) (k : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (b '' {i | blk i = k})

omit [CompleteSpace H] in
theorem blockSpace_finiteDimensional (b : HilbertBasis ι ℂ H) (blk : ι → ℕ) (k : ℕ)
    (hfin : {i | blk i = k}.Finite) : FiniteDimensional ℂ (blockSpace b blk k) :=
  FiniteDimensional.span_of_finite ℂ (hfin.image b)

omit [CompleteSpace H] in
theorem blockSpace_orthogonal (b : HilbertBasis ι ℂ H) (blk : ι → ℕ) (j k : ℕ) (hjk : j ≠ k) :
    ∀ x ∈ blockSpace b blk j, ∀ y ∈ blockSpace b blk k, inner ℂ x y = 0 := by
  have hle : blockSpace b blk k ≤ (blockSpace b blk j)ᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have hle' : blockSpace b blk j ≤ (Submodule.span ℂ {b l})ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      refine b.orthonormal.inner_eq_zero fun hil => hjk ?_
      have hi' : blk i = j := hi
      have hl' : blk l = k := hl
      rw [← hi', ← hl', hil]
    intro x hx
    have h := hle' hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h
    exact inner_eq_zero_symm.mp h
  intro x hx y hy
  exact (hle hy) x hx

omit [CompleteSpace H] in
theorem blockSpace_total (b : HilbertBasis ι ℂ H) (blk : ι → ℕ) :
    (⨆ k, blockSpace b blk k).topologicalClosure = ⊤ := by
  have hle : Submodule.span ℂ (Set.range b) ≤ ⨆ k, blockSpace b blk k := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (fun k => blockSpace b blk k) (blk i))
      (Submodule.subset_span ⟨i, rfl, rfl⟩)
  have h := Submodule.topologicalClosure_mono hle
  rw [b.dense_span] at h
  exact top_le_iff.mp h

namespace SpectralBlocks

variable (D : SpectralBlocks ι) (b : HilbertBasis ι ℂ H)

open Classical in
/-- Символ оператора `G` на одном блоке. -/
def blockSqSymbol (k : ℕ) (i : ι) : ℂ := if D.blk i = k then ((D.ω i ^ 2 : ℝ) : ℂ) else 0

theorem blockSqSymbol_norm_le (k : ℕ) (i : ι) : ‖D.blockSqSymbol k i‖ ≤ D.ξ (k + 1) ^ 2 := by
  unfold blockSqSymbol
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := D.upper i
    rw [h] at h1
    exact pow_le_pow_left₀ (D.ω_pos i).le (by linarith [D.δ_pos]) 2
  · rw [norm_zero]
    positivity

omit [CompleteSpace H] in
theorem invFreq_apply_basis (i : ι) : D.invFreq b (b i) = D.rho i • b i :=
  diagOp_apply_basis b D.rho _ D.rho_norm_le i

omit [CompleteSpace H] in
/-- На блоке оператор `R²` обратим: `R² (G_k h) = h`, причём `G_k h` остаётся в блоке. -/
theorem blockSpace_preimage (k : ℕ) :
    ∀ h ∈ blockSpace b D.blk k, diagOp b (D.blockSqSymbol k) h ∈ blockSpace b D.blk k ∧
      D.invFreq b (D.invFreq b (diagOp b (D.blockSqSymbol k) h)) = h := by
  let T : H →ₗ[ℂ] H := (diagOp b (D.blockSqSymbol k)).toLinearMap
  let Q : H →ₗ[ℂ] H := (D.invFreq b * D.invFreq b * diagOp b (D.blockSqSymbol k)).toLinearMap
  have hle : blockSpace b D.blk k ≤
      (blockSpace b D.blk k).comap T ⊓ LinearMap.eqLocus Q LinearMap.id := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi' : D.blk i = k := hi
    have hT : diagOp b (D.blockSqSymbol k) (b i) = ((D.ω i ^ 2 : ℝ) : ℂ) • b i := by
      rw [diagOp_apply_basis b (D.blockSqSymbol k) _ (D.blockSqSymbol_norm_le k) i]
      unfold blockSqSymbol
      rw [ite_eq_left hi']
    refine ⟨?_, ?_⟩
    · change diagOp b (D.blockSqSymbol k) (b i) ∈ blockSpace b D.blk k
      rw [hT]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · change D.invFreq b (D.invFreq b (diagOp b (D.blockSqSymbol k) (b i))) = b i
      rw [hT, map_smul, map_smul, D.invFreq_apply_basis b i, map_smul,
        D.invFreq_apply_basis b i, smul_smul, smul_smul, D.rho_eq i]
      have hne : (D.ω i : ℂ) ≠ 0 := by exact_mod_cast (D.ω_pos i).ne'
      have hone : ((D.ω i ^ 2 : ℝ) : ℂ) * (D.ω i : ℂ)⁻¹ * (D.ω i : ℂ)⁻¹ = 1 := by
        push_cast
        field_simp
      rw [hone, one_smul]
  intro h hh
  exact hle hh

omit [CompleteSpace H] in
/-- Оператор без внеблочных матричных элементов сохраняет конечный блок. -/
theorem blockSpace_invariant_of_entries (k : ℕ) (hfin : {i | D.blk i = k}.Finite)
    (Dg : H →L[ℂ] H) (hDg : ∀ i l, D.blk i ≠ D.blk l → opEntry b Dg i l = 0) :
    ∀ h ∈ blockSpace b D.blk k, Dg h ∈ blockSpace b D.blk k := by
  have hfd := blockSpace_finiteDimensional b D.blk k hfin
  have hclosed : IsClosed (blockSpace b D.blk k : Set H) :=
    (blockSpace b D.blk k).closed_of_finiteDimensional
  have hle : blockSpace b D.blk k ≤ (blockSpace b D.blk k).comap Dg.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have hl' : D.blk l = k := hl
    change Dg (b l) ∈ blockSpace b D.blk k
    refine hclosed.mem_of_tendsto (b.hasSum_repr (Dg (b l))) (Filter.Eventually.of_forall ?_)
    intro s
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : D.blk i = k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · have hz : b.repr (Dg (b l)) i = 0 := by
        rw [b.repr_apply_apply]
        exact hDg i l (fun h => hi (h.trans hl'))
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  intro h hh
  exact hle hh

/-- Инвариантные блоки возмущённого оператора. -/
theorem exists_invariant_blocks (S : H →L[ℂ] H) (hS : 40 * ‖S‖ ≤ D.δ)
    (hfin : ∀ k, {i | D.blk i = k}.Finite) :
    ∃ U : H ≃L[ℂ] H, ∀ k, ∀ v ∈ (blockSpace b D.blk k).map (U : H →L[ℂ] H).toLinearMap,
      ∃ g : H, D.invFreq b (D.invFreq b g) = v ∧
        g + S (D.invFreq b g) ∈ (blockSpace b D.blk k).map (U : H →L[ℂ] H).toLinearMap := by
  obtain ⟨U, M, Dg, h1, h2, h3⟩ := D.exists_block_similarity b S hS
  let Ue : H ≃L[ℂ] H := ContinuousLinearEquiv.equivOfInverse (U : H →L[ℂ] H)
    ((U⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)
    (fun x => by
      have h := congrArg (fun T : H →L[ℂ] H => T x) (Units.inv_mul U)
      exact h)
    (fun x => by
      have h := congrArg (fun T : H →L[ℂ] H => T x) (Units.mul_inv U)
      exact h)
  refine ⟨Ue, ?_⟩
  rintro k _ ⟨h, hh, rfl⟩
  obtain ⟨hmem, hinv⟩ := D.blockSpace_preimage b k h hh
  set h' := diagOp b (D.blockSqSymbol k) h with hh'
  have hD := D.blockSpace_invariant_of_entries b k (hfin k) Dg h3 h' hmem
  refine ⟨M h', ?_, ?_⟩
  · have e1 := congrArg (fun T : H →L[ℂ] H => T h') h1
    change (U : H →L[ℂ] H) (D.invFreq b (D.invFreq b h')) =
      D.invFreq b (D.invFreq b (M h')) at e1
    rw [← e1, hinv]
    rfl
  · have e2 := congrArg (fun T : H →L[ℂ] H => T h') h2
    change M h' + S (D.invFreq b (M h')) = (U : H →L[ℂ] H) (h' + Dg h') at e2
    rw [e2]
    exact ⟨h' + Dg h', Submodule.add_mem _ hmem hD, rfl⟩

/-- Базис Рисса со скобками из инвариантных конечномерных подпространств. -/
theorem exists_bracket_basis (S : H →L[ℂ] H) (hS : 40 * ‖S‖ ≤ D.δ)
    (hfin : ∀ k, {i | D.blk i = k}.Finite) :
    ∃ V : ℕ → Submodule ℂ H, Nonempty (RieszBasisWithBrackets V) ∧
      ∀ k, ∀ v ∈ V k, ∃ g : H, D.invFreq b (D.invFreq b g) = v ∧
        g + S (D.invFreq b g) ∈ V k := by
  obtain ⟨U, hU⟩ := D.exists_invariant_blocks b S hS hfin
  exact ⟨fun k => (blockSpace b D.blk k).map (U : H →L[ℂ] H).toLinearMap,
    ⟨rieszBracketsOfOrthogonal (fun k => blockSpace b D.blk k)
      (fun k => blockSpace_finiteDimensional b D.blk k (hfin k))
      (fun j k hjk => blockSpace_orthogonal b D.blk j k hjk)
      (blockSpace_total b D.blk) U⟩, hU⟩

end SpectralBlocks

end Involution
