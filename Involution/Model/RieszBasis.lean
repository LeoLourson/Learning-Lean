module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Базис Рисса как ограниченный обратимый оператор синтеза из ℓ².
Доказан перенос базиса ограниченным обратимым оператором. -/

@[expose] public noncomputable section

namespace Involution

open scoped lp

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Координатное представление обычного базиса Рисса, без группировки. -/
structure RieszBasis (ι : Type*) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  repr : E ≃L[ℂ] ℓ²(ι, ℂ)

namespace RieszBasis

def vector (b : RieszBasis ι E) (i : ι) : E := by
  classical
  exact b.repr.symm (lp.single 2 i (1 : ℂ))

open Classical in
theorem repr_vector (b : RieszBasis ι E) (i : ι) :
    b.repr (b.vector i) = lp.single 2 i (1 : ℂ) := by
  classical
  exact b.repr.apply_symm_apply _

open Classical in
theorem synthesis_single (b : RieszBasis ι E) (i : ι) (c : ℂ) :
    b.repr.symm (lp.single 2 i c) = c • b.vector i := by
  classical
  have h := lp.single_smul (E := fun _ : ι => ℂ) 2 i c (1 : ℂ)
  simp only [smul_eq_mul, mul_one] at h
  rw [h, map_smul]
  rfl

theorem hasSum_synthesis (b : RieszBasis ι E) (c : ℓ²(ι, ℂ)) :
    HasSum (fun i => c i • b.vector i) (b.repr.symm c) := by
  classical
  have h := b.repr.symm.toContinuousLinearMap.hasSum
    (lp.hasSum_single (by simp : (2 : ENNReal) ≠ ⊤) c)
  simpa only [ContinuousLinearEquiv.coe_coe, synthesis_single] using h

theorem hasSum_coordinates (b : RieszBasis ι E) (x : E) :
    HasSum (fun i => b.repr x i • b.vector i) x := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using b.hasSum_synthesis (b.repr x)

theorem synthesis_injective (b : RieszBasis ι E) (c d : ℓ²(ι, ℂ))
    (h : b.repr.symm c = b.repr.symm d) : c = d := b.repr.symm.injective h

theorem synthesis_norm_bound (b : RieszBasis ι E) (c : ℓ²(ι, ℂ)) :
    ‖b.repr.symm c‖ ≤ ‖b.repr.symm.toContinuousLinearMap‖ * ‖c‖ :=
  b.repr.symm.toContinuousLinearMap.le_opNorm c

theorem analysis_norm_bound (b : RieszBasis ι E) (c : ℓ²(ι, ℂ)) :
    ‖c‖ ≤ ‖b.repr.toContinuousLinearMap‖ * ‖b.repr.symm c‖ := by
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
    b.repr.toContinuousLinearMap.le_opNorm (b.repr.symm c)

theorem dense_span (b : RieszBasis ι E) :
    (Submodule.span ℂ (Set.range b.vector)).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine mem_closure_of_tendsto (b.hasSum_coordinates x) ?_
  exact Filter.Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

def map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : RieszBasis ι E) (T : E ≃L[ℂ] F) : RieszBasis ι F :=
  ⟨T.symm.trans b.repr⟩

theorem map_vector {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : RieszBasis ι E) (T : E ≃L[ℂ] F) (i : ι) :
    (b.map T).vector i = T (b.vector i) := by
  classical
  rfl

end RieszBasis

def rieszBasisOfHilbertBasis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (T : H ≃L[ℂ] E) : RieszBasis ι E :=
  ⟨T.symm.trans b.repr.toContinuousLinearEquiv⟩

theorem rieszBasisOfHilbertBasis_vector {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (T : H ≃L[ℂ] E) (i : ι) :
    (rieszBasisOfHilbertBasis b T).vector i = T (b i) := by
  classical
  rfl

end Involution
