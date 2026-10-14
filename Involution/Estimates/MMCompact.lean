module

public import Involution.Estimates.MMOperators
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Compactness of `K₀ = G⁻¹` when the eigenvalues tend to infinity, and finite-dimensionality
of ranges of compact idempotents. -/

@[expose] public noncomputable section

open Complex Set Filter Topology

namespace Involution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Rank-one operators are compact. -/
theorem isCompactOperator_rankOne (u v : H) :
    IsCompactOperator (fun x : H => inner ℂ u x • v) := by
  have h1 : IsCompactOperator (id : ℂ → ℂ) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).mpr inferInstance
  have h2 := (h1.comp_clm (innerSL ℂ u)).clm_comp (ContinuousLinearMap.toSpanSingleton ℂ v)
  convert h2 using 1
  funext x
  simp

omit [CompleteSpace H] in
/-- The range of a compact idempotent is finite-dimensional. -/
theorem finiteDimensional_range_of_compact_idem (P : H →L[ℂ] H) (hP : IsCompactOperator P)
    (hid : P * P = P) : FiniteDimensional ℂ (LinearMap.range (P : H →ₗ[ℂ] H)) := by
  set V := LinearMap.range (P : H →ₗ[ℂ] H)
  have hfix : ∀ v ∈ V, P v = v := by
    rintro v ⟨u, rfl⟩
    change (P * P) u = P u
    rw [hid]
  have hVcl : IsClosed (V : Set H) := by
    have : (V : Set H) = {v | P v = v} := by
      ext v; exact ⟨hfix v, fun h => ⟨v, h⟩⟩
    rw [this]
    exact isClosed_eq P.continuous continuous_id
  apply FiniteDimensional.of_isCompact_closedBall₀ ℂ (r := 1) one_pos
  rw [Subtype.isCompact_iff]
  have hsub : ((↑) : V → H) '' Metric.closedBall 0 1 ⊆ closure (P '' Metric.closedBall 0 1) := by
    rintro _ ⟨v, hv, rfl⟩
    refine subset_closure ⟨v, ?_, hfix v v.2⟩
    simpa using hv
  refine (hP.isCompact_closure_image_closedBall 1).of_isClosed_subset ?_ hsub
  have he : ((↑) : V → H) '' Metric.closedBall 0 1 = (V : Set H) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v.2, by simpa using hv⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h1⟩, by simpa using h2, rfl⟩
  rw [he]
  exact hVcl.inter Metric.isClosed_closedBall

namespace MMData

variable {ι : Type*} (D : MMData ι H)

/-- `K₀` is compact when only finitely many eigenvalues lie below any bound. -/
theorem isCompact_K (hfin : ∀ t : ℝ, {i | D.lam i ≤ t}.Finite) : IsCompactOperator D.K₀ := by
  classical
  -- truncations
  let Kt : ℕ → (H →L[ℂ] H) := fun n => ∑ i ∈ (hfin n).toFinset,
    (((D.lam i)⁻¹ : ℝ) : ℂ) •
      (ContinuousLinearMap.toSpanSingleton ℂ (D.b i)).comp (innerSL ℂ (D.b i))
  have hKt : ∀ n, IsCompactOperator (Kt n) := by
    intro n
    have : ∀ s : Finset ι, IsCompactOperator (⇑(∑ i ∈ s, (((D.lam i)⁻¹ : ℝ) : ℂ) •
        (ContinuousLinearMap.toSpanSingleton ℂ (D.b i)).comp (innerSL ℂ (D.b i)))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using isCompactOperator_zero
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        refine IsCompactOperator.add ?_ ih
        refine IsCompactOperator.smul ?_ _
        convert isCompactOperator_rankOne (D.b a) (D.b a) using 1
        funext x
        simp
    exact this _
  have hKtb : ∀ n j, Kt n (D.b j) =
      (if D.lam j ≤ n then (((D.lam j)⁻¹ : ℝ) : ℂ) else 0) • D.b j := by
    intro n j
    simp only [Kt, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    by_cases h : D.lam j ≤ n
    · simp only [h, ↓reduceIte]
      rw [Finset.sum_eq_single j]
      · simp [D.b.orthonormal.1 j]
      · intro i _ hij
        rw [orthonormal_iff_ite.mp D.b.orthonormal i j]; simp [hij]
      · intro hj
        exact absurd ((hfin n).mem_toFinset.mpr h) hj
    · simp only [h, ↓reduceIte, zero_smul]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hij : i ≠ j := fun e => h (e ▸ (hfin n).mem_toFinset.mp hi)
      rw [orthonormal_iff_ite.mp D.b.orthonormal i j]; simp [hij]
  have hdist : ∀ n : ℕ, 0 < (n : ℝ) → ‖D.K₀ - Kt n‖ ≤ (n : ℝ)⁻¹ := by
    intro n hn
    let φ : ι → ℂ := fun j => if D.lam j ≤ n then 0 else (((D.lam j)⁻¹ : ℝ) : ℂ)
    have hφ : ∀ j, ‖φ j‖ ≤ (n : ℝ)⁻¹ := by
      intro j
      simp only [φ]
      split_ifs with h
      · simp [hn.le]
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.lam_pos j))]
        exact inv_anti₀ hn (le_of_lt (not_le.mp h))
    have he : D.K₀ - Kt n = diagOp D.b φ := by
      apply clm_ext_basis D.b
      intro j
      rw [sub_apply, D.hK, hKtb, diagOp_apply_basis D.b φ _ hφ, ← sub_smul]
      congr 1
      simp only [φ]; split_ifs <;> simp
    rw [he]
    exact diagOp_norm_le D.b φ _ (inv_nonneg.mpr hn.le) hφ
  have ht : Tendsto Kt atTop (𝓝 D.K₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_nhds_zero_nat
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [norm_norm, norm_sub_rev]
    exact hdist n (by exact_mod_cast hn)
  exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto ht (Eventually.of_forall hKt)

end MMData

end Involution
