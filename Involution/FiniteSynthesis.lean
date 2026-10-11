module

public import Involution.FlattenedBounds
public import Mathlib.Analysis.Normed.Operator.Extend

/-! Продолжение конечного синтеза до координатного изоморфизма `ℓ² → E`
(`LinearEquiv.extend`) и критерий снятия скобок. -/

@[expose] public noncomputable section

open scoped BigOperators lp ComplexInnerProductSpace

namespace Involution

variable {ι : Type*}

def coordinateHilbertBasis : HilbertBasis ι ℂ ℓ²(ι, ℂ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

def finiteCoordinateEmbedding : (ι →₀ ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) :=
  Finsupp.linearCombination ℂ coordinateHilbertBasis

open Classical in
theorem finiteCoordinateEmbedding_single (i : ι) :
    finiteCoordinateEmbedding (Finsupp.single i (1 : ℂ)) = lp.single 2 i (1 : ℂ) := by
  change Finsupp.linearCombination ℂ coordinateHilbertBasis (Finsupp.single i 1) = _
  rw [Finsupp.linearCombination_single, one_smul]
  rfl

theorem finiteCoordinateSum_norm_sq (s : Finset ι) (c : ι → ℂ) :
    ‖∑ i ∈ s, c i • coordinateHilbertBasis i‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [coordinateHilbertBasis.orthonormal.inner_sum]
  simp [Complex.conj_mul', ← Complex.ofReal_pow]

theorem finiteCoordinateEmbedding_norm_sq (c : ι →₀ ℂ) :
    ‖finiteCoordinateEmbedding c‖ ^ 2 = ∑ i ∈ c.support, ‖c i‖ ^ 2 := by
  classical
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  change Complex.re ⟪Finsupp.linearCombination ℂ coordinateHilbertBasis c,
    Finsupp.linearCombination ℂ coordinateHilbertBasis c⟫ = _
  rw [coordinateHilbertBasis.orthonormal.inner_finsupp_eq_sum_left]
  simp [Finsupp.sum, Complex.conj_mul', ← Complex.ofReal_pow]

theorem finiteCoordinateEmbedding_dense : DenseRange (@finiteCoordinateEmbedding ι) := by
  change Dense (Set.range (Finsupp.linearCombination ℂ (@coordinateHilbertBasis ι)))
  rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr coordinateHilbertBasis.dense_span

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem finiteRiesz_synthesis_norm_bounds (v : ι → E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 < M) (h : FiniteRieszBounds v m M) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ v c‖ ≤ Real.sqrt M * ‖finiteCoordinateEmbedding c‖ ∧
      ‖finiteCoordinateEmbedding c‖ ≤ (Real.sqrt m)⁻¹ * ‖Finsupp.linearCombination ℂ v c‖ := by
  classical
  have hb := h c.support c
  change m * (∑ i ∈ c.support, ‖c i‖ ^ 2) ≤ ‖Finsupp.linearCombination ℂ v c‖ ^ 2 ∧
    ‖Finsupp.linearCombination ℂ v c‖ ^ 2 ≤ M * (∑ i ∈ c.support, ‖c i‖ ^ 2) at hb
  rw [← finiteCoordinateEmbedding_norm_sq c] at hb
  have hsm := Real.sq_sqrt hm.le
  have hsM := Real.sq_sqrt hM.le
  have hpos := Real.sqrt_pos.mpr hm
  constructor
  · nlinarith [norm_nonneg (Finsupp.linearCombination ℂ v c),
      norm_nonneg (finiteCoordinateEmbedding c), Real.sqrt_nonneg M,
      mul_nonneg (Real.sqrt_nonneg M) (norm_nonneg (finiteCoordinateEmbedding c))]
  · rw [mul_comm (Real.sqrt m)⁻¹]
    apply (le_mul_inv_iff₀ hpos).mpr
    nlinarith [norm_nonneg (Finsupp.linearCombination ℂ v c),
      norm_nonneg (finiteCoordinateEmbedding c),
      mul_nonneg (Real.sqrt_nonneg m) (norm_nonneg (finiteCoordinateEmbedding c))]

theorem finiteSynthesis_dense (v : ι → E)
    (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    DenseRange (LinearMap.range (Finsupp.linearCombination ℂ v)).subtype := by
  change Dense (Set.range (LinearMap.range (Finsupp.linearCombination ℂ v)).subtype)
  rw [← LinearMap.coe_range, Submodule.range_subtype, Finsupp.range_linearCombination]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htotal

variable [CompleteSpace E]

theorem finiteRiesz_exists_synthesis_equiv (v : ι → E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 < M) (h : FiniteRieszBounds v m M)
    (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    ∃ T : ℓ²(ι, ℂ) ≃L[ℂ] E,
      ∀ c : ι →₀ ℂ, T (finiteCoordinateEmbedding c) = Finsupp.linearCombination ℂ v c := by
  let S := Finsupp.linearCombination ℂ v
  let f := LinearEquiv.ofInjective S (finiteRiesz_linearCombination_injective v m M hm h)
  let e₁ := @finiteCoordinateEmbedding ι
  let e₂ := (LinearMap.range S).subtype
  have hd₁ : DenseRange e₁ := finiteCoordinateEmbedding_dense
  have hd₂ : DenseRange e₂ := finiteSynthesis_dense v htotal
  have hn₁ : ∃ C, ∀ c, ‖e₂ (f c)‖ ≤ C * ‖e₁ c‖ := by
    refine ⟨Real.sqrt M, fun c => ?_⟩
    exact (finiteRiesz_synthesis_norm_bounds v m M hm hM h c).1
  have hn₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖ := by
    refine ⟨(Real.sqrt m)⁻¹, fun x => ?_⟩
    have hx : S (f.symm x) = e₂ x := by
      exact congrArg (fun y : LinearMap.range S => (y : E)) (f.apply_symm_apply x)
    have hb := (finiteRiesz_synthesis_norm_bounds v m M hm hM h (f.symm x)).2
    change ‖e₁ (f.symm x)‖ ≤ (Real.sqrt m)⁻¹ * ‖S (f.symm x)‖ at hb
    rwa [hx] at hb
  exact ⟨f.extend e₁ e₂ hd₁ hn₁ hd₂ hn₂, fun c =>
    f.extend_eq e₁ e₂ hd₁ hn₁ hd₂ hn₂ c⟩

theorem finiteRiesz_exists_rieszBasis (v : ι → E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 < M) (h : FiniteRieszBounds v m M)
    (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    ∃ b : RieszBasis ι E, ∀ i, b.vector i = v i := by
  classical
  obtain ⟨T, hT⟩ := finiteRiesz_exists_synthesis_equiv v m M hm hM h htotal
  refine ⟨⟨T.symm⟩, fun i => ?_⟩
  have hi := hT (Finsupp.single i 1)
  rw [finiteCoordinateEmbedding_single, Finsupp.linearCombination_single, one_smul] at hi
  exact hi

omit [CompleteSpace E] in
theorem RieszBasis.exists_finiteRieszBounds (b : RieszBasis ι E) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ FiniteRieszBounds b.vector m M := by
  classical
  let A := ‖b.repr.toContinuousLinearMap‖ + 1
  let B := ‖b.repr.symm.toContinuousLinearMap‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(A⁻¹)^2, B^2, sq_pos_of_pos (inv_pos.mpr hA), sq_pos_of_pos hB, ?_⟩
  intro s c
  let x := ∑ i ∈ s, c i • b.vector i
  have hrepr : b.repr x = ∑ i ∈ s, c i • coordinateHilbertBasis i := by
    simp only [x, map_sum, map_smul, b.repr_vector]
    rfl
  have he : ‖b.repr x‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
    rw [hrepr, finiteCoordinateSum_norm_sq]
  have hl : ‖b.repr x‖ ≤ A * ‖x‖ := by
    calc
      _ ≤ ‖b.repr.toContinuousLinearMap‖ * ‖x‖ := b.repr.toContinuousLinearMap.le_opNorm x
      _ ≤ _ := by dsimp [A]; nlinarith [norm_nonneg x]
  have hu : ‖x‖ ≤ B * ‖b.repr x‖ := by
    calc
      _ ≤ ‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr x‖ := by
        simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
          using b.synthesis_norm_bound (b.repr x)
      _ ≤ _ := by dsimp [B]; nlinarith [norm_nonneg (b.repr x)]
  have hl' : A⁻¹ * ‖b.repr x‖ ≤ ‖x‖ := by
    rw [mul_comm A⁻¹, ← div_eq_mul_inv]
    exact (div_le_iff₀ hA).mpr (by simpa [mul_comm] using hl)
  rw [← he]
  change (A⁻¹)^2 * ‖b.repr x‖ ^ 2 ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ B^2 * ‖b.repr x‖ ^ 2
  constructor
  · nlinarith [mul_nonneg (inv_nonneg.mpr hA.le) (norm_nonneg (b.repr x)), norm_nonneg x]
  · nlinarith [mul_nonneg hB.le (norm_nonneg (b.repr x)), norm_nonneg x]

theorem exists_rieszBasis_iff_finiteBounds_dense (v : ι → E) :
    (∃ b : RieszBasis ι E, ∀ i, b.vector i = v i) ↔
      ((Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ ∧
        ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ FiniteRieszBounds v m M) := by
  constructor
  · rintro ⟨b, hb⟩
    have hv : b.vector = v := funext hb
    rw [← hv]
    exact ⟨b.dense_span, b.exists_finiteRieszBounds⟩
  · rintro ⟨htotal, m, M, hm, hM, h⟩
    exact finiteRiesz_exists_rieszBasis v m M hm hM h htotal

theorem exists_rieszBasis_iff_uniformBlockBounds {J : Type*} {K : J → Type*}
    [∀ j, Fintype (K j)] {V : J → Submodule ℂ E} (b : RieszBasisWithBrackets V)
    (e : ∀ j, K j → V j) (hspan : ∀ j, Submodule.span ℂ (Set.range (e j)) = ⊤) :
    (∃ r : RieszBasis (Σ j, K j) E, ∀ i, r.vector i = flattenedBlockVector e i) ↔
      (∃ m M : ℝ, 0 < m ∧ 0 < M ∧ UniformBlockBounds e m M) := by
  rw [exists_rieszBasis_iff_finiteBounds_dense]
  have hd := flattenedBlockVector_dense b e hspan
  simp only [hd, true_and]
  exact (exists_uniformBlockBounds_iff_finiteRiesz b e).symm

end Involution
