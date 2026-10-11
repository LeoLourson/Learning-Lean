module

public import Involution.SpectralGreen
public import Involution.BlockMultiplier
public import Involution.SparseCuts

/-! Линейная оценка счётной функции частот для операторов вида `W₁ G W₂`,
где `G` — обратный оператор Дирихле. Принцип минимакса не используется:
`G` приближается срезкой своего спектрального разложения, а число больших
собственных значений оценивается рангом приближения. -/

@[expose] public noncomputable section

namespace Involution

/-- Номер модели внутри своего канала. -/
def modeIndex : ℕ ⊕ ℕ → ℕ := Sum.elim id id

theorem modelDirichletEigenvalue_ge (i : ℕ ⊕ ℕ) (N : ℕ) (hN : N ≤ modeIndex i) :
    ((N : ℝ) * Real.pi) ^ 2 ≤ constantModelEigenvalue 0 i := by
  have hpi := Real.pi_pos
  cases i with
  | inl n =>
    have hn : (N : ℝ) ≤ n := by exact_mod_cast hN
    simp only [constantModelEigenvalue, Sum.elim_inl, add_zero, one_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hpi.le) 2
  | inr n =>
    have hn : (N : ℝ) ≤ n := by exact_mod_cast hN
    simp only [constantModelEigenvalue, Sum.elim_inr, sub_zero, one_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hpi.le) 2

theorem modelGreenWeight_norm_le_one (i : ℕ ⊕ ℕ) : ‖modelGreenWeight i‖ ≤ 1 := by
  rw [modelGreenWeight_norm]
  apply inv_le_one_of_one_le₀
  have hpi := Real.two_le_pi
  cases i with
  | inl n =>
    simp only [constantModelEigenvalue, Sum.elim_inl, add_zero, one_mul]
    have h : (1 : ℝ) ≤ ((n : ℝ) + 1 / 2) * Real.pi := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    exact one_le_pow₀ h
  | inr n =>
    simp only [constantModelEigenvalue, Sum.elim_inr, sub_zero, one_mul]
    have h : (1 : ℝ) ≤ ((n : ℝ) + 1) * Real.pi := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    exact one_le_pow₀ h

theorem modelGreenWeight_norm_le_tail (i : ℕ ⊕ ℕ) (N : ℕ) (hN0 : 1 ≤ N)
    (hN : N ≤ modeIndex i) : ‖modelGreenWeight i‖ ≤ (((N : ℝ) * Real.pi) ^ 2)⁻¹ := by
  rw [modelGreenWeight_norm]
  have hpos : 0 < ((N : ℝ) * Real.pi) ^ 2 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN0
    have := Real.pi_pos
    positivity
  exact inv_anti₀ hpos (modelDirichletEigenvalue_ge i N hN)

theorem spectralGreen_eq_diagOp :
    spectralGreen = diagOp constantModelHilbertBasis modelGreenWeight := by
  apply opEntry_ext constantModelHilbertBasis
  intro j i
  unfold opEntry
  rw [inner_basis_diagOp constantModelHilbertBasis modelGreenWeight 1
    modelGreenWeight_norm_le_one, constantModelHilbertBasis_coe]
  exact spectralGreen_coefficient _ j

open Classical in
/-- Младшая часть спектрального разложения: моды с номером меньше `N`. -/
def greenHeadSymbol (N : ℕ) (i : ℕ ⊕ ℕ) : ℂ := if modeIndex i < N then modelGreenWeight i else 0

open Classical in
/-- Хвост спектрального разложения. -/
def greenTailSymbol (N : ℕ) (i : ℕ ⊕ ℕ) : ℂ := if modeIndex i < N then 0 else modelGreenWeight i

theorem greenHeadSymbol_norm_le (N : ℕ) (i : ℕ ⊕ ℕ) : ‖greenHeadSymbol N i‖ ≤ 1 := by
  unfold greenHeadSymbol
  split_ifs
  · exact modelGreenWeight_norm_le_one i
  · simp

theorem greenTailSymbol_norm_le (N : ℕ) (hN : 1 ≤ N) (i : ℕ ⊕ ℕ) :
    ‖greenTailSymbol N i‖ ≤ (((N : ℝ) * Real.pi) ^ 2)⁻¹ := by
  unfold greenTailSymbol
  split_ifs with h
  · rw [norm_zero]
    positivity
  · exact modelGreenWeight_norm_le_tail i N hN (not_lt.mp h)

theorem spectralGreen_head_add_tail (N : ℕ) (hN : 1 ≤ N) :
    spectralGreen = diagOp constantModelHilbertBasis (greenHeadSymbol N) +
      diagOp constantModelHilbertBasis (greenTailSymbol N) := by
  rw [spectralGreen_eq_diagOp]
  apply opEntry_ext constantModelHilbertBasis
  intro j i
  rw [opEntry_add]
  unfold opEntry
  rw [inner_basis_diagOp constantModelHilbertBasis modelGreenWeight 1 modelGreenWeight_norm_le_one,
    inner_basis_diagOp constantModelHilbertBasis (greenHeadSymbol N) 1
      (greenHeadSymbol_norm_le N),
    inner_basis_diagOp constantModelHilbertBasis (greenTailSymbol N) _
      (greenTailSymbol_norm_le N hN), ← add_mul]
  congr 1
  unfold greenHeadSymbol greenTailSymbol
  split_ifs <;> simp

/-- Множество мод с номером меньше `N`. -/
def modeHead (N : ℕ) : Finset (ℕ ⊕ ℕ) := (Finset.range N).disjSum (Finset.range N)

theorem mem_modeHead (N : ℕ) (i : ℕ ⊕ ℕ) : i ∈ modeHead N ↔ modeIndex i < N := by
  cases i <;> simp [modeHead, modeIndex]

theorem card_modeHead (N : ℕ) : (modeHead N).card = 2 * N := by
  simp [modeHead, two_mul]

/-- Младшая часть имеет образ в линейной оболочке первых мод. -/
theorem greenHead_range (N : ℕ) (x : IntervalL2) :
    diagOp constantModelHilbertBasis (greenHeadSymbol N) x ∈
      Submodule.span ℂ (Set.range fun j : ↥(modeHead N) => constantModelHilbertBasis j) := by
  set P := Submodule.span ℂ (Set.range fun j : ↥(modeHead N) => constantModelHilbertBasis j)
    with hP
  have hfd : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hclosed : IsClosed (P : Set IntervalL2) := P.closed_of_finiteDimensional
  refine hclosed.mem_of_tendsto
    (constantModelHilbertBasis.hasSum_repr
      (diagOp constantModelHilbertBasis (greenHeadSymbol N) x))
    (Filter.Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : modeIndex j < N
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨j, (mem_modeHead N j).mpr hj⟩, rfl⟩
  · have hz : constantModelHilbertBasis.repr
        (diagOp constantModelHilbertBasis (greenHeadSymbol N) x) j = 0 := by
      rw [constantModelHilbertBasis.repr_apply_apply,
        inner_basis_diagOp constantModelHilbertBasis (greenHeadSymbol N) 1
          (greenHeadSymbol_norm_le N)]
      unfold greenHeadSymbol
      rw [ite_eq_right hj, zero_mul]
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

/-- Число собственных значений `W₁ G W₂`, не меньших `1 / t²`, растёт не быстрее
`(2 ν / π) t + 2`, если `‖W₁‖, ‖W₂‖ ≤ ν`. -/
theorem green_sandwich_eigen_count (W₁ W₂ : IntervalL2 →L[ℂ] IntervalL2) (ν : ℝ) (hν : 0 < ν)
    (h₁ : ‖W₁‖ ≤ ν) (h₂ : ‖W₂‖ ≤ ν) {ι : Type*} (u : ι → IntervalL2) (hu : Orthonormal ℂ u)
    (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hK : ∀ i, W₁ (spectralGreen (W₂ (u i))) = (((lam i)⁻¹ : ℝ) : ℂ) • u i)
    (t : ℝ) (ht : 0 ≤ t) (s : Finset ι) (hs : ∀ i ∈ s, lam i ≤ t ^ 2) :
    (s.card : ℝ) ≤ 2 * ν / Real.pi * t + 2 := by
  have hpi := Real.pi_pos
  rcases ht.eq_or_lt with ht0 | ht0
  · have hempty : s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      have h := hs i hi
      rw [← ht0] at h
      have := hlam i
      norm_num at h
      linarith
    rw [hempty, Finset.card_empty, ← ht0]
    norm_num
  set N := ⌊ν * t / Real.pi⌋₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNlt : ν * t / Real.pi < N := by
    rw [hNdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hNle : (N : ℝ) ≤ ν * t / Real.pi + 1 := by
    rw [hNdef]
    push_cast
    have := Nat.floor_le (a := ν * t / Real.pi) (by positivity)
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set F₀ := diagOp constantModelHilbertBasis (greenHeadSymbol N) with hF₀
  set E₀ := diagOp constantModelHilbertBasis (greenTailSymbol N) with hE₀
  have hsplit : spectralGreen = F₀ + E₀ := spectralGreen_head_add_tail N hN1
  set P := Submodule.span ℂ (Set.range fun j : ↥(modeHead N) => constantModelHilbertBasis j)
    with hP
  have hfdP : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hrankP : Module.finrank ℂ P ≤ 2 * N := by
    calc
      Module.finrank ℂ P ≤ Fintype.card ↥(modeHead N) :=
        finrank_range_le_card fun j : ↥(modeHead N) => constantModelHilbertBasis j
      _ = (modeHead N).card := Fintype.card_coe _
      _ = 2 * N := card_modeHead N
  have hrank : Module.finrank ℂ (P.map W₁.toLinearMap) ≤ 2 * N :=
    (Submodule.finrank_map_le _ _).trans hrankP
  have hE : ‖W₁ ∘L E₀ ∘L W₂‖ < (t ^ 2)⁻¹ := by
    have hE₀norm : ‖E₀‖ ≤ (((N : ℝ) * Real.pi) ^ 2)⁻¹ :=
      diagOp_norm_le constantModelHilbertBasis (greenTailSymbol N) _ (by positivity)
        (greenTailSymbol_norm_le N hN1)
    have hNpi : 0 < (N : ℝ) * Real.pi := by positivity
    have h1 : ‖W₁ ∘L E₀ ∘L W₂‖ ≤ ν * ((((N : ℝ) * Real.pi) ^ 2)⁻¹ * ν) := by
      calc
        ‖W₁ ∘L E₀ ∘L W₂‖ ≤ ‖W₁‖ * ‖E₀ ∘L W₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖W₁‖ * (‖E₀‖ * ‖W₂‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ ≤ ν * ((((N : ℝ) * Real.pi) ^ 2)⁻¹ * ν) :=
          mul_le_mul h₁ (mul_le_mul hE₀norm h₂ (norm_nonneg _) (by positivity))
            (by positivity) hν.le
    have hlt : ν * t < (N : ℝ) * Real.pi := by
      rwa [div_lt_iff₀ hpi] at hNlt
    have h2 : ν * ((((N : ℝ) * Real.pi) ^ 2)⁻¹ * ν) < (t ^ 2)⁻¹ := by
      have hsq : (ν * t) ^ 2 < ((N : ℝ) * Real.pi) ^ 2 :=
        pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      rw [← mul_assoc, mul_comm ν, mul_assoc, inv_mul_lt_iff₀ (by positivity),
        lt_mul_inv_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt h1 h2
  have hcard : s.card ≤ 2 * N := by
    refine card_le_of_finiteRank_approx (W₁ ∘L spectralGreen ∘L W₂) (W₁ ∘L F₀ ∘L W₂)
      (W₁ ∘L E₀ ∘L W₂) ?_ (P.map W₁.toLinearMap) (2 * N) hrank ?_ u hu
      (fun i => (((lam i)⁻¹ : ℝ) : ℂ)) hK (t ^ 2)⁻¹ hE s ?_
    · refine ContinuousLinearMap.ext fun x => ?_
      change W₁ (spectralGreen (W₂ x)) = W₁ (F₀ (W₂ x)) + W₁ (E₀ (W₂ x))
      rw [hsplit]
      exact map_add W₁ _ _
    · intro x
      exact ⟨F₀ (W₂ x), greenHead_range N (W₂ x), rfl⟩
    · intro i hi
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam i))]
      exact inv_anti₀ (hlam i) (hs i hi)
  have hcardR : (s.card : ℝ) ≤ 2 * N := by exact_mod_cast hcard
  calc
    (s.card : ℝ) ≤ 2 * N := hcardR
    _ ≤ 2 * (ν * t / Real.pi + 1) := by linarith
    _ = 2 * ν / Real.pi * t + 2 := by ring

end Involution
