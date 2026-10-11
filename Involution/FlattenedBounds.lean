module

public import Involution.BracketBounds
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Переход от целых конечных блоков к произвольным конечным наборам векторов.
Коэффициенты вне выбранного набора дополняются нулями. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Involution

variable {J : Type*} {K : J → Type*} [∀ j, Fintype (K j)]

open Classical in
theorem sum_padded_sigma {M : Type*} [AddCommMonoid M]
    (s : Finset (Σ j, K j)) (F : (Σ j, K j) → M) :
    (∑ j ∈ s.image Sigma.fst, ∑ k : K j, if (⟨j, k⟩ : Σ j, K j) ∈ s then F ⟨j, k⟩ else 0) =
      ∑ i ∈ s, F i := by
  classical
  have hsub : s ⊆ (s.image Sigma.fst).sigma (fun j => (Finset.univ : Finset (K j))) := by
    intro i hi
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, Finset.mem_univ _⟩
  rw [Finset.sum_sigma' (s.image Sigma.fst) (fun j => (Finset.univ : Finset (K j)))
    (fun j k => if (⟨j, k⟩ : Σ j, K j) ∈ s then F ⟨j, k⟩ else 0)]
  calc
    _ = ∑ i ∈ s, if i ∈ s then F i else 0 :=
      (Finset.sum_subset hsub (fun i _ hi => ite_eq_right hi)).symm
    _ = _ := Finset.sum_congr rfl (fun i hi => ite_eq_left hi)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {V : J → Submodule ℂ E}

def FiniteRieszBounds {ι : Type*} (v : ι → E) (m M : ℝ) : Prop :=
  ∀ (s : Finset ι) (c : ι → ℂ),
    m * (∑ i ∈ s, ‖c i‖ ^ 2) ≤ ‖∑ i ∈ s, c i • v i‖ ^ 2 ∧
      ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ M * (∑ i ∈ s, ‖c i‖ ^ 2)

theorem finiteRiesz_linearCombination_injective {ι : Type*} (v : ι → E)
    (m M : ℝ) (hm : 0 < m) (h : FiniteRieszBounds v m M) :
    Function.Injective (Finsupp.linearCombination ℂ v) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro c hc
  have hs : (∑ i ∈ c.support, c i • v i) = 0 := hc
  have hb := (h c.support c).1
  rw [hs, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hb
  have hn : 0 ≤ ∑ i ∈ c.support, ‖c i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : (∑ i ∈ c.support, ‖c i‖ ^ 2) = 0 := by nlinarith
  ext i
  by_cases hi : i ∈ c.support
  · have hle := Finset.single_le_sum (fun j _ => sq_nonneg ‖c j‖) hi
    rw [hz] at hle
    have hci : ‖c i‖ = 0 := by nlinarith [norm_nonneg (c i)]
    exact norm_eq_zero.mp hci
  · exact Finsupp.notMem_support_iff.mp hi

theorem globalBlockBounds_finiteRiesz (e : ∀ j, K j → V j) (m M : ℝ)
    (h : GlobalBlockBounds e m M) : FiniteRieszBounds (flattenedBlockVector e) m M := by
  classical
  intro s c
  let c' : ∀ j, K j → ℂ := fun j k => if (⟨j, k⟩ : Σ j, K j) ∈ s then c ⟨j, k⟩ else 0
  have hb := h (s.image Sigma.fst) c'
  have henergy : (∑ j ∈ s.image Sigma.fst, blockCoefficientEnergy c' j) = ∑ i ∈ s, ‖c i‖ ^ 2 := by
    convert sum_padded_sigma s (fun i => ‖c i‖ ^ 2) using 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [c']
    split_ifs <;> simp
  have hsynthesis : (∑ j ∈ s.image Sigma.fst, (blockSynthesis e c' j : E)) =
      ∑ i ∈ s, c i • flattenedBlockVector e i := by
    convert sum_padded_sigma s (fun i => c i • flattenedBlockVector e i) using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [blockSynthesis, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (if (⟨j, k⟩ : Σ j, K j) ∈ s then c ⟨j, k⟩ else 0) • (e j k : E) = _
    split_ifs <;> simp only [flattenedBlockVector, zero_smul]
  rw [henergy, hsynthesis] at hb
  exact hb

theorem uniformBlockBounds_finiteRiesz (b : RieszBasisWithBrackets V)
    (e : ∀ j, K j → V j) (m M : ℝ) (h : UniformBlockBounds e m M) :
    FiniteRieszBounds (flattenedBlockVector e) (b.lower * m) (b.upper * M) :=
  globalBlockBounds_finiteRiesz e _ _ (uniformBlockBounds_global b e m M h)

theorem finiteRiesz_globalBlockBounds (e : ∀ j, K j → V j) (m M : ℝ)
    (h : FiniteRieszBounds (flattenedBlockVector e) m M) : GlobalBlockBounds e m M := by
  classical
  intro t c
  have hb := h (t.sigma (fun j => (Finset.univ : Finset (K j)))) (fun i => c i.1 i.2)
  simpa only [Finset.sum_sigma, blockCoefficientEnergy, blockSynthesis,
    flattenedBlockVector, Submodule.coe_sum, Submodule.coe_smul] using hb

theorem exists_uniformBlockBounds_iff_finiteRiesz (b : RieszBasisWithBrackets V)
    (e : ∀ j, K j → V j) :
    (∃ m M : ℝ, 0 < m ∧ 0 < M ∧ UniformBlockBounds e m M) ↔
      (∃ m M : ℝ, 0 < m ∧ 0 < M ∧ FiniteRieszBounds (flattenedBlockVector e) m M) := by
  constructor
  · rintro ⟨m, M, hm, hM, h⟩
    exact ⟨b.lower * m, b.upper * M, mul_pos b.lower_pos hm, mul_pos b.upper_pos hM,
      uniformBlockBounds_finiteRiesz b e m M h⟩
  · rintro ⟨m, M, hm, hM, h⟩
    exact ⟨m, M, hm, hM, globalBlockBounds_uniform e m M
      (finiteRiesz_globalBlockBounds e m M h)⟩

end Involution
