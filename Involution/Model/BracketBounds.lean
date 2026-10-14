module

public import Involution.Model.RieszBasis
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Базис Рисса со скобками и количественный критерий снятия скобок.
Блоки конечномерны, их суммарное пространство плотно; общей границы размеров
блоков не предполагается. Здесь проверяются неравенства для конечных сумм;
глобальный координатный изоморфизм построен в `Involution.Model.FiniteSynthesis`. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Involution

variable {J : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Геометрический базис Рисса конечномерных подпространств. -/
structure RieszBasisWithBrackets (V : J → Submodule ℂ E) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  finite : ∀ j, FiniteDimensional ℂ (V j)
  total : (⨆ j, V j).topologicalClosure = ⊤
  bounds : ∀ (t : Finset J) (v : ∀ j, V j),
    lower * (∑ j ∈ t, ‖v j‖ ^ 2) ≤ ‖∑ j ∈ t, (v j : E)‖ ^ 2 ∧
      ‖∑ j ∈ t, (v j : E)‖ ^ 2 ≤ upper * (∑ j ∈ t, ‖v j‖ ^ 2)

variable {K : J → Type*} [∀ j, Fintype (K j)] {V : J → Submodule ℂ E}

def blockSynthesis (e : ∀ j, K j → V j) (c : ∀ j, K j → ℂ) (j : J) : V j :=
  ∑ k, c j k • e j k

def blockCoefficientEnergy (c : ∀ j, K j → ℂ) (j : J) : ℝ := ∑ k, ‖c j k‖ ^ 2

def UniformBlockBounds (e : ∀ j, K j → V j) (m M : ℝ) : Prop :=
  ∀ (j : J) (c : K j → ℂ),
    m * (∑ k, ‖c k‖ ^ 2) ≤ ‖∑ k, c k • e j k‖ ^ 2 ∧
      ‖∑ k, c k • e j k‖ ^ 2 ≤ M * (∑ k, ‖c k‖ ^ 2)

def GlobalBlockBounds (e : ∀ j, K j → V j) (m M : ℝ) : Prop :=
  ∀ (t : Finset J) (c : ∀ j, K j → ℂ),
    m * (∑ j ∈ t, blockCoefficientEnergy c j) ≤
      ‖∑ j ∈ t, (blockSynthesis e c j : E)‖ ^ 2 ∧
    ‖∑ j ∈ t, (blockSynthesis e c j : E)‖ ^ 2 ≤
      M * (∑ j ∈ t, blockCoefficientEnergy c j)

theorem uniformBlockBounds_global (b : RieszBasisWithBrackets V)
    (e : ∀ j, K j → V j) (m M : ℝ) (h : UniformBlockBounds e m M) :
    GlobalBlockBounds e (b.lower * m) (b.upper * M) := by
  intro t c
  have hb := b.bounds t (blockSynthesis e c)
  have hl : m * (∑ j ∈ t, blockCoefficientEnergy c j) ≤
      ∑ j ∈ t, ‖blockSynthesis e c j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (h j (c j)).1
  have hu : (∑ j ∈ t, ‖blockSynthesis e c j‖ ^ 2) ≤
      M * (∑ j ∈ t, blockCoefficientEnergy c j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (h j (c j)).2
  constructor
  · calc
      _ = b.lower * (m * ∑ j ∈ t, blockCoefficientEnergy c j) := mul_assoc _ _ _
      _ ≤ b.lower * (∑ j ∈ t, ‖blockSynthesis e c j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hl b.lower_pos.le
      _ ≤ _ := hb.1
  · calc
      _ ≤ b.upper * (∑ j ∈ t, ‖blockSynthesis e c j‖ ^ 2) := hb.2
      _ ≤ b.upper * (M * ∑ j ∈ t, blockCoefficientEnergy c j) :=
        mul_le_mul_of_nonneg_left hu b.upper_pos.le
      _ = _ := (mul_assoc _ _ _).symm

theorem globalBlockBounds_uniform (e : ∀ j, K j → V j) (m M : ℝ)
    (h : GlobalBlockBounds e m M) : UniformBlockBounds e m M := by
  classical
  intro j c
  let c' : ∀ i, K i → ℂ := Function.update (fun _ _ => 0) j c
  have hj := h {j} c'
  simpa only [Finset.sum_singleton, blockCoefficientEnergy, blockSynthesis,
    c', Function.update_self, Submodule.norm_coe] using hj

theorem exists_uniformBlockBounds_iff_global (b : RieszBasisWithBrackets V)
    (e : ∀ j, K j → V j) :
    (∃ m M : ℝ, 0 < m ∧ 0 < M ∧ UniformBlockBounds e m M) ↔
      (∃ m M : ℝ, 0 < m ∧ 0 < M ∧ GlobalBlockBounds e m M) := by
  constructor
  · rintro ⟨m, M, hm, hM, h⟩
    exact ⟨b.lower * m, b.upper * M, mul_pos b.lower_pos hm, mul_pos b.upper_pos hM,
      uniformBlockBounds_global b e m M h⟩
  · rintro ⟨m, M, hm, hM, h⟩
    exact ⟨m, M, hm, hM, globalBlockBounds_uniform e m M h⟩

def flattenedBlockVector (e : ∀ j, K j → V j) (i : Σ j, K j) : E := e i.1 i.2

omit [∀ j, Fintype (K j)] in
theorem flattenedBlockVector_dense (b : RieszBasisWithBrackets V)
    (e : ∀ j, K j → V j) (hspan : ∀ j, Submodule.span ℂ (Set.range (e j)) = ⊤) :
    (Submodule.span ℂ (Set.range (flattenedBlockVector e))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (flattenedBlockVector e))
  have hblocks : ∀ j, V j ≤ S := by
    intro j v hv
    have hs : Submodule.span ℂ (Set.range (e j)) ≤ S.comap (V j).subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨⟨j, k⟩, rfl⟩
    rw [hspan j] at hs
    exact hs (show (⟨v, hv⟩ : V j) ∈ (⊤ : Submodule ℂ (V j)) from trivial)
  have hd := Submodule.topologicalClosure_mono (iSup_le hblocks)
  rw [b.total] at hd
  exact top_le_iff.mp hd

theorem RieszBasisWithBrackets.finite_sum_eq_zero (b : RieszBasisWithBrackets V)
    (t : Finset J) (v : ∀ j, V j) (hsum : (∑ j ∈ t, (v j : E)) = 0) :
    ∀ j ∈ t, v j = 0 := by
  have hb := (b.bounds t v).1
  rw [hsum, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hb
  have hnonneg : 0 ≤ ∑ j ∈ t, ‖v j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : (∑ j ∈ t, ‖v j‖ ^ 2) = 0 := by
    nlinarith [b.lower_pos]
  intro j hj
  have hle : ‖v j‖ ^ 2 ≤ ∑ i ∈ t, ‖v i‖ ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) hj
  rw [hz] at hle
  have hn : ‖v j‖ = 0 := by nlinarith [norm_nonneg (v j)]
  exact norm_eq_zero.mp hn

end Involution
