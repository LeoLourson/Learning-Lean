module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Диагональные операторы и мультипликаторы Шура в гильбертовом базисе.
Оператор задаётся матричными элементами `opEntry`; мультипликатор `m` ограничен
константой `C`, если поэлементное умножение матрицы на `m` снова даёт ограниченный
оператор нормы не больше `C ‖X‖`. -/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Матричный элемент оператора в гильбертовом базисе. -/
def opEntry (b : HilbertBasis ι ℂ H) (X : H →L[ℂ] H) (i l : ι) : ℂ :=
  inner ℂ (b i) (X (b l))

omit [CompleteSpace H] in
/-- Оператор определяется своими матричными элементами. -/
theorem opEntry_ext (b : HilbertBasis ι ℂ H) {X Y : H →L[ℂ] H}
    (h : ∀ i l, opEntry b X i l = opEntry b Y i l) : X = Y := by
  apply ContinuousLinearMap.ext_on (s := Set.range b)
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  · rintro _ ⟨l, rfl⟩
    apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply]
    exact h i l

omit [CompleteSpace H] in
/-- Операторы, совпадающие на базисных векторах, равны. -/
theorem clm_ext_basis (b : HilbertBasis ι ℂ H) {X Y : H →L[ℂ] H}
    (h : ∀ i, X (b i) = Y (b i)) : X = Y := by
  apply ContinuousLinearMap.ext_on (s := Set.range b)
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  · rintro _ ⟨i, rfl⟩
    exact h i

omit [CompleteSpace H] in
/-- Оценка нормы оператора через суммы квадратов координат (Парсеваль). -/
theorem norm_le_of_coord_sum_le (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (x : H) (s : Finset ι), ∑ i ∈ s, ‖inner ℂ (b i) (T x)‖ ^ 2 ≤ (K * ‖x‖) ^ 2) :
    ‖T‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  rw [← b.repr.norm_map]
  refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun s => ?_
  simpa [Real.rpow_two, HilbertBasis.repr_apply_apply] using h x s

omit [CompleteSpace H] in
/-- Построение ограниченного оператора по линейному набору координат. -/
theorem exists_of_coord (b : HilbertBasis ι ℂ H) (c : H →ₗ[ℂ] (ι → ℂ)) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (x : H) (s : Finset ι), ∑ i ∈ s, ‖c x i‖ ^ 2 ≤ (K * ‖x‖) ^ 2) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ K ∧ ∀ i x, inner ℂ (b i) (T x) = c x i := by
  have hmem : ∀ x, Memℓp (c x) 2 := fun x =>
    memℓp_gen' (C := (K * ‖x‖) ^ 2) (fun s => by simpa [Real.rpow_two] using h x s)
  let L : H →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun x => ⟨c x, hmem x⟩
      map_add' := fun x y => by
        ext i
        change c (x + y) i = c x i + c y i
        rw [map_add]; rfl
      map_smul' := fun a x => by
        ext i
        change c (a • x) i = a • c x i
        rw [map_smul]; rfl }
  let T0 : H →ₗ[ℂ] H := b.repr.symm.toLinearEquiv.toLinearMap ∘ₗ L
  have hT0 : ∀ i x, inner ℂ (b i) (T0 x) = c x i := by
    intro i x
    rw [← HilbertBasis.repr_apply_apply]
    simp [T0, L]
  have hbd : ∀ x, ‖T0 x‖ ≤ K * ‖x‖ := by
    intro x
    rw [← b.repr.norm_map]
    refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun s => ?_
    simpa [Real.rpow_two, HilbertBasis.repr_apply_apply, hT0] using h x s
  exact ⟨T0.mkContinuous K hbd, ContinuousLinearMap.opNorm_le_bound _ hK hbd, hT0⟩

omit [CompleteSpace H] in
theorem diag_coord_bound (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (x : H) (s : Finset ι) :
    ∑ i ∈ s, ‖φ i * inner ℂ (b i) x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
  calc ∑ i ∈ s, ‖φ i * inner ℂ (b i) x‖ ^ 2
      ≤ ∑ i ∈ s, C ^ 2 * ‖inner ℂ (b i) x‖ ^ 2 := by
        gcongr with i
        rw [norm_mul, mul_pow]
        gcongr
        exact hφ i
    _ = C ^ 2 * ∑ i ∈ s, ‖inner ℂ (b i) x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ C ^ 2 * ‖x‖ ^ 2 := by gcongr; exact b.orthonormal.sum_inner_products_le x
    _ = _ := by ring

omit [CompleteSpace H] in
/-- Существование диагонального оператора с ограниченным символом. -/
theorem exists_diagOp (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ i, ‖φ i‖ ≤ C) :
    ∃ D : H →L[ℂ] H, ‖D‖ ≤ C ∧
      ∀ (i : ι) (x : H), inner ℂ (b i) (D x) = φ i * inner ℂ (b i) x := by
  let c : H →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun x i => φ i * inner ℂ (b i) x
      map_add' := fun x y => by ext i; simp [inner_add_right, mul_add]
      map_smul' := fun a x => by ext i; simp [inner_smul_right]; ring }
  obtain ⟨T, hT, hT'⟩ := exists_of_coord b c C hC (diag_coord_bound b φ C hφ)
  exact ⟨T, hT, fun i x => hT' i x⟩

open Classical in
/-- Диагональный оператор; для неограниченного символа равен нулю. -/
def diagOp (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) : H →L[ℂ] H :=
  if h : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖φ i‖ ≤ C then
    Classical.choose (exists_diagOp b φ h.choose h.choose_spec.1 h.choose_spec.2)
  else 0

omit [CompleteSpace H] in
theorem inner_basis_diagOp (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (i : ι) (x : H) :
    inner ℂ (b i) (diagOp b φ x) = φ i * inner ℂ (b i) x := by
  have hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖φ i‖ ≤ C :=
    ⟨max C 0, le_max_right _ _, fun i => (hφ i).trans (le_max_left _ _)⟩
  unfold diagOp
  rw [dite_eq_left hb]
  exact (Classical.choose_spec (exists_diagOp b φ _ hb.choose_spec.1 hb.choose_spec.2)).2 i x

omit [CompleteSpace H] in
theorem diagOp_apply_basis (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (i : ι) : diagOp b φ (b i) = φ i • b i := by
  classical
  apply b.repr.injective
  ext j
  simp only [HilbertBasis.repr_apply_apply, inner_basis_diagOp b φ C hφ, inner_smul_right,
    orthonormal_iff_ite.mp b.orthonormal]
  split_ifs with h <;> simp [h]

omit [CompleteSpace H] in
theorem diagOp_norm_le (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ i, ‖φ i‖ ≤ C) : ‖diagOp b φ‖ ≤ C := by
  refine norm_le_of_coord_sum_le b _ C hC fun x s => ?_
  simp only [inner_basis_diagOp b φ C hφ]
  exact diag_coord_bound b φ C hφ x s

omit [CompleteSpace H] in
theorem opEntry_diagOp_comp (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (diagOp b φ ∘L X) i l = φ i * opEntry b X i l := by
  simp only [opEntry, ContinuousLinearMap.comp_apply, inner_basis_diagOp b φ C hφ]

omit [CompleteSpace H] in
theorem opEntry_comp_diagOp (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (X ∘L diagOp b φ) i l = opEntry b X i l * φ l := by
  simp only [opEntry, ContinuousLinearMap.comp_apply, diagOp_apply_basis b φ C hφ, map_smul,
    inner_smul_right]
  ring

omit [CompleteSpace H] in
theorem diagOp_comp (b : HilbertBasis ι ℂ H) (φ ψ : ι → ℂ) (C C' : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (hψ : ∀ i, ‖ψ i‖ ≤ C') :
    diagOp b φ ∘L diagOp b ψ = diagOp b (fun i => φ i * ψ i) := by
  have hφψ : ∀ i, ‖φ i * ψ i‖ ≤ max C 0 * max C' 0 := fun i => by
    rw [norm_mul]
    exact mul_le_mul ((hφ i).trans (le_max_left _ _)) ((hψ i).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  apply clm_ext_basis b
  intro i
  simp [diagOp_apply_basis b _ _ hφψ, diagOp_apply_basis b _ _ hψ, diagOp_apply_basis b _ _ hφ,
    smul_smul, mul_comm]

omit [CompleteSpace H] in
theorem diagOp_one (b : HilbertBasis ι ℂ H) :
    diagOp b (fun _ => (1 : ℂ)) = ContinuousLinearMap.id ℂ H := by
  apply clm_ext_basis b
  intro i
  simp [diagOp_apply_basis b (fun _ => (1 : ℂ)) 1 (fun _ => by simp)]

omit [CompleteSpace H] in
theorem inner_diagOp_left (b : HilbertBasis ι ℂ H) (φ : ι → ℂ) (C : ℝ)
    (hφ : ∀ i, ‖φ i‖ ≤ C) (x y : H) :
    inner ℂ (diagOp b φ x) y = inner ℂ x (diagOp b (fun i => conj (φ i)) y) := by
  have hφ' : ∀ i, ‖conj (φ i)‖ ≤ C := fun i => by rw [Complex.norm_conj]; exact hφ i
  rw [← b.tsum_inner_mul_inner, ← b.tsum_inner_mul_inner x]
  congr 1
  ext i
  rw [← inner_conj_symm (diagOp b φ x) (b i), inner_basis_diagOp b φ C hφ,
    inner_basis_diagOp b _ C hφ', ← inner_conj_symm x (b i)]
  simp only [map_mul]
  ring

/-- Мультипликатор Шура `m` ограничен константой `C` в базисе `b`. -/
def SchurBound (b : HilbertBasis ι ℂ H) (m : ι → ι → ℂ) (C : ℝ) : Prop :=
  ∀ X : H →L[ℂ] H, ∃ Y : H →L[ℂ] H, ‖Y‖ ≤ C * ‖X‖ ∧
    ∀ i l, opEntry b Y i l = m i l * opEntry b X i l

omit [CompleteSpace H] in
theorem SchurBound.mono {b : HilbertBasis ι ℂ H} {m : ι → ι → ℂ} {C C' : ℝ}
    (h : SchurBound b m C) (hC : C ≤ C') : SchurBound b m C' := by
  intro X
  obtain ⟨Y, hY, hE⟩ := h X
  exact ⟨Y, hY.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _)), hE⟩

omit [CompleteSpace H] in
/-- Мультипликатор-произведение `f i * g l` реализуется двумя диагональными операторами. -/
theorem SchurBound.product (b : HilbertBasis ι ℂ H) (f g : ι → ℂ) (F G : ℝ)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hf : ∀ i, ‖f i‖ ≤ F) (hg : ∀ l, ‖g l‖ ≤ G) :
    SchurBound b (fun i l => f i * g l) (F * G) := by
  intro X
  refine ⟨diagOp b f ∘L (X ∘L diagOp b g), ?_, fun i l => ?_⟩
  · calc ‖diagOp b f ∘L (X ∘L diagOp b g)‖ ≤ ‖diagOp b f‖ * (‖X‖ * ‖diagOp b g‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ F * (‖X‖ * G) := by
          gcongr
          exacts [diagOp_norm_le b f F hF hf, diagOp_norm_le b g G hG hg]
      _ = F * G * ‖X‖ := by ring
  · rw [opEntry_diagOp_comp b f F hf, opEntry_comp_diagOp b g G hg]
    ring

omit [CompleteSpace H] in
theorem SchurBound.add {b : HilbertBasis ι ℂ H} {m m' : ι → ι → ℂ} {C C' : ℝ}
    (h : SchurBound b m C) (h' : SchurBound b m' C') :
    SchurBound b (fun i l => m i l + m' i l) (C + C') := by
  intro X
  obtain ⟨Y, hY, hE⟩ := h X
  obtain ⟨Y', hY', hE'⟩ := h' X
  refine ⟨Y + Y', (norm_add_le _ _).trans (by linarith), fun i l => ?_⟩
  simp only [opEntry, add_apply, inner_add_right] at hE hE' ⊢
  rw [hE, hE']
  ring

omit [CompleteSpace H] in
theorem SchurBound.const_mul {b : HilbertBasis ι ℂ H} {m : ι → ι → ℂ} {C : ℝ}
    (c : ℂ) (h : SchurBound b m C) :
    SchurBound b (fun i l => c * m i l) (‖c‖ * C) := by
  intro X
  obtain ⟨Y, hY, hE⟩ := h X
  refine ⟨c • Y, ?_, fun i l => ?_⟩
  · rw [norm_smul, mul_assoc]
    gcongr
  · simp only [opEntry, smul_apply, inner_smul_right] at hE ⊢
    rw [hE]
    ring

/-- Абсолютно сходящаяся сумма мультипликаторов. -/
theorem SchurBound.of_hasSum {α : Type*} {b : HilbertBasis ι ℂ H} (m : α → ι → ι → ℂ)
    (C : α → ℝ) (M : ι → ι → ℂ) (_hC0 : ∀ a, 0 ≤ C a) (hC : Summable C)
    (hm : ∀ a, SchurBound b (m a) (C a))
    (hM : ∀ i l, HasSum (fun a => m a i l) (M i l)) :
    SchurBound b M (∑' a, C a) := by
  intro X
  choose Y hY hE using fun a => hm a X
  have hs : Summable fun a => ‖Y a‖ :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hY (hC.mul_right ‖X‖)
  have hYs : Summable Y := hs.of_norm
  refine ⟨∑' a, Y a, ?_, fun i l => ?_⟩
  · calc ‖∑' a, Y a‖ ≤ ∑' a, ‖Y a‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' a, C a * ‖X‖ := hs.tsum_le_tsum hY (hC.mul_right ‖X‖)
      _ = (∑' a, C a) * ‖X‖ := tsum_mul_right
  · let E : (H →L[ℂ] H) →L[ℂ] ℂ :=
      (innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b l))
    have hE' : ∀ Z, E Z = opEntry b Z i l := fun Z => rfl
    have h1 := hYs.hasSum.mapL E
    simp only [hE', hE] at h1
    exact h1.unique ((hM i l).mul_right _)

omit [CompleteSpace H] in
theorem hasSum_norm_sq_inner (b : HilbertBasis ι ℂ H) (v : H) :
    HasSum (fun i => ‖inner ℂ (b i) v‖ ^ 2) (‖v‖ ^ 2) := by
  have := lp.hasSum_norm (p := 2) (by norm_num) (b.repr v)
  simpa [Real.rpow_two, HilbertBasis.repr_apply_apply] using this

theorem norm_indicator_one_le (S : Set ι) (i : ι) : ‖S.indicator (1 : ι → ℂ) i‖ ≤ 1 := by
  by_cases h : i ∈ S <;> simp [h]

omit [CompleteSpace H] in
/-- Проекторы на попарно непересекающиеся координатные множества: `∑ ‖P_S x‖² ≤ ‖x‖²`. -/
theorem sum_norm_sq_proj_le {α : Type*} (b : HilbertBasis ι ℂ H) (S : α → Set ι) (O : Finset α)
    (hS : ∀ o ∈ O, ∀ o' ∈ O, o ≠ o' → Disjoint (S o) (S o')) (x : H) :
    ∑ o ∈ O, ‖diagOp b ((S o).indicator 1) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h1 : ∀ o, HasSum (fun l => ‖(S o).indicator (1 : ι → ℂ) l * inner ℂ (b l) x‖ ^ 2)
      (‖diagOp b ((S o).indicator 1) x‖ ^ 2) := by
    intro o
    have := hasSum_norm_sq_inner b (diagOp b ((S o).indicator 1) x)
    simpa only [inner_basis_diagOp b _ 1 (norm_indicator_one_le _)] using this
  rw [← (hasSum_norm_sq_inner b x).tsum_eq]
  calc ∑ o ∈ O, ‖diagOp b ((S o).indicator 1) x‖ ^ 2
      = ∑ o ∈ O, ∑' l, ‖(S o).indicator (1 : ι → ℂ) l * inner ℂ (b l) x‖ ^ 2 :=
        Finset.sum_congr rfl fun o _ => (h1 o).tsum_eq.symm
    _ = ∑' l, ∑ o ∈ O, ‖(S o).indicator (1 : ι → ℂ) l * inner ℂ (b l) x‖ ^ 2 :=
        (Summable.tsum_finsetSum fun o _ => (h1 o).summable).symm
    _ ≤ ∑' l, ‖inner ℂ (b l) x‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun l => ?_) (summable_sum fun o _ => (h1 o).summable)
          (hasSum_norm_sq_inner b x).summable
        by_cases h : ∃ o ∈ O, l ∈ S o
        · obtain ⟨o0, ho0, hl⟩ := h
          rw [Finset.sum_eq_single o0]
          · simp [hl]
          · intro o ho hne
            have : l ∉ S o := fun h' => Set.disjoint_left.mp (hS o0 ho0 o ho hne.symm) hl h'
            simp [this]
          · intro h'; exact absurd ho0 h'
        · push Not at h
          rw [Finset.sum_eq_zero fun o ho => by simp [h o ho]]
          positivity

omit [CompleteSpace H] in
/-- Сумма мультипликаторов с попарно непересекающимися строками и столбцами
имеет ту же константу, что и слагаемые. -/
theorem SchurBound.blockSum {κ : Type*} {b : HilbertBasis ι ℂ H} (A B : κ → Set ι)
    (hA : Pairwise (fun j k => Disjoint (A j) (A k)))
    (hB : Pairwise (fun j k => Disjoint (B j) (B k)))
    (m : κ → ι → ι → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ k, SchurBound b (m k) C)
    (M : ι → ι → ℂ) (hM : ∀ k i l, i ∈ A k → l ∈ B k → M i l = m k i l)
    (hM0 : ∀ i l, (∀ k, ¬ (i ∈ A k ∧ l ∈ B k)) → M i l = 0) :
    SchurBound b M C := by
  classical
  intro X
  choose Y hY hE using fun k => hm k X
  set kf : ι → Option κ := fun i => if h : ∃ k, i ∈ A k then some h.choose else none with hkf
  let P : Set ι → H →L[ℂ] H := fun S => diagOp b (S.indicator 1)
  let Bs : Option κ → Set ι := fun o => o.elim ∅ B
  let V : Option κ → H →L[ℂ] H := fun o => o.elim 0 (fun k => Y k ∘L P (B k))
  have hV : ∀ o x, ‖V o x‖ ≤ C * ‖X‖ * ‖P (Bs o) x‖ := by
    intro o x
    cases o with
    | none => simp only [V, Option.elim, zero_apply, norm_zero]; positivity
    | some k =>
      calc ‖(Y k ∘L P (B k)) x‖ ≤ ‖Y k‖ * ‖P (B k) x‖ := (Y k).le_opNorm _
        _ ≤ C * ‖X‖ * ‖P (B k) x‖ := by gcongr; exact hY k
  have hBs : ∀ o o', o ≠ o' → Disjoint (Bs o) (Bs o') := by
    intro o o' h
    cases o with
    | none => simp [Bs]
    | some k =>
      cases o' with
      | none => simp [Bs]
      | some k' => exact hB (fun h' => h (by rw [h']))
  let c : H →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun x i => inner ℂ (b i) (V (kf i) x)
      map_add' := fun x y => by ext i; simp [inner_add_right]
      map_smul' := fun a x => by ext i; simp [inner_smul_right] }
  obtain ⟨T, hT, hTc⟩ := exists_of_coord b c (C * ‖X‖) (by positivity) (by
    intro x s
    change ∑ i ∈ s, ‖inner ℂ (b i) (V (kf i) x)‖ ^ 2 ≤ (C * ‖X‖ * ‖x‖) ^ 2
    rw [← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem kf hi)]
    calc ∑ o ∈ s.image kf, ∑ i ∈ s with kf i = o, ‖inner ℂ (b i) (V (kf i) x)‖ ^ 2
        = ∑ o ∈ s.image kf, ∑ i ∈ s with kf i = o, ‖inner ℂ (b i) (V o x)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.mp hi).2]
      _ ≤ ∑ o ∈ s.image kf, ‖V o x‖ ^ 2 := by
          gcongr with o
          exact b.orthonormal.sum_inner_products_le _
      _ ≤ ∑ o ∈ s.image kf, (C * ‖X‖) ^ 2 * ‖P (Bs o) x‖ ^ 2 := by
          gcongr with o
          rw [← mul_pow]
          gcongr
          exact hV o x
      _ = (C * ‖X‖) ^ 2 * ∑ o ∈ s.image kf, ‖P (Bs o) x‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * ‖X‖) ^ 2 * ‖x‖ ^ 2 := by
          gcongr
          exact sum_norm_sq_proj_le b Bs _ (fun o _ o' _ h => hBs o o' h) x
      _ = (C * ‖X‖ * ‖x‖) ^ 2 := by ring)
  refine ⟨T, hT, fun i l => ?_⟩
  change inner ℂ (b i) (T (b l)) = M i l * opEntry b X i l
  rw [hTc i (b l)]
  change inner ℂ (b i) (V (kf i) (b l)) = _
  by_cases h : ∃ k, i ∈ A k
  · have hk : kf i = some h.choose := by simp only [hkf, dite_eq_left h]
    have hiA : i ∈ A h.choose := h.choose_spec
    rw [hk]
    change inner ℂ (b i) (Y h.choose (P (B h.choose) (b l))) = _
    rw [show P (B h.choose) (b l) = (B h.choose).indicator 1 l • b l from
      diagOp_apply_basis b _ 1 (norm_indicator_one_le _) l, map_smul, inner_smul_right]
    have := hE h.choose i l
    simp only [opEntry] at this ⊢
    rw [this]
    by_cases hl : l ∈ B h.choose
    · rw [hM _ i l hiA hl]
      simp [hl]
    · rw [hM0 i l ?_]
      · simp [hl]
      · rintro k' ⟨hi', hl'⟩
        have : k' = h.choose := by
          by_contra hne
          exact Set.disjoint_left.mp (hA hne) hi' hiA
        subst this
        exact hl hl'
  · have hk : kf i = none := by simp only [hkf, dite_eq_right h]
    rw [hk]
    simp only [V, Option.elim, zero_apply, inner_zero_right]
    rw [hM0 i l fun k hk => h ⟨k, hk.1⟩, zero_mul]

/-- Ряд из мультипликаторов-произведений. -/
theorem schurBound_series (b : HilbertBasis ι ℂ H) (f g : ℕ → ι → ℂ) (F G : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n) (hf : ∀ n i, ‖f n i‖ ≤ F n)
    (hg : ∀ n l, ‖g n l‖ ≤ G n) (hs : Summable fun n => F n * G n) (M : ι → ι → ℂ)
    (hM : ∀ i l, HasSum (fun n => f n i * g n l) (M i l)) :
    SchurBound b M (∑' n, F n * G n) :=
  SchurBound.of_hasSum (fun n i l => f n i * g n l) (fun n => F n * G n) M
    (fun n => mul_nonneg (hF n) (hG n)) hs
    (fun n => SchurBound.product b (f n) (g n) (F n) (G n) (hF n) (hG n) (hf n) (hg n)) hM

theorem hasSum_geom_uv (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) :
    HasSum (fun n : ℕ => (v ^ (n + 1))⁻¹ * u ^ n) (v - u)⁻¹ := by
  have hv : 0 < v := lt_of_le_of_lt hu huv
  have hr : |u / v| < 1 := by
    rw [abs_of_nonneg (div_nonneg hu hv.le), div_lt_one hv]; exact huv
  have hne : v - u ≠ 0 := by linarith
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_left v⁻¹
  convert h using 1
  · ext n
    rw [div_pow, pow_succ]
    field_simp
  · rw [one_sub_div hv.ne', inv_div]
    field_simp

open Classical in
/-- Разделённые спектры, строки в верхнем множестве: `1 / (ω i - s ω l)`, `s = ±1`.
Ряд Неймана `∑ (s ω l) ^ n / (ω i) ^ (n + 1)` и `SchurBound.product`. -/
theorem schurBound_separated_upper (b : HilbertBasis ι ℂ H) (ω : ι → ℝ) (A B : Set ι)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hA : ∀ i ∈ A, v ≤ ω i)
    (hB : ∀ l ∈ B, 0 ≤ ω l ∧ ω l ≤ u) (s : ℝ) (hs : |s| = 1) :
    SchurBound b
      (fun i l => if i ∈ A ∧ l ∈ B then (((ω i - s * ω l : ℝ) : ℂ))⁻¹ else 0) (v - u)⁻¹ := by
  have hv : 0 < v := lt_of_le_of_lt hu huv
  have hωA : ∀ i ∈ A, 0 < ω i := fun i hi => lt_of_lt_of_le hv (hA i hi)
  have hsum := hasSum_geom_uv u v hu huv
  rw [← hsum.tsum_eq]
  refine schurBound_series b
    (fun n i => ((if i ∈ A then (ω i ^ (n + 1))⁻¹ else 0 : ℝ) : ℂ))
    (fun n l => ((if l ∈ B then (s * ω l) ^ n else 0 : ℝ) : ℂ))
    (fun n => (v ^ (n + 1))⁻¹) (fun n => u ^ n) (fun n => by positivity) (fun n => by positivity)
    ?_ ?_ hsum.summable _ ?_
  · intro n i
    rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hi
    · have := hωA i hi
      rw [abs_of_pos (by positivity)]
      gcongr
      exact hA i hi
    · simp only [abs_zero]; positivity
  · intro n l
    rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hl
    · rw [abs_pow, abs_mul, hs, one_mul, abs_of_nonneg (hB l hl).1]
      exact pow_le_pow_left₀ (hB l hl).1 (hB l hl).2 n
    · simp only [abs_zero]; positivity
  · intro i l
    have key : HasSum (fun n => (if i ∈ A then (ω i ^ (n + 1))⁻¹ else 0 : ℝ) *
        (if l ∈ B then (s * ω l) ^ n else 0)) (if i ∈ A ∧ l ∈ B then (ω i - s * ω l)⁻¹ else 0) := by
      by_cases hi : i ∈ A
      · by_cases hl : l ∈ B
        · simp only [hi, hl, ite_true, and_self]
          have hω := hωA i hi
          have hl1 := hB l hl
          have hi1 := hA i hi
          have hr : |s * ω l / ω i| < 1 := by
            rw [abs_div, abs_mul, hs, one_mul, abs_of_nonneg hl1.1, abs_of_pos hω, div_lt_one hω]
            linarith
          have hne : ω i - s * ω l ≠ 0 := by
            have : |s * ω l| ≤ u := by rw [abs_mul, hs, one_mul, abs_of_nonneg hl1.1]; exact hl1.2
            have := neg_abs_le (s * ω l)
            have := le_abs_self (s * ω l)
            intro h; linarith
          have h := (hasSum_geometric_of_abs_lt_one hr).mul_left (ω i)⁻¹
          convert h using 1
          · ext n
            rw [div_pow, pow_succ]
            field_simp
          · rw [one_sub_div hω.ne', inv_div]
            field_simp
        · simp only [hl, ite_false, mul_zero, and_false]; exact hasSum_zero
      · simp only [hi, ite_false, zero_mul, false_and]; exact hasSum_zero
    have := Complex.hasSum_ofReal.mpr key
    convert this using 1
    · ext n; push_cast; rfl
    · split_ifs <;> push_cast <;> rfl

open Classical in
/-- Разделённые спектры, строки в нижнем множестве. -/
theorem schurBound_separated_lower (b : HilbertBasis ι ℂ H) (ω : ι → ℝ) (A B : Set ι)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hA : ∀ i ∈ A, v ≤ ω i)
    (hB : ∀ l ∈ B, 0 ≤ ω l ∧ ω l ≤ u) (s : ℝ) (hs : |s| = 1) :
    SchurBound b
      (fun i l => if i ∈ B ∧ l ∈ A then (((ω i - s * ω l : ℝ) : ℂ))⁻¹ else 0) (v - u)⁻¹ := by
  have hv : 0 < v := lt_of_le_of_lt hu huv
  have hωA : ∀ i ∈ A, 0 < ω i := fun i hi => lt_of_lt_of_le hv (hA i hi)
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hsum : HasSum (fun n : ℕ => u ^ n * (v ^ (n + 1))⁻¹) (v - u)⁻¹ := by
    simpa only [mul_comm] using hasSum_geom_uv u v hu huv
  rw [← hsum.tsum_eq]
  refine schurBound_series b
    (fun n i => ((if i ∈ B then -s * (s * ω i) ^ n else 0 : ℝ) : ℂ))
    (fun n l => ((if l ∈ A then (ω l ^ (n + 1))⁻¹ else 0 : ℝ) : ℂ))
    (fun n => u ^ n) (fun n => (v ^ (n + 1))⁻¹) (fun n => by positivity) (fun n => by positivity)
    ?_ ?_ hsum.summable _ ?_
  · intro n i
    rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hi
    · rw [abs_mul, abs_neg, hs, one_mul, abs_pow, abs_mul, hs, one_mul,
        abs_of_nonneg (hB i hi).1]
      exact pow_le_pow_left₀ (hB i hi).1 (hB i hi).2 n
    · simp only [abs_zero]; positivity
  · intro n l
    rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hl
    · have := hωA l hl
      rw [abs_of_pos (by positivity)]
      gcongr
      exact hA l hl
    · simp only [abs_zero]; positivity
  · intro i l
    have key : HasSum (fun n => (if i ∈ B then -s * (s * ω i) ^ n else 0 : ℝ) *
        (if l ∈ A then (ω l ^ (n + 1))⁻¹ else 0))
        (if i ∈ B ∧ l ∈ A then (ω i - s * ω l)⁻¹ else 0) := by
      by_cases hi : i ∈ B
      · by_cases hl : l ∈ A
        · simp only [hi, hl, ite_true, and_self]
          have hω := hωA l hl
          have hi1 := hB i hi
          have hl1 := hA l hl
          have hr : |s * ω i / ω l| < 1 := by
            rw [abs_div, abs_mul, hs, one_mul, abs_of_nonneg hi1.1, abs_of_pos hω, div_lt_one hω]
            linarith
          have hne : ω l - s * ω i ≠ 0 := by
            have : |s * ω i| ≤ u := by rw [abs_mul, hs, one_mul, abs_of_nonneg hi1.1]; exact hi1.2
            have := le_abs_self (s * ω i)
            intro h; linarith
          have hne' : ω i - s * ω l ≠ 0 := by
            intro h; apply hne
            linear_combination (-s) * h - ω l * hs2
          have h := (hasSum_geometric_of_abs_lt_one hr).mul_left (-s / ω l)
          convert h using 1
          · ext n
            rw [div_pow, pow_succ]
            field_simp
          · have e : ω l - s * ω i = -s * (ω i - s * ω l) := by
              linear_combination (-ω l) * hs2
            rw [one_sub_div hω.ne', inv_div, div_mul_div_cancel₀ hω.ne', eq_div_iff hne, e]
            field_simp
        · simp only [hl, ite_false, mul_zero, and_false]; exact hasSum_zero
      · simp only [hi, ite_false, zero_mul, false_and]; exact hasSum_zero
    have := Complex.hasSum_ofReal.mpr key
    convert this using 1
    · ext n; push_cast; rfl
    · split_ifs <;> push_cast <;> rfl

/-- Продолжение по плотности: если `B`, составленный с неограниченным диагональным
символом `φ`, равномерно ограничен на конечных срезах, то существует ограниченный
оператор с `B' (b i) = φ i • B (b i)`. -/
theorem exists_weighted_extension (b : HilbertBasis ι ℂ H) (B : H →L[ℂ] H) (φ : ι → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (s : Finset ι) (x : H),
      ‖B (∑ i ∈ s, (φ i * inner ℂ (b i) x) • b i)‖ ≤ C * ‖x‖) :
    ∃ B' : H →L[ℂ] H, ‖B'‖ ≤ C ∧ ∀ i, B' (b i) = φ i • B (b i) := by
  have hsum : ∀ x : H, Summable fun i => (φ i * inner ℂ (b i) x) • B (b i) := by
    intro x
    rw [summable_iff_vanishing_norm]
    intro ε hε
    have hx := (b.hasSum_repr x).summable
    rw [summable_iff_vanishing_norm] at hx
    obtain ⟨s, hs⟩ := hx (ε / (C + 1)) (by positivity)
    refine ⟨s, fun t ht => ?_⟩
    set y := ∑ i ∈ t, (b.repr x) i • b i with hy_def
    have hy : ∀ i ∈ t, inner ℂ (b i) y = inner ℂ (b i) x := by
      intro i hi
      rw [hy_def, b.orthonormal.inner_right_sum _ hi, HilbertBasis.repr_apply_apply]
    have hrw : ∑ i ∈ t, (φ i * inner ℂ (b i) x) • B (b i) =
        B (∑ i ∈ t, (φ i * inner ℂ (b i) y) • b i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, hy i hi]
    rw [hrw]
    calc ‖B (∑ i ∈ t, (φ i * inner ℂ (b i) y) • b i)‖ ≤ C * ‖y‖ := h t y
      _ ≤ C * (ε / (C + 1)) := by gcongr; exact (hs t ht).le
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  let L : H →ₗ[ℂ] H :=
    { toFun := fun x => ∑' i, (φ i * inner ℂ (b i) x) • B (b i)
      map_add' := fun x y => by
        rw [← (hsum x).tsum_add (hsum y)]
        congr 1
        ext i
        simp only [inner_add_right, mul_add, add_smul]
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [← (hsum x).tsum_const_smul a]
        congr 1
        ext i
        simp only [inner_smul_right, smul_smul]
        ring_nf }
  have hbd : ∀ x, ‖L x‖ ≤ C * ‖x‖ := by
    intro x
    have ht : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, (φ i * inner ℂ (b i) x) • B (b i))
        Filter.atTop (nhds (L x)) := (hsum x).hasSum
    refine le_of_tendsto' ((continuous_norm.tendsto _).comp ht) fun s => ?_
    have := h s x
    simpa only [Function.comp_apply, map_sum, map_smul] using this
  refine ⟨L.mkContinuous C hbd, ContinuousLinearMap.opNorm_le_bound _ hC hbd, fun j => ?_⟩
  change ∑' i, (φ i * inner ℂ (b i) (b j)) • B (b i) = φ j • B (b j)
  classical
  rw [tsum_eq_single j]
  · simp [b.orthonormal.1 j]
  · intro i hij
    simp [orthonormal_iff_ite.mp b.orthonormal, hij]

end Involution
