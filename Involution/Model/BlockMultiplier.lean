module

public import Involution.Model.SchurMultiplier

/-! Мультипликаторы Шура для разреженных спектральных блоков.
Частоты `ω i` разбиты на блоки разрезами `ξ k`, удваивающимися на каждом шаге,
с зазором `δ` до всех частот. Мультипликаторы `1 / (ω i ∓ ω l)` вне диагональных
блоков ограничены константой `4 / δ`, блочно-диагональная часть — единицей. -/

@[expose] public noncomputable section

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem opEntry_add (b : HilbertBasis ι ℂ H) (X Y : H →L[ℂ] H) (i l : ι) :
    opEntry b (X + Y) i l = opEntry b X i l + opEntry b Y i l := by
  simp [opEntry, inner_add_right]

omit [CompleteSpace H] in
theorem opEntry_sub (b : HilbertBasis ι ℂ H) (X Y : H →L[ℂ] H) (i l : ι) :
    opEntry b (X - Y) i l = opEntry b X i l - opEntry b Y i l := by
  simp [opEntry, inner_sub_right]

omit [CompleteSpace H] in
theorem opEntry_smul (b : HilbertBasis ι ℂ H) (c : ℂ) (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (c • X) i l = c * opEntry b X i l := by
  simp [opEntry, inner_smul_right]

omit [CompleteSpace H] in
theorem opEntry_neg (b : HilbertBasis ι ℂ H) (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (-X) i l = -opEntry b X i l := by
  simp [opEntry, inner_neg_right]

/-- Линейное отображение, заданное ограниченным мультипликатором Шура. -/
def schurMap (b : HilbertBasis ι ℂ H) (m : ι → ι → ℂ) (C : ℝ) (h : SchurBound b m C) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun X := Classical.choose (h X)
  map_add' X Y := by
    apply opEntry_ext b
    intro i l
    rw [(Classical.choose_spec (h (X + Y))).2, opEntry_add, opEntry_add,
      (Classical.choose_spec (h X)).2, (Classical.choose_spec (h Y)).2, mul_add]
  map_smul' c X := by
    apply opEntry_ext b
    intro i l
    rw [RingHom.id_apply, (Classical.choose_spec (h (c • X))).2, opEntry_smul, opEntry_smul,
      (Classical.choose_spec (h X)).2]
    ring

omit [CompleteSpace H] in
theorem schurMap_entry (b : HilbertBasis ι ℂ H) (m : ι → ι → ℂ) (C : ℝ)
    (h : SchurBound b m C) (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (schurMap b m C h X) i l = m i l * opEntry b X i l :=
  (Classical.choose_spec (h X)).2 i l

omit [CompleteSpace H] in
theorem schurMap_norm_le (b : HilbertBasis ι ℂ H) (m : ι → ι → ℂ) (C : ℝ)
    (h : SchurBound b m C) (X : H →L[ℂ] H) : ‖schurMap b m C h X‖ ≤ C * ‖X‖ :=
  (Classical.choose_spec (h X)).1

omit [CompleteSpace H] in
theorem SchurBound.congr {b : HilbertBasis ι ℂ H} {m m' : ι → ι → ℂ} {C : ℝ}
    (h : SchurBound b m C) (hm : ∀ i l, m i l = m' i l) : SchurBound b m' C := by
  have he : m = m' := funext fun i => funext fun l => hm i l
  rwa [← he]

/-- Частоты, разбитые на блоки разрезами с зазором `δ` и удвоением. -/
structure SpectralBlocks (ι : Type*) where
  ω : ι → ℝ
  blk : ι → ℕ
  ξ : ℕ → ℝ
  δ : ℝ
  ω₀ : ℝ
  δ_pos : 0 < δ
  ω₀_pos : 0 < ω₀
  ω_ge : ∀ i, ω₀ ≤ ω i
  ξ_one : δ ≤ ξ 1
  ξ_double : ∀ k, 1 ≤ k → 2 * ξ k ≤ ξ (k + 1)
  upper : ∀ i, ω i + δ ≤ ξ (blk i + 1)
  lower : ∀ i, 1 ≤ blk i → ξ (blk i) + δ ≤ ω i

namespace SpectralBlocks

variable (D : SpectralBlocks ι)

theorem ω_pos (i : ι) : 0 < D.ω i := D.ω₀_pos.trans_le (D.ω_ge i)

theorem ξ_pow (j : ℕ) (hj : 1 ≤ j) (n : ℕ) : 2 ^ n * D.ξ j ≤ D.ξ (j + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := D.ξ_double (j + n) (by omega)
    calc
      2 ^ (n + 1) * D.ξ j = 2 * (2 ^ n * D.ξ j) := by ring
      _ ≤ 2 * D.ξ (j + n) := by linarith
      _ ≤ D.ξ (j + (n + 1)) := h

theorem δ_le_ξ (j : ℕ) (hj : 1 ≤ j) : D.δ ≤ D.ξ j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = 1 + n := ⟨j - 1, by omega⟩
  have h := D.ξ_pow 1 le_rfl n
  have h1 := D.ξ_one
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith [D.δ_pos]

theorem ξ_mono {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : D.ξ j ≤ D.ξ k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have h := D.ξ_pow j hj n
  have hpos := D.δ_pos.trans_le (D.δ_le_ξ j hj)
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith

/-- Частоты разных блоков различны, причём блок с большим номером лежит выше. -/
theorem ω_lt_of_blk_lt {i l : ι} (h : D.blk l < D.blk i) : D.ω l + 2 * D.δ ≤ D.ω i := by
  have h1 := D.upper l
  have h2 := D.lower i (by omega)
  have h3 := D.ξ_mono (j := D.blk l + 1) (k := D.blk i) (by omega) (by omega)
  linarith

theorem ω_ne_of_blk_ne {i l : ι} (h : D.blk i ≠ D.blk l) : D.ω i ≠ D.ω l := by
  rcases lt_or_gt_of_ne h with h | h
  · have := D.ω_lt_of_blk_lt h
    have := D.δ_pos
    intro he
    linarith
  · have := D.ω_lt_of_blk_lt h
    have := D.δ_pos
    intro he
    linarith

/-- Оценка зазора между блоками `k` и `k + n + 1`. -/
theorem block_gap (k n : ℕ) :
    ((D.ξ (k + n + 1) + D.δ) - (D.ξ (k + 1) - D.δ))⁻¹ ≤ (1 / 2 : ℝ) ^ n * D.δ⁻¹ := by
  have h := D.ξ_pow (k + 1) (by omega) n
  have hδ := D.δ_le_ξ (k + 1) (by omega)
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hidx : k + 1 + n = k + n + 1 := by omega
  rw [hidx] at h
  have hgap : 2 ^ n * D.δ ≤ (D.ξ (k + n + 1) + D.δ) - (D.ξ (k + 1) - D.δ) := by
    nlinarith [D.δ_pos]
  have hpos : 0 < (2 : ℝ) ^ n * D.δ := mul_pos (by positivity) D.δ_pos
  calc
    _ ≤ (2 ^ n * D.δ)⁻¹ := inv_anti₀ hpos hgap
    _ = _ := by rw [mul_inv, one_div, inv_pow]

open Classical in
/-- Блоки строк выше блоков столбцов ровно на `n + 1`. -/
def upperMult (s : ℝ) (n : ℕ) (i l : ι) : ℂ :=
  if D.blk i = D.blk l + n + 1 then (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0

open Classical in
/-- Блоки строк ниже блоков столбцов ровно на `n + 1`. -/
def lowerMult (s : ℝ) (n : ℕ) (i l : ι) : ℂ :=
  if D.blk l = D.blk i + n + 1 then (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0

open Classical in
def aboveMult (s : ℝ) (i l : ι) : ℂ :=
  if D.blk l < D.blk i then (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0

open Classical in
def belowMult (s : ℝ) (i l : ι) : ℂ :=
  if D.blk i < D.blk l then (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0

open Classical in
/-- Мультипликатор `1 / (ω i - s ω l)` вне диагональных блоков. -/
def offMult (s : ℝ) (i l : ι) : ℂ :=
  if D.blk i ≠ D.blk l then (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0

open Classical in
/-- Блочно-диагональная часть. -/
def diagMult (i l : ι) : ℂ := if D.blk i = D.blk l then 1 else 0

theorem upperMult_bound (b : HilbertBasis ι ℂ H) (s : ℝ) (hs : |s| = 1) (n : ℕ) :
    SchurBound b (D.upperMult s n) ((1 / 2 : ℝ) ^ n * D.δ⁻¹) := by
  have hδ := D.δ_pos
  refine SchurBound.blockSum (κ := ℕ) (fun k => {i | D.blk i = k + n + 1})
    (fun k => {l | D.blk l = k}) ?_ ?_
    (fun k i l => if D.blk i = k + n + 1 ∧ D.blk l = k then
      (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0) _ (by positivity) ?_ _ ?_ ?_
  · intro j k hjk
    exact Set.disjoint_left.mpr fun i (hi : D.blk i = j + n + 1) (hk : D.blk i = k + n + 1) =>
      hjk (by omega)
  · intro j k hjk
    exact Set.disjoint_left.mpr fun i (hi : D.blk i = j) (hk : D.blk i = k) => hjk (by omega)
  · intro k
    have hu : 0 ≤ D.ξ (k + 1) - D.δ := sub_nonneg.mpr (D.δ_le_ξ (k + 1) (by omega))
    have huv : D.ξ (k + 1) - D.δ < D.ξ (k + n + 1) + D.δ := by
      have := D.ξ_mono (j := k + 1) (k := k + n + 1) (by omega) (by omega)
      linarith
    have hsep := (schurBound_separated_upper b D.ω {i | D.blk i = k + n + 1} {l | D.blk l = k}
      (D.ξ (k + 1) - D.δ) (D.ξ (k + n + 1) + D.δ) hu huv
      (fun i (hi : D.blk i = k + n + 1) => by
        have := D.lower i (by omega)
        rwa [hi] at this)
      (fun l (hl : D.blk l = k) => by
        have := D.upper l
        rw [hl] at this
        exact ⟨(D.ω_pos l).le, by linarith⟩) s hs).mono (D.block_gap k n)
    refine SchurBound.congr hsep fun i l => ?_
    by_cases hc : D.blk i = k + n + 1 ∧ D.blk l = k
    · rw [ite_eq_left hc]
      exact ite_eq_left hc
    · rw [ite_eq_right hc]
      exact ite_eq_right hc
  · intro k i l (hi : D.blk i = k + n + 1) (hl : D.blk l = k)
    unfold upperMult
    rw [ite_eq_left (by omega), ite_eq_left ⟨hi, hl⟩]
  · intro i l h
    unfold upperMult
    exact ite_eq_right fun hc => h (D.blk l) ⟨hc, rfl⟩

theorem lowerMult_bound (b : HilbertBasis ι ℂ H) (s : ℝ) (hs : |s| = 1) (n : ℕ) :
    SchurBound b (D.lowerMult s n) ((1 / 2 : ℝ) ^ n * D.δ⁻¹) := by
  have hδ := D.δ_pos
  refine SchurBound.blockSum (κ := ℕ) (fun k => {i | D.blk i = k})
    (fun k => {l | D.blk l = k + n + 1}) ?_ ?_
    (fun k i l => if D.blk i = k ∧ D.blk l = k + n + 1 then
      (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ else 0) _ (by positivity) ?_ _ ?_ ?_
  · intro j k hjk
    exact Set.disjoint_left.mpr fun i (hi : D.blk i = j) (hk : D.blk i = k) => hjk (by omega)
  · intro j k hjk
    exact Set.disjoint_left.mpr fun i (hi : D.blk i = j + n + 1) (hk : D.blk i = k + n + 1) =>
      hjk (by omega)
  · intro k
    have hu : 0 ≤ D.ξ (k + 1) - D.δ := sub_nonneg.mpr (D.δ_le_ξ (k + 1) (by omega))
    have huv : D.ξ (k + 1) - D.δ < D.ξ (k + n + 1) + D.δ := by
      have := D.ξ_mono (j := k + 1) (k := k + n + 1) (by omega) (by omega)
      linarith
    have hsep := (schurBound_separated_lower b D.ω {i | D.blk i = k + n + 1} {l | D.blk l = k}
      (D.ξ (k + 1) - D.δ) (D.ξ (k + n + 1) + D.δ) hu huv
      (fun i (hi : D.blk i = k + n + 1) => by
        have := D.lower i (by omega)
        rwa [hi] at this)
      (fun l (hl : D.blk l = k) => by
        have := D.upper l
        rw [hl] at this
        exact ⟨(D.ω_pos l).le, by linarith⟩) s hs).mono (D.block_gap k n)
    refine SchurBound.congr hsep fun i l => ?_
    by_cases hc : D.blk i = k ∧ D.blk l = k + n + 1
    · rw [ite_eq_left hc]
      exact ite_eq_left hc
    · rw [ite_eq_right hc]
      exact ite_eq_right hc
  · intro k i l (hi : D.blk i = k) (hl : D.blk l = k + n + 1)
    unfold lowerMult
    rw [ite_eq_left (by omega), ite_eq_left ⟨hi, hl⟩]
  · intro i l h
    unfold lowerMult
    exact ite_eq_right fun hc => h (D.blk i) ⟨rfl, hc⟩

theorem geometric_bound_summable :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * D.δ⁻¹) :=
  summable_geometric_two.mul_right _

theorem geometric_bound_tsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ n * D.δ⁻¹ = 2 * D.δ⁻¹ := by
  rw [tsum_mul_right, tsum_geometric_two]

theorem aboveMult_bound (b : HilbertBasis ι ℂ H) (s : ℝ) (hs : |s| = 1) :
    SchurBound b (D.aboveMult s) (2 * D.δ⁻¹) := by
  classical
  have hδ := D.δ_pos
  have h := SchurBound.of_hasSum (b := b) (fun n => D.upperMult s n)
    (fun n => (1 / 2 : ℝ) ^ n * D.δ⁻¹) (D.aboveMult s) (fun n => by positivity)
    D.geometric_bound_summable (fun n => D.upperMult_bound b s hs n) ?_
  · rwa [D.geometric_bound_tsum] at h
  · intro i l
    by_cases hlt : D.blk l < D.blk i
    · have hval : D.aboveMult s i l = D.upperMult s (D.blk i - D.blk l - 1) i l := by
        unfold aboveMult upperMult
        rw [ite_eq_left hlt, ite_eq_left (by omega)]
      rw [hval]
      apply hasSum_single
      intro n hn
      unfold upperMult
      exact ite_eq_right (by omega)
    · have hzero : (fun n => D.upperMult s n i l) = fun _ => 0 := by
        funext n
        unfold upperMult
        exact ite_eq_right (by omega)
      have hval : D.aboveMult s i l = 0 := by
        unfold aboveMult
        exact ite_eq_right hlt
      rw [hzero, hval]
      exact hasSum_zero

theorem belowMult_bound (b : HilbertBasis ι ℂ H) (s : ℝ) (hs : |s| = 1) :
    SchurBound b (D.belowMult s) (2 * D.δ⁻¹) := by
  classical
  have hδ := D.δ_pos
  have h := SchurBound.of_hasSum (b := b) (fun n => D.lowerMult s n)
    (fun n => (1 / 2 : ℝ) ^ n * D.δ⁻¹) (D.belowMult s) (fun n => by positivity)
    D.geometric_bound_summable (fun n => D.lowerMult_bound b s hs n) ?_
  · rwa [D.geometric_bound_tsum] at h
  · intro i l
    by_cases hlt : D.blk i < D.blk l
    · have hval : D.belowMult s i l = D.lowerMult s (D.blk l - D.blk i - 1) i l := by
        unfold belowMult lowerMult
        rw [ite_eq_left hlt, ite_eq_left (by omega)]
      rw [hval]
      apply hasSum_single
      intro n hn
      unfold lowerMult
      exact ite_eq_right (by omega)
    · have hzero : (fun n => D.lowerMult s n i l) = fun _ => 0 := by
        funext n
        unfold lowerMult
        exact ite_eq_right (by omega)
      have hval : D.belowMult s i l = 0 := by
        unfold belowMult
        exact ite_eq_right hlt
      rw [hzero, hval]
      exact hasSum_zero

theorem offMult_bound (b : HilbertBasis ι ℂ H) (s : ℝ) (hs : |s| = 1) :
    SchurBound b (D.offMult s) (4 * D.δ⁻¹) := by
  classical
  have h := (D.aboveMult_bound b s hs).add (D.belowMult_bound b s hs)
  have heq : D.offMult s = fun i l => D.aboveMult s i l + D.belowMult s i l := by
    funext i l
    unfold offMult aboveMult belowMult
    rcases lt_trichotomy (D.blk i) (D.blk l) with h | h | h
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h, zero_add]
    · rw [ite_eq_right (by simp [h]), ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
    · rw [ite_eq_left (by omega), ite_eq_left h, ite_eq_right (by omega), add_zero]
  rw [heq]
  exact h.mono (by linarith)

omit [CompleteSpace H] in
theorem diagMult_bound (b : HilbertBasis ι ℂ H) : SchurBound b D.diagMult 1 := by
  refine SchurBound.blockSum (κ := ℕ) (fun k => {i | D.blk i = k}) (fun k => {l | D.blk l = k})
    ?_ ?_ (fun k i l => (if D.blk i = k then (1 : ℂ) else 0) * (if D.blk l = k then (1 : ℂ) else 0))
    1 zero_le_one ?_ _ ?_ ?_
  · intro j k hjk
    exact Set.disjoint_left.mpr fun i (hi : D.blk i = j) (hk : D.blk i = k) => hjk (by omega)
  · intro j k hjk
    exact Set.disjoint_left.mpr fun i (hi : D.blk i = j) (hk : D.blk i = k) => hjk (by omega)
  · intro k
    have h := SchurBound.product b (fun i => if D.blk i = k then (1 : ℂ) else 0)
      (fun l => if D.blk l = k then (1 : ℂ) else 0) 1 1 zero_le_one zero_le_one
      (fun i => by split_ifs <;> simp) (fun l => by split_ifs <;> simp)
    simpa only [mul_one] using h
  · intro k i l (hi : D.blk i = k) (hl : D.blk l = k)
    unfold diagMult
    rw [ite_eq_left (by omega), ite_eq_left hi, ite_eq_left hl, mul_one]
  · intro i l h
    unfold diagMult
    exact ite_eq_right fun hc => h (D.blk l) ⟨hc, rfl⟩

end SpectralBlocks

end Involution
