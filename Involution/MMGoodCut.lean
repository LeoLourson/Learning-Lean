module

public import Involution.MMCuts
public import Involution.MMWindowCut

/-! Existence of cuts with uniform resolvent bounds (Wyss, Proposition 5.5 and Corollary 5.6,
in the variable `ω = √z`). From the counting bound, every half-line `[a, ∞)` contains a window
of fixed width with boundedly many `ω i`; inside it, `window_cut` provides a cut point. -/

@[expose] public noncomputable section

open Complex Set Filter Topology

namespace Involution

theorem finite_of_count {ι : Type*} (ω : ι → ℝ) (c₂ C₀ : ℝ)
    (hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, ω i ≤ t) → (s.card : ℝ) ≤ c₂ * t + C₀)
    (t : ℝ) : {i | ω i ≤ t}.Finite := by
  have hsub : {i | ω i ≤ t} ⊆ {i | ω i ≤ max t 0} :=
    fun i (hi : ω i ≤ t) => show ω i ≤ max t 0 from le_trans hi (le_max_left _ _)
  refine Set.Finite.subset ?_ hsub
  by_contra hinf
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈c₂ * max t 0 + C₀⌉₊ + 1)
  have := hcount (max t 0) (le_max_right _ _) s (fun i hi => hs hi)
  rw [hcard] at this
  push_cast at this
  linarith [Nat.le_ceil (c₂ * max t 0 + C₀)]

theorem exists_sparse_window {ι : Type*} (ω : ι → ℝ) (c₂ C₀ W : ℝ) (hc₂ : 0 ≤ c₂)
    (hC₀ : 0 ≤ C₀) (hW : 0 < W)
    (hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, ω i ≤ t) → (s.card : ℝ) ≤ c₂ * t + C₀)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ x₀ : ℝ, a ≤ x₀ ∧ ∃ J : Finset ι, (∀ i, i ∈ J ↔ |ω i - x₀| < W) ∧
      J.card ≤ ⌈c₂ * (1 + 2 * W) + C₀⌉₊ := by
  classical
  set Mp := ⌈c₂ * (1 + 2 * W) + C₀⌉₊
  set T := ⌈a⌉₊ + 1 with hT
  have hTa : a ≤ T := by
    have := Nat.le_ceil a; simp only [T]; push_cast; linarith
  have hT1 : (1 : ℝ) ≤ T := by simp only [T]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈a⌉₊]
  set x : ℕ → ℝ := fun t => a + W + 2 * W * t
  have hfin : ∀ t : ℕ, {i | |ω i - x t| < W}.Finite := fun t =>
    (finite_of_count ω c₂ C₀ hcount (x t + W)).subset fun i hi => by
      have := (abs_lt.mp (show |ω i - x t| < W from hi)).2; simp only [mem_ofPred_eq]; linarith
  set Jt : ℕ → Finset ι := fun t => (hfin t).toFinset
  have hJt : ∀ t i, i ∈ Jt t ↔ |ω i - x t| < W := fun t i => by simp [Jt]
  by_contra hcon
  push Not at hcon
  have hbig : ∀ t ∈ Finset.range T, Mp + 1 ≤ (Jt t).card := by
    intro t ht
    have := hcon (x t) (by have := Nat.cast_nonneg (α := ℝ) t; simp only [x]; nlinarith)
      (Jt t) (hJt t)
    omega
  have hdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint Jt := by
    intro s _ t _ hst
    rw [Function.onFun, Finset.disjoint_left]
    intro i his hit
    rw [hJt] at his hit
    have h1 := abs_lt.mp his; have h2 := abs_lt.mp hit
    simp only [x] at h1 h2
    rcases lt_or_gt_of_ne hst with h | h
    · have : (s : ℝ) + 1 ≤ t := by exact_mod_cast h
      nlinarith
    · have : (t : ℝ) + 1 ≤ s := by exact_mod_cast h
      nlinarith
  set U := (Finset.range T).biUnion Jt
  have hU1 : T * (Mp + 1) ≤ U.card := by
    rw [Finset.card_biUnion hdisj]
    calc T * (Mp + 1) = ∑ _t ∈ Finset.range T, (Mp + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum hbig
  have hU2 : (U.card : ℝ) ≤ c₂ * (a + 2 * W * T) + C₀ := by
    refine hcount _ (by positivity) U fun i hi => ?_
    obtain ⟨t, ht, hi⟩ := Finset.mem_biUnion.mp hi
    rw [hJt] at hi
    have h1 := (abs_lt.mp hi).2
    have : (t : ℝ) + 1 ≤ T := by exact_mod_cast Finset.mem_range.mp ht
    simp only [x] at h1
    nlinarith
  have hU1' : (T : ℝ) * (Mp + 1) ≤ U.card := by exact_mod_cast hU1
  have hMp : c₂ * (1 + 2 * W) + C₀ ≤ Mp := Nat.le_ceil _
  have : c₂ * (a + 2 * W * T) + C₀ ≤ T * (c₂ * (1 + 2 * W) + C₀) := by nlinarith
  nlinarith

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace MMData

theorem exists_cuts (β c₂ C₀ : ℝ) (hβ : 0 ≤ β) (hc₂ : 0 < c₂) (hC₀ : 0 ≤ C₀) :
    ∃ M : ℝ, ∀ D : MMData ι H, D.b₁ = β →
      (∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, D.ω i ≤ t) → (s.card : ℝ) ≤ c₂ * t + C₀) →
      M ≤ D.m → Nonempty (CutData D) := by
  classical
  set α := 2 * β + 1 with hα
  have hα0 : 0 < α := by linarith
  have hW0 : 0 < winW β := by unfold winW; linarith
  obtain ⟨X₀, ε, CW, hε, hCW, hwc⟩ :=
    window_cut (ι := ι) (H := H) β hβ ⌈c₂ * (1 + 2 * winW β) + C₀⌉₊
  refine ⟨|X₀| + 2 * α + 1, fun D hD hcount hm => ?_⟩
  have hX := abs_nonneg X₀
  have hgood : ∀ a : ℝ, |X₀| ≤ a → ∃ x : ℝ, a ≤ x ∧ (∀ i, ε ≤ |x - D.ω i|) ∧
      ∀ y : ℝ, |y| ≤ α → IsUnit (1 + D.N (((x : ℂ) + y * I) ^ 2)) ∧
        ‖Ring.inverse (1 + D.N (((x : ℂ) + y * I) ^ 2))‖ ≤ CW := by
    intro a ha
    obtain ⟨x₀, hx₀, J, hJ, hJc⟩ := exists_sparse_window D.ω c₂ C₀ (winW β) hc₂.le hC₀ hW0
      hcount (a + 1) (by linarith)
    obtain ⟨x, hx, hsep, hW⟩ := hwc D hD x₀ (by linarith [le_abs_self X₀]) J hJ hJc
    exact ⟨x, by linarith [(abs_le.mp hx).1], hsep, hW⟩
  set g : ℝ → ℝ := fun a => if h : |X₀| ≤ a then (hgood a h).choose else a with hgdef
  have hg : ∀ a, |X₀| ≤ a → a ≤ g a ∧ (∀ i, ε ≤ |g a - D.ω i|) ∧
      ∀ y : ℝ, |y| ≤ α → IsUnit (1 + D.N (((g a : ℂ) + y * I) ^ 2)) ∧
        ‖Ring.inverse (1 + D.N (((g a : ℂ) + y * I) ^ 2))‖ ≤ CW := by
    intro a ha
    simp only [g, dite_eq_left ha]
    exact (hgood a ha).choose_spec
  let ξ : ℕ → ℝ := fun k => Nat.rec (motive := fun _ => ℝ) (D.m - α) (fun _ x => g (x + 1)) k
  have hξ0 : ξ 0 = D.m - α := rfl
  have hξs : ∀ k, ξ (k + 1) = g (ξ k + 1) := fun k => rfl
  have hξlow : ∀ k, D.m - α ≤ ξ k := by
    intro k
    induction k with
    | zero => rw [hξ0]
    | succ k ih =>
      rw [hξs]
      have := (hg (ξ k + 1) (by linarith)).1
      linarith
  have hgk : ∀ k, |X₀| ≤ ξ k + 1 := fun k => by linarith [hξlow k]
  have hb : D.b₁ / α ≤ 1 / 2 := by rw [hD, div_le_iff₀ hα0]; linarith
  refine ⟨⟨ξ, α, min ε α, 1, CW, hα0, by rw [hD]; linarith, by rw [hξ0]; linarith,
    by rw [hξ0]; linarith, lt_min hε hα0, one_pos,
    fun k => by rw [hξs]; exact (hg _ (hgk k)).1, ?_, hCW, ?_, ?_⟩⟩
  · intro k i
    cases k with
    | zero =>
      refine (min_le_right _ _).trans ?_
      rw [hξ0]
      have := D.m_le_ω i
      rw [abs_of_nonpos (by linarith)]
      linarith
    | succ k =>
      rw [hξs]
      exact (min_le_left _ _).trans ((hg _ (hgk k)).2.1 i)
  · intro k y hy
    cases k with
    | zero =>
      rw [hξ0]
      have hfar : ∀ i, α ≤ ‖(D.ω i : ℂ) - (((D.m - α : ℝ) : ℂ) + y * I)‖ ∧
          α ≤ ‖(D.ω i : ℂ) + (((D.m - α : ℝ) : ℂ) + y * I)‖ := by
        intro i
        have := D.m_le_ω i
        constructor
        · refine le_trans ?_ (abs_re_le_norm _)
          simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
            mul_one, sub_self, add_zero]
          rw [abs_of_nonneg (by linarith)]
          linarith
        · refine le_trans ?_ (Complex.re_le_norm _)
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
            mul_one, sub_self, add_zero]
          linarith
      obtain ⟨-, h1, h2, -⟩ := D.good_far hα0 hfar hb
      exact ⟨h1, h2.trans hCW⟩
    | succ k =>
      rw [hξs]
      exact (hg _ (hgk k)).2.2 y hy
  · intro t
    refine (finite_of_count D.ω c₂ C₀ hcount (Real.sqrt t)).subset fun i hi => ?_
    simp only [mem_ofPred_eq] at hi ⊢
    exact Real.sqrt_le_sqrt hi

end MMData

end Involution
