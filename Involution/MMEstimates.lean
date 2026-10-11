module

public import Involution.MMCuts
public import Involution.MMScalar
public import Involution.MMSideInt
public import Involution.MMPointwise

/-! The spectral projections `Q k` of `G` and the estimates of the sums of `P k - Q k`
(Wyss, Lemmas 5.1–5.3, in the variable `ω = √z`). -/

@[expose] public noncomputable section

open Complex Set Filter Topology

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CutData

variable {D : MMData ι H} (C : CutData D)

/-- The index set of the `k`-th block of eigenvalues. -/
def blk (k : ℕ) : Set ι := {i | C.ξ k < D.ω i ∧ D.ω i < C.ξ (k + 1)}

theorem ω_not_mem_bdry (k : ℕ) (i : ι) :
    (D.ω i : ℂ) ∉ bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α := by
  have h1 := C.hsep k i
  have h2 := C.hsep (k + 1) i
  have hα := C.hα
  rintro (⟨_, e | e⟩ | ⟨_, e | e⟩) <;> simp only [ofReal_im, ofReal_re, zero_eq_neg] at e
  · linarith
  · linarith
  · rw [e, sub_self, abs_zero] at h1; linarith [C.hε]
  · rw [e, sub_self, abs_zero] at h2; linarith [C.hε]

theorem Q_apply_basis (k : ℕ) (i : ι) :
    C.Q k (D.b i) = (C.blk k).indicator (1 : ι → ℂ) i • D.b i := by
  have hab := (C.ξ_lt_succ k).le
  have hcd := C.hαlt.le
  have hg := fun ω hω => (C.good_bdry k ω hω).2
  have hF := continuousOn_cF (K := D.K₀) (B := 0) hg
  have h1 := clm_rint (ContinuousLinearMap.apply ℂ H (D.b i)) hab hcd hF
  simp only [ContinuousLinearMap.apply_apply] at h1
  have e : ∀ ω ∈ bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α, cF D.K₀ 0 ω (D.b i) =
      ((-1 : ℂ) * (2 * ω / (ω ^ 2 - (D.ω i : ℂ) ^ 2))) • D.b i := by
    intro ω hω
    have hu : IsUnit (1 - ω ^ 2 • D.K₀) := good0_iff.mp (hg ω hω)
    obtain ⟨hne, -⟩ := D.inv_one_sub_apply_basis hu i
    rw [cF, smul_apply, D.res0_apply_basis hu i, smul_smul]
    congr 1
    have hl : (D.lam i : ℂ) = (D.ω i : ℂ) ^ 2 := by rw [← D.ω_sq]; push_cast; ring
    rw [hl] at hne ⊢
    have hne' : ω ^ 2 - (D.ω i : ℂ) ^ 2 ≠ 0 := fun h => hne (by linear_combination -h)
    field_simp
    ring
  unfold Q rP
  rw [smul_apply, h1, rint_congr hab hcd e, rint_const_smul, smul_smul]
  have hk : rint (fun ω => (-1 : ℂ) * (2 * ω / (ω ^ 2 - (D.ω i : ℂ) ^ 2)))
      (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α =
      -rint (fun ω : ℂ => (ω - D.ω i)⁻¹) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α := by
    have := rint_smul (E := ℂ) (f := fun ω => 2 * ω / (ω ^ 2 - (D.ω i : ℂ) ^ 2))
      (a := C.ξ k) (b := C.ξ (k + 1)) (c := -C.α) (d := C.α) (-1 : ℂ)
    simp only [smul_eq_mul] at this
    rw [this, rint_kernel_omega (C.ξ_pos k) hab hcd (by simpa using D.ω_pos i)
      (C.ω_not_mem_bdry k i)]
    ring
  rw [hk]
  congr 1
  by_cases hi : i ∈ C.blk k
  · rw [Set.indicator_of_mem hi, rint_inv_sub_of_mem]
    · simp only [Pi.one_apply]
      field_simp [two_pi_I_ne]
    · exact ⟨by simpa using (show C.ξ k < D.ω i ∧ D.ω i < C.ξ (k + 1) from hi), by simp [C.hα]⟩
  · rw [Set.indicator_of_notMem hi, rint_inv_sub_of_not_mem hab hcd]
    · simp
    · rintro ⟨⟨h1, h2⟩, _⟩
      simp only [ofReal_re] at h1 h2
      have s1 := C.hsep k i
      have s2 := C.hsep (k + 1) i
      apply hi
      constructor
      · rcases h1.lt_or_eq with h | h
        · exact h
        · rw [h, sub_self, abs_zero] at s1; linarith [C.hε]
      · rcases h2.lt_or_eq with h | h
        · exact h
        · rw [h, sub_self, abs_zero] at s2; linarith [C.hε]

theorem Q_eq (k : ℕ) : C.Q k = diagOp D.b ((C.blk k).indicator 1) := by
  apply clm_ext_basis D.b
  intro i
  rw [C.Q_apply_basis, diagOp_apply_basis D.b _ 1 (norm_indicator_one_le _)]

/-- The weight `1 / |ω_i - ω|²`. -/
def _root_.Involution.MMData.hinv (D : MMData ι H) (i : ι) : ℂ → ℝ :=
  fun ω => 1 / ‖(D.ω i : ℂ) - ω‖ ^ 2

/-- The horizontal weight `1 / ((x - ω_i)² + α²)`. -/
def gh (i : ι) : ℝ → ℝ := fun x => 1 / ((x - D.ω i) ^ 2 + C.α ^ 2)

theorem gh_cont (i : ι) : Continuous (C.gh i) := by
  refine Continuous.div continuous_const (by fun_prop) fun x => ?_
  have := C.hα; positivity

theorem gh_nonneg (i : ι) (x : ℝ) : 0 ≤ C.gh i x := by
  unfold gh; have := C.hα; positivity

theorem hinv_cont (k : ℕ) (i : ι) :
    ContinuousOn (D.hinv i) (bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α) := by
  refine ContinuousOn.div continuousOn_const
    ((continuous_const.sub continuous_id).norm.pow 2).continuousOn fun ω hω => ?_
  have : (D.ω i : ℂ) - ω ≠ 0 := fun h => C.ω_not_mem_bdry k i (by rwa [sub_eq_zero.mp h])
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr this)

theorem hinv_horiz (i : ι) (x y : ℝ) (hy : y ^ 2 = C.α ^ 2) :
    D.hinv i (x + y * I) = C.gh i x := by
  unfold MMData.hinv gh
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

theorem integral_vert_le (i : ι) (ξ : ℝ) (hξ : C.ε ≤ |ξ - D.ω i|) :
    ∫ y in (-C.α)..C.α, D.hinv i (ξ + y * I) ≤ 2 * C.α / (ξ - D.ω i) ^ 2 := by
  have hα := C.hα
  have hpos : 0 < (ξ - D.ω i) ^ 2 := by
    have := C.hε
    have : 0 < |ξ - D.ω i| := by linarith
    rw [← sq_abs]; positivity
  have hle : ∀ y ∈ Icc (-C.α) C.α, D.hinv i (ξ + y * I) ≤ 1 / (ξ - D.ω i) ^ 2 := by
    intro y _
    unfold MMData.hinv
    apply one_div_le_one_div_of_le hpos
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg y]
  have hcont : Continuous fun y : ℝ => D.hinv i (ξ + y * I) := by
    unfold MMData.hinv
    refine Continuous.div continuous_const (by fun_prop) fun y => ?_
    have : (D.ω i : ℂ) - (ξ + y * I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have h0 : ξ - D.ω i = 0 := by linarith
      rw [h0, abs_zero] at hξ
      linarith [C.hε]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr this)
  calc ∫ y in (-C.α)..C.α, D.hinv i (ξ + y * I) ≤ ∫ y in (-C.α)..C.α, 1 / (ξ - D.ω i) ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
          intervalIntegrable_const hle
    _ = 2 * C.α / (ξ - D.ω i) ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem sideInt_hinv_le (k : ℕ) (i : ι) :
    sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α ≤
      2 * (∫ x in (C.ξ k)..(C.ξ (k + 1)), C.gh i x) + 2 * C.α / (C.ξ (k + 1) - D.ω i) ^ 2 +
        2 * C.α / (C.ξ k - D.ω i) ^ 2 := by
  unfold sideInt
  have e1 : (∫ x in (C.ξ k)..(C.ξ (k + 1)), D.hinv i (x + ((-C.α : ℝ) : ℂ) * I)) =
      ∫ x in (C.ξ k)..(C.ξ (k + 1)), C.gh i x :=
    intervalIntegral.integral_congr fun x _ => C.hinv_horiz i x _ (by ring)
  have e2 : (∫ x in (C.ξ k)..(C.ξ (k + 1)), D.hinv i (x + (C.α : ℂ) * I)) =
      ∫ x in (C.ξ k)..(C.ξ (k + 1)), C.gh i x :=
    intervalIntegral.integral_congr fun x _ => C.hinv_horiz i x _ rfl
  rw [e1, e2]
  have h3 := C.integral_vert_le i (C.ξ (k + 1)) (C.hsep (k + 1) i)
  have h4 := C.integral_vert_le i (C.ξ k) (C.hsep k i)
  linarith

theorem inv_sq_le (k : ℕ) (i : ι) : 1 / (C.ξ k - D.ω i) ^ 2 ≤ 1 / C.ε ^ 2 := by
  apply one_div_le_one_div_of_le (pow_pos C.hε 2)
  have := pow_le_pow_left₀ C.hε.le (C.hsep k i) 2
  rwa [sq_abs] at this

/-- The per-rectangle bound. -/
theorem sideInt_hinv_le_M1 (k : ℕ) (i : ι) :
    sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α ≤
      2 * Real.pi / C.α + 4 * C.α / C.ε ^ 2 := by
  have h1 := C.sideInt_hinv_le k i
  have h2 := integral_inv_sq_add_sq_le (D.ω i) C.α (C.ξ k) (C.ξ (k + 1)) C.hα
  have h3 := C.inv_sq_le (k + 1) i
  have h4 := C.inv_sq_le k i
  have hα := C.hα
  have e : ∀ x : ℝ, 2 * C.α / x = 2 * C.α * (1 / x) := fun x => by ring
  rw [e, e] at h1
  have : ∫ x in (C.ξ k)..(C.ξ (k + 1)), C.gh i x ≤ Real.pi / C.α := h2
  calc _ ≤ _ := h1
    _ ≤ 2 * (Real.pi / C.α) + 2 * C.α * (1 / C.ε ^ 2) + 2 * C.α * (1 / C.ε ^ 2) := by gcongr
    _ = _ := by ring

/-- The bound for sums over rectangles. -/
theorem sum_sideInt_hinv_le (t : Finset ℕ) (i : ι) :
    ∑ k ∈ t, sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α ≤
      2 * Real.pi / C.α + 8 * C.α * (1 / C.ε ^ 2 + 1 / (C.ε * C.d)) := by
  set N := t.sup id + 1
  have ht : t ⊆ Finset.range N := fun k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  set F : ℕ → ℝ := fun k => 2 * (∫ x in (C.ξ k)..(C.ξ (k + 1)), C.gh i x) +
    2 * C.α / (C.ξ (k + 1) - D.ω i) ^ 2 + 2 * C.α / (C.ξ k - D.ω i) ^ 2
  have hα := C.hα
  have hF0 : ∀ k, 0 ≤ F k := by
    intro k
    have : 0 ≤ ∫ x in (C.ξ k)..(C.ξ (k + 1)), C.gh i x :=
      intervalIntegral.integral_nonneg (C.ξ_lt_succ k).le fun x _ => C.gh_nonneg i x
    simp only [F]; positivity
  have hS := sum_inv_sq_sep C.ξ C.ε C.d C.hε C.hd C.hgap (D.ω i) (C.hsep · i)
  calc ∑ k ∈ t, sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α ≤ ∑ k ∈ t, F k :=
        Finset.sum_le_sum fun k _ => C.sideInt_hinv_le k i
    _ ≤ ∑ k ∈ Finset.range N, F k :=
        Finset.sum_le_sum_of_subset_of_nonneg ht fun k _ _ => hF0 k
    _ = 2 * (∫ x in (C.ξ 0)..(C.ξ N), C.gh i x) +
          2 * C.α * ∑ k ∈ Finset.range N, 1 / (C.ξ (k + 1) - D.ω i) ^ 2 +
          2 * C.α * ∑ k ∈ Finset.range N, 1 / (C.ξ k - D.ω i) ^ 2 := by
        rw [← intervalIntegral.sum_integral_adjacent_intervals
          (fun k _ => (C.gh_cont i).intervalIntegrable _ _)]
        simp only [F, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · congr 1
          refine Finset.sum_congr rfl fun k _ => ?_; ring
        · refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ 2 * (Real.pi / C.α) + 2 * C.α * (2 * (1 / C.ε ^ 2 + 1 / (C.ε * C.d))) +
          2 * C.α * (2 * (1 / C.ε ^ 2 + 1 / (C.ε * C.d))) := by
        gcongr
        · exact integral_inv_sq_add_sq_le _ _ _ _ C.hα
        · calc ∑ k ∈ Finset.range N, 1 / (C.ξ (k + 1) - D.ω i) ^ 2
              ≤ ∑ j ∈ Finset.range (N + 1), 1 / (C.ξ j - D.ω i) ^ 2 := by
                have e := Finset.sum_range_succ' (fun j => 1 / (C.ξ j - D.ω i) ^ 2) N
                have : 0 ≤ 1 / (C.ξ 0 - D.ω i) ^ 2 := by positivity
                linarith
            _ ≤ _ := hS (N + 1)
        · exact hS N
    _ = _ := by ring

theorem two_mul_le_amgm (x y τ : ℝ) (hτ : 0 < τ) : 2 * x * y ≤ τ * x ^ 2 + y ^ 2 / τ := by
  have h1 : 0 ≤ (τ * x - y) ^ 2 / τ := by positivity
  have h2 : (τ * x - y) ^ 2 / τ = τ * x ^ 2 + y ^ 2 / τ - 2 * x * y := by
    field_simp; ring
  linarith

/-- Units and bounds on the boundary of the `k`-th rectangle. -/
theorem bdry_W (k : ℕ) : ∀ ω ∈ bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α,
    0 ≤ ω.re ∧ IsUnit (1 - ω ^ 2 • D.K₀) ∧ IsUnit (1 + D.N (ω ^ 2)) ∧
      ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤ C.CW := by
  intro ω hω
  have hre : 0 ≤ ω.re := by
    have := (bdry_subset_crect _ _ _ _ (C.ξ_lt_succ k).le C.hαlt.le hω).1.1
    linarith [C.ξ_pos k]
  refine ⟨hre, ?_⟩
  rcases hω with ⟨_, e | e⟩ | ⟨⟨h1, h2⟩, e | e⟩
  · obtain ⟨a, b, c, -⟩ := C.good_of_far (C.far_of_off (ω := ω) hre
      (Or.inl (by rw [e, abs_neg, abs_of_pos C.hα])))
    exact ⟨a, b, c.trans C.hCW⟩
  · obtain ⟨a, b, c, -⟩ := C.good_of_far (C.far_of_off (ω := ω) hre
      (Or.inl (by rw [e, abs_of_pos C.hα])))
    exact ⟨a, b, c.trans C.hCW⟩
  · have hω : ω = (C.ξ k : ℂ) + ω.im * I := by apply Complex.ext <;> simp [e]
    have hy : |ω.im| ≤ C.α := abs_le.mpr ⟨h1, h2⟩
    rw [hω]
    exact ⟨C.vert_unit k _, (C.hW k _ hy).1, (C.hW k _ hy).2⟩
  · have hω : ω = (C.ξ (k + 1) : ℂ) + ω.im * I := by apply Complex.ext <;> simp [e]
    have hy : |ω.im| ≤ C.α := abs_le.mpr ⟨h1, h2⟩
    rw [hω]
    exact ⟨C.vert_unit (k + 1) _, (C.hW (k + 1) _ hy).1, (C.hW (k + 1) _ hy).2⟩

/-- The estimate for a single rectangle, for finite coordinate vectors. -/
theorem est_k (k : ℕ) (s : Finset ι) (y w : ι → ℂ) (τ : ℝ) (hτ : 0 < τ) :
    ‖inner ℂ (∑ i ∈ s, w i • D.b i) ((C.P k - C.Q k) (∑ i ∈ s, y i • D.b i))‖ ≤
      (2 * Real.pi)⁻¹ * ∑ i ∈ s, (C.CW * D.b₁ * (τ * ‖y i‖ ^ 2 + ‖w i‖ ^ 2 / τ)) *
        sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α := by
  have hab := (C.ξ_lt_succ k).le
  have hcd := C.hαlt.le
  have hgB := fun ω hω => (C.good_bdry k ω hω).1
  have hg0 := fun ω hω => (C.good_bdry k ω hω).2
  set yv := ∑ i ∈ s, y i • D.b i
  set wv := ∑ i ∈ s, w i • D.b i
  set F : ℂ → (H →L[ℂ] H) := fun ω => cF D.K₀ D.B ω - cF D.K₀ 0 ω
  have hF : ContinuousOn F (bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α) :=
    (continuousOn_cF hgB).sub (continuousOn_cF hg0)
  have hPQ : C.P k - C.Q k = (-(2 * Real.pi * I)⁻¹) • rint F (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α := by
    unfold P Q rP
    rw [← smul_sub, ← rint_sub hab hcd (continuousOn_cF hgB) (continuousOn_cF hg0)]
  set L : (H →L[ℂ] H) →L[ℂ] ℂ := (innerSL ℂ wv).comp (ContinuousLinearMap.apply ℂ H yv)
  have hL : ∀ X : H →L[ℂ] H, L X = inner ℂ wv (X yv) := fun X => rfl
  have h1 := clm_rint L hab hcd hF
  set G : ℂ → ℝ := fun ω => ∑ i ∈ s, (C.CW * D.b₁ * (τ * ‖y i‖ ^ 2 + ‖w i‖ ^ 2 / τ)) *
    D.hinv i ω
  have hGc : ContinuousOn G (bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (C.hinv_cont k i)
  have hpt : ∀ ω ∈ bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α, ‖L (F ω)‖ ≤ G ω := by
    intro ω hω
    obtain ⟨hre, hz, hN, hW⟩ := C.bdry_W k ω hω
    rw [hL]
    refine (D.pointwise hre hz hN hW s y w).trans ?_
    set A := ∑ i ∈ s, ‖y i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2
    set Cw := ∑ i ∈ s, ‖w i‖ ^ 2 / ‖(D.ω i : ℂ) - ω‖ ^ 2
    have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
    have hC : 0 ≤ Cw := Finset.sum_nonneg fun i _ => by positivity
    have hcb : 0 ≤ C.CW * D.b₁ := mul_nonneg (by linarith [C.hCW]) D.hb₁
    have h2 := two_mul_le_amgm (Real.sqrt A) (Real.sqrt Cw) τ hτ
    rw [Real.sq_sqrt hA, Real.sq_sqrt hC] at h2
    have hG : G ω = C.CW * D.b₁ * (τ * A + Cw / τ) := by
      simp only [G, A, Cw, MMData.hinv, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hG]
    calc 2 * C.CW * D.b₁ * Real.sqrt A * Real.sqrt Cw =
        C.CW * D.b₁ * (2 * Real.sqrt A * Real.sqrt Cw) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hcb
  have hLc : ContinuousOn (fun ω => ‖L (F ω)‖) (bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α) :=
    (L.continuous.comp_continuousOn hF).norm
  rw [hPQ, smul_apply, inner_smul_right, norm_mul, ← hL, h1]
  have hn : ‖-(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_neg, norm_inv, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, show ‖(2 : ℂ)‖ = 2 by simp, mul_one]
  rw [hn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖rint (fun ω => L (F ω)) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α‖
      ≤ sideInt (fun ω => ‖L (F ω)‖) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α :=
        norm_rint_le_sideInt hab hcd
    _ ≤ sideInt G (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α := sideInt_mono hab hcd hLc hGc hpt
    _ = _ := sideInt_sum s _ _ hab hcd fun i _ => C.hinv_cont k i

/-- The constant of the estimates. -/
def cst : ℝ := (2 * Real.pi)⁻¹ * C.CW * D.b₁ * 2 *
  Real.sqrt ((2 * Real.pi / C.α + 4 * C.α / C.ε ^ 2) *
    (2 * Real.pi / C.α + 8 * C.α * (1 / C.ε ^ 2 + 1 / (C.ε * C.d))))

theorem cst_nonneg : 0 ≤ C.cst := by
  unfold cst
  have := C.hCW
  have := D.hb₁
  have : 0 ≤ C.CW := by linarith
  positivity

theorem sideInt_hinv_nonneg (k : ℕ) (i : ι) :
    0 ≤ sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α := by
  unfold sideInt
  have hab := (C.ξ_lt_succ k).le
  have hcd := C.hαlt.le
  have h0 : ∀ ω, 0 ≤ D.hinv i ω := fun ω => by unfold MMData.hinv; positivity
  have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hab
    fun x _ => h0 (x + ((-C.α : ℝ) : ℂ) * I)
  have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hab
    fun x _ => h0 (x + (C.α : ℂ) * I)
  have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hcd
    fun y _ => h0 ((C.ξ (k + 1) : ℂ) + y * I)
  have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hcd
    fun y _ => h0 ((C.ξ k : ℂ) + y * I)
  linarith

/-- First estimate, for finite coordinate vectors. -/
theorem est1_fin (t : Finset ℕ) (s : Finset ι) (y : ℕ → ι → ℂ) (w : ι → ℂ) :
    ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, w i • D.b i) ((C.P k - C.Q k) (∑ i ∈ s, y k i • D.b i))‖ ≤
      C.cst * Real.sqrt (∑ k ∈ t, ∑ i ∈ s, ‖y k i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) := by
  set M1 := 2 * Real.pi / C.α + 4 * C.α / C.ε ^ 2
  set M2 := 2 * Real.pi / C.α + 8 * C.α * (1 / C.ε ^ 2 + 1 / (C.ε * C.d))
  set K := (2 * Real.pi)⁻¹ * (C.CW * D.b₁)
  have hK : 0 ≤ K := by
    have := C.hCW; have := D.hb₁; have : 0 ≤ C.CW := by linarith
    positivity
  set Y := ∑ k ∈ t, ∑ i ∈ s, ‖y k i‖ ^ 2
  set Wn := ∑ i ∈ s, ‖w i‖ ^ 2
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0 ≤ Wn := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM1 : 0 ≤ M1 := by
    have := C.hα; have := C.hε; positivity
  have hM2 : 0 ≤ M2 := by
    have := C.hα; have := C.hε; have := C.hd; positivity
  have key : ∀ τ : ℝ, 0 < τ → ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, w i • D.b i)
      ((C.P k - C.Q k) (∑ i ∈ s, y k i • D.b i))‖ ≤ τ * (K * M1 * Y) + K * M2 * Wn / τ := by
    intro τ hτ
    set S : ℕ → ι → ℝ := fun k i => sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α
    have hS0 : ∀ k i, 0 ≤ S k i := fun k i => C.sideInt_hinv_nonneg k i
    have h1 : ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, w i • D.b i) ((C.P k - C.Q k) (∑ i ∈ s, y k i • D.b i))‖
        ≤ ∑ k ∈ t, (∑ i ∈ s, K * τ * ‖y k i‖ ^ 2 * S k i + ∑ i ∈ s, K * τ⁻¹ * ‖w i‖ ^ 2 * S k i) :=
      Finset.sum_le_sum fun k _ => (C.est_k k s (y k) w τ hτ).trans_eq (by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [K, S]; rw [div_eq_mul_inv]; ring)
    have hA : ∑ k ∈ t, ∑ i ∈ s, K * τ * ‖y k i‖ ^ 2 * S k i ≤ τ * (K * M1 * Y) := by
      calc _ ≤ ∑ k ∈ t, ∑ i ∈ s, K * τ * ‖y k i‖ ^ 2 * M1 :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (C.sideInt_hinv_le_M1 k i) (by positivity)
        _ = _ := by
            simp only [Y, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    have hB : ∑ k ∈ t, ∑ i ∈ s, K * τ⁻¹ * ‖w i‖ ^ 2 * S k i ≤ K * M2 * Wn / τ := by
      rw [Finset.sum_comm]
      calc _ = ∑ i ∈ s, K * τ⁻¹ * ‖w i‖ ^ 2 * ∑ k ∈ t, S k i :=
            Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ s, K * τ⁻¹ * ‖w i‖ ^ 2 * M2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (C.sum_sideInt_hinv_le t i) (by positivity)
        _ = _ := by
            simp only [Wn, Finset.mul_sum, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
    rw [Finset.sum_add_distrib] at h1
    linarith
  have h := le_of_forall_amgm (by positivity) (by positivity) key
  calc _ ≤ 2 * Real.sqrt (K * M1 * Y * (K * M2 * Wn)) := h
    _ = C.cst * Real.sqrt Y * Real.sqrt Wn := by
        have e : K * M1 * Y * (K * M2 * Wn) = K ^ 2 * (M1 * M2) * Y * Wn := by ring
        rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq hK]
        simp only [cst, K, M1, M2]
        ring

/-- Second estimate, for finite coordinate vectors. -/
theorem est2_fin (t : Finset ℕ) (s : Finset ι) (y : ι → ℂ) (w : ℕ → ι → ℂ) :
    ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, w k i • D.b i) ((C.P k - C.Q k) (∑ i ∈ s, y i • D.b i))‖ ≤
      C.cst * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) * Real.sqrt (∑ k ∈ t, ∑ i ∈ s, ‖w k i‖ ^ 2) := by
  set M1 := 2 * Real.pi / C.α + 4 * C.α / C.ε ^ 2
  set M2 := 2 * Real.pi / C.α + 8 * C.α * (1 / C.ε ^ 2 + 1 / (C.ε * C.d))
  set K := (2 * Real.pi)⁻¹ * (C.CW * D.b₁)
  have hK : 0 ≤ K := by
    have := C.hCW; have := D.hb₁; have : 0 ≤ C.CW := by linarith
    positivity
  set Yn := ∑ i ∈ s, ‖y i‖ ^ 2
  set W := ∑ k ∈ t, ∑ i ∈ s, ‖w k i‖ ^ 2
  have hY : 0 ≤ Yn := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM1 : 0 ≤ M1 := by
    have := C.hα; have := C.hε; positivity
  have hM2 : 0 ≤ M2 := by
    have := C.hα; have := C.hε; have := C.hd; positivity
  have key : ∀ τ : ℝ, 0 < τ → ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, w k i • D.b i)
      ((C.P k - C.Q k) (∑ i ∈ s, y i • D.b i))‖ ≤ τ * (K * M2 * Yn) + K * M1 * W / τ := by
    intro τ hτ
    set S : ℕ → ι → ℝ := fun k i => sideInt (D.hinv i) (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α
    have hS0 : ∀ k i, 0 ≤ S k i := fun k i => C.sideInt_hinv_nonneg k i
    have h1 : ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, w k i • D.b i) ((C.P k - C.Q k) (∑ i ∈ s, y i • D.b i))‖
        ≤ ∑ k ∈ t, (∑ i ∈ s, K * τ * ‖y i‖ ^ 2 * S k i + ∑ i ∈ s, K * τ⁻¹ * ‖w k i‖ ^ 2 * S k i) :=
      Finset.sum_le_sum fun k _ => (C.est_k k s y (w k) τ hτ).trans_eq (by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [K, S]; rw [div_eq_mul_inv]; ring)
    have hA : ∑ k ∈ t, ∑ i ∈ s, K * τ * ‖y i‖ ^ 2 * S k i ≤ τ * (K * M2 * Yn) := by
      rw [Finset.sum_comm]
      calc _ = ∑ i ∈ s, K * τ * ‖y i‖ ^ 2 * ∑ k ∈ t, S k i :=
            Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ s, K * τ * ‖y i‖ ^ 2 * M2 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (C.sum_sideInt_hinv_le t i) (by positivity)
        _ = _ := by
            simp only [Yn, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    have hB : ∑ k ∈ t, ∑ i ∈ s, K * τ⁻¹ * ‖w k i‖ ^ 2 * S k i ≤ K * M1 * W / τ := by
      calc _ ≤ ∑ k ∈ t, ∑ i ∈ s, K * τ⁻¹ * ‖w k i‖ ^ 2 * M1 :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (C.sideInt_hinv_le_M1 k i) (by positivity)
        _ = _ := by
            simp only [W, Finset.mul_sum, Finset.sum_div]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by
              rw [div_eq_mul_inv]; ring
    rw [Finset.sum_add_distrib] at h1
    linarith
  have h := le_of_forall_amgm (by positivity) (by positivity) key
  calc _ ≤ 2 * Real.sqrt (K * M2 * Yn * (K * M1 * W)) := h
    _ = C.cst * Real.sqrt Yn * Real.sqrt W := by
        have e : K * M2 * Yn * (K * M1 * W) = K ^ 2 * (M1 * M2) * Yn * W := by ring
        rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq hK]
        simp only [cst, K, M1, M2]
        ring

theorem estimates : ∃ c : ℝ, 0 ≤ c ∧
    (∀ (t : Finset ℕ) (x : ℕ → H) (w : H),
      ∑ k ∈ t, ‖inner ℂ w ((C.P k - C.Q k) (x k))‖ ≤ c * Real.sqrt (∑ k ∈ t, ‖x k‖ ^ 2) * ‖w‖) ∧
    (∀ (t : Finset ℕ) (u : H) (w : ℕ → H),
      ∑ k ∈ t, ‖inner ℂ (w k) ((C.P k - C.Q k) u)‖ ≤ c * ‖u‖ * Real.sqrt (∑ k ∈ t, ‖w k‖ ^ 2)) := by
  have hc := C.cst_nonneg
  have hrepr : ∀ v : H, Tendsto (fun s : Finset ι => ∑ i ∈ s, inner ℂ (D.b i) v • D.b i)
      atTop (𝓝 v) := fun v => by
    have := D.b.hasSum_repr v
    simp only [HilbertBasis.repr_apply_apply] at this
    exact this
  have hbes : ∀ (v : H) (s : Finset ι),
      Real.sqrt (∑ i ∈ s, ‖inner ℂ (D.b i) v‖ ^ 2) ≤ ‖v‖ := fun v s => by
    rw [Real.sqrt_le_left (norm_nonneg _)]
    exact D.b.orthonormal.sum_inner_products_le v
  refine ⟨C.cst, hc, ?_, ?_⟩
  · intro t x w
    have hlim : Tendsto (fun s : Finset ι => ∑ k ∈ t, ‖inner ℂ (∑ i ∈ s, inner ℂ (D.b i) w • D.b i)
        ((C.P k - C.Q k) (∑ i ∈ s, inner ℂ (D.b i) (x k) • D.b i))‖) atTop
        (𝓝 (∑ k ∈ t, ‖inner ℂ w ((C.P k - C.Q k) (x k))‖)) :=
      tendsto_finsetSum t fun k _ =>
        ((hrepr w).inner (((C.P k - C.Q k).continuous.tendsto _).comp (hrepr (x k)))).norm
    refine le_of_tendsto' hlim fun s => ?_
    refine (C.est1_fin t s (fun k i => inner ℂ (D.b i) (x k)) (fun i => inner ℂ (D.b i) w)).trans ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hc) (hbes w s) (Real.sqrt_nonneg _)
      (by positivity)
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
      D.b.orthonormal.sum_inner_products_le (x k))
  · intro t u w
    have hlim : Tendsto (fun s : Finset ι => ∑ k ∈ t, ‖inner ℂ
        (∑ i ∈ s, inner ℂ (D.b i) (w k) • D.b i)
        ((C.P k - C.Q k) (∑ i ∈ s, inner ℂ (D.b i) u • D.b i))‖) atTop
        (𝓝 (∑ k ∈ t, ‖inner ℂ (w k) ((C.P k - C.Q k) u)‖)) :=
      tendsto_finsetSum t fun k _ =>
        ((hrepr (w k)).inner (((C.P k - C.Q k).continuous.tendsto _).comp (hrepr u))).norm
    refine le_of_tendsto' hlim fun s => ?_
    refine (C.est2_fin t s (fun i => inner ℂ (D.b i) u) (fun k i => inner ℂ (D.b i) (w k))).trans ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hbes u s) hc) ?_ (Real.sqrt_nonneg _)
      (by positivity)
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
      D.b.orthonormal.sum_inner_products_le (w k))

end CutData

end Involution
