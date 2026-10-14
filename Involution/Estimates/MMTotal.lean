module

public import Involution.Estimates.MMCuts
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Completeness of the system of subspaces `V k` (Wyss, Theorem 2.3, via a symmetric
large rectangle in the `ω`-plane). -/

@[expose] public noncomputable section

open Complex Set Filter Topology

namespace Involution

section general

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_rint_le_mul {f : ℂ → E} {a b c d M : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : ∀ ω ∈ bdry a b c d, ‖f ω‖ ≤ M) : ‖rint f a b c d‖ ≤ (2 * (b - a) + 2 * (d - c)) * M := by
  have h1 : ‖∫ x : ℝ in a..b, f (x + c * I)‖ ≤ M * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => h _ (mem_bdry_bottom
      (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩))
  have h2 : ‖∫ x : ℝ in a..b, f (x + d * I)‖ ≤ M * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => h _ (mem_bdry_top
      (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩))
  have h3 : ‖∫ y : ℝ in c..d, f (b + y * I)‖ ≤ M * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => h _ (mem_bdry_right
      (by rw [uIoc_of_le hcd] at hy; exact ⟨hy.1.le, hy.2⟩))
  have h4 : ‖∫ y : ℝ in c..d, f (a + y * I)‖ ≤ M * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => h _ (mem_bdry_left
      (by rw [uIoc_of_le hcd] at hy; exact ⟨hy.1.le, hy.2⟩))
  rw [abs_of_nonneg (by linarith)] at h1 h2
  rw [abs_of_nonneg (by linarith)] at h3 h4
  unfold rint
  calc _ ≤ ‖∫ x : ℝ in a..b, f (x + c * I)‖ + ‖∫ x : ℝ in a..b, f (x + d * I)‖ +
        ‖I • ∫ y : ℝ in c..d, f (b + y * I)‖ + ‖I • ∫ y : ℝ in c..d, f (a + y * I)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
        simp only [norm_smul, norm_I, one_mul]
        linarith

end general

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

theorem cF_neg (K B : A) (ω : ℂ) : cF K B (-ω) = -cF K B ω := by
  simp [cF]

theorem good_neg {K B : A} {ω : ℂ} : Good K B (-ω) ↔ Good K B ω := by
  simp [Good]

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lower bound for `|λ - ω²|` from distances to `±√λ`. -/
theorem norm_lam_sub_sq_ge' {p r : ℝ} {ω : ℂ} (hr : 0 < r) (h1 : r ≤ ‖(p : ℂ) - ω‖)
    (h2 : r ≤ ‖(p : ℂ) + ω‖) : r * ‖ω‖ ≤ ‖(p : ℂ) ^ 2 - ω ^ 2‖ := by
  have e : (p : ℂ) ^ 2 - ω ^ 2 = ((p : ℂ) - ω) * ((p : ℂ) + ω) := by ring
  rw [e, norm_mul]
  have htri : 2 * ‖ω‖ ≤ ‖(p : ℂ) - ω‖ + ‖(p : ℂ) + ω‖ := by
    have := norm_sub_le ((p : ℂ) + ω) ((p : ℂ) - ω)
    rw [show (p : ℂ) + ω - ((p : ℂ) - ω) = 2 * ω by ring, norm_mul] at this
    simp at this
    linarith
  rcases le_total ‖(p : ℂ) - ω‖ ‖(p : ℂ) + ω‖ with h | h
  · nlinarith [norm_nonneg ω]
  · nlinarith [norm_nonneg ω]

namespace CutData

variable {D : MMData ι H} (C : CutData D)

/-- Goodness on the boundary of `[ξ j, ξ n] × [-α, α]`. -/
theorem good_bdry2 (j n : ℕ) :
    ∀ ω ∈ bdry (C.ξ j) (C.ξ n) (-C.α) C.α, Good D.K₀ D.B ω := by
  intro ω hω
  rcases hω with ⟨⟨h1, _⟩, e | e⟩ | ⟨⟨h1, h2⟩, e | e⟩
  · exact (C.good_of_far (C.far_of_off (ω := ω) (by linarith [C.ξ_pos j])
      (Or.inl (by rw [e, abs_neg, abs_of_pos C.hα])))).2.2.2
  · exact (C.good_of_far (C.far_of_off (ω := ω) (by linarith [C.ξ_pos j])
      (Or.inl (by rw [e, abs_of_pos C.hα])))).2.2.2
  · have hω : ω = (C.ξ j : ℂ) + ω.im * I := by apply Complex.ext <;> simp [e]
    rw [hω]; exact C.good_vert j (abs_le.mpr ⟨h1, h2⟩)
  · have hω : ω = (C.ξ n : ℂ) + ω.im * I := by apply Complex.ext <;> simp [e]
    rw [hω]; exact C.good_vert n (abs_le.mpr ⟨h1, h2⟩)

/-- Sum of the first `n` projections. -/
theorem sum_P (n : ℕ) : ∑ k ∈ Finset.range n, C.P k = rP D.K₀ D.B (C.ξ 0) (C.ξ n) (-C.α) C.α := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold rP rint
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold P rP
    rw [← smul_add, ← rint_split_x (C.ξ_mono (Nat.zero_le n)) (C.ξ_lt_succ n).le
      (continuousOn_cF (C.good_bdry2 0 n))
      (continuousOn_cF (C.good_bdry2 n (n + 1)))]

/-- Separation constant on the large rectangles. -/
def r : ℝ := min C.ε C.α

theorem r_pos : 0 < C.r := lt_min C.hε C.hα

/-- Estimates on the right half of the boundary of a large symmetric rectangle. -/
theorem half_good (n : ℕ) (hn : 2 * C.α ≤ C.ξ n) {ω : ℂ} (hre : 0 ≤ ω.re)
    (hb : C.ξ n ≤ |ω.im| ∨ ω.re = C.ξ n) :
    IsUnit (1 - ω ^ 2 • D.K₀) ∧ IsUnit (1 + D.N (ω ^ 2)) ∧
      ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤ C.CW ∧
      ∀ i, C.r ≤ ‖(D.ω i : ℂ) - ω‖ ∧ C.r ≤ ‖(D.ω i : ℂ) + ω‖ := by
  have hrα : C.r ≤ C.α := min_le_right _ _
  have hrε : C.r ≤ C.ε := min_le_left _ _
  by_cases him : C.α ≤ |ω.im|
  · have hf := C.far_of_off hre (Or.inl him)
    obtain ⟨h1, h2, h3, -⟩ := C.good_of_far hf
    exact ⟨h1, h2, h3.trans C.hCW, fun i => ⟨hrα.trans (hf i).1, hrα.trans (hf i).2⟩⟩
  · push Not at him
    have hre' : ω.re = C.ξ n := by
      rcases hb with hb | hb
      · linarith [C.hα]
      · exact hb
    have hω : ω = (C.ξ n : ℂ) + ω.im * I := by apply Complex.ext <;> simp [hre']
    rw [hω]
    refine ⟨C.vert_unit n _, (C.hW n _ him.le).1, (C.hW n _ him.le).2, fun i => ?_⟩
    have := C.vert_sep n ω.im i
    exact ⟨hrε.trans this.1, hrε.trans this.2⟩

/-- Estimates on the boundary of a large symmetric rectangle. -/
theorem big_good (n : ℕ) (hn : 2 * C.α ≤ C.ξ n) {ω : ℂ}
    (hω : ω ∈ bdry (-C.ξ n) (C.ξ n) (-C.ξ n) (C.ξ n)) :
    IsUnit (1 - ω ^ 2 • D.K₀) ∧ IsUnit (1 + D.N (ω ^ 2)) ∧
      ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤ C.CW ∧
      ∀ i, C.r ≤ ‖(D.ω i : ℂ) - ω‖ ∧ C.r ≤ ‖(D.ω i : ℂ) + ω‖ := by
  have hX := C.ξ_pos n
  have hb : C.ξ n ≤ |ω.im| ∨ ω.re = C.ξ n ∨ ω.re = -C.ξ n := by
    rcases hω with ⟨_, e | e⟩ | ⟨_, e | e⟩
    · left; rw [e, abs_neg, abs_of_pos hX]
    · left; rw [e, abs_of_pos hX]
    · right; right; exact e
    · right; left; exact e
  rcases le_or_gt 0 ω.re with hre | hre
  · refine C.half_good n hn hre ?_
    rcases hb with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr hb
    · linarith
  · have h := C.half_good n hn (ω := -ω) (by simp; linarith) (by
      rcases hb with hb | hb | hb
      · left; simpa using hb
      · linarith
      · right; simp [hb])
    rw [neg_sq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, fun i => ⟨?_, ?_⟩⟩
    · have := (h4 i).2; rwa [← sub_eq_add_neg] at this
    · have := (h4 i).1; rwa [sub_neg_eq_add] at this

/-- Goodness between the large rectangle and the strip rectangle. -/
theorem good_big_region (n : ℕ) :
    ∀ ω ∈ crect 0 (C.ξ n) (-C.ξ n) (C.ξ n), ω ∉ orect (C.ξ 0) (C.ξ n) (-C.α) C.α →
      Good D.K₀ D.B ω := by
  intro ω ⟨⟨h1, h2⟩, _⟩ hno
  by_cases h0 : ω.re ≤ C.ξ 0
  · exact (C.good_of_far (C.far_of_off h1 (Or.inr h0))).2.2.2
  by_cases him : C.α ≤ |ω.im|
  · exact (C.good_of_far (C.far_of_off h1 (Or.inl him))).2.2.2
  push Not at h0 him
  have hre : ω.re = C.ξ n := by
    by_contra hne
    exact hno ⟨⟨h0, lt_of_le_of_ne h2 hne⟩, (abs_lt.mp him).1, (abs_lt.mp him).2⟩
  have hω : ω = (C.ξ n : ℂ) + ω.im * I := by apply Complex.ext <;> simp [hre]
  rw [hω]
  exact C.good_vert n him.le

/-- The contour integral over the large symmetric rectangle is twice that over the strip. -/
theorem big_eq (n : ℕ) (hn : 2 * C.α ≤ C.ξ n) :
    rint (cF D.K₀ D.B) (-C.ξ n) (C.ξ n) (-C.ξ n) (C.ξ n) =
      (2 : ℂ) • rint (cF D.K₀ D.B) (C.ξ 0) (C.ξ n) (-C.α) C.α := by
  have hX := C.ξ_pos n
  have hreg := C.good_big_region n
  have hR : ∀ ω ∈ bdry 0 (C.ξ n) (-C.ξ n) (C.ξ n), Good D.K₀ D.B ω := by
    intro ω hω
    refine hreg ω (bdry_subset_crect _ _ _ _ hX.le (by linarith) hω) ?_
    rintro ⟨⟨r1, r2⟩, i1, i2⟩
    rcases hω with ⟨_, e | e⟩ | ⟨_, e | e⟩
    · rw [e] at i1; linarith [C.hα]
    · rw [e] at i2; linarith [C.hα]
    · rw [e] at r1; linarith [C.hξ0]
    · rw [e] at r2; linarith
  have hL : ∀ ω ∈ bdry (-C.ξ n) 0 (-C.ξ n) (C.ξ n), Good D.K₀ D.B ω := by
    intro ω hω
    rw [← good_neg]
    refine hR (-ω) ?_
    rcases hω with ⟨⟨a1, a2⟩, e | e⟩ | ⟨⟨a1, a2⟩, e | e⟩
    · left; refine ⟨⟨by simp; linarith, by simp; linarith⟩, Or.inr (by simp [e])⟩
    · left; refine ⟨⟨by simp; linarith, by simp; linarith⟩, Or.inl (by simp [e])⟩
    · right; refine ⟨⟨by simp; linarith, by simp; linarith⟩, Or.inr (by simp [e])⟩
    · right; refine ⟨⟨by simp; linarith, by simp; linarith⟩, Or.inl (by simp [e])⟩
  rw [rint_split_x (m := 0) (by linarith) hX.le (continuousOn_cF hL) (continuousOn_cF hR)]
  have hodd := rint_odd (cF_neg D.K₀ D.B) 0 (C.ξ n) (-C.ξ n) (C.ξ n)
  simp only [neg_zero, neg_neg] at hodd
  rw [hodd, ← two_smul ℂ]
  congr 1
  exact rint_deform (le_of_lt C.hξ0) (C.ξ_mono (Nat.zero_le n)) le_rfl (by linarith [C.hα])
    C.hαlt.le (by linarith [C.hα]) fun ω h1 h2 => differentiableAt_cF (hreg ω h1 h2)

theorem norm_ge_of_big (n : ℕ) {ω : ℂ} (hω : ω ∈ bdry (-C.ξ n) (C.ξ n) (-C.ξ n) (C.ξ n)) :
    C.ξ n ≤ ‖ω‖ := by
  have hX := C.ξ_pos n
  rcases hω with ⟨_, e | e⟩ | ⟨_, e | e⟩
  · have := abs_im_le_norm ω; rw [e, abs_neg, abs_of_pos hX] at this; exact this
  · have := abs_im_le_norm ω; rw [e, abs_of_pos hX] at this; exact this
  · have := abs_re_le_norm ω; rw [e, abs_neg, abs_of_pos hX] at this; exact this
  · have := abs_re_le_norm ω; rw [e, abs_of_pos hX] at this; exact this

/-- `‖2 ω R_T(ω²)‖ ≤ 2 CW / r` on the large rectangles. -/
theorem norm_cF_big (n : ℕ) (hn : 2 * C.α ≤ C.ξ n) {ω : ℂ}
    (hω : ω ∈ bdry (-C.ξ n) (C.ξ n) (-C.ξ n) (C.ξ n)) :
    Good D.K₀ D.B ω ∧ ‖cF D.K₀ D.B ω‖ ≤ 2 * C.CW / C.r := by
  obtain ⟨h1, h2, h3, h4⟩ := C.big_good n hn hω
  have hX := C.ξ_pos n
  have hωn : 0 < ‖ω‖ := hX.trans_le (C.norm_ge_of_big n hω)
  have hr := C.r_pos
  have hbd : ∀ i, ‖1 / ((D.lam i : ℂ) - ω ^ 2)‖ ≤ 1 / (C.r * ‖ω‖) := by
    intro i
    have h := norm_lam_sub_sq_ge' hr (h4 i).1 (h4 i).2
    have hl : (D.ω i : ℂ) ^ 2 = D.lam i := by rw [← D.ω_sq]; push_cast; ring
    rw [hl] at h
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by positivity) h
  have hRG : Res D.K₀ 0 (ω ^ 2) = diagOp D.b (fun i => 1 / ((D.lam i : ℂ) - ω ^ 2)) := by
    apply clm_ext_basis D.b
    intro i
    rw [D.res0_apply_basis h1 i, diagOp_apply_basis D.b _ _ hbd]
  have hRGn : ‖Res D.K₀ 0 (ω ^ 2)‖ ≤ 1 / (C.r * ‖ω‖) := by
    rw [hRG]; exact diagOp_norm_le D.b _ _ (by positivity) hbd
  refine ⟨D.isUnit_Lop h1 h2, ?_⟩
  rw [cF, D.Res_eq h1 h2, norm_smul]
  calc ‖2 * ω‖ * ‖Res D.K₀ 0 (ω ^ 2) * Ring.inverse (1 + D.N (ω ^ 2))‖
      ≤ ‖2 * ω‖ * (1 / (C.r * ‖ω‖) * C.CW) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul hRGn h3 (norm_nonneg _) (by positivity))
    _ = 2 * C.CW / C.r := by
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
        field_simp

theorem total : (⨆ k, C.V k).topologicalClosure = ⊤ := by
  set Wc := (⨆ k, C.V k).topologicalClosure with hWc
  have hα := C.hα
  have hr := C.r_pos
  have hCW : 0 < C.CW := by linarith [C.hCW]
  -- the reference point
  set ω₀ : ℂ := C.α * I with hω₀
  have hf0 : ∀ i, C.α ≤ ‖(D.ω i : ℂ) - ω₀‖ ∧ C.α ≤ ‖(D.ω i : ℂ) + ω₀‖ := by
    refine C.far_of_off (by simp [ω₀]) (Or.inl ?_)
    simp [ω₀, abs_of_pos C.hα]
  obtain ⟨L, hL⟩ : Good D.K₀ D.B ω₀ := (C.good_of_far hf0).2.2.2
  set z₀ := ω₀ ^ 2 with hz₀
  have hz₀' : z₀ = -((C.α : ℂ) ^ 2) := by
    rw [hz₀, hω₀, mul_pow, I_sq]; ring
  set R := Res D.K₀ D.B z₀ with hR
  -- the main estimate
  have hest : ∀ n : ℕ, 2 * C.α ≤ C.ξ n → ∀ w : H,
      ‖(∑ k ∈ Finset.range n, C.P k) (R w) - R w‖ ≤ 2 * C.CW * ‖w‖ / (C.r * C.ξ n) := by
    intro n hn w
    set X := C.ξ n with hXdef
    have hX : 0 < X := C.ξ_pos n
    have hab : -X ≤ X := by linarith
    have hgood := fun ω hω => (C.norm_cF_big n hn (ω := ω) hω).1
    have hne : ∀ ω ∈ bdry (-X) X (-X) X, ω ^ 2 - z₀ ≠ 0 := by
      intro ω hω h
      have h1 := C.norm_ge_of_big n hω
      have : ω ^ 2 = -((C.α : ℂ) ^ 2) := by rw [← hz₀']; linear_combination h
      have h2 : ‖ω‖ ^ 2 = C.α ^ 2 := by
        rw [← norm_pow, this, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith
    -- (a)
    have hcF := continuousOn_cF hgood
    have hcont1 : ContinuousOn (fun ω : ℂ => (ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω) (bdry (-X) X (-X) X) :=
      (((continuous_pow 2).sub continuous_const).continuousOn.inv₀ hne).smul hcF
    have hcont2 : ContinuousOn (fun ω : ℂ => (2 * ω / (ω ^ 2 - z₀))) (bdry (-X) X (-X) X) :=
      (continuous_const.mul continuous_id).continuousOn.div
        ((continuous_pow 2).sub continuous_const).continuousOn hne
    have ha : rint (cF D.K₀ D.B) (-X) X (-X) X * R =
        rint (fun ω : ℂ => (ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω) (-X) X (-X) X -
          rint (fun ω : ℂ => 2 * ω / (ω ^ 2 - z₀)) (-X) X (-X) X • R := by
      have h1 := clm_rint ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip R) hab hab hcF
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h1
      rw [h1, ← rint_const_smul (E := H →L[ℂ] H) (g := fun ω : ℂ => 2 * ω / (ω ^ 2 - z₀)) R,
        ← rint_sub (f := fun ω => (ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω)
          (g := fun ω : ℂ => (2 * ω / (ω ^ 2 - z₀)) • R) hab hab hcont1
          (hcont2.smul continuousOn_const)]
      refine rint_congr hab hab fun ω hω => ?_
      have hs := res_sub (K := D.K₀) (B := D.B) (hgood ω hω) ⟨L, hL⟩
      have hne' := hne ω hω
      have e : Res D.K₀ D.B (ω ^ 2) * R = (ω ^ 2 - z₀)⁻¹ • (Res D.K₀ D.B (ω ^ 2) - R) := by
        rw [hs, smul_smul, inv_mul_cancel₀ hne', one_smul]
      simp only [cF, smul_mul_assoc, e, smul_sub, smul_smul]
      rw [div_eq_mul_inv]
      congr 1
      ring_nf
    -- (b)
    have hb : rint (fun ω : ℂ => 2 * ω / (ω ^ 2 - z₀)) (-X) X (-X) X = 4 * Real.pi * I := by
      have hin : ∀ p : ℂ, p.re = 0 → |p.im| = C.α → p ∈ orect (-X) X (-X) X := by
        intro p h1 h2
        have := abs_lt.mp (show |p.im| < X by linarith)
        exact ⟨⟨by linarith, by linarith⟩, this.1, this.2⟩
      have hm1 : ω₀ ∈ orect (-X) X (-X) X := hin _ (by simp [ω₀]) (by simp [ω₀, abs_of_pos hα])
      have hm2 : -ω₀ ∈ orect (-X) X (-X) X := hin _ (by simp [ω₀]) (by simp [ω₀, abs_of_pos hα])
      have hnb : ∀ p ∈ orect (-X) X (-X) X, p ∉ bdry (-X) X (-X) X := by
        rintro p ⟨⟨a1, a2⟩, b1, b2⟩ (⟨_, e | e⟩ | ⟨_, e | e⟩) <;> linarith
      rw [rint_two_mul_div hab hab (hnb _ hm1) (hnb _ hm2), rint_inv_sub_of_mem hm1,
        rint_inv_sub_of_mem hm2]
      ring
    -- (c)
    have hc : rint (cF D.K₀ D.B) (-X) X (-X) X =
        (-(4 * Real.pi * I)) • ∑ k ∈ Finset.range n, C.P k := by
      rw [C.sum_P n, C.big_eq n hn]
      unfold rP
      rw [smul_smul]
      congr 1
      field_simp [two_pi_I_ne]
      ring
    have h4 : (4 * Real.pi * I : ℂ) ≠ 0 := by
      have := two_pi_I_ne; intro h; apply this; linear_combination h / 2
    have h5 : (-(4 * Real.pi * I)) • ((∑ k ∈ Finset.range n, C.P k) * R) =
        rint (fun ω : ℂ => (ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω) (-X) X (-X) X -
          (4 * Real.pi * I) • R := by
      rw [← smul_mul_assoc, ← hc, ha, hb]
    have key : (∑ k ∈ Finset.range n, C.P k) * R - R =
        (-(4 * Real.pi * I))⁻¹ •
          rint (fun ω : ℂ => (ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω) (-X) X (-X) X := by
      rw [eq_inv_smul_iff₀ (neg_ne_zero.mpr h4), smul_sub, h5, neg_smul, sub_neg_eq_add,
        sub_add_cancel]
    set J := rint (fun ω : ℂ => (ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω) (-X) X (-X) X
    have hX2 : 0 < X ^ 2 - C.α ^ 2 := by nlinarith
    have hpt : ∀ ω ∈ bdry (-X) X (-X) X, ‖(ω ^ 2 - z₀)⁻¹ • cF D.K₀ D.B ω‖ ≤
        (X ^ 2 - C.α ^ 2)⁻¹ * (2 * C.CW / C.r) := by
      intro ω hω
      rw [norm_smul, norm_inv]
      have h1 := C.norm_ge_of_big n hω
      have h2 : X ^ 2 - C.α ^ 2 ≤ ‖ω ^ 2 - z₀‖ := by
        rw [hz₀', sub_neg_eq_add]
        have := norm_sub_le (ω ^ 2 + (C.α : ℂ) ^ 2) ((C.α : ℂ) ^ 2)
        rw [add_sub_cancel_right, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          sq_abs] at this
        nlinarith
      exact mul_le_mul (inv_anti₀ hX2 h2) (C.norm_cF_big n hn hω).2 (norm_nonneg _)
        (inv_nonneg.mpr hX2.le)
    have hJ := norm_rint_le_mul hab hab hpt
    have hpi := Real.pi_gt_three
    calc ‖(∑ k ∈ Finset.range n, C.P k) (R w) - R w‖
        = ‖((∑ k ∈ Finset.range n, C.P k) * R - R) w‖ := by
          rw [sub_apply, mul_apply_eq_comp]
      _ ≤ ‖(∑ k ∈ Finset.range n, C.P k) * R - R‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ = (4 * Real.pi)⁻¹ * ‖J‖ * ‖w‖ := by
          rw [key, norm_smul, norm_inv, norm_neg, norm_mul, norm_mul, norm_I, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos, show ‖(4 : ℂ)‖ = 4 by simp]
          ring
      _ ≤ (4 * Real.pi)⁻¹ * ((2 * (X - -X) + 2 * (X - -X)) *
            ((X ^ 2 - C.α ^ 2)⁻¹ * (2 * C.CW / C.r))) * ‖w‖ := by gcongr
      _ ≤ 2 * C.CW * ‖w‖ / (C.r * X) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hw := norm_nonneg w
          have e : (4 * Real.pi)⁻¹ * ((2 * (X - -X) + 2 * (X - -X)) *
              ((X ^ 2 - C.α ^ 2)⁻¹ * (2 * C.CW * C.r⁻¹))) * ‖w‖ =
              (2 * C.CW * ‖w‖ * (C.r * X)⁻¹) * (2 * X ^ 2 / (Real.pi * (X ^ 2 - C.α ^ 2))) := by
            field_simp
            ring
          rw [e]
          have h6 : 2 * X ^ 2 / (Real.pi * (X ^ 2 - C.α ^ 2)) ≤ 1 := by
            rw [div_le_one (by positivity)]
            nlinarith
          have h7 : 0 ≤ 2 * C.CW * ‖w‖ * (C.r * X)⁻¹ := by positivity
          nlinarith
  have key : ∀ w : H, R w ∈ Wc := by
    intro w
    rw [← SetLike.mem_coe, hWc, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro δ hδ
    set T := max (2 * C.α) (2 * C.CW * ‖w‖ / (C.r * δ)) + 1
    obtain ⟨n, hn⟩ := exists_nat_gt (T / C.d)
    have hξn : T ≤ C.ξ n := by
      have h1 := C.ξ_add_le (Nat.zero_le n)
      simp only [Nat.sub_zero] at h1
      have h2 : T < n * C.d := by rwa [div_lt_iff₀ C.hd] at hn
      linarith [C.hξ0]
    have hT1 : 2 * C.α ≤ C.ξ n := by
      have := le_max_left (2 * C.α) (2 * C.CW * ‖w‖ / (C.r * δ)); linarith
    have hT2 : 2 * C.CW * ‖w‖ / (C.r * δ) < C.ξ n := by
      have := le_max_right (2 * C.α) (2 * C.CW * ‖w‖ / (C.r * δ)); linarith
    have hX := C.ξ_pos n
    refine ⟨(∑ k ∈ Finset.range n, C.P k) (R w), ?_, ?_⟩
    · rw [sum_apply]
      exact Submodule.sum_mem _ fun k _ => Submodule.mem_iSup_of_mem k ⟨R w, rfl⟩
    · rw [dist_comm, dist_eq_norm]
      refine (hest n hT1 w).trans_lt ?_
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hT2
      linarith
  have hb : ∀ i, D.b i = R ((L : H →L[ℂ] H) ((D.lam i : ℂ) • D.b i)) := by
    intro i
    have hl : (D.lam i : ℂ) ≠ 0 := by exact_mod_cast (D.lam_pos i).ne'
    have hLL : (↑L⁻¹ : H →L[ℂ] H) ((L : H →L[ℂ] H) ((D.lam i : ℂ) • D.b i)) =
        (D.lam i : ℂ) • D.b i := by
      rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
    rw [hR, Res, ← hL, Ring.inverse_unit, mul_apply_eq_comp, hLL, map_smul, D.hK, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hl, one_smul]
  rw [eq_top_iff, ← D.b.dense_span]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [hb i]
  exact key _

end CutData

end Involution
