module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A minimum-modulus lemma for bounded holomorphic functions (a variant of Wyss, Lemma 5.4):
zeros in a disc are divided out one at a time (their number is bounded since the function is
bounded and not too small at the centre), the zero-free quotient is bounded below by the
Borel–Carathéodory theorem applied to a holomorphic logarithm, and a vertical segment far from
the zeros and from finitely many prescribed points is selected by pigeonholing. -/

@[expose] public noncomputable section

open Complex Set Metric Filter Topology

namespace Involution

theorem norm_ge_of_ne_zero_ball {h : ℂ → ℂ} {R Ch : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (ball 0 R)) (hne : ∀ z ∈ ball (0 : ℂ) R, h z ≠ 0)
    (hC : ∀ z ∈ ball (0 : ℂ) R, ‖h z‖ ≤ Ch) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ‖h 0‖ * Real.exp (-(2 * (Real.log (Ch / ‖h 0‖) + 1) * ‖z‖ / (R - ‖z‖))) ≤ ‖h z‖ := by
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hh0 : 0 < ‖h 0‖ := norm_pos_iff.mpr (hne 0 h0mem)
  have hd' : DifferentiableOn ℂ (fun z => deriv h z / h z) (ball 0 R) :=
    (hd.deriv isOpen_ball).div hd hne
  obtain ⟨F, hF0, hF⟩ := (hd'.isExactOn_ball).with_val_at 0 0
  have hG : ∀ w ∈ ball (0 : ℂ) R, HasDerivAt (fun w => h w * Complex.exp (-F w)) 0 w := by
    intro w hw
    have h1 : HasDerivAt h (deriv h w) w :=
      (hd.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h2 := ((hF w hw).neg).cexp
    convert h1.mul h2 using 1
    field_simp [hne w hw]
    ring
  have hGc : ∀ w ∈ ball (0 : ℂ) R, h w * Complex.exp (-F w) = h 0 := by
    intro w hw
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
      (f := fun w => h w * Complex.exp (-F w))
      (fun x hx => (hG x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hG x hx).deriv) hw h0mem
    simpa [hF0] using this
  have hrep : ∀ w ∈ ball (0 : ℂ) R, ‖h w‖ = ‖h 0‖ * Real.exp (F w).re := by
    intro w hw
    have e : h w = h 0 * Complex.exp (F w) := by
      rw [← hGc w hw, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    rw [e, norm_mul, Complex.norm_exp]
  set M := Real.log (Ch / ‖h 0‖) + 1
  have hCh : ‖h 0‖ ≤ Ch := hC 0 h0mem
  have hM : 0 < M := by
    have : 0 ≤ Real.log (Ch / ‖h 0‖) :=
      Real.log_nonneg ((one_le_div hh0).mpr hCh)
    linarith
  have hmaps : MapsTo F (ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    simp only [mem_ofPred_eq]
    have h1 := hrep w hw
    have h2 := hC w hw
    have h3 : Real.exp (F w).re ≤ Ch / ‖h 0‖ := by
      rw [le_div_iff₀ hh0, mul_comm, ← h1]; exact h2
    have h4 : (F w).re ≤ Real.log (Ch / ‖h 0‖) := by
      rw [← Real.exp_le_exp, Real.exp_log ((Real.exp_pos _).trans_le h3)]; exact h3
    linarith
  have hFd : DifferentiableOn ℂ F (ball 0 R) :=
    fun w hw => (hF w hw).differentiableAt.differentiableWithinAt
  have hBC := borelCaratheodory_zero hM hFd hmaps hR hz hF0
  have hre : -(2 * M * ‖z‖ / (R - ‖z‖)) ≤ (F z).re := by
    have := neg_abs_le (F z).re
    have := abs_re_le_norm (F z)
    linarith
  rw [hrep z hz]
  gcongr

theorem exists_zero_factor {R₁ R₂ R₃ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂) (h23 : R₂ < R₃) :
    ∀ n : ℕ, ∀ (g : ℂ → ℂ) (C d : ℝ), 0 < d → DifferentiableOn ℂ g (ball 0 R₃) →
      (∀ z ∈ closedBall (0 : ℂ) R₂, ‖g z‖ ≤ C) → d ≤ ‖g 0‖ → C < ((R₂ - R₁) / R₁) ^ n * d →
      ∃ k < n, ∃ w : Fin k → ℂ, (∀ i, ‖w i‖ ≤ R₁) ∧ ∃ h : ℂ → ℂ,
        DifferentiableOn ℂ h (ball 0 R₃) ∧ (∀ z ∈ closedBall (0 : ℂ) R₁, h z ≠ 0) ∧
        (∀ z ∈ closedBall (0 : ℂ) R₂, ‖h z‖ ≤ C / (R₂ - R₁) ^ k) ∧ d / R₁ ^ k ≤ ‖h 0‖ ∧
        ∀ z, g z = (∏ i, (z - w i)) * h z := by
  intro n
  induction n with
  | zero =>
    intro g C d hd _ hC hg0 hlt
    have := hC 0 (mem_closedBall_self (by linarith))
    simp at hlt; linarith
  | succ n ih =>
    intro g C d hd hg hC hg0 hlt
    by_cases hz : ∃ w ∈ closedBall (0 : ℂ) R₁, g w = 0
    · obtain ⟨w, hw, hgw⟩ := hz
      have hwR : ‖w‖ ≤ R₁ := by simpa using hw
      have hrep : ∀ z, g z = (z - w) * dslope g w z := by
        intro z
        have := sub_smul_dslope g w z
        rw [hgw, sub_zero, smul_eq_mul] at this
        exact this.symm
      have hw0 : w ≠ 0 := by
        rintro rfl
        have := hrep 0
        rw [sub_self, zero_mul] at this
        rw [this, norm_zero] at hg0; linarith
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hg1 : DifferentiableOn ℂ (dslope g w) (ball 0 R₃) :=
        (differentiableOn_dslope (isOpen_ball.mem_nhds (by simp; linarith))).mpr hg
      have hC1 : ∀ z ∈ closedBall (0 : ℂ) R₂, ‖dslope g w z‖ ≤ C / (R₂ - R₁) := by
        intro z hz
        have hR2 : R₂ ≠ 0 := by linarith
        rw [← closure_ball (0 : ℂ) hR2] at hz
        refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball ?_ ?_ hz
        · apply DifferentiableOn.diffContOnCl
          rw [closure_ball (0 : ℂ) hR2]
          exact hg1.mono (closedBall_subset_ball h23)
        · intro u hu
          rw [frontier_ball (0 : ℂ) hR2] at hu
          have hu' : ‖u‖ = R₂ := by simpa using hu
          have hsep : R₂ - R₁ ≤ ‖u - w‖ := by
            have := norm_sub_norm_le u w; linarith
          have hpos : 0 < ‖u - w‖ := by linarith
          have e := hrep u
          rw [le_div_iff₀ (by linarith)]
          calc ‖dslope g w u‖ * (R₂ - R₁) ≤ ‖dslope g w u‖ * ‖u - w‖ := by gcongr
            _ = ‖g u‖ := by rw [e, norm_mul, mul_comm]
            _ ≤ C := hC u (by rw [mem_closedBall_zero_iff, hu'])
      have hd1 : d / R₁ ≤ ‖dslope g w 0‖ := by
        have e := congrArg norm (hrep 0)
        rw [zero_sub, norm_mul, norm_neg] at e
        rw [e] at hg0
        rw [div_le_iff₀ h1]
        calc d ≤ ‖w‖ * ‖dslope g w 0‖ := hg0
          _ ≤ R₁ * ‖dslope g w 0‖ := by gcongr
          _ = _ := by ring
      have hlt1 : C / (R₂ - R₁) < ((R₂ - R₁) / R₁) ^ n * (d / R₁) := by
        rw [div_lt_iff₀ (by linarith)]
        calc C < ((R₂ - R₁) / R₁) ^ (n + 1) * d := hlt
          _ = _ := by
            have hR : R₁ ≠ 0 := h1.ne'
            rw [pow_succ]; field_simp
      obtain ⟨k, hk, w', hw', h, hhd, hhne, hhC, hh0, hgh⟩ :=
        ih (dslope g w) (C / (R₂ - R₁)) (d / R₁) (div_pos hd h1) hg1 hC1 hd1 hlt1
      refine ⟨k + 1, by omega, Fin.cons w w', ?_, h, hhd, hhne, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hwR
        · simpa using hw' j
      · intro z hz
        refine (hhC z hz).trans_eq ?_
        rw [pow_succ]; field_simp
      · refine le_trans (le_of_eq ?_) hh0
        rw [pow_succ]; field_simp
      · intro z
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [hrep z, hgh z, mul_assoc]
    · push Not at hz
      refine ⟨0, by omega, Fin.elim0, fun i => Fin.elim0 i, g, hg, hz, ?_, ?_, ?_⟩
      · intro z hz; simpa using hC z hz
      · simpa using hg0
      · intro z; simp

theorem exists_spaced_point (bad : Finset ℝ) (K : ℕ) (hK : bad.card < K + 1) (A s : ℝ)
    (hs : 0 < s) : ∃ a ∈ Finset.range (K + 1), ∀ p ∈ bad, s / 2 ≤ |A + a * s - p| := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : Finset.range (K + 1) ⊆ bad.biUnion
      (fun p => (Finset.range (K + 1)).filter (fun a : ℕ => |A + a * s - p| < s / 2)) := by
    intro a ha
    obtain ⟨p, hp, hlt⟩ := hcon a ha
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨ha, hlt⟩⟩
  have hle : ∀ p ∈ bad, ((Finset.range (K + 1)).filter
      (fun a : ℕ => |A + a * s - p| < s / 2)).card ≤ 1 := by
    intro p _
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have h1 := ha.2; have h2 := hb.2
    have : |(a : ℝ) * s - b * s| < s := by
      calc |(a : ℝ) * s - b * s| = |(A + a * s - p) - (A + b * s - p)| := by ring_nf
        _ ≤ |A + a * s - p| + |A + b * s - p| := abs_sub _ _
        _ < s / 2 + s / 2 := add_lt_add h1 h2
        _ = s := by ring
    rw [← sub_mul, abs_mul, abs_of_pos hs] at this
    have h3 : |(a : ℝ) - b| < 1 := by
      by_contra h; push Not at h; nlinarith
    have h4 : (a : ℤ) = b := by
      have : |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| < 1 := by exact_mod_cast h3
      rw [← Int.cast_sub, ← Int.cast_abs] at this
      have : |(a : ℤ) - b| < 1 := by exact_mod_cast this
      rw [abs_lt] at this; omega
    exact_mod_cast h4
  have := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_card_nsmul _ _ 1 hle))
  simp at this
  omega

theorem min_modulus_segment (L α y₀ Cu δ : ℝ) (Mp : ℕ) (hL : 0 < L) (hα : 0 ≤ α)
    (hy₀ : 0 ≤ y₀) (hδ : 0 < δ) :
    ∃ ε > 0, ∃ κ > 0, ∀ (x₀ : ℝ) (f : ℂ → ℂ) (pts : Finset ℝ), pts.card ≤ Mp →
      DifferentiableOn ℂ f (ball ((x₀ : ℂ) + y₀ * I) (2 * (L + y₀ + α) + 4)) →
      (∀ z ∈ ball ((x₀ : ℂ) + y₀ * I) (2 * (L + y₀ + α) + 4), ‖f z‖ ≤ Cu) →
      δ ≤ ‖f (x₀ + y₀ * I)‖ →
      ∃ x : ℝ, |x - x₀| ≤ L ∧ (∀ p ∈ pts, ε ≤ |x - p|) ∧
        ∀ y : ℝ, |y| ≤ α → κ ≤ ‖f (x + y * I)‖ := by
  classical
  set r := L + y₀ + α with hr
  have hr0 : 0 < r := by positivity
  set R₁ := r + 1
  set R₂ := 2 * r + 3
  set R₃ := 2 * (L + y₀ + α) + 4
  have hq : 1 < (R₂ - R₁) / R₁ := by
    rw [one_lt_div (by positivity)]; linarith
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (Cu / δ) hq
  set K := Mp + n₀ + 1
  have hKpos : (0 : ℝ) < K := by positivity
  set s := 2 * L / K
  have hs : 0 < s := by positivity
  set ε := s / 2
  set η := min ε 1
  have hη : 0 < η := lt_min (by positivity) one_pos
  set δ₁ := δ / R₁ ^ n₀
  have hδ₁ : 0 < δ₁ := by positivity
  set κ := η ^ n₀ * δ₁ * Real.exp (-(2 * (Real.log (Cu / δ₁) + 1) * r))
  refine ⟨ε, by positivity, κ, by positivity, ?_⟩
  intro x₀ f pts hpts hfd hfC hf0
  set c : ℂ := (x₀ : ℂ) + y₀ * I
  set g : ℂ → ℂ := fun z => f (z + c)
  have hCu : δ ≤ Cu := hf0.trans (hfC c (mem_ball_self (by positivity)))
  have hgd : DifferentiableOn ℂ g (ball 0 R₃) := by
    intro z hz
    refine (hfd (z + c) ?_).comp z ((differentiableAt_id.add_const c).differentiableWithinAt)
      (fun u hu => ?_)
    · simpa [dist_eq_norm] using hz
    · simpa [dist_eq_norm] using hu
  have hgC : ∀ z ∈ closedBall (0 : ℂ) R₂, ‖g z‖ ≤ Cu := by
    intro z hz
    apply hfC
    have : ‖z‖ ≤ R₂ := by simpa using hz
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_right]
    linarith
  have hg0 : δ ≤ ‖g 0‖ := by simpa [g] using hf0
  have hlt : Cu < ((R₂ - R₁) / R₁) ^ n₀ * δ := by
    rwa [div_lt_iff₀ hδ] at hn₀
  obtain ⟨k, hk, w, hw, h, hhd, hhne, hhC, hh0, hgh⟩ :=
    exists_zero_factor (by positivity : (0 : ℝ) < R₁) (by linarith) (by linarith) n₀ g Cu δ
      hδ hgd hgC hg0 hlt
  set bad := pts ∪ Finset.univ.image (fun i => (w i).re + x₀)
  have hbad : bad.card < K + 1 := by
    have := Finset.card_union_le pts (Finset.univ.image (fun i => (w i).re + x₀))
    have h2 : (Finset.univ.image (fun i => (w i).re + x₀)).card ≤ k :=
      Finset.card_image_le.trans (by simp)
    simp only [K, bad]
    omega
  obtain ⟨a, ha, hsep⟩ := exists_spaced_point bad K hbad (x₀ - L) s hs
  have haK : (a : ℝ) ≤ K := by
    have := Finset.mem_range.mp ha; exact_mod_cast Nat.lt_succ_iff.mp this
  refine ⟨x₀ - L + a * s, ?_, ?_, ?_⟩
  · have h1 : (a : ℝ) * s ≤ 2 * L := by
      calc (a : ℝ) * s ≤ K * s := by gcongr
        _ = 2 * L := by simp only [s]; field_simp
    have h2 : 0 ≤ (a : ℝ) * s := by positivity
    rw [abs_le]; constructor <;> linarith
  · intro p hp
    exact hsep p (Finset.mem_union_left _ hp)
  · intro y hy
    set u : ℂ := ((x₀ - L + a * s : ℝ) : ℂ) + y * I - c
    have hfu : f ((x₀ - L + a * s : ℝ) + y * I) = g u := by simp [g, u]
    have hure : u.re = -L + a * s := by simp [u, c]; ring
    have huim : u.im = y - y₀ := by simp [u, c]
    have hunorm : ‖u‖ ≤ r := by
      have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      have h2 : |u.re| ≤ L := by
        have h1 : (a : ℝ) * s ≤ 2 * L := by
          calc (a : ℝ) * s ≤ K * s := by gcongr
            _ = 2 * L := by simp only [s]; field_simp
        have h2 : 0 ≤ (a : ℝ) * s := by positivity
        rw [hure, abs_le]; constructor <;> linarith
      have h3 : |u.im| ≤ y₀ + α := by
        rw [huim]; rw [abs_le] at hy ⊢; constructor <;> linarith
      linarith
    rw [hfu, hgh u, norm_mul, norm_prod]
    have hprod : η ^ n₀ ≤ ∏ i, ‖u - w i‖ := by
      calc η ^ n₀ ≤ η ^ k := pow_le_pow_of_le_one hη.le (min_le_right _ _) hk.le
        _ = ∏ _i : Fin k, η := by simp
        _ ≤ ∏ i, ‖u - w i‖ := by
          apply Finset.prod_le_prod₀ (fun _ _ => hη.le)
          intro i _
          have h1 := hsep ((w i).re + x₀) (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
          have h2 : |(u - w i).re| ≤ ‖u - w i‖ := abs_re_le_norm _
          have h3 : (u - w i).re = (x₀ - L + a * s) - ((w i).re + x₀) := by
            rw [sub_re, hure]; ring
          rw [h3] at h2
          exact (min_le_left _ _).trans (h1.trans h2)
    have hR1 : (1 : ℝ) ≤ R₁ := by linarith
    have hh0' : δ₁ ≤ ‖h 0‖ := by
      refine le_trans ?_ hh0
      apply div_le_div_of_nonneg_left hδ.le (by positivity)
      exact pow_le_pow_right₀ hR1 hk.le
    have hhCu : ∀ z ∈ ball (0 : ℂ) R₁, ‖h z‖ ≤ Cu := by
      intro z hz
      refine (hhC z (ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith)) hz)).trans ?_
      apply div_le_self (by linarith)
      exact one_le_pow₀ (by linarith)
    have hu1 : u ∈ ball (0 : ℂ) R₁ := by simp only [mem_ball_zero_iff]; linarith
    have hlow := norm_ge_of_ne_zero_ball (by positivity : (0 : ℝ) < R₁)
      (hhd.mono (ball_subset_ball (by linarith))) (fun z hz => hhne z (ball_subset_closedBall hz))
      hhCu hu1
    have hh0pos : 0 < ‖h 0‖ := hδ₁.trans_le hh0'
    have hexp : Real.exp (-(2 * (Real.log (Cu / δ₁) + 1) * r)) ≤
        Real.exp (-(2 * (Real.log (Cu / ‖h 0‖) + 1) * ‖u‖ / (R₁ - ‖u‖))) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      have hlog : Real.log (Cu / ‖h 0‖) ≤ Real.log (Cu / δ₁) := by
        apply Real.log_le_log (div_pos (by linarith) hh0pos)
        exact div_le_div_of_nonneg_left (by linarith) hδ₁ hh0'
      have hlog0 : 0 ≤ Real.log (Cu / ‖h 0‖) := by
        apply Real.log_nonneg
        rw [one_le_div hh0pos]
        exact hhCu 0 (mem_ball_self (by positivity))
      have hfrac : ‖u‖ / (R₁ - ‖u‖) ≤ r := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg u]
      calc 2 * (Real.log (Cu / ‖h 0‖) + 1) * ‖u‖ / (R₁ - ‖u‖)
          = 2 * (Real.log (Cu / ‖h 0‖) + 1) * (‖u‖ / (R₁ - ‖u‖)) := by ring
        _ ≤ 2 * (Real.log (Cu / δ₁) + 1) * r := by
          apply mul_le_mul (by linarith) hfrac (div_nonneg (norm_nonneg _) (by linarith))
            (by linarith)
    calc κ = η ^ n₀ * (δ₁ * Real.exp (-(2 * (Real.log (Cu / δ₁) + 1) * r))) := by ring
      _ ≤ (∏ i, ‖u - w i‖) * ‖h u‖ := by
        apply mul_le_mul hprod _ (by positivity) (by positivity)
        exact (mul_le_mul hh0' hexp (by positivity) hh0pos.le).trans hlow

end Involution
