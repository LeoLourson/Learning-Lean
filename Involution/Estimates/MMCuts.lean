module

public import Involution.Estimates.MMCompact

/-! Cut data: vertical lines `Re ω = ξ k` in the `ω`-plane (`z = ω²`) on which the perturbed
resolvent is uniformly bounded. The Riesz projections `P k` of the rectangles
`[ξ k, ξ (k+1)] × [-α, α]` are idempotent, mutually annihilating, of finite rank, and their
ranges are invariant under `T`. -/

@[expose] public noncomputable section

open Complex Set Filter Topology

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cuts with uniform resolvent bounds. -/
structure CutData (D : MMData ι H) where
  ξ : ℕ → ℝ
  α : ℝ
  ε : ℝ
  d : ℝ
  CW : ℝ
  hα : 0 < α
  hbα : 2 * D.b₁ ≤ α
  hξ0 : 0 < ξ 0
  hξm : ξ 0 + α ≤ D.m
  hε : 0 < ε
  hd : 0 < d
  hgap : ∀ k, ξ k + d ≤ ξ (k + 1)
  hsep : ∀ k i, ε ≤ |ξ k - D.ω i|
  hCW : 2 ≤ CW
  hW : ∀ k (y : ℝ), |y| ≤ α → IsUnit (1 + D.N (((ξ k : ℂ) + y * I) ^ 2)) ∧
    ‖Ring.inverse (1 + D.N (((ξ k : ℂ) + y * I) ^ 2))‖ ≤ CW
  hfin : ∀ t : ℝ, {i | D.lam i ≤ t}.Finite

namespace CutData

variable {D : MMData ι H} (C : CutData D)

theorem ξ_add_le {j k : ℕ} (h : j ≤ k) : C.ξ j + (k - j : ℕ) * C.d ≤ C.ξ k := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have := C.hgap k
    rw [Nat.succ_sub hjk]
    push_cast
    linarith

theorem ξ_mono {j k : ℕ} (h : j ≤ k) : C.ξ j ≤ C.ξ k := by
  have := C.ξ_add_le h
  have : 0 ≤ ((k - j : ℕ) : ℝ) * C.d := mul_nonneg (Nat.cast_nonneg _) C.hd.le
  linarith

theorem ξ_lt_succ (k : ℕ) : C.ξ k < C.ξ (k + 1) := by
  have := C.hgap k; have := C.hd; linarith

theorem ξ_pos (k : ℕ) : 0 < C.ξ k := C.hξ0.trans_le (C.ξ_mono (Nat.zero_le k))

theorem norm_sub_ge_im (p : ℝ) (ω : ℂ) : |ω.im| ≤ ‖(p : ℂ) - ω‖ := by
  refine (abs_im_le_norm _).trans_eq' ?_
  simp

theorem norm_add_ge_im (p : ℝ) (ω : ℂ) : |ω.im| ≤ ‖(p : ℂ) + ω‖ := by
  refine (abs_im_le_norm _).trans_eq' ?_
  simp

theorem norm_sub_ge_re (p : ℝ) (ω : ℂ) : |p - ω.re| ≤ ‖(p : ℂ) - ω‖ := by
  refine (abs_re_le_norm _).trans_eq' ?_
  simp

theorem norm_add_ge_re (p : ℝ) (ω : ℂ) : |p + ω.re| ≤ ‖(p : ℂ) + ω‖ := by
  refine (abs_re_le_norm _).trans_eq' ?_
  simp

/-- Points far from all `±ω i` (distance `≥ α`). -/
theorem good_of_far {ω : ℂ} (h : ∀ i, C.α ≤ ‖(D.ω i : ℂ) - ω‖ ∧ C.α ≤ ‖(D.ω i : ℂ) + ω‖) :
    IsUnit (1 - ω ^ 2 • D.K₀) ∧ IsUnit (1 + D.N (ω ^ 2)) ∧
      ‖Ring.inverse (1 + D.N (ω ^ 2))‖ ≤ 2 ∧ Good D.K₀ D.B ω := by
  refine D.good_far C.hα h ?_
  rw [div_le_iff₀ C.hα]; linarith [C.hbα]

/-- Away from the strip, or left of `ξ 0`, everything is good. -/
theorem far_of_off {ω : ℂ} (h0 : 0 ≤ ω.re) (h : C.α ≤ |ω.im| ∨ ω.re ≤ C.ξ 0) :
    ∀ i, C.α ≤ ‖(D.ω i : ℂ) - ω‖ ∧ C.α ≤ ‖(D.ω i : ℂ) + ω‖ := by
  intro i
  have hm := D.m_le_ω i
  rcases h with h | h
  · exact ⟨h.trans (norm_sub_ge_im _ _), h.trans (norm_add_ge_im _ _)⟩
  · constructor
    · refine le_trans ?_ (norm_sub_ge_re _ _)
      rw [abs_of_nonneg (by linarith [C.hξm, C.hα])]
      linarith [C.hξm]
    · refine le_trans ?_ (norm_add_ge_re _ _)
      rw [abs_of_nonneg (by linarith [C.hξm, C.hξ0, D.hm])]
      linarith [C.hξm, C.hα, C.hξ0]

/-- On the vertical cut lines. -/
theorem vert_sep (k : ℕ) (y : ℝ) :
    ∀ i, C.ε ≤ ‖(D.ω i : ℂ) - ((C.ξ k : ℂ) + y * I)‖ ∧
      C.ε ≤ ‖(D.ω i : ℂ) + ((C.ξ k : ℂ) + y * I)‖ := by
  intro i
  have h1 := C.hsep k i
  have hk := C.ξ_pos k
  have hi := D.ω_pos i
  constructor
  · refine le_trans ?_ (norm_sub_ge_re _ _)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    rwa [abs_sub_comm]
  · refine le_trans ?_ (norm_add_ge_re _ _)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    rw [abs_of_pos (by linarith)]
    refine h1.trans ?_
    rw [abs_le]; constructor <;> linarith

theorem vert_unit (k : ℕ) (y : ℝ) :
    IsUnit (1 - ((C.ξ k : ℂ) + y * I) ^ 2 • D.K₀) :=
  (D.far C.hε (C.vert_sep k y)).1

theorem good_vert (k : ℕ) {y : ℝ} (hy : |y| ≤ C.α) : Good D.K₀ D.B ((C.ξ k : ℂ) + y * I) :=
  D.isUnit_Lop (C.vert_unit k y) (C.hW k y hy).1

theorem good0_iff {ω : ℂ} : Good D.K₀ 0 ω ↔ IsUnit (1 - ω ^ 2 • D.K₀) := by
  rw [Good, D.Lop_zero]

/-- Goodness on the boundary of the `k`-th rectangle. -/
theorem good_bdry (k : ℕ) :
    ∀ ω ∈ bdry (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α, Good D.K₀ D.B ω ∧ Good D.K₀ 0 ω := by
  intro ω hω
  rcases hω with ⟨⟨h1, _⟩, e | e⟩ | ⟨⟨h1, h2⟩, e | e⟩
  · have hf := C.far_of_off (ω := ω) (by linarith [C.ξ_pos k])
      (Or.inl (by rw [e, abs_neg, abs_of_pos C.hα]))
    exact ⟨(C.good_of_far hf).2.2.2, good0_iff.mpr (C.good_of_far hf).1⟩
  · have hf := C.far_of_off (ω := ω) (by linarith [C.ξ_pos k])
      (Or.inl (by rw [e, abs_of_pos C.hα]))
    exact ⟨(C.good_of_far hf).2.2.2, good0_iff.mpr (C.good_of_far hf).1⟩
  · have hω : ω = (C.ξ k : ℂ) + ω.im * I := by
      apply Complex.ext <;> simp [e]
    have hy : |ω.im| ≤ C.α := abs_le.mpr ⟨h1, h2⟩
    rw [hω]
    exact ⟨C.good_vert k hy, good0_iff.mpr (C.vert_unit k _)⟩
  · have hω : ω = (C.ξ (k + 1) : ℂ) + ω.im * I := by
      apply Complex.ext <;> simp [e]
    have hy : |ω.im| ≤ C.α := abs_le.mpr ⟨h1, h2⟩
    rw [hω]
    exact ⟨C.good_vert (k + 1) hy, good0_iff.mpr (C.vert_unit (k + 1) _)⟩

/-- The Riesz projection of the `k`-th rectangle. -/
def P (k : ℕ) : H →L[ℂ] H := rP D.K₀ D.B (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α

/-- The corresponding spectral projection of `G`. -/
def Q (k : ℕ) : H →L[ℂ] H := rP D.K₀ 0 (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α

/-- The subspaces. -/
def V (k : ℕ) : Submodule ℂ H := LinearMap.range (C.P k : H →ₗ[ℂ] H)

theorem hαlt : -C.α < C.α := by linarith [C.hα]

theorem P_idem (k : ℕ) : C.P k * C.P k = C.P k :=
  rP_idem (C.ξ_pos k) (C.ξ_lt_succ k).le C.hαlt.le fun ω hω => (C.good_bdry k ω hω).1

theorem P_mul_of_lt {j k : ℕ} (h : j < k) : C.P j * C.P k = 0 ∧ C.P k * C.P j = 0 :=
  rP_mul_side (C.ξ_pos j) (C.ξ_lt_succ j) (C.ξ_mono h) (C.ξ_lt_succ k) C.hαlt C.hαlt
    (fun ω hω => (C.good_bdry j ω hω).1) (fun ω hω => (C.good_bdry k ω hω).1)

theorem P_mul_ne {j k : ℕ} (h : j ≠ k) : C.P j * C.P k = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · exact (C.P_mul_of_lt h).1
  · exact (C.P_mul_of_lt h).2

theorem P_eq_K_mul (k : ℕ) : C.P k = D.K₀ * Qint D.K₀ D.B (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α :=
  rP_eq_mul_Qint (C.ξ_lt_succ k).le C.hαlt.le fun ω hω => (C.good_bdry k ω hω).1

theorem V_finite (k : ℕ) : FiniteDimensional ℂ (C.V k) := by
  refine finiteDimensional_range_of_compact_idem _ ?_ (C.P_idem k)
  rw [C.P_eq_K_mul k]
  exact (D.isCompact_K C.hfin).comp_clm _

theorem P_apply_of_mem {k : ℕ} {v : H} (hv : v ∈ C.V k) : C.P k v = v := by
  obtain ⟨u, rfl⟩ := hv
  change (C.P k * C.P k) u = C.P k u
  rw [C.P_idem]

theorem K_injective : Function.Injective D.K₀ := by
  intro x y hxy
  rw [← sub_eq_zero]
  set g := x - y
  have hg' : D.K₀ g = 0 := by simp [g, hxy]
  have hc : ∀ i, inner ℂ (D.b i) g = 0 := by
    intro i
    have h1 : inner ℂ (D.b i) (D.K₀ g) = 0 := by rw [hg', inner_zero_right]
    have h2 : inner ℂ (D.b i) (D.K₀ g) = (((D.lam i)⁻¹ : ℝ) : ℂ) * inner ℂ (D.b i) g := by
      rw [D.K_eq_diag, inner_basis_diagOp D.b _ ((D.m ^ 2)⁻¹)]
      intro j
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.lam_pos j))]
      exact inv_anti₀ (pow_pos D.hm 2) (D.hlam j)
    rw [h2] at h1
    have hne : (((D.lam i)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (inv_pos.mpr (D.lam_pos i)).ne'
    exact (mul_eq_zero.mp h1).resolve_left hne
  have : D.b.repr g = 0 := by
    ext i
    simp [HilbertBasis.repr_apply_apply, hc i]
  simpa using congrArg D.b.repr.symm this

/-- The ranges are invariant under `T`. -/
theorem V_invariant (k : ℕ) : ∀ v ∈ C.V k, ∃ g : H, D.K₀ g = v ∧ g + D.B g ∈ C.V k := by
  intro v hv
  set Qk := Qint D.K₀ D.B (C.ξ k) (C.ξ (k + 1)) (-C.α) C.α
  refine ⟨Qk v, ?_, ?_⟩
  · have := congrArg (fun X : H →L[ℂ] H => X v) (C.P_eq_K_mul k)
    conv_rhs => rw [← C.P_apply_of_mem hv]
    exact this.symm
  -- a reference point in the resolvent set
  set ω₀ : ℂ := C.α * I
  have hf : ∀ i, C.α ≤ ‖(D.ω i : ℂ) - ω₀‖ ∧ C.α ≤ ‖(D.ω i : ℂ) + ω₀‖ := by
    refine C.far_of_off (by simp [ω₀]) (Or.inl ?_)
    simp [ω₀, abs_of_pos C.hα]
  have hg0 : Good D.K₀ D.B ω₀ := (C.good_of_far hf).2.2.2
  obtain ⟨L, hL⟩ := hg0
  set z₀ := ω₀ ^ 2
  set R := Res D.K₀ D.B z₀
  have hRP : R * C.P k = C.P k * R :=
    res_mul_rP ⟨L, hL⟩ (C.ξ_lt_succ k).le C.hαlt.le fun ω hω => (C.good_bdry k ω hω).1
  have hRinj : Function.Injective R := by
    intro x y hxy
    have : D.K₀ ((↑L⁻¹ : H →L[ℂ] H) x) = D.K₀ ((↑L⁻¹ : H →L[ℂ] H) y) := by
      simpa [R, Res, ← hL, Ring.inverse_unit] using hxy
    have h2 := congrArg (fun u => (L : H →L[ℂ] H) u) (K_injective this)
    simpa [← mul_apply_eq_comp] using h2
  set g := Qk v
  have hKg : D.K₀ g = v := by
    have := congrArg (fun X : H →L[ℂ] H => X v) (C.P_eq_K_mul k)
    conv_rhs => rw [← C.P_apply_of_mem hv]
    exact this.symm
  set u := g + D.B g
  -- `R u = v + z₀ R v`
  have hRu : R u = v + z₀ • R v := by
    have hLop : (1 + D.B : H →L[ℂ] H) = (L : H →L[ℂ] H) + z₀ • D.K₀ := by
      rw [hL]; simp [Lop]
    have hu : u = (1 + D.B) g := by simp [u]
    rw [hu, hLop]
    simp only [R, Res, ← hL, Ring.inverse_unit, mul_apply_eq_comp, add_apply, smul_apply,
      map_add, map_smul]
    rw [show (↑L⁻¹ : H →L[ℂ] H) ((L : H →L[ℂ] H) g) = g by
      rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self], hKg]
  have hRv : R v ∈ C.V k := by
    refine ⟨R v, ?_⟩
    change (C.P k * R) v = R v
    rw [← hRP, mul_apply_eq_comp, C.P_apply_of_mem hv]
  have hRuV : R u ∈ C.V k := by
    rw [hRu]; exact Submodule.add_mem _ hv (Submodule.smul_mem _ _ hRv)
  have hfix : C.P k u = u := by
    apply hRinj
    have := congrArg (fun X : H →L[ℂ] H => X u) hRP
    simp only [mul_apply_eq_comp] at this
    rw [this, C.P_apply_of_mem hRuV]
  exact ⟨u, hfix⟩

end CutData

end Involution
