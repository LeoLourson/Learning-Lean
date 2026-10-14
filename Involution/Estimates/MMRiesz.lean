module

public import Involution.Estimates.MMContour

/-! Riesz projections for the pencil `L(z) = 1 + B - z K` in a complex Banach algebra.
The resolvent is `R(z) = K L(z)⁻¹` (for `K = G⁻¹`, `B = S G⁻¹` this is `(G + S - z)⁻¹`).
Projections are contour integrals over rectangles in the variable `ω = √z`,
`P = -(2πi)⁻¹ ∮ 2ω R(ω²) dω`. -/

@[expose] public noncomputable section

open Complex Set

namespace Involution

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The pencil `1 + B - z K`. -/
def Lop (K B : A) (z : ℂ) : A := 1 + B - z • K

/-- The resolvent `K (1 + B - z K)⁻¹`. -/
def Res (K B : A) (z : ℂ) : A := K * Ring.inverse (Lop K B z)

/-- The integrand `2 ω R(ω²)`. -/
def cF (K B : A) (ω : ℂ) : A := (2 * ω) • Res K B (ω ^ 2)

/-- `ω²` lies in the resolvent set. -/
def Good (K B : A) (ω : ℂ) : Prop := IsUnit (Lop K B (ω ^ 2))

/-- Riesz projection for a rectangle in the `ω`-plane. -/
def rP (K B : A) (a b c d : ℝ) : A := (-(2 * Real.pi * I)⁻¹) • rint (cF K B) a b c d

variable {K B : A}

omit [CompleteSpace A] in
theorem Lop_sub_Lop (z w : ℂ) : Lop K B w - Lop K B z = (z - w) • K := by
  simp only [Lop, sub_smul]; abel

omit [CompleteSpace A] in
theorem res_sub {z w : ℂ} (hz : IsUnit (Lop K B z)) (hw : IsUnit (Lop K B w)) :
    Res K B z - Res K B w = (z - w) • (Res K B z * Res K B w) := by
  obtain ⟨u, hu⟩ := hz
  obtain ⟨v, hv⟩ := hw
  have h : (v : A) - u = (z - w) • K := by rw [hu, hv]; exact Lop_sub_Lop z w
  simp only [Res, ← hu, ← hv, Ring.inverse_unit]
  have e : (↑u⁻¹ : A) - ↑v⁻¹ = ↑u⁻¹ * ((v : A) - u) * ↑v⁻¹ := by
    rw [mul_sub, sub_mul, Units.inv_mul, one_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [← mul_sub, e, h]
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]

omit [CompleteSpace A] in
theorem res_comm {z w : ℂ} (hz : IsUnit (Lop K B z)) (hw : IsUnit (Lop K B w)) :
    Res K B z * Res K B w = Res K B w * Res K B z := by
  by_cases hzw : z = w
  · rw [hzw]
  · have h1 := res_sub hz hw
    have h2 := res_sub hw hz
    have hne : z - w ≠ 0 := sub_ne_zero.mpr hzw
    have : (z - w) • (Res K B z * Res K B w) = (z - w) • (Res K B w * Res K B z) := by
      rw [← h1, show z - w = -(w - z) by ring, neg_smul, ← h2]; abel
    exact smul_right_injective A hne this

theorem isOpen_good : IsOpen {ω : ℂ | Good K B ω} := by
  have hc : Continuous fun ω : ℂ => Lop K B (ω ^ 2) := by
    unfold Lop; fun_prop
  exact Units.isOpen.preimage hc

theorem differentiableAt_cF {ω : ℂ} (hω : Good K B ω) : DifferentiableAt ℂ (cF K B) ω := by
  have h1 : DifferentiableAt ℂ (fun ω : ℂ => Lop K B (ω ^ 2)) ω := by
    unfold Lop; fun_prop
  have h2 := h1.inverse hω
  unfold cF Res
  exact (differentiableAt_const _ |>.mul differentiableAt_id).smul
    ((differentiableAt_const K).mul h2)

theorem continuousOn_cF {S : Set ℂ} (h : ∀ ω ∈ S, Good K B ω) : ContinuousOn (cF K B) S :=
  continuousOn_of_diffAt fun ω hω => differentiableAt_cF (h ω hω)

omit [CompleteSpace A] in
theorem cF_mul_cF {ω η : ℂ} (hω : Good K B ω) (hη : Good K B η) (hne : ω ^ 2 - η ^ 2 ≠ 0) :
    cF K B ω * cF K B η =
      (2 * η / (ω ^ 2 - η ^ 2)) • cF K B ω - (2 * ω / (ω ^ 2 - η ^ 2)) • cF K B η := by
  have h := res_sub hω hη
  have e : Res K B (ω ^ 2) * Res K B (η ^ 2) =
      (ω ^ 2 - η ^ 2)⁻¹ • (Res K B (ω ^ 2) - Res K B (η ^ 2)) := by
    rw [h, smul_smul, inv_mul_cancel₀ hne, one_smul]
  simp only [cF, smul_mul_smul_comm, e, smul_smul, smul_sub]
  congr 2 <;> field_simp

theorem crect_re_pos {a b c d : ℝ} (ha : 0 < a) {ω : ℂ} (hω : ω ∈ crect a b c d) : 0 < ω.re :=
  ha.trans_le hω.1.1

theorem bdry_re_pos {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hcd : c ≤ d) {ω : ℂ}
    (hω : ω ∈ bdry a b c d) : 0 < ω.re :=
  crect_re_pos ha (bdry_subset_crect a b c d hab hcd hω)

theorem sq_sub_sq_ne {ω η : ℂ} (hne : ω ≠ η) (hpos : 0 < ω.re + η.re) : ω ^ 2 - η ^ 2 ≠ 0 := by
  rw [sq_sub_sq]
  refine mul_ne_zero ?_ (sub_ne_zero.mpr hne)
  intro e
  have := congrArg Complex.re e
  simp at this
  linarith

/-- The scalar kernel: `∮ 2η / (η² - p²) dη` as a sum of two winding integrals. -/
theorem rint_two_mul_div {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {p : ℂ}
    (h1 : p ∉ bdry a b c d) (h2 : -p ∉ bdry a b c d) :
    rint (fun η => 2 * η / (η ^ 2 - p ^ 2)) a b c d =
      rint (fun η : ℂ => (η - p)⁻¹) a b c d + rint (fun η : ℂ => (η - -p)⁻¹) a b c d := by
  have hne1 : ∀ η ∈ bdry a b c d, η - p ≠ 0 := fun η hη e => h1 (sub_eq_zero.mp e ▸ hη)
  have hne2 : ∀ η ∈ bdry a b c d, η - -p ≠ 0 := fun η hη e => h2 (sub_eq_zero.mp e ▸ hη)
  rw [← rint_add hab hcd]
  · refine rint_congr hab hcd fun η hη => ?_
    have e1 := hne1 η hη
    have e2 := hne2 η hη
    have e3 : η ^ 2 - p ^ 2 = (η - p) * (η - -p) := by ring
    rw [e3]
    field_simp
    ring
  · exact continuousOn_of_diffAt fun η hη =>
      (differentiableAt_id.sub_const p).inv (hne1 η hη)
  · exact continuousOn_of_diffAt fun η hη =>
      (differentiableAt_id.sub_const (-p)).inv (hne2 η hη)

/-- Product of two contour integrals of the resolvent, reduced to scalar kernels. -/
theorem rint_mul_rint {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ} (ha₁ : 0 < a₁) (h₁ : a₁ ≤ b₁)
    (h₁' : c₁ ≤ d₁) (ha₂ : 0 < a₂) (h₂ : a₂ ≤ b₂) (h₂' : c₂ ≤ d₂)
    (hdisj : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, ω ∉ bdry a₂ b₂ c₂ d₂)
    (hg₁ : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, Good K B ω) (hg₂ : ∀ η ∈ bdry a₂ b₂ c₂ d₂, Good K B η) :
    rint ((cF K B)) a₁ b₁ c₁ d₁ * rint ((cF K B)) a₂ b₂ c₂ d₂ =
      rint (fun ω => rint (fun η => 2 * η / (ω ^ 2 - η ^ 2)) a₂ b₂ c₂ d₂ • (cF K B) ω)
        a₁ b₁ c₁ d₁ -
      rint (fun η => rint (fun ω => 2 * ω / (ω ^ 2 - η ^ 2)) a₁ b₁ c₁ d₁ • (cF K B) η)
        a₂ b₂ c₂ d₂ := by
  have hF₁ : ContinuousOn (cF K B) (bdry a₁ b₁ c₁ d₁) := continuousOn_cF hg₁
  have hF₂ : ContinuousOn (cF K B) (bdry a₂ b₂ c₂ d₂) := continuousOn_cF hg₂
  have hne : ∀ z ∈ bdry a₁ b₁ c₁ d₁ ×ˢ bdry a₂ b₂ c₂ d₂, z.1 ^ 2 - z.2 ^ 2 ≠ 0 := by
    rintro ⟨ω, η⟩ ⟨hω, hη⟩
    refine sq_sub_sq_ne (fun e => hdisj ω hω (by rw [show ω = η from e]; exact hη)) ?_
    have := bdry_re_pos ha₁ h₁ h₁' hω
    have := bdry_re_pos ha₂ h₂ h₂' hη
    simp only; linarith
  have hk₂ : ContinuousOn (fun z : ℂ × ℂ => 2 * z.2 / (z.1 ^ 2 - z.2 ^ 2))
      (bdry a₁ b₁ c₁ d₁ ×ˢ bdry a₂ b₂ c₂ d₂) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) hne
  have hk₁ : ContinuousOn (fun z : ℂ × ℂ => 2 * z.1 / (z.1 ^ 2 - z.2 ^ 2))
      (bdry a₁ b₁ c₁ d₁ ×ˢ bdry a₂ b₂ c₂ d₂) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) hne
  have hFsnd : ContinuousOn (fun z : ℂ × ℂ => (cF K B) z.2)
      (bdry a₁ b₁ c₁ d₁ ×ˢ bdry a₂ b₂ c₂ d₂) :=
    hF₂.comp continuous_snd.continuousOn fun z hz => hz.2
  have hY : ContinuousOn (fun z : ℂ × ℂ => (2 * z.1 / (z.1 ^ 2 - z.2 ^ 2)) • (cF K B) z.2)
      (bdry a₁ b₁ c₁ d₁ ×ˢ bdry a₂ b₂ c₂ d₂) := hk₁.smul hFsnd
  -- step 1
  have s1 : rint (cF K B) a₁ b₁ c₁ d₁ * rint (cF K B) a₂ b₂ c₂ d₂ =
      rint (fun ω => (cF K B) ω * rint (cF K B) a₂ b₂ c₂ d₂) a₁ b₁ c₁ d₁ := by
    have hm := clm_rint ((ContinuousLinearMap.mul ℂ A).flip (rint (cF K B) a₂ b₂ c₂ d₂)) h₁ h₁' hF₁
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hm
  -- steps 2, 3
  have s2 : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, (cF K B) ω * rint (cF K B) a₂ b₂ c₂ d₂ =
      rint (fun η => 2 * η / (ω ^ 2 - η ^ 2)) a₂ b₂ c₂ d₂ • (cF K B) ω -
        rint (fun η => (2 * ω / (ω ^ 2 - η ^ 2)) • (cF K B) η) a₂ b₂ c₂ d₂ := by
    intro ω hω
    have hslice : ∀ η ∈ bdry a₂ b₂ c₂ d₂, ω ^ 2 - η ^ 2 ≠ 0 := fun η hη =>
      hne (ω, η) ⟨hω, hη⟩
    have cc₂ : ContinuousOn (fun η : ℂ => 2 * η / (ω ^ 2 - η ^ 2)) (bdry a₂ b₂ c₂ d₂) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hslice
    have cc₁ : ContinuousOn (fun η : ℂ => 2 * ω / (ω ^ 2 - η ^ 2)) (bdry a₂ b₂ c₂ d₂) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hslice
    have hm := clm_rint (ContinuousLinearMap.mul ℂ A ((cF K B) ω)) h₂ h₂' hF₂
    simp only [ContinuousLinearMap.mul_apply'] at hm
    rw [hm, rint_congr h₂ h₂' (fun η hη => cF_mul_cF (hg₁ ω hω) (hg₂ η hη) (hslice η hη)),
      rint_sub (f := fun η => (2 * η / (ω ^ 2 - η ^ 2)) • (cF K B) ω)
        (g := fun η => (2 * ω / (ω ^ 2 - η ^ 2)) • (cF K B) η) h₂ h₂'
        (cc₂.smul continuousOn_const) (cc₁.smul hF₂), rint_const_smul]
  rw [s1, rint_congr h₁ h₁' s2]
  rw [rint_sub h₁ h₁']
  · congr 1
    rw [rint_rint_swap h₁ h₁' h₂ h₂' hY]
    refine rint_congr h₂ h₂' fun η _ => ?_
    exact rint_const_smul _
  · refine ContinuousOn.smul ?_ hF₁
    exact rint_param_continuousOn (G := fun ω η => 2 * η / (ω ^ 2 - η ^ 2)) h₂ h₂' hk₂
  · exact rint_param_continuousOn (G := fun ω η => (2 * ω / (ω ^ 2 - η ^ 2)) • (cF K B) η)
      h₂ h₂' hY

theorem neg_not_mem_crect {a b c d : ℝ} (ha : 0 < a) {ω : ℂ} (hω : 0 < ω.re) :
    -ω ∉ crect a b c d := by
  intro h
  have := h.1.1
  simp at this
  linarith

/-- The kernel integral `∮ 2η/(ω² - η²) dη` (with respect to `η`). -/
theorem rint_kernel_eta {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hcd : c ≤ d) {ω : ℂ}
    (hω : 0 < ω.re) (hb : ω ∉ bdry a b c d) :
    rint (fun η => 2 * η / (ω ^ 2 - η ^ 2)) a b c d =
      -(rint (fun η : ℂ => (η - ω)⁻¹) a b c d) := by
  have hneg : -ω ∉ bdry a b c d := fun h =>
    neg_not_mem_crect ha hω (bdry_subset_crect a b c d hab hcd h)
  have e : (fun η => 2 * η / (ω ^ 2 - η ^ 2)) = fun η => (-1 : ℂ) • (2 * η / (η ^ 2 - ω ^ 2)) := by
    funext η; rw [smul_eq_mul, ← neg_sub, div_neg]; ring
  rw [e, rint_smul, rint_two_mul_div hab hcd hb hneg,
    rint_inv_sub_of_not_mem hab hcd (neg_not_mem_crect ha hω)]
  simp

/-- The kernel integral `∮ 2ω/(ω² - η²) dω` (with respect to `ω`). -/
theorem rint_kernel_omega {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hcd : c ≤ d) {η : ℂ}
    (hη : 0 < η.re) (hb : η ∉ bdry a b c d) :
    rint (fun ω => 2 * ω / (ω ^ 2 - η ^ 2)) a b c d = rint (fun ω : ℂ => (ω - η)⁻¹) a b c d := by
  have hneg : -η ∉ bdry a b c d := fun h =>
    neg_not_mem_crect ha hη (bdry_subset_crect a b c d hab hcd h)
  rw [rint_two_mul_div hab hcd hb hneg, rint_inv_sub_of_not_mem hab hcd (neg_not_mem_crect ha hη)]
  simp

theorem two_pi_I_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, I_ne_zero]

/-- Riesz projections of nested rectangles: `P₁ P₂ = P₁`. -/
theorem rP_mul_nested {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ} (ha₂ : 0 < a₂) (ha : a₂ < a₁)
    (h₁ : a₁ ≤ b₁) (hb : b₁ < b₂) (hc : c₂ < c₁) (h₁' : c₁ ≤ d₁) (hd : d₁ < d₂)
    (hg₁ : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, Good K B ω) (hg₂ : ∀ η ∈ bdry a₂ b₂ c₂ d₂, Good K B η) :
    rP K B a₁ b₁ c₁ d₁ * rP K B a₂ b₂ c₂ d₂ = rP K B a₁ b₁ c₁ d₁ := by
  have ha₁ : 0 < a₁ := ha₂.trans ha
  have h₂ : a₂ ≤ b₂ := by linarith
  have h₂' : c₂ ≤ d₂ := by linarith
  have hin : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, ω ∈ orect a₂ b₂ c₂ d₂ := by
    intro ω hω
    obtain ⟨⟨r1, r2⟩, i1, i2⟩ := bdry_subset_crect _ _ _ _ h₁ h₁' hω
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hout : ∀ η ∈ bdry a₂ b₂ c₂ d₂, η ∉ crect a₁ b₁ c₁ d₁ := by
    intro η hη hc1
    obtain ⟨⟨r1, r2⟩, i1, i2⟩ := hc1
    rcases hη with ⟨_, e | e⟩ | ⟨_, e | e⟩ <;> linarith
  have hdisj : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, ω ∉ bdry a₂ b₂ c₂ d₂ := fun ω hω hω' =>
    hout ω hω' (bdry_subset_crect _ _ _ _ h₁ h₁' hω)
  have key := rint_mul_rint ha₁ h₁ h₁' ha₂ h₂ h₂' hdisj hg₁ hg₂
  have k1 : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, rint (fun η => 2 * η / (ω ^ 2 - η ^ 2)) a₂ b₂ c₂ d₂ •
      cF K B ω = (-(2 * Real.pi * I)) • cF K B ω := by
    intro ω hω
    rw [rint_kernel_eta ha₂ h₂ h₂' (bdry_re_pos ha₁ h₁ h₁' hω) (hdisj ω hω),
      rint_inv_sub_of_mem (hin ω hω)]
  have k2 : ∀ η ∈ bdry a₂ b₂ c₂ d₂, rint (fun ω => 2 * ω / (ω ^ 2 - η ^ 2)) a₁ b₁ c₁ d₁ •
      cF K B η = (0 : ℂ) • cF K B η := by
    intro η hη
    rw [rint_kernel_omega ha₁ h₁ h₁' (bdry_re_pos ha₂ h₂ h₂' hη)
      (fun h => hout η hη (bdry_subset_crect _ _ _ _ h₁ h₁' h)),
      rint_inv_sub_of_not_mem h₁ h₁' (hout η hη)]
  rw [rint_congr h₁ h₁' k1, rint_congr h₂ h₂' k2, rint_smul, rint_smul, zero_smul,
    sub_zero] at key
  unfold rP
  rw [smul_mul_smul_comm, key, smul_smul]
  congr 1
  field_simp [two_pi_I_ne]

/-- Riesz projections of disjoint rectangles: `P₁ P₂ = 0`. -/
theorem rP_mul_disjoint {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ} (ha₁ : 0 < a₁) (h₁ : a₁ ≤ b₁)
    (h₁' : c₁ ≤ d₁) (ha₂ : 0 < a₂) (h₂ : a₂ ≤ b₂) (h₂' : c₂ ≤ d₂)
    (hdisj : ∀ ω ∈ crect a₁ b₁ c₁ d₁, ω ∉ crect a₂ b₂ c₂ d₂)
    (hg₁ : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, Good K B ω) (hg₂ : ∀ η ∈ bdry a₂ b₂ c₂ d₂, Good K B η) :
    rP K B a₁ b₁ c₁ d₁ * rP K B a₂ b₂ c₂ d₂ = 0 := by
  have hd' : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, ω ∉ bdry a₂ b₂ c₂ d₂ := fun ω hω hω' =>
    hdisj ω (bdry_subset_crect _ _ _ _ h₁ h₁' hω) (bdry_subset_crect _ _ _ _ h₂ h₂' hω')
  have key := rint_mul_rint ha₁ h₁ h₁' ha₂ h₂ h₂' hd' hg₁ hg₂
  have k1 : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, rint (fun η => 2 * η / (ω ^ 2 - η ^ 2)) a₂ b₂ c₂ d₂ •
      cF K B ω = (0 : ℂ) • cF K B ω := by
    intro ω hω
    rw [rint_kernel_eta ha₂ h₂ h₂' (bdry_re_pos ha₁ h₁ h₁' hω) (hd' ω hω),
      rint_inv_sub_of_not_mem h₂ h₂' (hdisj ω (bdry_subset_crect _ _ _ _ h₁ h₁' hω))]
    simp
  have k2 : ∀ η ∈ bdry a₂ b₂ c₂ d₂, rint (fun ω => 2 * ω / (ω ^ 2 - η ^ 2)) a₁ b₁ c₁ d₁ •
      cF K B η = (0 : ℂ) • cF K B η := by
    intro η hη
    have hη' : η ∉ crect a₁ b₁ c₁ d₁ := fun h => hdisj η h (bdry_subset_crect _ _ _ _ h₂ h₂' hη)
    rw [rint_kernel_omega ha₁ h₁ h₁' (bdry_re_pos ha₂ h₂ h₂' hη)
      (fun h => hη' (bdry_subset_crect _ _ _ _ h₁ h₁' h)), rint_inv_sub_of_not_mem h₁ h₁' hη']
  rw [rint_congr h₁ h₁' k1, rint_congr h₂ h₂' k2, rint_smul, rint_smul, zero_smul,
    zero_smul, sub_zero] at key
  unfold rP
  rw [smul_mul_smul_comm, key, smul_zero]

theorem rP_deform {a b c d a' b' c' d' : ℝ} (ha : a' ≤ a) (hab : a ≤ b)
    (hb : b ≤ b') (hc : c' ≤ c) (hcd : c ≤ d) (hd : d ≤ d')
    (hg : ∀ ω ∈ crect a' b' c' d', ω ∉ orect a b c d → Good K B ω) :
    rP K B a' b' c' d' = rP K B a b c d := by
  unfold rP
  rw [rint_deform ha hab hb hc hcd hd fun ω h1 h2 => differentiableAt_cF (hg ω h1 h2)]

/-- `P` commutes with the resolvent. -/
theorem res_mul_rP {z : ℂ} (hz : IsUnit (Lop K B z)) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hg : ∀ ω ∈ bdry a b c d, Good K B ω) :
    Res K B z * rP K B a b c d = rP K B a b c d * Res K B z := by
  have hF := continuousOn_cF hg
  unfold rP
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h1 := clm_rint (ContinuousLinearMap.mul ℂ A (Res K B z)) hab hcd hF
  have h2 := clm_rint ((ContinuousLinearMap.mul ℂ A).flip (Res K B z)) hab hcd hF
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at h1 h2
  rw [h1, h2]
  refine rint_congr hab hcd fun ω hω => ?_
  simp only [cF, mul_smul_comm, smul_mul_assoc]
  rw [res_comm hz (hg ω hω)]

/-- The "inner" integral: `P = K Q`. -/
def Qint (K B : A) (a b c d : ℝ) : A :=
  (-(2 * Real.pi * I)⁻¹) • rint (fun ω => (2 * ω) • Ring.inverse (Lop K B (ω ^ 2))) a b c d

theorem continuousOn_inv_Lop {S : Set ℂ} (h : ∀ ω ∈ S, Good K B ω) :
    ContinuousOn (fun ω : ℂ => (2 * ω) • Ring.inverse (Lop K B (ω ^ 2))) S := by
  refine continuousOn_of_diffAt fun ω hω => ?_
  have h1 : DifferentiableAt ℂ (fun ω : ℂ => Lop K B (ω ^ 2)) ω := by
    unfold Lop; fun_prop
  exact (differentiableAt_const _ |>.mul differentiableAt_id).smul (h1.inverse (h ω hω))

theorem rP_eq_mul_Qint {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hg : ∀ ω ∈ bdry a b c d, Good K B ω) : rP K B a b c d = K * Qint K B a b c d := by
  unfold rP Qint
  rw [mul_smul_comm]
  congr 1
  have h1 := clm_rint (ContinuousLinearMap.mul ℂ A K) hab hcd (continuousOn_inv_Lop hg)
  simp only [ContinuousLinearMap.mul_apply'] at h1
  rw [h1]
  refine rint_congr hab hcd fun ω _ => ?_
  simp only [cF, Res, mul_smul_comm]

theorem one_add_mul_Qint {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hg : ∀ ω ∈ bdry a b c d, Good K B ω) :
    (1 + B) * Qint K B a b c d =
      (-(2 * Real.pi * I)⁻¹) • rint (fun ω => ω ^ 2 • cF K B ω) a b c d := by
  unfold Qint
  rw [mul_smul_comm]
  congr 1
  have h1 := clm_rint (ContinuousLinearMap.mul ℂ A (1 + B)) hab hcd (continuousOn_inv_Lop hg)
  simp only [ContinuousLinearMap.mul_apply'] at h1
  rw [h1]
  have e : ∀ ω ∈ bdry a b c d, (1 + B) * ((2 * ω) • Ring.inverse (Lop K B (ω ^ 2))) =
      (2 * ω) • (1 : A) + ω ^ 2 • cF K B ω := by
    intro ω hω
    obtain ⟨u, hu⟩ := hg ω hω
    have h1B : (1 + B : A) = Lop K B (ω ^ 2) + ω ^ 2 • K := by simp [Lop]
    rw [h1B, ← hu, Ring.inverse_unit, mul_smul_comm, add_mul, Units.mul_inv]
    simp only [cF, Res, ← hu, Ring.inverse_unit, smul_add, smul_mul_assoc, smul_smul]
    ring_nf
  rw [rint_congr hab hcd e, rint_add hab hcd]
  · rw [rint_eq_zero (f := fun ω : ℂ => (2 * ω) • (1 : A)) hab hcd (fun ω _ => by fun_prop),
      zero_add]
  · exact (continuous_const.mul continuous_id).smul continuous_const |>.continuousOn
  · exact (continuous_pow 2).continuousOn.smul (continuousOn_cF hg)

omit [NormedAlgebra ℂ A] in
/-- Neumann series: `1 + X` is invertible when `‖X‖ ≤ q < 1`. -/
theorem isUnit_one_add_of_norm_le (X : A) {q : ℝ} (hq : q < 1) (hX : ‖X‖ ≤ q)
    (h1 : ‖(1 : A)‖ ≤ 1) : IsUnit (1 + X) ∧ ‖Ring.inverse (1 + X)‖ ≤ (1 - q)⁻¹ := by
  have ht : ‖-X‖ < 1 := by rw [norm_neg]; linarith
  have e : (1 : A) + X = 1 - -X := by abel
  refine ⟨e ▸ (Units.oneSub (-X) ht).isUnit, ?_⟩
  rw [e, ← geom_series_eq_inverse (-X) ht]
  refine (tsum_geometric_le_of_norm_lt_one (-X) ht).trans ?_
  have h2 : (1 - ‖-X‖)⁻¹ ≤ (1 - q)⁻¹ := by
    rw [norm_neg]; exact inv_anti₀ (by linarith) (by linarith)
  linarith

theorem isCompact_bdry {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) : IsCompact (bdry a b c d) := by
  have hc : IsCompact (crect a b c d) := by
    have := (isCompact_Icc (a := a) (b := b)).reProdIm (isCompact_Icc (a := c) (b := d))
    convert this using 1
    ext ω; simp [crect, mem_reProdIm]
  have e : bdry a b c d = (re ⁻¹' Icc a b ∩ (im ⁻¹' {c} ∪ im ⁻¹' {d})) ∪
      (im ⁻¹' Icc c d ∩ (re ⁻¹' {a} ∪ re ⁻¹' {b})) := by
    ext ω; simp [bdry]
  have hcl : IsClosed (bdry a b c d) := by
    rw [e]
    exact ((isClosed_Icc.preimage continuous_re).inter ((isClosed_singleton.preimage
      continuous_im).union (isClosed_singleton.preimage continuous_im))).union
      ((isClosed_Icc.preimage continuous_im).inter ((isClosed_singleton.preimage
      continuous_re).union (isClosed_singleton.preimage continuous_re)))
  exact hc.of_isClosed_subset hcl (bdry_subset_crect a b c d hab hcd)

theorem good_thickening {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hg : ∀ ω ∈ bdry a b c d, Good K B ω) :
    ∃ δ > 0, ∀ ω p : ℂ, p ∈ bdry a b c d → |ω.re - p.re| ≤ δ → |ω.im - p.im| ≤ δ →
      Good K B ω := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_bdry hab hcd).exists_thickening_subset_open
    (isOpen_good (K := K) (B := B)) hg
  refine ⟨δ / 3, by positivity, fun ω p hp h1 h2 => hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨p, hp, ?_⟩
  rw [dist_eq_norm]
  refine (norm_le_abs_re_add_abs_im _).trans_lt ?_
  simp only [sub_re, sub_im]
  linarith

theorem near_bdry_outer {a b c d δ : ℝ} (hδ : 0 ≤ δ) (hcd : c ≤ d) {ω : ℂ}
    (h1 : ω.re ∈ Icc (a - δ) (b + δ)) (h2 : ω.im ∈ Icc (c - δ) (d + δ))
    (h3 : ω ∉ orect a b c d) :
    ∃ p ∈ bdry a b c d, |ω.re - p.re| ≤ δ ∧ |ω.im - p.im| ≤ δ := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  by_cases hre : ω.re ∈ Ioo a b
  · have him : ω.im ∉ Ioo c d := fun h => h3 ⟨hre, h⟩
    by_cases hc : ω.im ≤ c
    · refine ⟨⟨ω.re, c⟩, Or.inl ⟨⟨hre.1.le, hre.2.le⟩, Or.inl rfl⟩, ?_, ?_⟩ <;>
        simp only [sub_self, abs_zero] <;>
        first | exact hδ | exact abs_le.2 ⟨by linarith, by linarith⟩
    · have hd : d ≤ ω.im := by
        by_contra h; exact him ⟨lt_of_not_ge hc, lt_of_not_ge h⟩
      refine ⟨⟨ω.re, d⟩, Or.inl ⟨⟨hre.1.le, hre.2.le⟩, Or.inr rfl⟩, ?_, ?_⟩ <;>
        simp only [sub_self, abs_zero] <;>
        first | exact hδ | exact abs_le.2 ⟨by linarith, by linarith⟩
  · set y := max c (min ω.im d) with hy
    have hy1 : c ≤ y := le_max_left _ _
    have hy2 : y ≤ d := max_le hcd (min_le_right _ _)
    have hyd : |ω.im - y| ≤ δ := by
      rw [abs_le]; constructor
      · rw [hy]; rcases le_total ω.im d with h | h
        · rw [min_eq_left h]; rcases le_total c ω.im with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_right h, max_eq_right hcd]; linarith
      · rw [hy]; rcases le_total ω.im d with h | h
        · rw [min_eq_left h]; rcases le_total c ω.im with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_right h, max_eq_right hcd]; linarith
    by_cases ha : ω.re ≤ a
    · refine ⟨⟨a, y⟩, Or.inr ⟨⟨hy1, hy2⟩, Or.inl rfl⟩, ?_, hyd⟩
      simp only; rw [abs_le]; constructor <;> linarith
    · have hb : b ≤ ω.re := by
        by_contra h; exact hre ⟨lt_of_not_ge ha, lt_of_not_ge h⟩
      refine ⟨⟨b, y⟩, Or.inr ⟨⟨hy1, hy2⟩, Or.inr rfl⟩, ?_, hyd⟩
      simp only; rw [abs_le]; constructor <;> linarith

theorem near_bdry_inner {a b c d δ : ℝ} (hδ : 0 ≤ δ) {ω : ℂ}
    (h1 : ω.re ∈ Icc a b) (h2 : ω.im ∈ Icc c d)
    (h3 : ω ∉ orect (a + δ) (b - δ) (c + δ) (d - δ)) :
    ∃ p ∈ bdry a b c d, |ω.re - p.re| ≤ δ ∧ |ω.im - p.im| ≤ δ := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  by_cases ha : ω.re ≤ a + δ
  · refine ⟨⟨a, ω.im⟩, Or.inr ⟨⟨h2a, h2b⟩, Or.inl rfl⟩, ?_, ?_⟩ <;> simp only <;>
      rw [abs_le] <;> constructor <;> linarith
  by_cases hb : b - δ ≤ ω.re
  · refine ⟨⟨b, ω.im⟩, Or.inr ⟨⟨h2a, h2b⟩, Or.inr rfl⟩, ?_, ?_⟩ <;> simp only <;>
      rw [abs_le] <;> constructor <;> linarith
  by_cases hc : ω.im ≤ c + δ
  · refine ⟨⟨ω.re, c⟩, Or.inl ⟨⟨h1a, h1b⟩, Or.inl rfl⟩, ?_, ?_⟩ <;> simp only <;>
      rw [abs_le] <;> constructor <;> linarith
  · have hd : d - δ ≤ ω.im := by
      by_contra h
      exact h3 ⟨⟨lt_of_not_ge ha, lt_of_not_ge hb⟩, lt_of_not_ge hc, lt_of_not_ge h⟩
    refine ⟨⟨ω.re, d⟩, Or.inl ⟨⟨h1a, h1b⟩, Or.inr rfl⟩, ?_, ?_⟩ <;> simp only <;>
      rw [abs_le] <;> constructor <;> linarith

/-- Riesz projections are idempotent. -/
theorem rP_idem {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hcd : c ≤ d)
    (hg : ∀ ω ∈ bdry a b c d, Good K B ω) :
    rP K B a b c d * rP K B a b c d = rP K B a b c d := by
  obtain ⟨δ, hδ, hgood⟩ := good_thickening hab hcd hg
  set δ' := min δ (a / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (half_pos ha)
  have hδ'1 : δ' ≤ δ := min_le_left _ _
  have hδ'2 : δ' ≤ a / 2 := min_le_right _ _
  have hann : ∀ ω ∈ crect (a - δ') (b + δ') (c - δ') (d + δ'), ω ∉ orect a b c d →
      Good K B ω := by
    intro ω hω hno
    obtain ⟨p, hp, h1, h2⟩ := near_bdry_outer hδ'0.le hcd hω.1 hω.2 hno
    exact hgood ω p hp (h1.trans hδ'1) (h2.trans hδ'1)
  have hg' : ∀ ω ∈ bdry (a - δ') (b + δ') (c - δ') (d + δ'), Good K B ω := by
    intro ω hω
    refine hann ω (bdry_subset_crect _ _ _ _ (by linarith) (by linarith) hω) ?_
    rintro ⟨⟨r1, r2⟩, i1, i2⟩
    rcases hω with ⟨_, e | e⟩ | ⟨_, e | e⟩ <;> linarith
  have hdef := rP_deform (K := K) (B := B) (by linarith : a - δ' ≤ a) hab
    (by linarith : b ≤ b + δ') (by linarith : c - δ' ≤ c) hcd (by linarith : d ≤ d + δ') hann
  have hn := rP_mul_nested (K := K) (B := B) (by linarith : 0 < a - δ') (by linarith : a - δ' < a)
    hab (by linarith : b < b + δ') (by linarith : c - δ' < c) hcd (by linarith : d < d + δ') hg hg'
  rw [hdef] at hn
  exact hn

theorem rP_shrink {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hg : ∀ ω ∈ bdry a b c d, Good K B ω) :
    ∃ δ > 0, δ ≤ (b - a) / 3 ∧ δ ≤ (d - c) / 3 ∧ ∀ δ', 0 < δ' → δ' ≤ δ → rP K B a b c d =
      rP K B (a + δ') (b - δ') (c + δ') (d - δ') ∧
      ∀ ω ∈ bdry (a + δ') (b - δ') (c + δ') (d - δ'), Good K B ω := by
  obtain ⟨δ, hδ, hgood⟩ := good_thickening hab.le hcd.le hg
  refine ⟨min δ (min ((b - a) / 3) ((d - c) / 3)), ?_, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), fun δ' h0 h1 => ?_⟩
  · exact lt_min hδ (lt_min (by linarith) (by linarith))
  have e1 : δ' ≤ δ := h1.trans (min_le_left _ _)
  have e2 : δ' ≤ (b - a) / 3 := h1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : δ' ≤ (d - c) / 3 := h1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hann : ∀ ω ∈ crect a b c d, ω ∉ orect (a + δ') (b - δ') (c + δ') (d - δ') →
      Good K B ω := by
    intro ω hω hno
    obtain ⟨p, hp, q1, q2⟩ := near_bdry_inner h0.le hω.1 hω.2 hno
    exact hgood ω p hp (q1.trans e1) (q2.trans e1)
  refine ⟨(rP_deform (K := K) (B := B) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hann), fun ω hω => hann ω ?_ ?_⟩
  · obtain ⟨⟨r1, r2⟩, i1, i2⟩ := bdry_subset_crect _ _ _ _ (by linarith) (by linarith) hω
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨r1, r2⟩, i1, i2⟩
    rcases hω with ⟨_, e | e⟩ | ⟨_, e | e⟩ <;> linarith

/-- Riesz projections of rectangles side by side (sharing at most an edge) annihilate. -/
theorem rP_mul_side {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ} (ha₁ : 0 < a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂)
    (h₂ : a₂ < b₂) (h₁' : c₁ < d₁) (h₂' : c₂ < d₂)
    (hg₁ : ∀ ω ∈ bdry a₁ b₁ c₁ d₁, Good K B ω) (hg₂ : ∀ η ∈ bdry a₂ b₂ c₂ d₂, Good K B η) :
    rP K B a₁ b₁ c₁ d₁ * rP K B a₂ b₂ c₂ d₂ = 0 ∧ rP K B a₂ b₂ c₂ d₂ * rP K B a₁ b₁ c₁ d₁ = 0 := by
  obtain ⟨δ₁, hδ₁, l₁, l₁', k₁⟩ := rP_shrink h₁ h₁' hg₁
  obtain ⟨δ₂, hδ₂, l₂, l₂', k₂⟩ := rP_shrink h₂ h₂' hg₂
  set δ := min δ₁ (min δ₂ (a₁ / 2)) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (lt_min hδ₂ (half_pos ha₁))
  have f1 : δ ≤ δ₁ := min_le_left _ _
  have f2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have f3 : δ ≤ a₁ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨E1, G1⟩ := k₁ δ hδ0 f1
  obtain ⟨E2, G2⟩ := k₂ δ hδ0 f2
  rw [E1, E2]
  have hd : ∀ ω ∈ crect (a₁ + δ) (b₁ - δ) (c₁ + δ) (d₁ - δ),
      ω ∉ crect (a₂ + δ) (b₂ - δ) (c₂ + δ) (d₂ - δ) := by
    rintro ω ⟨⟨r1, r2⟩, _⟩ ⟨⟨r3, r4⟩, _⟩; linarith
  have hd' : ∀ ω ∈ crect (a₂ + δ) (b₂ - δ) (c₂ + δ) (d₂ - δ),
      ω ∉ crect (a₁ + δ) (b₁ - δ) (c₁ + δ) (d₁ - δ) := fun ω h1 h2 => hd ω h2 h1
  exact ⟨rP_mul_disjoint (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hd G1 G2, rP_mul_disjoint (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) hd' G2 G1⟩

end Involution
