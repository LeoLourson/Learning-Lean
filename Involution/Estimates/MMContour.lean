module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Contour integrals over boundaries of rectangles `[a, b] × [c, d]` in `ℂ`
(counterclockwise), with values in a complex Banach space: additivity, the Cauchy
theorem, the integral of `(ω - p)⁻¹`, deformation of nested rectangles. -/

@[expose] public noncomputable section

open Complex MeasureTheory Set intervalIntegral

namespace Involution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Integral over the counterclockwise boundary of `[a, b] × [c, d]`. -/
def rint (f : ℂ → E) (a b c d : ℝ) : E :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
    I • (∫ y : ℝ in c..d, f (b + y * I)) - I • (∫ y : ℝ in c..d, f (a + y * I))

/-- Closed rectangle. -/
def crect (a b c d : ℝ) : Set ℂ := {ω | ω.re ∈ Icc a b ∧ ω.im ∈ Icc c d}

/-- Open rectangle. -/
def orect (a b c d : ℝ) : Set ℂ := {ω | ω.re ∈ Ioo a b ∧ ω.im ∈ Ioo c d}

/-- Boundary of a rectangle. -/
def bdry (a b c d : ℝ) : Set ℂ :=
  {ω | ω.re ∈ Icc a b ∧ (ω.im = c ∨ ω.im = d)} ∪ {ω | ω.im ∈ Icc c d ∧ (ω.re = a ∨ ω.re = b)}

theorem bdry_subset_crect (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    bdry a b c d ⊆ crect a b c d := by
  rintro ω (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩) <;>
    exact ⟨by simp_all [Icc], by simp_all [Icc]⟩

theorem mem_bdry_bottom {a b c d x : ℝ} (hx : x ∈ Icc a b) : (x : ℂ) + c * I ∈ bdry a b c d :=
  Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩

theorem mem_bdry_top {a b c d x : ℝ} (hx : x ∈ Icc a b) : (x : ℂ) + d * I ∈ bdry a b c d :=
  Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩

theorem mem_bdry_left {a b c d y : ℝ} (hy : y ∈ Icc c d) : (a : ℂ) + y * I ∈ bdry a b c d :=
  Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩

theorem mem_bdry_right {a b c d y : ℝ} (hy : y ∈ Icc c d) : (b : ℂ) + y * I ∈ bdry a b c d :=
  Or.inr ⟨by simpa using hy, Or.inr (by simp)⟩

theorem continuous_horiz (c : ℝ) : Continuous fun x : ℝ => (x : ℂ) + c * I := by fun_prop

theorem continuous_vert (a : ℝ) : Continuous fun y : ℝ => (a : ℂ) + y * I := by fun_prop

section integrability

variable {f : ℂ → E} {a b c d : ℝ}

omit [NormedSpace ℂ E] in
theorem ii_bottom (hab : a ≤ b) (hf : ContinuousOn f (bdry a b c d)) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hf.comp (continuous_horiz c).continuousOn fun x hx => mem_bdry_bottom hx

omit [NormedSpace ℂ E] in
theorem ii_top (hab : a ≤ b) (hf : ContinuousOn f (bdry a b c d)) :
    IntervalIntegrable (fun x : ℝ => f (x + d * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hf.comp (continuous_horiz d).continuousOn fun x hx => mem_bdry_top hx

omit [NormedSpace ℂ E] in
theorem ii_left (hcd : c ≤ d) (hf : ContinuousOn f (bdry a b c d)) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hcd]
  exact hf.comp (continuous_vert a).continuousOn fun y hy => mem_bdry_left hy

omit [NormedSpace ℂ E] in
theorem ii_right (hcd : c ≤ d) (hf : ContinuousOn f (bdry a b c d)) :
    IntervalIntegrable (fun y : ℝ => f (b + y * I)) volume c d := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hcd]
  exact hf.comp (continuous_vert b).continuousOn fun y hy => mem_bdry_right hy

end integrability

/-- Splitting a rectangle by a vertical line. -/
theorem rint_split_x {f : ℂ → E} {a m b c d : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (h1 : ContinuousOn f (bdry a m c d)) (h2 : ContinuousOn f (bdry m b c d)) :
    rint f a b c d = rint f a m c d + rint f m b c d := by
  unfold rint
  rw [← integral_add_adjacent_intervals (ii_bottom ham h1) (ii_bottom hmb h2),
    ← integral_add_adjacent_intervals (ii_top ham h1) (ii_top hmb h2)]
  abel

/-- Splitting a rectangle by a horizontal line. -/
theorem rint_split_y {f : ℂ → E} {a b c m d : ℝ} (hcm : c ≤ m) (hmd : m ≤ d)
    (h1 : ContinuousOn f (bdry a b c m)) (h2 : ContinuousOn f (bdry a b m d)) :
    rint f a b c d = rint f a b c m + rint f a b m d := by
  unfold rint
  rw [← integral_add_adjacent_intervals (ii_left hcm h1) (ii_left hmd h2),
    ← integral_add_adjacent_intervals (ii_right hcm h1) (ii_right hmd h2)]
  simp only [smul_add]
  abel

/-- Cauchy theorem for a rectangle. -/
theorem rint_eq_zero {f : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ∀ ω ∈ crect a b c d, DifferentiableAt ℂ f ω) : rint f a b c d = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn f (a + c * I) (b + d * I) ?_
  · simpa [rint] using h
  · intro ω hω
    apply (hf ω _).differentiableWithinAt
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, add_im, mul_im, zero_add, uIcc_of_le hab,
      uIcc_of_le hcd] at hω
    exact hω

theorem rint_add {f g : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (bdry a b c d)) (hg : ContinuousOn g (bdry a b c d)) :
    rint (fun ω => f ω + g ω) a b c d = rint f a b c d + rint g a b c d := by
  unfold rint
  rw [integral_add (ii_bottom hab hf) (ii_bottom hab hg),
    integral_add (ii_top hab hf) (ii_top hab hg),
    integral_add (ii_right hcd hf) (ii_right hcd hg),
    integral_add (ii_left hcd hf) (ii_left hcd hg)]
  simp only [smul_add]
  abel

theorem rint_sub {f g : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (bdry a b c d)) (hg : ContinuousOn g (bdry a b c d)) :
    rint (fun ω => f ω - g ω) a b c d = rint f a b c d - rint g a b c d := by
  unfold rint
  rw [integral_sub (ii_bottom hab hf) (ii_bottom hab hg),
    integral_sub (ii_top hab hf) (ii_top hab hg),
    integral_sub (ii_right hcd hf) (ii_right hcd hg),
    integral_sub (ii_left hcd hf) (ii_left hcd hg)]
  simp only [smul_sub]
  abel

theorem rint_smul {f : ℂ → E} {a b c d : ℝ} (k : ℂ) :
    rint (fun ω => k • f ω) a b c d = k • rint f a b c d := by
  unfold rint
  simp only [intervalIntegral.integral_smul, smul_sub, smul_add, smul_comm k I]

theorem rint_const_smul [CompleteSpace E] {g : ℂ → ℂ} {a b c d : ℝ} (v : E) :
    rint (fun ω => g ω • v) a b c d = rint g a b c d • v := by
  unfold rint
  simp only [intervalIntegral.integral_smul_const, sub_smul, add_smul, smul_assoc]

theorem clm_rint [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (L : E →L[ℂ] F) {f : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (bdry a b c d)) :
    L (rint f a b c d) = rint (fun ω => L (f ω)) a b c d := by
  unfold rint
  simp only [map_sub, map_add, map_smul, L.intervalIntegral_comp_comm (ii_bottom hab hf),
    L.intervalIntegral_comp_comm (ii_top hab hf), L.intervalIntegral_comp_comm (ii_right hcd hf),
    L.intervalIntegral_comp_comm (ii_left hcd hf)]

theorem norm_rint_le {f : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ‖rint f a b c d‖ ≤ (∫ x in a..b, ‖f (x + c * I)‖) + (∫ x in a..b, ‖f (x + d * I)‖) +
      (∫ y in c..d, ‖f (b + y * I)‖) + ∫ y in c..d, ‖f (a + y * I)‖ := by
  unfold rint
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add (norm_integral_le_integral_norm hab) (norm_integral_le_integral_norm hab))) ?_)) ?_
  · rw [norm_smul, norm_I, one_mul]; exact norm_integral_le_integral_norm hcd
  · rw [norm_smul, norm_I, one_mul]; exact norm_integral_le_integral_norm hcd

/-- Symmetry `ω ↦ -ω` for odd integrands. -/
theorem rint_odd {f : ℂ → E} (hf : ∀ ω, f (-ω) = -f ω) (a b c d : ℝ) :
    rint f (-b) (-a) (-d) (-c) = rint f a b c d := by
  have h1 : ∀ x y : ℝ, f (((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -f (x + y * I) := by
    intro x y; rw [← hf]; congr 1; push_cast; ring
  unfold rint
  rw [← integral_comp_neg (fun x : ℝ => f (x + ((-d : ℝ) : ℂ) * I)),
    ← integral_comp_neg (fun x : ℝ => f (x + ((-c : ℝ) : ℂ) * I)),
    ← integral_comp_neg (fun y : ℝ => f (((-a : ℝ) : ℂ) + y * I)),
    ← integral_comp_neg (fun y : ℝ => f (((-b : ℝ) : ℂ) + y * I))]
  simp only [h1, intervalIntegral.integral_neg, smul_neg]
  abel

/-- Translation invariance. -/
theorem rint_translate (f : ℂ → E) (p : ℂ) (a b c d : ℝ) :
    rint (fun ω => f (ω - p)) (a + p.re) (b + p.re) (c + p.im) (d + p.im) = rint f a b c d := by
  have e1 : ∀ x y : ℝ, ((x + p.re : ℝ) : ℂ) + ((y + p.im : ℝ) : ℂ) * I - p = x + y * I := by
    intro x y; apply Complex.ext <;> simp
  unfold rint
  rw [← integral_comp_add_right (fun x : ℝ => f (x + ((c + p.im : ℝ) : ℂ) * I - p)),
    ← integral_comp_add_right (fun x : ℝ => f (x + ((d + p.im : ℝ) : ℂ) * I - p)),
    ← integral_comp_add_right (fun y : ℝ => f (((b + p.re : ℝ) : ℂ) + y * I - p)),
    ← integral_comp_add_right (fun y : ℝ => f (((a + p.re : ℝ) : ℂ) + y * I - p))]
  simp only [e1]

theorem continuousOn_of_diffAt {f : ℂ → E} {S : Set ℂ} (h : ∀ ω ∈ S, DifferentiableAt ℂ f ω) :
    ContinuousOn f S := fun ω hω => (h ω hω).continuousAt.continuousWithinAt

theorem crect_mono {p q r t a' b' c' d' : ℝ} (h1 : a' ≤ p) (h2 : q ≤ b') (h3 : c' ≤ r)
    (h4 : t ≤ d') : crect p q r t ⊆ crect a' b' c' d' := by
  rintro ω ⟨⟨h5, h6⟩, h7, h8⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Deformation of a rectangle contour into a smaller nested one. -/
theorem rint_deform {f : ℂ → E} {a b c d a' b' c' d' : ℝ} (ha : a' ≤ a) (hab : a ≤ b)
    (hb : b ≤ b') (hc : c' ≤ c) (hcd : c ≤ d) (hd : d ≤ d')
    (hf : ∀ ω ∈ crect a' b' c' d', ω ∉ orect a b c d → DifferentiableAt ℂ f ω) :
    rint f a' b' c' d' = rint f a b c d := by
  have hA : ∀ ω : ℂ, ω ∈ crect a' b' c' d' →
      (ω.re ≤ a ∨ b ≤ ω.re ∨ ω.im ≤ c ∨ d ≤ ω.im) → DifferentiableAt ℂ f ω := by
    intro ω h1 h3
    refine hf ω h1 ?_
    rintro ⟨⟨h4, h5⟩, h6, h7⟩
    rcases h3 with h3 | h3 | h3 | h3 <;> linarith
  have hc' : c' ≤ d' := hc.trans (hcd.trans hd)
  have cont : ∀ p q r t : ℝ, a' ≤ p → q ≤ b' → c' ≤ r → t ≤ d' → p ≤ q → r ≤ t →
      (∀ ω ∈ bdry p q r t, ω.re ≤ a ∨ b ≤ ω.re ∨ ω.im ≤ c ∨ d ≤ ω.im) →
      ContinuousOn f (bdry p q r t) := by
    intro p q r t h1 h2 h3 h4 hpq hrt h
    exact continuousOn_of_diffAt fun ω hω =>
      hA ω (crect_mono h1 h2 h3 h4 (bdry_subset_crect p q r t hpq hrt hω)) (h ω hω)
  have zero : ∀ p q r t : ℝ, a' ≤ p → q ≤ b' → c' ≤ r → t ≤ d' → p ≤ q → r ≤ t →
      (∀ ω ∈ crect p q r t, ω.re ≤ a ∨ b ≤ ω.re ∨ ω.im ≤ c ∨ d ≤ ω.im) →
      rint f p q r t = 0 := by
    intro p q r t h1 h2 h3 h4 hpq hrt h
    exact rint_eq_zero hpq hrt fun ω hω => hA ω (crect_mono h1 h2 h3 h4 hω) (h ω hω)
  have c1 := cont a' a c' d' le_rfl (hab.trans hb) le_rfl le_rfl ha hc' (fun ω hω =>
    Or.inl (bdry_subset_crect _ _ _ _ ha hc' hω).1.2)
  have c2 := cont a b' c' d' ha le_rfl le_rfl le_rfl (hab.trans hb) hc' (by
    rintro ω (⟨_, h | h⟩ | ⟨_, h | h⟩)
    · exact Or.inr (Or.inr (Or.inl (h ▸ hc)))
    · exact Or.inr (Or.inr (Or.inr (h ▸ hd)))
    · exact Or.inl h.le
    · exact Or.inr (Or.inl (h ▸ hb)))
  have c3 := cont a b c' d' ha hb le_rfl le_rfl hab hc' (by
    rintro ω (⟨_, h | h⟩ | ⟨_, h | h⟩)
    · exact Or.inr (Or.inr (Or.inl (h ▸ hc)))
    · exact Or.inr (Or.inr (Or.inr (h ▸ hd)))
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.ge))
  have c4 := cont b b' c' d' (ha.trans hab) le_rfl le_rfl le_rfl hb hc' (fun ω hω =>
    Or.inr (Or.inl (bdry_subset_crect _ _ _ _ hb hc' hω).1.1))
  have c5 := cont a b c' c ha hb le_rfl (hcd.trans hd) hab hc (fun ω hω =>
    Or.inr (Or.inr (Or.inl (bdry_subset_crect _ _ _ _ hab hc hω).2.2)))
  have c6 := cont a b c d' ha hb hc le_rfl hab (hcd.trans hd) (by
    rintro ω (⟨_, h | h⟩ | ⟨_, h | h⟩)
    · exact Or.inr (Or.inr (Or.inl h.le))
    · exact Or.inr (Or.inr (Or.inr (h ▸ hd)))
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.ge))
  have c7 := cont a b c d ha hb hc (hd) hab hcd (by
    rintro ω (⟨_, h | h⟩ | ⟨_, h | h⟩)
    · exact Or.inr (Or.inr (Or.inl h.le))
    · exact Or.inr (Or.inr (Or.inr h.ge))
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.ge))
  have c8 := cont a b d d' ha hb (hc.trans hcd) le_rfl hab hd (fun ω hω =>
    Or.inr (Or.inr (Or.inr (bdry_subset_crect _ _ _ _ hab hd hω).2.1)))
  rw [rint_split_x ha (hab.trans hb) c1 c2, rint_split_x hab hb c3 c4,
    rint_split_y hc (hcd.trans hd) c5 c6, rint_split_y hcd hd c7 c8,
    zero a' a c' d' le_rfl (hab.trans hb) le_rfl le_rfl ha hc' (fun ω hω => Or.inl hω.1.2),
    zero b b' c' d' (ha.trans hab) le_rfl le_rfl le_rfl hb hc' (fun ω hω => Or.inr (Or.inl hω.1.1)),
    zero a b c' c ha hb le_rfl (hcd.trans hd) hab hc
      (fun ω hω => Or.inr (Or.inr (Or.inl hω.2.2))),
    zero a b d d' ha hb (hc.trans hcd) le_rfl hab hd
      (fun ω hω => Or.inr (Or.inr (Or.inr hω.2.1)))]
  simp

theorem integral_two_h_div (h : ℝ) (hh : 0 < h) :
    ∫ x in (-h)..h, 2 * h / (x ^ 2 + h ^ 2) = Real.pi := by
  have : ∀ x : ℝ, 2 * h / (x ^ 2 + h ^ 2) = 2 * (1 / h) * (1 + (x / h) ^ 2)⁻¹ := by
    intro x; field_simp; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) hh.ne', integral_inv_one_add_sq]
  rw [neg_div, div_self hh.ne', Real.arctan_neg, Real.arctan_one]
  field_simp; ring

theorem rint_inv_square (h : ℝ) (hh : 0 < h) :
    rint (fun ω : ℂ => ω⁻¹) (-h) h (-h) h = 2 * Real.pi * I := by
  have n1 : ∀ x : ℝ, ((x : ℂ) + ((-h : ℝ) : ℂ) * I) ≠ 0 := by
    intro x e; have := congrArg Complex.im e; simp at this; linarith
  have n2 : ∀ x : ℝ, ((x : ℂ) + (h : ℂ) * I) ≠ 0 := by
    intro x e; have := congrArg Complex.im e; simp at this; linarith
  have n3 : ∀ y : ℝ, ((h : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y e; have := congrArg Complex.re e; simp at this; linarith
  have n4 : ∀ y : ℝ, (((-h : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y e; have := congrArg Complex.re e; simp at this; linarith
  have e1 : ∀ x : ℝ, ((x : ℂ) + ((-h : ℝ) : ℂ) * I)⁻¹ - ((x : ℂ) + (h : ℂ) * I)⁻¹ =
      ((2 * h / (x ^ 2 + h ^ 2) : ℝ) : ℂ) * I := by
    intro x
    have hab : ((x : ℂ) + ((-h : ℝ) : ℂ) * I) * ((x : ℂ) + (h : ℂ) * I) =
        ((x ^ 2 + h ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [inv_sub_inv (n1 x) (n2 x), hab]
    push_cast; ring
  have e2 : ∀ y : ℝ, I * (((h : ℂ) + (y : ℂ) * I)⁻¹ - (((-h : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) =
      ((2 * h / (y ^ 2 + h ^ 2) : ℝ) : ℂ) * I := by
    intro y
    have hab : ((h : ℂ) + (y : ℂ) * I) * (((-h : ℝ) : ℂ) + (y : ℂ) * I) =
        -((y ^ 2 + h ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [inv_sub_inv (n3 y) (n4 y), hab, div_neg]
    push_cast; ring
  have i1 : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + ((-h : ℝ) : ℂ) * I)⁻¹) volume (-h) h :=
    (Continuous.inv₀ (by fun_prop) n1).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (h : ℂ) * I)⁻¹) volume (-h) h :=
    (Continuous.inv₀ (by fun_prop) n2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun y : ℝ => ((h : ℂ) + (y : ℂ) * I)⁻¹) volume (-h) h :=
    (Continuous.inv₀ (by fun_prop) n3).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun y : ℝ => (((-h : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) volume (-h) h :=
    (Continuous.inv₀ (by fun_prop) n4).intervalIntegrable _ _
  have hsum : rint (fun ω : ℂ => ω⁻¹) (-h) h (-h) h =
      (∫ x in (-h)..h, (((x : ℂ) + ((-h : ℝ) : ℂ) * I)⁻¹ - ((x : ℂ) + (h : ℂ) * I)⁻¹)) +
      ∫ y in (-h)..h, I * (((h : ℂ) + (y : ℂ) * I)⁻¹ - (((-h : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) := by
    unfold rint
    rw [integral_sub i1 i2, intervalIntegral.integral_const_mul, integral_sub i3 i4]
    simp only [smul_eq_mul]
    ring
  rw [hsum]
  simp only [e1, e2]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    integral_two_h_div h hh]
  ring

/-- The integral of `(ω - p)⁻¹` over a rectangle containing `p` in its interior. -/
theorem rint_inv_sub_of_mem {a b c d : ℝ} {p : ℂ} (hp : p ∈ orect a b c d) :
    rint (fun ω : ℂ => (ω - p)⁻¹) a b c d = 2 * Real.pi * I := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  set h := min (min (p.re - a) (b - p.re)) (min (p.im - c) (d - p.im)) / 2 with hh
  have hpos : 0 < h := by
    rw [hh]; apply half_pos; apply lt_min <;> apply lt_min <;> linarith
  have hle1 : h ≤ (p.re - a) / 2 := by
    rw [hh]; gcongr; exact (min_le_left _ _).trans (min_le_left _ _)
  have hle2 : h ≤ (b - p.re) / 2 := by
    rw [hh]; gcongr; exact (min_le_left _ _).trans (min_le_right _ _)
  have hle3 : h ≤ (p.im - c) / 2 := by
    rw [hh]; gcongr; exact (min_le_right _ _).trans (min_le_left _ _)
  have hle4 : h ≤ (d - p.im) / 2 := by
    rw [hh]; gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
  rw [rint_deform (a := -h + p.re) (b := h + p.re) (c := -h + p.im) (d := h + p.im)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · rw [rint_translate (fun ω : ℂ => ω⁻¹) p (-h) h (-h) h]
    exact rint_inv_square h hpos
  · intro ω _ hω
    have hne : ω - p ≠ 0 := by
      intro e
      apply hω
      have e' : ω = p := sub_eq_zero.mp e
      subst e'
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    exact (differentiableAt_id.sub_const p).inv hne

theorem rint_inv_sub_of_not_mem {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {p : ℂ}
    (hp : p ∉ crect a b c d) : rint (fun ω : ℂ => (ω - p)⁻¹) a b c d = 0 := by
  refine rint_eq_zero hab hcd fun ω hω => ?_
  have hne : ω - p ≠ 0 := by
    intro e; exact hp (sub_eq_zero.mp e ▸ hω)
  exact (differentiableAt_id.sub_const p).inv hne

section fubini

theorem param_integral_swap {g : ℂ → ℂ → E} {S₁ S₂ : Set ℂ} {p q : ℝ → ℂ}
    (hp : Continuous p) (hq : Continuous q) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hpS : ∀ s ∈ Icc a b, p s ∈ S₁) (hqS : ∀ t ∈ Icc c d, q t ∈ S₂)
    (hg : ContinuousOn (fun z : ℂ × ℂ => g z.1 z.2) (S₁ ×ˢ S₂)) :
    IntervalIntegrable (fun s => ∫ t in c..d, g (p s) (q t)) volume a b ∧
      ∫ s in a..b, ∫ t in c..d, g (p s) (q t) = ∫ t in c..d, ∫ s in a..b, g (p s) (q t) := by
  set φ : ℝ → ℝ → E := fun s t => g (p (projIcc a b hab s)) (q (projIcc c d hcd t)) with hφ
  have hφc : Continuous (Function.uncurry φ) := by
    have h1 : Continuous fun z : ℝ × ℝ => (p (projIcc a b hab z.1), q (projIcc c d hcd z.2)) :=
      ((hp.comp continuous_subtype_val).comp (continuous_projIcc.comp continuous_fst)).prodMk
        ((hq.comp continuous_subtype_val).comp (continuous_projIcc.comp continuous_snd))
    exact hg.comp_continuous h1 fun z => ⟨hpS _ (projIcc a b hab z.1).2,
      hqS _ (projIcc c d hcd z.2).2⟩
  have eq1 : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d, g (p s) (q t) = φ s t := by
    intro s hs t ht
    simp [hφ, projIcc_of_mem hab hs, projIcc_of_mem hcd ht]
  have eq2 : ∀ s ∈ Icc a b, ∫ t in c..d, g (p s) (q t) = ∫ t in c..d, φ s t := by
    intro s hs
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hcd] at ht
    exact eq1 s hs t ht
  have eq3 : ∀ t ∈ Icc c d, ∫ s in a..b, g (p s) (q t) = ∫ s in a..b, φ s t := by
    intro t ht
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    exact eq1 s hs t ht
  constructor
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (continuous_parametric_intervalIntegral_of_continuous' hφc c d).continuousOn.congr
      eq2
  · rw [integral_congr (fun s hs => eq2 s (by rwa [uIcc_of_le hab] at hs)),
      integral_congr (fun t ht => eq3 t (by rwa [uIcc_of_le hcd] at ht))]
    apply intervalIntegral_intervalIntegral_swap
    refine (hφc.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d)))).mono_set ?_
    rw [uIoc_of_le hab, uIoc_of_le hcd]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self

/-- Data of the four sides of the boundary of a rectangle. -/
def sideW : Fin 4 → ℂ := ![1, -1, I, -I]

def sideLo (a c : ℝ) : Fin 4 → ℝ := ![a, a, c, c]

def sideHi (b d : ℝ) : Fin 4 → ℝ := ![b, b, d, d]

def sidePath (a b c d : ℝ) : Fin 4 → ℝ → ℂ :=
  ![fun t => t + c * I, fun t => t + d * I, fun t => b + t * I, fun t => a + t * I]

theorem rint_eq_sum (f : ℂ → E) (a b c d : ℝ) :
    rint f a b c d = ∑ k : Fin 4, sideW k •
      ∫ t in sideLo a c k..sideHi b d k, f (sidePath a b c d k t) := by
  simp only [rint, Fin.sum_univ_four, sideW, sideLo, sideHi, sidePath]
  simp
  abel

theorem sidePath_continuous (a b c d : ℝ) (k : Fin 4) : Continuous (sidePath a b c d k) := by
  fin_cases k <;>
    simp only [sidePath, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop

theorem sidePath_mem {a b c d : ℝ} (k : Fin 4) {t : ℝ}
    (ht : t ∈ Icc (sideLo a c k) (sideHi b d k)) :
    sidePath a b c d k t ∈ bdry a b c d := by
  fin_cases k
  · exact mem_bdry_bottom ht
  · exact mem_bdry_top ht
  · exact mem_bdry_right ht
  · exact mem_bdry_left ht

theorem sideLo_le {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (k : Fin 4) :
    sideLo a c k ≤ sideHi b d k := by
  fin_cases k <;> simp [sideLo, sideHi, hab, hcd]

theorem param_side_continuousOn {G : ℂ → ℂ → E} {S T : Set ℂ} {q : ℝ → ℂ} (hq : Continuous q)
    {c d : ℝ} (hcd : c ≤ d) (hqT : ∀ t ∈ Icc c d, q t ∈ T)
    (hG : ContinuousOn (fun z : ℂ × ℂ => G z.1 z.2) (S ×ˢ T)) :
    ContinuousOn (fun ω => ∫ t in c..d, G ω (q t)) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  set φ : S → ℝ → E := fun ω t => G ω (q (projIcc c d hcd t)) with hφ
  have hφc : Continuous (Function.uncurry φ) := by
    have h1 : Continuous fun z : S × ℝ => ((z.1 : ℂ), q (projIcc c d hcd z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        ((hq.comp continuous_subtype_val).comp (continuous_projIcc.comp continuous_snd))
    exact hG.comp_continuous h1 fun z => ⟨z.1.2, hqT _ (projIcc c d hcd z.2).2⟩
  refine (continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hφc c d).congr
    fun ω => ?_
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hcd] at ht
  simp [hφ, projIcc_of_mem hcd ht]

/-- Continuity of a contour integral depending on a parameter. -/
theorem rint_param_continuousOn {G : ℂ → ℂ → E} {S : Set ℂ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hG : ContinuousOn (fun z : ℂ × ℂ => G z.1 z.2) (S ×ˢ bdry a b c d)) :
    ContinuousOn (fun ω => rint (G ω) a b c d) S := by
  simp only [rint_eq_sum]
  refine continuousOn_finsetSum _ fun k _ => ContinuousOn.const_smul ?_ _
  exact param_side_continuousOn (sidePath_continuous a b c d k) (sideLo_le hab hcd k)
    (fun t ht => sidePath_mem k ht) hG

theorem rint_congr {f g : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : ∀ ω ∈ bdry a b c d, f ω = g ω) : rint f a b c d = rint g a b c d := by
  unfold rint
  rw [integral_congr (fun x hx => h _ (mem_bdry_bottom (by rwa [uIcc_of_le hab] at hx))),
    integral_congr (fun x hx => h _ (mem_bdry_top (by rwa [uIcc_of_le hab] at hx))),
    integral_congr (fun y hy => h _ (mem_bdry_right (by rwa [uIcc_of_le hcd] at hy))),
    integral_congr (fun y hy => h _ (mem_bdry_left (by rwa [uIcc_of_le hcd] at hy)))]

/-- Fubini theorem for iterated contour integrals over rectangle boundaries. -/
theorem rint_rint_swap {G : ℂ → ℂ → E} {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₁' : c₁ ≤ d₁) (h₂ : a₂ ≤ b₂) (h₂' : c₂ ≤ d₂)
    (hG : ContinuousOn (fun z : ℂ × ℂ => G z.1 z.2) (bdry a₁ b₁ c₁ d₁ ×ˢ bdry a₂ b₂ c₂ d₂)) :
    rint (fun ω => rint (fun η => G ω η) a₂ b₂ c₂ d₂) a₁ b₁ c₁ d₁ =
      rint (fun η => rint (fun ω => G ω η) a₁ b₁ c₁ d₁) a₂ b₂ c₂ d₂ := by
  have key := fun k l => param_integral_swap (g := G) (sidePath_continuous a₁ b₁ c₁ d₁ k)
    (sidePath_continuous a₂ b₂ c₂ d₂ l) (sideLo_le h₁ h₁' k) (sideLo_le h₂ h₂' l)
    (fun s hs => sidePath_mem k hs) (fun t ht => sidePath_mem l ht) hG
  simp only [rint_eq_sum]
  have e1 : ∀ k : Fin 4, ∫ s in sideLo a₁ c₁ k..sideHi b₁ d₁ k, ∑ l : Fin 4, sideW l •
      ∫ t in sideLo a₂ c₂ l..sideHi b₂ d₂ l,
        G (sidePath a₁ b₁ c₁ d₁ k s) (sidePath a₂ b₂ c₂ d₂ l t) =
      ∑ l : Fin 4, sideW l • ∫ t in sideLo a₂ c₂ l..sideHi b₂ d₂ l,
        ∫ s in sideLo a₁ c₁ k..sideHi b₁ d₁ k,
          G (sidePath a₁ b₁ c₁ d₁ k s) (sidePath a₂ b₂ c₂ d₂ l t) := by
    intro k
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_smul, (key k l).2]
    · intro l _; exact ((key k l).1).smul (sideW l)
  have e2 : ∀ l : Fin 4, ∫ t in sideLo a₂ c₂ l..sideHi b₂ d₂ l, ∑ k : Fin 4, sideW k •
      ∫ s in sideLo a₁ c₁ k..sideHi b₁ d₁ k,
        G (sidePath a₁ b₁ c₁ d₁ k s) (sidePath a₂ b₂ c₂ d₂ l t) =
      ∑ k : Fin 4, sideW k • ∫ t in sideLo a₂ c₂ l..sideHi b₂ d₂ l,
        ∫ s in sideLo a₁ c₁ k..sideHi b₁ d₁ k,
          G (sidePath a₁ b₁ c₁ d₁ k s) (sidePath a₂ b₂ c₂ d₂ l t) := by
    intro l
    have hint : ∀ k : Fin 4, IntervalIntegrable (fun t => ∫ s in sideLo a₁ c₁ k..sideHi b₁ d₁ k,
        G (sidePath a₁ b₁ c₁ d₁ k s) (sidePath a₂ b₂ c₂ d₂ l t)) volume
        (sideLo a₂ c₂ l) (sideHi b₂ d₂ l) := by
      intro k
      have hG' : ContinuousOn (fun z : ℂ × ℂ => G z.2 z.1)
          (bdry a₂ b₂ c₂ d₂ ×ˢ bdry a₁ b₁ c₁ d₁) :=
        hG.comp continuous_swap.continuousOn fun z hz => ⟨hz.2, hz.1⟩
      exact (param_integral_swap (g := fun x y => G y x) (sidePath_continuous a₂ b₂ c₂ d₂ l)
        (sidePath_continuous a₁ b₁ c₁ d₁ k) (sideLo_le h₂ h₂' l) (sideLo_le h₁ h₁' k)
        (fun s hs => sidePath_mem l hs) (fun t ht => sidePath_mem k ht) hG').1
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_smul]
    · intro k _; exact (hint k).smul (sideW k)
  simp only [e1, e2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm]

end fubini

end Involution
