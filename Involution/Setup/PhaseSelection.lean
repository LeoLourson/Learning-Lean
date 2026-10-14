module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! Выбор нечётной фазы `ψ` (запись C19, утверждение 3). Для вещественной непрерывной на
`[-1, 1]` функции `a` с `|a(x) a(-x)| < 1` существует гладкая нечётная `ψ`, для которой
`|a(x) e^{-ψ(x)} + a(-x) e^{ψ(x)}| ≤ 2 α` на `[-1, 1]` при некотором `α < 1`. -/

@[expose] public noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Involution

/-- Переформулировка условия `|p e^{-t} + q e^{t}| < 2` через `u = e^t`. -/
theorem phase_lt_two_iff (p q t : ℝ) :
    |p * Real.exp (-t) + q * Real.exp t| < 2 ↔ |p + q * Real.exp t ^ 2| < 2 * Real.exp t := by
  have hu := Real.exp_pos t
  have e : p * Real.exp (-t) + q * Real.exp t = (p + q * Real.exp t ^ 2) / Real.exp t := by
    rw [Real.exp_neg]; field_simp
  rw [e, abs_div, abs_of_pos hu, div_lt_iff₀ hu, mul_comm]

/-- Существование `u > 0` с `|p + q u^2| < 2 u` при `|p q| < 1`. -/
theorem exists_phase_u (p q : ℝ) (hpq : |p * q| < 1) :
    ∃ u : ℝ, 0 < u ∧ |p + q * u ^ 2| < 2 * u := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine ⟨|p| + 1, by positivity, ?_⟩
    simp; linarith [abs_nonneg p]
  rcases eq_or_ne p 0 with rfl | hp
  · refine ⟨1 / (|q| + 1), by positivity, ?_⟩
    have h1 : 0 < |q| + 1 := by positivity
    rw [zero_add, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1 / (|q| + 1)) ^ 2)]
    field_simp
    nlinarith [abs_nonneg q]
  rcases le_or_gt (p * q) 0 with h | h
  · have hpq' : 0 < -p / q := by
      rcases lt_or_gt_of_ne hq with hq | hq
      · apply div_pos_of_neg_of_neg _ hq
        rcases lt_or_gt_of_ne hp with hp | hp <;> nlinarith
      · apply div_pos _ hq
        rcases lt_or_gt_of_ne hp with hp | hp <;> nlinarith
    refine ⟨Real.sqrt (-p / q), Real.sqrt_pos.2 hpq', ?_⟩
    rw [Real.sq_sqrt hpq'.le]
    have e : p + q * (-p / q) = 0 := by field_simp; ring
    rw [e, abs_zero]
    have := Real.sqrt_pos.2 hpq'
    linarith
  · have hpq' : 0 < p / q := by
      have : p / q = (p * q) / q ^ 2 := by field_simp
      rw [this]; positivity
    refine ⟨Real.sqrt (p / q), Real.sqrt_pos.2 hpq', ?_⟩
    rw [Real.sq_sqrt hpq'.le]
    have e : p + q * (p / q) = 2 * p := by field_simp; ring
    rw [e, abs_mul, abs_two]
    have : |p| < Real.sqrt (p / q) := by
      rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
      have : p / q = (p * q) / q ^ 2 := by field_simp
      rw [this, lt_div_iff₀ (by positivity)]
      rw [abs_lt] at hpq
      nlinarith
    linarith

/-- Множество `{u > 0 | q u^2 - 2u + p < 0}` порядково связно. -/
theorem quad_neg_ordConnected (p q u1 u u2 : ℝ) (h0 : 0 < u1) (h1 : u1 ≤ u) (h2 : u ≤ u2)
    (k1 : q * u1 ^ 2 - 2 * u1 + p < 0) (k2 : q * u2 ^ 2 - 2 * u2 + p < 0) :
    q * u ^ 2 - 2 * u + p < 0 := by
  rcases le_or_gt 0 q with hq | hq
  · rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact k1
    · have h3 : 0 < u2 - u1 := by linarith
      have : (q * u ^ 2 - 2 * u + p) * (u2 - u1) ≤
          (u2 - u) * (q * u1 ^ 2 - 2 * u1 + p) + (u - u1) * (q * u2 ^ 2 - 2 * u2 + p) := by
        nlinarith [mul_nonneg (mul_nonneg hq (sub_nonneg.2 h1)) (sub_nonneg.2 h2)]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (le_of_lt (neg_pos.2 k1)),
        mul_nonneg (sub_nonneg.2 h1) (le_of_lt (neg_pos.2 k2))]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (by nlinarith : (0:ℝ) ≤ 2 - q * (u1 + u))]

/-- При фиксированной паре `p q` с `|p q| < 1` найдётся `t` с `|p e^{-t} + q e^{t}| < 2`. -/
theorem exists_phase_value (p q : ℝ) (hpq : |p * q| < 1) :
    ∃ t : ℝ, |p * Real.exp (-t) + q * Real.exp t| < 2 := by
  obtain ⟨u, hu, h⟩ := exists_phase_u p q hpq
  refine ⟨Real.log u, ?_⟩
  rw [phase_lt_two_iff, Real.exp_log hu]
  exact h

/-- Множество допустимых значений фазы выпукло. -/
theorem convex_phase_values (p q : ℝ) :
    Convex ℝ {t : ℝ | |p * Real.exp (-t) + q * Real.exp t| < 2} := by
  apply Set.OrdConnected.convex
  refine ⟨fun t1 ht1 t2 ht2 s hs => ?_⟩
  have h1 := (phase_lt_two_iff p q t1).1 ht1
  have h2 := (phase_lt_two_iff p q t2).1 ht2
  rw [mem_ofPred_eq, phase_lt_two_iff]
  rw [abs_lt] at h1 h2 ⊢
  have e1 := Real.exp_le_exp.2 hs.1
  have e2 := Real.exp_le_exp.2 hs.2
  have h0 := Real.exp_pos t1
  constructor
  · have := quad_neg_ordConnected (-p) (-q) _ _ _ h0 e1 e2 (by linarith) (by linarith)
    linarith
  · have := quad_neg_ordConnected p q _ _ _ h0 e1 e2 (by linarith) (by linarith)
    linarith

/-- **Выбор фазы.** Гладкая нечётная `ψ`, равная нулю около нуля, уменьшает чётную часть
калиброванного коэффициента `a e^{-ψ}` до `α < 1`. -/
theorem exists_odd_phase (a : ℝ → ℝ) (ha : ContinuousOn a (Icc (-1 : ℝ) 1))
    (hprod : ∀ x ∈ Icc (-1 : ℝ) 1, |a x * a (-x)| < 1) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ x, ψ (-x) = -ψ x) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| < δ → ψ x = 0) ∧
      ∃ α : ℝ, α < 1 ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
        |a x * Real.exp (-ψ x) + a (-x) * Real.exp (ψ x)| ≤ 2 * α := by
  set F : ℝ → ℝ → ℝ := fun x s => a x * Real.exp (-s) + a (-x) * Real.exp s with hF
  have hneg : ContinuousOn (fun x => a (-x)) (Icc (-1 : ℝ) 1) :=
    ha.comp continuousOn_neg (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hFc : ∀ c : ℝ, ContinuousOn (fun x => F x c) (Icc (-1 : ℝ) 1) := fun c =>
    (ha.mul continuousOn_const).add (hneg.mul continuousOn_const)
  have hmem0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- a neighbourhood of `0` where the trivial phase works
  have h00 : |F 0 0| < 2 := by
    have h := hprod 0 hmem0
    simp only [neg_zero] at h
    have : |a 0| < 1 := by
      rw [abs_mul] at h
      nlinarith [abs_nonneg (a 0)]
    simp only [hF, neg_zero, Real.exp_zero, mul_one]
    calc |a 0 + a 0| ≤ |a 0| + |a 0| := abs_add_le _ _
      _ < 2 := by linarith
  have hev : ∀ᶠ x in 𝓝[Icc (-1 : ℝ) 1] 0, |F x 0| < 2 :=
    ((continuous_abs.continuousAt.comp_continuousWithinAt (hFc 0 0 hmem0))).eventually_lt
      continuousWithinAt_const h00
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hsmall : ∀ y, 0 ≤ y → y < ε → y ≤ 1 → |F y 0| < 2 := fun y h1 h2 h3 =>
    hεs ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg h1]; exact h2,
      ⟨by linarith, h3⟩⟩
  set δ := ε / 2 with hδ
  have hδpos : 0 < δ := by positivity
  -- the family of convex constraint sets
  set T : ℝ → Set ℝ := fun x =>
    if x ≤ δ then {0} else if x ≤ 1 then {s | |F x s| < 2} else univ with hT
  have hTconv : ∀ x, Convex ℝ (T x) := by
    intro x
    simp only [hT]
    split_ifs
    · exact convex_singleton 0
    · exact convex_phase_values _ _
    · exact convex_univ
  have hloc : ∀ x : ℝ, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ T y := by
    intro x
    rcases le_or_gt x δ with hx | hx
    · refine ⟨0, ?_⟩
      filter_upwards [Iio_mem_nhds (show x < ε by linarith)] with y hy
      simp only [hT]
      split_ifs with h1 h2
      · rfl
      · exact hsmall y (by linarith) hy h2
      · trivial
    rcases le_or_gt x 1 with hx1 | hx1
    · have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
      obtain ⟨c, hc⟩ := exists_phase_value (a x) (a (-x)) (hprod x hxI)
      have hev2 : ∀ᶠ y in 𝓝[Icc (-1 : ℝ) 1] x, |F y c| < 2 :=
        ((continuous_abs.continuousAt.comp_continuousWithinAt (hFc c x hxI))).eventually_lt
          continuousWithinAt_const hc
      rw [eventually_nhdsWithin_iff] at hev2
      refine ⟨c, ?_⟩
      filter_upwards [hev2, Ioi_mem_nhds hx] with y hy hyδ
      simp only [hT, mem_Ioi] at hyδ ⊢
      rw [ite_eq_right (not_le.2 hyδ)]
      split_ifs with h2
      · exact hy ⟨by linarith, h2⟩
      · trivial
    · refine ⟨0, ?_⟩
      filter_upwards [Ioi_mem_nhds hx1, Ioi_mem_nhds hx] with y hy hy'
      simp only [hT, mem_Ioi] at hy hy' ⊢
      split_ifs <;> first | trivial | (exfalso; linarith)
  obtain ⟨g, hg⟩ :=
    exists_contMDiffMap_forall_mem_convex_of_local_const (n := (⊤ : ℕ∞)) 𝓘(ℝ, ℝ) hTconv hloc
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := contMDiff_iff_contDiff.mp g.contMDiff
  have hg0 : ∀ x, x ≤ δ → g x = 0 := by
    intro x hx
    have := hg x
    simp only [hT, ite_eq_left hx] at this
    exact this
  set ψ : ℝ → ℝ := fun x => g x - g (-x) with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := hgs.sub (hgs.comp contDiff_neg)
  have hψodd : ∀ x, ψ (-x) = -ψ x := by intro x; simp [hψ]
  -- pointwise bound on `[0, 1]`
  have hpos : ∀ x, 0 ≤ x → x ≤ 1 → |F x (ψ x)| < 2 := by
    intro x h0 h1
    have : ψ x = g x := by simp [hψ, hg0 (-x) (by linarith)]
    rw [this]
    rcases le_or_gt x δ with hx | hx
    · rw [hg0 x hx]
      exact hsmall x h0 (by linarith) h1
    · have := hg x
      simp only [hT, ite_eq_right (not_le.2 hx), ite_eq_left h1] at this
      exact this
  have hall : ∀ x ∈ Icc (-1 : ℝ) 1, |F x (ψ x)| < 2 := by
    intro x hx
    rcases le_or_gt 0 x with h0 | h0
    · exact hpos x h0 hx.2
    · have h := hpos (-x) (by linarith) (by linarith [hx.1])
      have e : F x (ψ x) = F (-x) (ψ (-x)) := by
        simp only [hF, hψodd, neg_neg]
        ring
      rw [e]; exact h
  -- compactness
  have hcont : ContinuousOn (fun x => |F x (ψ x)|) (Icc (-1 : ℝ) 1) := by
    have hψc : Continuous ψ := hψs.continuous
    exact (ha.mul (Real.continuous_exp.comp hψc.neg).continuousOn).add
      (hneg.mul (Real.continuous_exp.comp hψc).continuousOn) |>.abs
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, hmem0⟩ hcont
  refine ⟨ψ, hψs, hψodd, ⟨δ, hδpos, fun x hx => ?_⟩, |F x0 (ψ x0)| / 2, ?_, fun x hx => ?_⟩
  · rw [abs_lt] at hx
    simp [hψ, hg0 x (by linarith), hg0 (-x) (by linarith)]
  · linarith [hall x0 hx0]
  · have := hmax hx
    simp only [mem_ofPred_eq] at this
    change |F x (ψ x)| ≤ _
    linarith

end Involution
