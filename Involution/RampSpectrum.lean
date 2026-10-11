module

public import Involution.OneSidedExample
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Липшицев односторонний коэффициент `a(x) = max(x, 0)`: область без собственных значений.
Коэффициент принадлежит `W¹∞`, и `a(x) a(-x) = 0`. Энергетическая оценка для уравнения
`w'' = -λ w` показывает, что собственные значения не могут лежать вблизи большой положительной
части вещественной оси на расстоянии порядка `√|λ|`. Тригонометрия и асимптотики не нужны. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Involution

/-- Энергия `|w'|² + |λ| |w|²` решения `w'' = -λ w` растёт не быстрее `exp(κ (r - l))`,
если `| |λ| - λ | ≤ κ √|λ|`. -/
theorem cauchy_energy_bound {l r : ℝ} (hlr : l ≤ r) (lam : ℂ) (κ : ℝ) (hκnn : 0 ≤ κ)
    (hκ : ‖((‖lam‖ : ℝ) : ℂ) - lam‖ ≤ κ * Real.sqrt ‖lam‖) (W W₁ : ℝ → ℂ)
    (hWc : ContinuousOn W (Icc l r)) (hW₁c : ContinuousOn W₁ (Icc l r))
    (hW : ∀ x ∈ Ioo l r, HasDerivAt W (W₁ x) x)
    (hW₁ : ∀ x ∈ Ioo l r, HasDerivAt W₁ (-lam * W x) x) :
    ‖W₁ r‖ ^ 2 + ‖lam‖ * ‖W r‖ ^ 2 ≤
      Real.exp (κ * (r - l)) * (‖W₁ l‖ ^ 2 + ‖lam‖ * ‖W l‖ ^ 2) := by
  let e : ℝ → ℝ := fun x => ‖W₁ x‖ ^ 2 + ‖lam‖ * ‖W x‖ ^ 2
  let φ : ℝ → ℝ := fun x => e x * Real.exp (-κ * x)
  let s := Real.sqrt ‖lam‖
  have hs : s ^ 2 = ‖lam‖ := Real.sq_sqrt (norm_nonneg lam)
  have hec : ContinuousOn e (Icc l r) :=
    (hW₁c.norm.pow 2).add (continuousOn_const.mul (hWc.norm.pow 2))
  have hφc : ContinuousOn φ (Icc l r) :=
    hec.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hφd : ∀ x ∈ Ioo l r, HasDerivAt φ
      ((2 * inner ℝ (W₁ x) (-lam * W x) + ‖lam‖ * (2 * inner ℝ (W x) (W₁ x))) *
        Real.exp (-κ * x) + e x * (Real.exp (-κ * x) * (-κ * 1))) x := fun x hx =>
    ((hW₁ x hx).norm_sq.add ((hW x hx).norm_sq.const_mul ‖lam‖)).mul
      (((hasDerivAt_id x).const_mul (-κ)).exp)
  have hdle : ∀ x, 2 * inner ℝ (W₁ x) (-lam * W x) + ‖lam‖ * (2 * inner ℝ (W x) (W₁ x)) ≤
      κ * e x := by
    intro x
    have h1 : 2 * inner ℝ (W₁ x) (-lam * W x) + ‖lam‖ * (2 * inner ℝ (W x) (W₁ x)) =
        2 * inner ℝ (W₁ x) ((((‖lam‖ : ℝ) : ℂ) - lam) * W x) := by
      have h2 : inner ℝ (W₁ x) (((‖lam‖ : ℝ) : ℂ) * W x) = ‖lam‖ * inner ℝ (W x) (W₁ x) := by
        rw [← Complex.real_smul, inner_smul_right, real_inner_comm]
      rw [sub_mul, inner_sub_right, h2, neg_mul, inner_neg_right]
      ring
    rw [h1]
    calc
      2 * inner ℝ (W₁ x) ((((‖lam‖ : ℝ) : ℂ) - lam) * W x) ≤
          2 * (‖W₁ x‖ * ‖(((‖lam‖ : ℝ) : ℂ) - lam) * W x‖) :=
        mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by norm_num)
      _ = 2 * (‖W₁ x‖ * (‖((‖lam‖ : ℝ) : ℂ) - lam‖ * ‖W x‖)) := by rw [norm_mul]
      _ ≤ 2 * (‖W₁ x‖ * (κ * s * ‖W x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hκ (norm_nonneg _)) (norm_nonneg _)) (by norm_num)
      _ = κ * (2 * ‖W₁ x‖ * (s * ‖W x‖)) := by ring
      _ ≤ κ * (‖W₁ x‖ ^ 2 + (s * ‖W x‖) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) hκnn
      _ = κ * e x := by
        change _ = κ * (‖W₁ x‖ ^ 2 + ‖lam‖ * ‖W x‖ ^ 2)
        rw [mul_pow, hs]
  have hanti : AntitoneOn φ (Icc l r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc l r) hφc
    · rw [interior_Icc]
      exact fun x hx => (hφd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hφd x hx).deriv]
      calc
        _ = (2 * inner ℝ (W₁ x) (-lam * W x) + ‖lam‖ * (2 * inner ℝ (W x) (W₁ x)) -
            κ * e x) * Real.exp (-κ * x) := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hdle x)) (Real.exp_pos _).le
  have hφ : φ r ≤ φ l := hanti (left_mem_Icc.mpr hlr) (right_mem_Icc.mpr hlr) hlr
  have her : e r = φ r * Real.exp (κ * r) := by
    change e r = e r * Real.exp (-κ * r) * Real.exp (κ * r)
    rw [mul_assoc, ← Real.exp_add, show -κ * r + κ * r = 0 by ring, Real.exp_zero, mul_one]
  have hel : φ l * Real.exp (κ * r) = Real.exp (κ * (r - l)) * e l := by
    change e l * Real.exp (-κ * l) * Real.exp (κ * r) = Real.exp (κ * (r - l)) * e l
    rw [mul_assoc, ← Real.exp_add, show -κ * l + κ * r = κ * (r - l) by ring, mul_comm]
  change e r ≤ Real.exp (κ * (r - l)) * e l
  rw [her, ← hel]
  exact mul_le_mul_of_nonneg_right hφ (Real.exp_pos _).le

/-- Липшицев односторонний коэффициент `max(x, 0)`. -/
def rampCoefficient : ℝ → ℝ := fun x => max x 0

theorem rampCoefficient_lipschitz : LipschitzWith 1 rampCoefficient :=
  LipschitzWith.id.max_const 0

theorem rampCoefficient_of_nonneg {x : ℝ} (hx : 0 ≤ x) : rampCoefficient x = x :=
  max_eq_left hx

theorem rampCoefficient_of_nonpos {x : ℝ} (hx : x ≤ 0) : rampCoefficient x = 0 :=
  max_eq_right hx

theorem rampCoefficient_product (x : ℝ) : rampCoefficient x * rampCoefficient (-x) = 0 := by
  rcases le_total 0 x with hx | hx
  · rw [rampCoefficient_of_nonpos (by linarith : -x ≤ 0), mul_zero]
  · rw [rampCoefficient_of_nonpos hx, zero_mul]

theorem rampCoefficient_memLp : MemLp rampCoefficient ∞ intervalMeasure := by
  apply memLp_top_of_bound (measurable_id.max measurable_const).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change ‖max x 0‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le hx.2.le zero_le_one

def rampClass : IntervalLInfinity := realIntervalCoefficient rampCoefficient rampCoefficient_memLp

/-- Область без собственных значений: собственное значение `λ` с `|λ| ≥ 1/8` и
`| |λ| - λ | ≤ κ √|λ|` удовлетворяет `|λ| ≤ 32 exp(2κ)`. -/
theorem ramp_eigenvalue_bound (f : IntervalL2) (hf : MemDirichletH2 f) (hne : f ≠ 0) (lam : ℂ)
    (he : variableSobolevOperator rampClass f hf.1 = lam • f) (κ : ℝ) (hκnn : 0 ≤ κ)
    (hκ : ‖((‖lam‖ : ℝ) : ℂ) - lam‖ ≤ κ * Real.sqrt ‖lam‖) (hlam : 1 / 8 ≤ ‖lam‖) :
    ‖lam‖ ≤ 32 * Real.exp (2 * κ) := by
  obtain ⟨g, h, F, G, hF, hG, hFac, hGac, hdF, hdG, hl, hr⟩ := hf.acRealization
  have hder := acRealization_derivatives_eq f g h F G hf hF hG hFac hGac hdF hdG
  have hFd := acRealization_first_derivative f g F G hf hF hG hFac hdF
  have hFc : ContinuousOn F (Icc (-1 : ℝ) 1) := hF.1
  have hGc : ContinuousOn G (Icc (-1 : ℝ) 1) := hG.1
  have hE : ∀ᵐ x ∂intervalMeasure,
      -h x - (rampCoefficient x : ℂ) * h (-x) = lam * F x := by
    have h1 := variableSobolevOperator_ae rampClass f hf.1
    rw [he, hder.2] at h1
    filter_upwards [h1, Lp.coeFn_smul lam f, hF.2,
      realIntervalCoefficient_ae rampCoefficient rampCoefficient_memLp]
      with x hx hs hfx hax
    have hax' : rampClass x = (rampCoefficient x : ℂ) := hax
    rw [← hax', hfx]
    calc
      -h x - rampClass x * h (-x) = (lam • f : IntervalL2) x := hx.symm
      _ = lam * f x := by
        rw [hs]
        rfl
  have hEn : ∀ᵐ x ∂intervalMeasure,
      -h (-x) - (rampCoefficient (-x) : ℂ) * h x = lam * F (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hE] with x hx
    simpa only [neg_neg] using hx
  have hEv : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 →
      -h x - (rampCoefficient x : ℂ) * h (-x) = lam * F x :=
    (ae_restrict_iff' measurableSet_Ioo).mp hE
  have hEnv : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 →
      -h (-x) - (rampCoefficient (-x) : ℂ) * h x = lam * F (-x) :=
    (ae_restrict_iff' measurableSet_Ioo).mp hEn
  have hleft : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 0 → h x = -lam * F x := by
    filter_upwards [hEv] with x hx hmem
    have hx' := hx ⟨hmem.1, hmem.2.trans (by norm_num)⟩
    rw [rampCoefficient_of_nonpos hmem.2.le] at hx'
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hx'
    linear_combination -hx'
  have hright : ∀ᵐ x, x ∈ Ioo (0 : ℝ) 1 → h x = -lam * F x + lam * (x : ℂ) * F (-x) := by
    filter_upwards [hEv, hEnv] with x hx hxn hmem
    have hm : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hmem.1], hmem.2⟩
    have h1 := hx hm
    have h2 := hxn hm
    rw [rampCoefficient_of_nonneg hmem.1.le] at h1
    rw [rampCoefficient_of_nonpos (by linarith [hmem.1] : -x ≤ 0)] at h2
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at h2
    linear_combination -h1 + (x : ℂ) * h2
  have hnegmaps : MapsTo (fun x : ℝ => -x) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hFneg : ContinuousOn (fun x => F (-x)) (Icc (-1 : ℝ) 1) :=
    hFc.comp continuous_neg.continuousOn hnegmaps
  have hGneg : ContinuousOn (fun x => G (-x)) (Icc (-1 : ℝ) 1) :=
    hGc.comp continuous_neg.continuousOn hnegmaps
  have sL : Icc (-1 : ℝ) 0 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc le_rfl (by norm_num)
  have sR : Icc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by norm_num) le_rfl
  have oL : Ioo (-1 : ℝ) 0 ⊆ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self.trans sL
  have oR : Ioo (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self.trans sR
  have cx : Continuous fun y : ℝ => (y : ℂ) := Complex.continuous_ofReal
  have hGl : ∀ x ∈ Ioo (-1 : ℝ) 0, HasDerivAt G (-lam * F x) x :=
    hasDerivAt_of_ac_of_ae_eq hGac hdG oL ((continuousOn_const.mul hFc).mono oL) hleft
  have hGr : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (-lam * F x + lam * (x : ℂ) * F (-x)) x :=
    hasDerivAt_of_ac_of_ae_eq hGac hdG oR
      (((continuousOn_const.mul hFc).add
        (((continuous_const.mul cx).continuousOn).mul hFneg)).mono oR) hright
  let P : ℝ → ℂ := fun x => F x + ((x : ℂ) * (x : ℂ) / 4) * (-G (-x)) - ((x : ℂ) / 4) * F (-x)
  let P₁ : ℝ → ℂ := fun x => G x + ((x : ℂ) / 4) * (-G (-x)) -
    (lam * ((x : ℂ) * (x : ℂ)) / 4) * F (-x) - F (-x) / 4
  have hPc : ContinuousOn P (Icc (0 : ℝ) 1) :=
    ((hFc.mono sR).add (((((cx.mul cx).div_const 4).continuousOn).mul
      (hGneg.mono sR).neg))).sub (((cx.div_const 4).continuousOn).mul (hFneg.mono sR))
  have hP₁c : ContinuousOn P₁ (Icc (0 : ℝ) 1) :=
    ((((hGc.mono sR).add (((cx.div_const 4).continuousOn).mul (hGneg.mono sR).neg))).sub
      ((((continuous_const.mul (cx.mul cx)).div_const 4).continuousOn).mul
        (hFneg.mono sR))).sub ((hFneg.mono sR).div_const 4)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt P (P₁ x) x ∧ HasDerivAt P₁ (-lam * P x) x := by
    intro x hx
    have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hnx : -x ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hnx1 : -x ∈ Ioo (-1 : ℝ) 1 := ⟨hnx.1, by linarith [hx.1]⟩
    have dF : HasDerivAt F (G x) x := hFd x hx1
    have dG : HasDerivAt G (-lam * F x + lam * (x : ℂ) * F (-x)) x := hGr x hx
    have dV : HasDerivAt (fun y => F (-y)) (-G (-x)) x := by
      have hc : HasDerivAt (fun y => F (-y)) ((-1 : ℝ) • G (-x)) x :=
        HasDerivAt.scomp x (hFd (-x) hnx1) (hasDerivAt_neg x)
      simpa using hc
    have dV₁ : HasDerivAt (fun y => -G (-y)) (-lam * F (-x)) x := by
      have hc : HasDerivAt (fun y => G (-y)) ((-1 : ℝ) • (-lam * F (-x))) x :=
        HasDerivAt.scomp x (hGl (-x) hnx) (hasDerivAt_neg x)
      have hn : HasDerivAt (fun y => -G (-y)) (-((-1 : ℝ) • (-lam * F (-x)))) x := hc.neg
      simpa using hn
    have dx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have dxx : HasDerivAt (fun y : ℝ => (y : ℂ) * (y : ℂ)) (1 * (x : ℂ) + (x : ℂ) * 1) x :=
      dx.mul dx
    constructor
    · have key : HasDerivAt
          (fun y => F y + ((y : ℂ) * (y : ℂ) / 4) * (-G (-y)) - ((y : ℂ) / 4) * F (-y))
          (G x + ((1 * (x : ℂ) + (x : ℂ) * 1) / 4 * (-G (-x)) +
            ((x : ℂ) * (x : ℂ) / 4) * (-lam * F (-x))) -
            (1 / 4 * F (-x) + (x : ℂ) / 4 * (-G (-x)))) x :=
        (dF.add ((dxx.div_const 4).mul dV₁)).sub ((dx.div_const 4).mul dV)
      convert key using 1
      change G x + ((x : ℂ) / 4) * (-G (-x)) - (lam * ((x : ℂ) * (x : ℂ)) / 4) * F (-x) -
        F (-x) / 4 = _
      ring
    · have key : HasDerivAt
          (fun y => G y + ((y : ℂ) / 4) * (-G (-y)) -
            (lam * ((y : ℂ) * (y : ℂ)) / 4) * F (-y) - F (-y) / 4)
          ((-lam * F x + lam * (x : ℂ) * F (-x)) +
            (1 / 4 * (-G (-x)) + (x : ℂ) / 4 * (-lam * F (-x))) -
            ((lam * (1 * (x : ℂ) + (x : ℂ) * 1)) / 4 * F (-x) +
              (lam * ((x : ℂ) * (x : ℂ)) / 4) * (-G (-x))) - (-G (-x)) / 4) x :=
        (((dG.add ((dx.div_const 4).mul dV₁)).sub
          (((dxx.const_mul lam).div_const 4).mul dV))).sub (dV.div_const 4)
      convert key using 1
      change -lam * (F x + ((x : ℂ) * (x : ℂ) / 4) * (-G (-x)) - ((x : ℂ) / 4) * F (-x)) = _
      ring
  have hP0 : P 0 = F 0 := by
    change F 0 + (((0 : ℝ) : ℂ) * ((0 : ℝ) : ℂ) / 4) * (-G (-0)) -
      (((0 : ℝ) : ℂ) / 4) * F (-0) = F 0
    simp
  have hP₁0 : P₁ 0 = G 0 - F 0 / 4 := by
    change G 0 + (((0 : ℝ) : ℂ) / 4) * (-G (-0)) -
      (lam * (((0 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) / 4) * F (-0) - F (-0) / 4 = G 0 - F 0 / 4
    simp
  have hP1 : P 1 = -G (-1) / 4 := by
    change F 1 + (((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) / 4) * (-G (-1)) -
      (((1 : ℝ) : ℂ) / 4) * F (-1) = -G (-1) / 4
    rw [hr, hl]
    simp
    ring
  by_cases hG1 : G (-1) = 0
  · exfalso
    apply hne
    have hLz := cauchy_zero_unique lam F G (hFc.mono sL) (hGc.mono sL)
      (fun x hx => hFd x ⟨hx.1, hx.2.trans (by norm_num)⟩) hGl hl hG1
    have hF0 : F 0 = 0 := (hLz 0 ⟨by norm_num, le_rfl⟩).1
    have hG0 : G 0 = 0 := (hLz 0 ⟨by norm_num, le_rfl⟩).2
    have hPz := cauchy_zero_unique lam P P₁ hPc hP₁c (fun x hx => (hderiv x hx).1)
      (fun x hx => (hderiv x hx).2) (by rw [hP0, hF0]) (by rw [hP₁0, hG0, hF0]; simp)
    have hFz : ∀ x ∈ Icc (-1 : ℝ) 1, F x = 0 := by
      intro x hx
      rcases le_total x 0 with hx0 | hx0
      · exact (hLz x ⟨hx.1, hx0⟩).1
      · have hn : -x ∈ Icc (-1 : ℝ) 0 := ⟨by linarith [hx.2], by linarith⟩
        have hd := (hPz x ⟨hx0, hx.2⟩).1
        change F x + ((x : ℂ) * (x : ℂ) / 4) * (-G (-x)) - ((x : ℂ) / 4) * F (-x) = 0 at hd
        rw [(hLz (-x) hn).1, (hLz (-x) hn).2] at hd
        simpa using hd
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hF.2, ae_restrict_mem measurableSet_Ioo] with x hfx hx
    rw [← hfx]
    exact hFz x (Ioo_subset_Icc_self hx)
  · have hgpos : 0 < ‖G (-1)‖ ^ 2 := by positivity
    let E := Real.exp κ
    have hE : 0 < E := Real.exp_pos κ
    have hleftE := cauchy_energy_bound (l := -1) (r := 0) (by norm_num) lam κ hκnn hκ F G
      (hFc.mono sL) (hGc.mono sL)
      (fun x hx => hFd x ⟨hx.1, hx.2.trans (by norm_num)⟩) hGl
    have hrightE := cauchy_energy_bound (l := 0) (r := 1) (by norm_num) lam κ hκnn hκ P P₁
      hPc hP₁c (fun x hx => (hderiv x hx).1) (fun x hx => (hderiv x hx).2)
    rw [hl, norm_zero, show κ * (0 - -1) = κ by ring] at hleftE
    rw [hP0, hP₁0, hP1, show κ * (1 - 0) = κ by ring] at hrightE
    have hnl : 0 ≤ ‖lam‖ := norm_nonneg lam
    have h1 : ‖G 0‖ ^ 2 + ‖lam‖ * ‖F 0‖ ^ 2 ≤ E * ‖G (-1)‖ ^ 2 := by
      simpa using hleftE
    have h2 : ‖G 0 - F 0 / 4‖ ^ 2 ≤ 2 * ‖G 0‖ ^ 2 + ‖F 0‖ ^ 2 / 8 := by
      have hn := norm_sub_le (G 0) (F 0 / 4)
      have hq : ‖F 0 / 4‖ = ‖F 0‖ / 4 := by simp
      rw [hq] at hn
      nlinarith [sq_nonneg (‖G 0‖ - ‖F 0‖ / 4), norm_nonneg (G 0 - F 0 / 4),
        norm_nonneg (G 0), norm_nonneg (F 0)]
    have h3 : ‖G 0 - F 0 / 4‖ ^ 2 + ‖lam‖ * ‖F 0‖ ^ 2 ≤ 2 * (E * ‖G (-1)‖ ^ 2) := by
      nlinarith [sq_nonneg ‖F 0‖, sq_nonneg ‖G 0‖]
    have h4 : ‖lam‖ * ‖-G (-1) / 4‖ ^ 2 ≤ E * (2 * (E * ‖G (-1)‖ ^ 2)) := by
      have hnn : 0 ≤ ‖P₁ 1‖ ^ 2 := sq_nonneg _
      calc
        ‖lam‖ * ‖-G (-1) / 4‖ ^ 2 ≤ ‖P₁ 1‖ ^ 2 + ‖lam‖ * ‖-G (-1) / 4‖ ^ 2 := by linarith
        _ ≤ E * (‖G 0 - F 0 / 4‖ ^ 2 + ‖lam‖ * ‖F 0‖ ^ 2) := hrightE
        _ ≤ E * (2 * (E * ‖G (-1)‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 hE.le
    have hq : ‖-G (-1) / 4‖ ^ 2 = ‖G (-1)‖ ^ 2 / 16 := by
      rw [norm_div, norm_neg]
      simp
      ring
    rw [hq] at h4
    have hEE : Real.exp (2 * κ) = E * E := by
      change Real.exp (2 * κ) = Real.exp κ * Real.exp κ
      rw [← Real.exp_add]
      ring_nf
    rw [hEE]
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    nlinarith [mul_pos hgpos (sub_pos.mpr hcon)]

end Involution
