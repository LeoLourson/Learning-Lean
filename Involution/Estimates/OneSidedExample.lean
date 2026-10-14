module

public import Involution.Model.CompactInverse
public import Involution.Setup.ACDomain
public import Involution.Model.BracketBounds
public import Involution.Model.SobolevModes
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Пример без базисности: односторонний коэффициент `a = 4` на `(0,1)` и `a = 0` на `(-1,0)`.
Здесь `a(x) a(-x) = 0`, так что оценка произведения выполнена с `κ = 0`, но оператор `L_a`
не имеет ни одного собственного значения. Следовательно, нет ни базиса Рисса из собственных
функций, ни базиса со скобками из конечномерных инвариантных подпространств обратного оператора.
Коэффициент разрывен в нуле: пример лежит в классе `L∞`, но не в `W¹∞`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Involution

/-- Единственность нулевого решения задачи Коши `W' = W₁`, `W₁' = -λ W` на отрезке.
Производные требуются только во внутренних точках. -/
theorem cauchy_zero_unique {l r : ℝ} (lam : ℂ) (W W₁ : ℝ → ℂ)
    (hWc : ContinuousOn W (Icc l r)) (hW₁c : ContinuousOn W₁ (Icc l r))
    (hW : ∀ x ∈ Ioo l r, HasDerivAt W (W₁ x) x)
    (hW₁ : ∀ x ∈ Ioo l r, HasDerivAt W₁ (-lam * W x) x)
    (h0 : W l = 0) (h1 : W₁ l = 0) :
    ∀ x ∈ Icc l r, W x = 0 ∧ W₁ x = 0 := by
  let f : ℝ → ℂ × ℂ := fun x => (W x, W₁ x)
  let f' : ℝ → ℂ × ℂ := fun x => (W₁ x, -lam * W x)
  let K : ℝ := max 1 ‖lam‖
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have hfc : ContinuousOn f (Icc l r) := hWc.prodMk hW₁c
  have hbound : ∀ y, ‖f' y‖ ≤ K * ‖f y‖ := by
    intro y
    change max ‖W₁ y‖ ‖-lam * W y‖ ≤ K * max ‖W y‖ ‖W₁ y‖
    apply max_le
    · calc
        ‖W₁ y‖ = 1 * ‖W₁ y‖ := (one_mul _).symm
        _ ≤ K * max ‖W y‖ ‖W₁ y‖ :=
          mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) hK
    · rw [norm_mul, norm_neg]
      exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _) hK
  have hfl : f l = 0 := by
    change (W l, W₁ l) = 0
    rw [h0, h1]
    rfl
  have hzero : ∀ x ∈ Icc l r, f x = 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with he | hlt
    · rw [← he]
      exact hfl
    by_contra hne
    have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hne
    let E := Real.exp (K * (r - l))
    have hE : 0 < E := Real.exp_pos _
    have hcl : ContinuousWithinAt f (Icc l r) l := hfc l ⟨le_rfl, hx.1.trans hx.2⟩
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.mp hcl (‖f x‖ / E) (div_pos hpos hE)
    let c := l + min δ (x - l) / 2
    have hmin : 0 < min δ (x - l) := lt_min hδ (sub_pos.mpr hlt)
    have hm1 : min δ (x - l) ≤ x - l := min_le_right _ _
    have hm2 : min δ (x - l) ≤ δ := min_le_left _ _
    have hcl' : l < c := by
      change l < l + min δ (x - l) / 2
      linarith
    have hcx : c < x := by
      change l + min δ (x - l) / 2 < x
      linarith
    have hcδ : dist c l < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hcl')]
      change l + min δ (x - l) / 2 - l < δ
      linarith
    have hsmall : ‖f c‖ < ‖f x‖ / E := by
      have h := hδf ⟨hcl'.le, hcx.le.trans hx.2⟩ hcδ
      rwa [hfl, dist_zero_right] at h
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f')
      (δ := ‖f c‖) (K := K) (ε := 0) (a := c) (b := x)
      (hfc.mono (Icc_subset_Icc hcl'.le hx.2))
      (fun y hy => (HasDerivAt.prodMk (hW y ⟨hcl'.trans_le hy.1, hy.2.trans_le hx.2⟩)
        (hW₁ y ⟨hcl'.trans_le hy.1, hy.2.trans_le hx.2⟩)).hasDerivWithinAt)
      le_rfl (fun y _ => by simpa using hbound y) x ⟨hcx.le, le_rfl⟩
    rw [gronwallBound_ε0] at hgr
    have hexp : Real.exp (K * (x - c)) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hK)
    have hlt' : ‖f x‖ < ‖f x‖ :=
      calc
        ‖f x‖ ≤ ‖f c‖ * Real.exp (K * (x - c)) := hgr
        _ ≤ ‖f c‖ * E := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ < ‖f x‖ / E * E := mul_lt_mul_of_pos_right hsmall hE
        _ = ‖f x‖ := div_mul_cancel₀ _ hE.ne'
    exact lt_irrefl _ hlt'
  intro x hx
  have h := hzero x hx
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Абсолютно непрерывная функция дифференцируема всюду на интервале, где её производная
почти всюду совпадает с непрерывной функцией. -/
theorem hasDerivAt_of_ac_of_ae_eq {G h H : ℝ → ℂ} {p q : ℝ}
    (hG : AbsolutelyContinuousOnInterval G (-1) 1)
    (hdG : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt G (h x) x)
    (hsub : Ioo p q ⊆ Icc (-1 : ℝ) 1) (hH : ContinuousOn H (Ioo p q))
    (heq : ∀ᵐ x, x ∈ Ioo p q → h x = H x) :
    ∀ x ∈ Ioo p q, HasDerivAt G (H x) x := by
  intro x₀ hx₀
  have hint : HasDerivAt (fun u => ∫ t in x₀..u, H t) (H x₀) x₀ :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hH.stronglyMeasurableAtFilter isOpen_Ioo x₀ hx₀)
      (hH.continuousAt (isOpen_Ioo.mem_nhds hx₀))
  have hev : G =ᶠ[𝓝 x₀] fun u => G x₀ + ∫ t in x₀..u, H t := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀] with u hu
    have hsubu : uIcc x₀ u ⊆ Ioo p q := by
      intro y hy
      rcases le_total x₀ u with hle | hle
      · rw [uIcc_of_le hle] at hy
        exact ⟨hx₀.1.trans_le hy.1, hy.2.trans_lt hu.2⟩
      · rw [uIcc_of_ge hle] at hy
        exact ⟨hu.1.trans_le hy.1, hy.2.trans_lt hx₀.2⟩
    have hac : AbsolutelyContinuousOnInterval G x₀ u := hG.mono (by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact hsubu.trans hsub)
    have hi : IntervalIntegrable H volume x₀ u := (hH.mono hsubu).intervalIntegrable
    have hd : ∀ᵐ y, y ∈ uIcc x₀ u → HasDerivAt G (H y) y := by
      filter_upwards [hdG, heq] with y hy he hmem
      rw [← he (hsubu hmem)]
      exact hy (hsub (hsubu hmem))
    rw [complex_ac_integral_eq_sub hac hi hd]
    ring
  exact (hint.const_add (G x₀)).congr_of_eventuallyEq hev

/-- Односторонний коэффициент: `4` при `x > 0` и `0` при `x ≤ 0`. -/
def oneSidedCoefficient : ℝ → ℝ := fun x => if 0 < x then 4 else 0

theorem oneSidedCoefficient_memLp : MemLp oneSidedCoefficient ∞ intervalMeasure := by
  apply memLp_top_of_bound
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const).aestronglyMeasurable 4
  refine Filter.Eventually.of_forall fun x => ?_
  change ‖(if 0 < x then (4 : ℝ) else 0)‖ ≤ 4
  split_ifs <;> norm_num

theorem oneSidedCoefficient_of_pos {x : ℝ} (hx : 0 < x) : oneSidedCoefficient x = 4 := by
  simp [oneSidedCoefficient, hx]

theorem oneSidedCoefficient_of_nonpos {x : ℝ} (hx : x ≤ 0) : oneSidedCoefficient x = 0 := by
  simp [oneSidedCoefficient, not_lt.mpr hx]

theorem oneSidedCoefficient_product (x : ℝ) :
    oneSidedCoefficient x * oneSidedCoefficient (-x) = 0 := by
  rcases lt_or_ge 0 x with hx | hx
  · rw [oneSidedCoefficient_of_nonpos (by linarith : -x ≤ 0), mul_zero]
  · rw [oneSidedCoefficient_of_nonpos hx, zero_mul]

def oneSidedClass : IntervalLInfinity :=
  realIntervalCoefficient oneSidedCoefficient oneSidedCoefficient_memLp

/-- Оператор с односторонним коэффициентом не имеет собственных функций ни при каком
комплексном `λ`: уравнение `L_a f = λ f` на слабой области Дирихле влечёт `f = 0`. -/
theorem oneSided_no_eigenfunction (f : IntervalL2) (hf : MemDirichletH2 f) (lam : ℂ)
    (he : variableSobolevOperator oneSidedClass f hf.1 = lam • f) : f = 0 := by
  obtain ⟨g, h, F, G, hF, hG, hFac, hGac, hdF, hdG, hl, hr⟩ := hf.acRealization
  have hder := acRealization_derivatives_eq f g h F G hf hF hG hFac hGac hdF hdG
  have hFd := acRealization_first_derivative f g F G hf hF hG hFac hdF
  have hFc : ContinuousOn F (Icc (-1 : ℝ) 1) := hF.1
  have hGc : ContinuousOn G (Icc (-1 : ℝ) 1) := hG.1
  have hE : ∀ᵐ x ∂intervalMeasure,
      -h x - (oneSidedCoefficient x : ℂ) * h (-x) = lam * F x := by
    have h1 := variableSobolevOperator_ae oneSidedClass f hf.1
    rw [he, hder.2] at h1
    filter_upwards [h1, Lp.coeFn_smul lam f, hF.2,
      realIntervalCoefficient_ae oneSidedCoefficient oneSidedCoefficient_memLp]
      with x hx hs hfx hax
    have hax' : oneSidedClass x = (oneSidedCoefficient x : ℂ) := hax
    rw [← hax', hfx]
    calc
      -h x - oneSidedClass x * h (-x) = (lam • f : IntervalL2) x := hx.symm
      _ = lam * f x := by
        rw [hs]
        rfl
  have hEn : ∀ᵐ x ∂intervalMeasure,
      -h (-x) - (oneSidedCoefficient (-x) : ℂ) * h x = lam * F (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hE] with x hx
    simpa only [neg_neg] using hx
  have hEv : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 →
      -h x - (oneSidedCoefficient x : ℂ) * h (-x) = lam * F x :=
    (ae_restrict_iff' measurableSet_Ioo).mp hE
  have hEnv : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 1 →
      -h (-x) - (oneSidedCoefficient (-x) : ℂ) * h x = lam * F (-x) :=
    (ae_restrict_iff' measurableSet_Ioo).mp hEn
  have hleft : ∀ᵐ x, x ∈ Ioo (-1 : ℝ) 0 → h x = -lam * F x := by
    filter_upwards [hEv] with x hx hmem
    have hx' := hx ⟨hmem.1, hmem.2.trans (by norm_num)⟩
    have ha : oneSidedCoefficient x = 0 := oneSidedCoefficient_of_nonpos hmem.2.le
    rw [ha] at hx'
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hx'
    linear_combination -hx'
  have hright : ∀ᵐ x, x ∈ Ioo (0 : ℝ) 1 → h x = -lam * F x + 4 * lam * F (-x) := by
    filter_upwards [hEv, hEnv] with x hx hxn hmem
    have hm : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hmem.1], hmem.2⟩
    have h1 := hx hm
    have h2 := hxn hm
    have ha : oneSidedCoefficient x = 4 := oneSidedCoefficient_of_pos hmem.1
    have han : oneSidedCoefficient (-x) = 0 :=
      oneSidedCoefficient_of_nonpos (by linarith [hmem.1])
    rw [ha] at h1
    rw [han] at h2
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at h2
    push_cast at h1
    linear_combination -h1 + 4 * h2
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
  have hGl : ∀ x ∈ Ioo (-1 : ℝ) 0, HasDerivAt G (-lam * F x) x :=
    hasDerivAt_of_ac_of_ae_eq hGac hdG oL ((continuousOn_const.mul hFc).mono oL) hleft
  have hGr : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (-lam * F x + 4 * lam * F (-x)) x :=
    hasDerivAt_of_ac_of_ae_eq hGac hdG oR
      (((continuousOn_const.mul hFc).add (continuousOn_const.mul hFneg)).mono oR) hright
  let D : ℝ → ℂ := fun x => F x + 2 * (x : ℂ) * (-G (-x)) - F (-x)
  let D₁ : ℝ → ℂ := fun x => G x + (-G (-x)) - 2 * lam * (x : ℂ) * F (-x)
  have cx : Continuous fun y : ℝ => (y : ℂ) := Complex.continuous_ofReal
  have hDc : ContinuousOn D (Icc (0 : ℝ) 1) :=
    ((hFc.mono sR).add (((continuous_const.mul cx).continuousOn).mul
      (hGneg.mono sR).neg)).sub (hFneg.mono sR)
  have hD₁c : ContinuousOn D₁ (Icc (0 : ℝ) 1) :=
    ((hGc.mono sR).add (hGneg.mono sR).neg).sub
      (((continuous_const.mul cx).continuousOn).mul (hFneg.mono sR))
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt D (D₁ x) x ∧ HasDerivAt D₁ (-lam * D x) x := by
    intro x hx
    have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hnx : -x ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hnx1 : -x ∈ Ioo (-1 : ℝ) 1 := ⟨hnx.1, by linarith [hx.1]⟩
    have dF : HasDerivAt F (G x) x := hFd x hx1
    have dG : HasDerivAt G (-lam * F x + 4 * lam * F (-x)) x := hGr x hx
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
    constructor
    · have key : HasDerivAt (fun y => F y + 2 * (y : ℂ) * (-G (-y)) - F (-y))
          (G x + (2 * 1 * (-G (-x)) + 2 * (x : ℂ) * (-lam * F (-x))) - (-G (-x))) x :=
        (dF.add ((dx.const_mul (2 : ℂ)).mul dV₁)).sub dV
      convert key using 1
      change G x + (-G (-x)) - 2 * lam * (x : ℂ) * F (-x) = _
      ring
    · have key : HasDerivAt (fun y => G y + (-G (-y)) - 2 * lam * (y : ℂ) * F (-y))
          ((-lam * F x + 4 * lam * F (-x)) + (-lam * F (-x)) -
            (2 * lam * 1 * F (-x) + 2 * lam * (x : ℂ) * (-G (-x)))) x :=
        (dG.add dV₁).sub ((dx.const_mul (2 * lam)).mul dV)
      convert key using 1
      change -lam * (F x + 2 * (x : ℂ) * (-G (-x)) - F (-x)) = _
      ring
  have hD0 : D 0 = 0 := by
    change F 0 + 2 * ((0 : ℝ) : ℂ) * (-G (-0)) - F (-0) = 0
    simp
  have hD₁0 : D₁ 0 = 0 := by
    change G 0 + (-G (-0)) - 2 * lam * ((0 : ℝ) : ℂ) * F (-0) = 0
    simp
  have hDz := cauchy_zero_unique lam D D₁ hDc hD₁c (fun x hx => (hderiv x hx).1)
    (fun x hx => (hderiv x hx).2) hD0 hD₁0
  have hG1 : G (-1) = 0 := by
    have h1 := (hDz 1 ⟨zero_le_one, le_rfl⟩).1
    change F 1 + 2 * ((1 : ℝ) : ℂ) * (-G (-1)) - F (-1) = 0 at h1
    rw [hr, hl] at h1
    simpa using h1
  have hLz := cauchy_zero_unique lam F G (hFc.mono sL) (hGc.mono sL)
    (fun x hx => hFd x ⟨hx.1, hx.2.trans (by norm_num)⟩) hGl hl hG1
  have hFz : ∀ x ∈ Icc (-1 : ℝ) 1, F x = 0 := by
    intro x hx
    rcases le_total x 0 with hx0 | hx0
    · exact (hLz x ⟨hx.1, hx0⟩).1
    · have hn : -x ∈ Icc (-1 : ℝ) 0 := ⟨by linarith [hx.2], by linarith⟩
      have hd := (hDz x ⟨hx0, hx.2⟩).1
      change F x + 2 * (x : ℂ) * (-G (-x)) - F (-x) = 0 at hd
      rw [(hLz (-x) hn).1, (hLz (-x) hn).2] at hd
      simpa using hd
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hF.2, ae_restrict_mem measurableSet_Ioo] with x hfx hx
  rw [← hfx]
  exact hFz x (Ioo_subset_Icc_self hx)

theorem oneSidedClass_product :
    ∀ᵐ x ∂intervalMeasure, |oneSidedCoefficient x * oneSidedCoefficient (-x)| ≤ 0 :=
  Filter.Eventually.of_forall fun x => by rw [oneSidedCoefficient_product, abs_zero]

/-- Компактный обратный к `L_a` для одностороннего коэффициента. -/
def oneSidedGreen : IntervalL2 →L[ℂ] IntervalL2 :=
  variableGreen oneSidedClass
    (determinantInverse oneSidedCoefficient oneSidedCoefficient_memLp 0 (by norm_num)
      oneSidedClass_product)

theorem oneSidedGreen_compact : IsCompactOperator oneSidedGreen := variableGreen_compact _ _

theorem oneSidedGreen_injective : Function.Injective oneSidedGreen :=
  variableGreen_injective _ _
    (determinantInverse_identity oneSidedCoefficient oneSidedCoefficient_memLp 0 (by norm_num)
      oneSidedClass_product)

/-- Компактный обратный не имеет собственных векторов: он квазинильпотентен в точечном смысле. -/
theorem oneSidedGreen_no_eigenvector (v : IntervalL2) (mu : ℂ)
    (hv : oneSidedGreen v = mu • v) : v = 0 := by
  by_contra hne
  have hmu : mu ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← map_zero oneSidedGreen] at hv
    exact hne (oneSidedGreen_injective hv)
  have hd := determinantInverse_identity oneSidedCoefficient oneSidedCoefficient_memLp 0
    (by norm_num) oneSidedClass_product
  have hv' : oneSidedGreen v = (mu⁻¹)⁻¹ • v := by rwa [inv_inv]
  obtain ⟨hf, he⟩ := (variableOperator_eigen_iff oneSidedClass _ hd v mu⁻¹
    (inv_ne_zero hmu)).mpr hv'
  exact hne (oneSided_no_eigenfunction v hf mu⁻¹ he)

/-- Нет ненулевых конечномерных подпространств, инвариантных относительно обратного оператора:
корневых подпространств у `L_a` нет. -/
theorem oneSided_invariant_block_eq_bot (V : Submodule ℂ IntervalL2) [FiniteDimensional ℂ V]
    (hinv : ∀ f ∈ V, oneSidedGreen f ∈ V) : V = ⊥ := by
  by_contra hne
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hne
  let T : Module.End ℂ V := oneSidedGreen.toLinearMap.restrict hinv
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hmu.exists_hasEigenvector
  have hTv : T v = mu • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoe : oneSidedGreen (v : IntervalL2) = mu • (v : IntervalL2) :=
    congrArg Subtype.val hTv
  exact hv.2 (Subtype.ext (oneSidedGreen_no_eigenvector (v : IntervalL2) mu hcoe))

theorem intervalL2_bot_closure_ne_top :
    (⊥ : Submodule ℂ IntervalL2).topologicalClosure ≠ ⊤ := by
  intro htop
  have hcl : (⊥ : Submodule ℂ IntervalL2).topologicalClosure = ⊥ :=
    IsClosed.submodule_topologicalClosure_eq (by
      rw [Submodule.bot_coe]
      exact isClosed_singleton)
  rw [hcl] at htop
  have hmem : sineWaveL2 ((1 : ℕ) * Real.pi) ∈ (⊥ : Submodule ℂ IntervalL2) := by
    rw [htop]
    trivial
  exact sineModeL2_ne_zero 1 one_pos ((Submodule.mem_bot ℂ).mp hmem)

/-- Нет базиса Рисса из собственных функций `L_a` для одностороннего коэффициента. -/
theorem oneSided_no_riesz_eigenbasis :
    ¬ ∃ (ι : Type) (b : RieszBasis ι IntervalL2), ∀ i : ι,
      ∃ hf : MemDirichletH2 (b.vector i), ∃ lam : ℂ,
        variableSobolevOperator oneSidedClass (b.vector i) hf.1 = lam • b.vector i := by
  rintro ⟨ι, b, hb⟩
  have hz : ∀ i, b.vector i = 0 := fun i => by
    obtain ⟨hf, lam, he⟩ := hb i
    exact oneSided_no_eigenfunction _ hf lam he
  have hspan : Submodule.span ℂ (Set.range b.vector) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    exact hz i
  have hd := b.dense_span
  rw [hspan] at hd
  exact intervalL2_bot_closure_ne_top hd

/-- Нет и базиса Рисса со скобками, блоки которого инвариантны относительно обратного
оператора (то есть составлены из корневых подпространств). -/
theorem oneSided_no_bracket_basis {J : Type*} (V : J → Submodule ℂ IntervalL2)
    (b : RieszBasisWithBrackets V)
    (hinv : ∀ j, ∀ f ∈ V j, oneSidedGreen f ∈ V j) : False := by
  have hbot : ∀ j, V j = ⊥ := fun j => by
    have := b.finite j
    exact oneSided_invariant_block_eq_bot (V j) (hinv j)
  have hsup : (⨆ j, V j) = ⊥ := by
    rw [iSup_eq_bot]
    exact hbot
  have ht := b.total
  rw [hsup] at ht
  exact intervalL2_bot_closure_ne_top ht

end Involution
