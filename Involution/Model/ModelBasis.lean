module

public import Involution.Model.SobolevModes
public import Involution.Model.RieszBasis
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Ортонормированность и полнота модельной системы
`cos((n + 1/2)πx)`, `sin((n + 1)πx)` в `L²(-1, 1)` с ненормированной мерой Лебега.
Доказательство получено от Aristotle (проект 94d172f6-5648-4b7e-859a-b69130301e10). -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

def constantModelVector : ℕ ⊕ ℕ → IntervalL2 :=
  Sum.elim
    (fun n => cosineWaveL2 (((n : ℝ) + 1 / 2) * Real.pi))
    (fun n => sineWaveL2 (((n : ℝ) + 1) * Real.pi))

/-! ### Вычисление скалярных произведений -/

theorem integral_intervalMeasure_eq (f : ℝ → ℂ) :
    ∫ x, f x ∂intervalMeasure = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  rfl

theorem inner_of_real_reps (U V : IntervalL2) (u v : ℝ → ℝ)
    (hU : U =ᵐ[intervalMeasure] fun x => (u x : ℂ))
    (hV : V =ᵐ[intervalMeasure] fun x => (v x : ℂ)) :
    inner ℂ U V = ((∫ x in (-1 : ℝ)..1, u x * v x : ℝ) : ℂ) := by
  rw [L2.inner_def, ← intervalIntegral.integral_ofReal, ← integral_intervalMeasure_eq]
  refine integral_congr_ae ?_
  filter_upwards [hU, hV] with x hx hy
  rw [hx, hy]
  simp [RCLike.inner_apply, mul_comm]

theorem integral_cos_int_mul_pi (m : ℤ) :
    ∫ x in (-1 : ℝ)..1, Real.cos ((m : ℝ) * Real.pi * x) = if m = 0 then 2 else 0 := by
  split_ifs with hm
  · subst hm; norm_num
  · have hc : (m : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Real.pi_ne_zero
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have h1 : Real.sin ((m : ℝ) * Real.pi * 1) = 0 := by
      rw [mul_one]; exact Real.sin_int_mul_pi m
    have h2 : Real.sin ((m : ℝ) * Real.pi * (-1)) = 0 := by
      rw [mul_neg_one, Real.sin_neg, Real.sin_int_mul_pi, neg_zero]
    rw [h1, h2]; simp

theorem integral_sin_mul_symm (c : ℝ) :
    ∫ x in (-1 : ℝ)..1, Real.sin (c * x) = 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin]
    simp [mul_neg, Real.cos_neg]

theorem inner_cos_cos (n m : ℕ) :
    inner ℂ (cosineWaveL2 (((n : ℝ) + 1 / 2) * Real.pi))
      (cosineWaveL2 (((m : ℝ) + 1 / 2) * Real.pi)) = if n = m then 1 else 0 := by
  rw [inner_of_real_reps _ _ _ _ (cosineWaveL2_ae _) (cosineWaveL2_ae _)]
  have h : (fun x : ℝ => Real.cos (((n : ℝ) + 1 / 2) * Real.pi * x) *
      Real.cos (((m : ℝ) + 1 / 2) * Real.pi * x)) = fun x =>
      (Real.cos (((n - m : ℤ) : ℝ) * Real.pi * x) +
        Real.cos (((n + m + 1 : ℤ) : ℝ) * Real.pi * x)) / 2 := by
    funext x
    have e1 : ((n - m : ℤ) : ℝ) * Real.pi * x =
        ((n : ℝ) + 1 / 2) * Real.pi * x - ((m : ℝ) + 1 / 2) * Real.pi * x := by
      push_cast; ring
    have e2 : ((n + m + 1 : ℤ) : ℝ) * Real.pi * x =
        ((n : ℝ) + 1 / 2) * Real.pi * x + ((m : ℝ) + 1 / 2) * Real.pi * x := by
      push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  rw [h, intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul_pi, integral_cos_int_mul_pi]
  have hnm : (n + m + 1 : ℤ) ≠ 0 := by omega
  by_cases h : n = m
  · subst h; simp [hnm]
  · have : (n - m : ℤ) ≠ 0 := by omega
    simp [this, h, hnm]

theorem inner_sin_sin (n m : ℕ) :
    inner ℂ (sineWaveL2 (((n : ℝ) + 1) * Real.pi))
      (sineWaveL2 (((m : ℝ) + 1) * Real.pi)) = if n = m then 1 else 0 := by
  rw [inner_of_real_reps _ _ _ _ (sineWaveL2_ae _) (sineWaveL2_ae _)]
  have h : (fun x : ℝ => Real.sin (((n : ℝ) + 1) * Real.pi * x) *
      Real.sin (((m : ℝ) + 1) * Real.pi * x)) = fun x =>
      (Real.cos (((n - m : ℤ) : ℝ) * Real.pi * x) -
        Real.cos (((n + m + 2 : ℤ) : ℝ) * Real.pi * x)) / 2 := by
    funext x
    have e1 : ((n - m : ℤ) : ℝ) * Real.pi * x =
        ((n : ℝ) + 1) * Real.pi * x - ((m : ℝ) + 1) * Real.pi * x := by
      push_cast; ring
    have e2 : ((n + m + 2 : ℤ) : ℝ) * Real.pi * x =
        ((n : ℝ) + 1) * Real.pi * x + ((m : ℝ) + 1) * Real.pi * x := by
      push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  rw [h, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul_pi, integral_cos_int_mul_pi]
  have hnm : (n + m + 2 : ℤ) ≠ 0 := by omega
  by_cases h : n = m
  · subst h; simp [hnm]
  · have : (n - m : ℤ) ≠ 0 := by omega
    simp [this, h, hnm]

theorem integral_cos_mul_sin (a b : ℝ) :
    ∫ x in (-1 : ℝ)..1, Real.cos (a * x) * Real.sin (b * x) = 0 := by
  have h : (fun x : ℝ => Real.cos (a * x) * Real.sin (b * x)) = fun x =>
      (Real.sin ((b + a) * x) + Real.sin ((b - a) * x)) / 2 := by
    funext x
    rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]; ring
  rw [h, intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sin_mul_symm, integral_sin_mul_symm]
  simp

theorem inner_cos_sin (a b : ℝ) : inner ℂ (cosineWaveL2 a) (sineWaveL2 b) = 0 := by
  rw [inner_of_real_reps _ _ _ _ (cosineWaveL2_ae _) (sineWaveL2_ae _), integral_cos_mul_sin]
  simp

theorem inner_sin_cos (a b : ℝ) : inner ℂ (sineWaveL2 a) (cosineWaveL2 b) = 0 := by
  rw [inner_of_real_reps _ _ _ _ (sineWaveL2_ae _) (cosineWaveL2_ae _)]
  simp_rw [mul_comm (Real.sin _)]
  rw [integral_cos_mul_sin]
  simp

theorem constantModel_orthonormal : Orthonormal ℂ constantModelVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro (n | n) (m | m)
  · simpa [constantModelVector] using inner_cos_cos n m
  · simp [constantModelVector, inner_cos_sin]
  · simp [constantModelVector, inner_sin_cos]
  · simpa [constantModelVector] using inner_sin_sin n m

/-! ### Полнота: нечётное отражение относительно `x = 1` и ряд Фурье периода 4 -/

/-- Скалярные представители модельных векторов. -/
def constantModelFun : ℕ ⊕ ℕ → ℝ → ℂ :=
  Sum.elim
    (fun n => cosineWave (((n : ℝ) + 1 / 2) * Real.pi))
    (fun n => sineWave (((n : ℝ) + 1) * Real.pi))

theorem constantModelVector_ae (i : ℕ ⊕ ℕ) :
    constantModelVector i =ᵐ[intervalMeasure] constantModelFun i := by
  cases i with
  | inl n => exact cosineWaveL2_ae _
  | inr n => exact sineWaveL2_ae _

theorem continuous_constantModelFun (i : ℕ ⊕ ℕ) : Continuous (constantModelFun i) := by
  cases i with
  | inl n => exact (contDiff_cosineWave _).continuous
  | inr n => exact (contDiff_sineWave _).continuous

theorem conj_constantModelFun (i : ℕ ⊕ ℕ) (x : ℝ) :
    (starRingEnd ℂ) (constantModelFun i x) = constantModelFun i x := by
  cases i <;> simp only [constantModelFun, Sum.elim_inl, Sum.elim_inr, cosineWave, sineWave,
    Complex.conj_ofReal]

/-- Разность значений экспоненты периода 4 в точках `x` и `2 - x`. -/
def fourierDiff (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x / 4) -
    Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * ((2 - x : ℝ) : ℂ) / 4)

theorem fourierDiff_even (j : ℤ) (x : ℝ) :
    fourierDiff (2 * j) x =
      -2 * Complex.I * ((Real.sin ((j : ℝ) * Real.pi * x) : ℝ) : ℂ) := by
  open Complex in
  have h2 : 2 * Real.pi * I * ((-(2 * j) : ℤ) : ℂ) * ((2 - x : ℝ) : ℂ) / 4 =
      ((-j : ℤ) : ℂ) * (2 * Real.pi * I) + ((j : ℝ) * Real.pi * x : ℝ) * I := by
    push_cast; ring
  open Complex in
  have h1 : 2 * Real.pi * I * ((-(2 * j) : ℤ) : ℂ) * (x : ℂ) / 4 =
      -(((j : ℝ) * Real.pi * x : ℝ) * I) := by
    push_cast; ring
  rw [fourierDiff, h1, h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
    Complex.ofReal_sin, Complex.sin]
  ring_nf
  rw [Complex.I_sq]; ring

theorem fourierDiff_odd (j : ℤ) (x : ℝ) :
    fourierDiff (2 * j + 1) x =
      2 * ((Real.cos (((j : ℝ) + 1 / 2) * Real.pi * x) : ℝ) : ℂ) := by
  open Complex in
  have h2 : 2 * Real.pi * I * ((-(2 * j + 1) : ℤ) : ℂ) * ((2 - x : ℝ) : ℂ) / 4 =
      ((-j - 1 : ℤ) : ℂ) * (2 * Real.pi * I) + (Real.pi * I +
        (((j : ℝ) + 1 / 2) * Real.pi * x : ℝ) * I) := by
    push_cast; ring
  open Complex in
  have h1 : 2 * Real.pi * I * ((-(2 * j + 1) : ℤ) : ℂ) * (x : ℂ) / 4 =
      -((((j : ℝ) + 1 / 2) * Real.pi * x : ℝ) * I) := by
    push_cast; ring
  rw [fourierDiff, h1, h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
    Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_cos, Complex.cos]
  simp only [neg_mul]
  ring

/-- Каждая разность `fourierDiff k` либо тождественно равна нулю, либо пропорциональна
одной из модельных функций. -/
theorem fourierDiff_mode (k : ℤ) :
    (∀ x, fourierDiff k x = 0) ∨
      ∃ (i : ℕ ⊕ ℕ) (c : ℂ), ∀ x, fourierDiff k x = c * constantModelFun i x := by
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · rcases lt_trichotomy j 0 with hj | rfl | hj
    · refine Or.inr ⟨Sum.inr ((-j).toNat - 1), 2 * Complex.I, fun x => ?_⟩
      have hc : ((((-j).toNat - 1 : ℕ) : ℝ) + 1) = -(j : ℝ) := by
        have : (((-j).toNat - 1 : ℕ) : ℤ) + 1 = -j := by omega
        exact_mod_cast this
      rw [fourierDiff_even, constantModelFun, Sum.elim_inr, sineWave, hc]
      have : (j : ℝ) * Real.pi * x = -(-(j : ℝ) * Real.pi * x) := by ring
      rw [this, Real.sin_neg]
      push_cast; ring
    · left; intro x
      simpa using fourierDiff_even 0 x
    · refine Or.inr ⟨Sum.inr (j.toNat - 1), -2 * Complex.I, fun x => ?_⟩
      have hc : (((j.toNat - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by
        have : ((j.toNat - 1 : ℕ) : ℤ) + 1 = j := by omega
        exact_mod_cast this
      rw [fourierDiff_even, constantModelFun, Sum.elim_inr, sineWave, hc]
  · rcases lt_or_ge j 0 with hj | hj
    · refine Or.inr ⟨Sum.inl ((-j - 1).toNat), 2, fun x => ?_⟩
      have hc : (((-j - 1).toNat : ℕ) : ℝ) = -(j : ℝ) - 1 := by
        have : (((-j - 1).toNat : ℕ) : ℤ) = -j - 1 := by omega
        exact_mod_cast this
      rw [fourierDiff_odd, constantModelFun, Sum.elim_inl, cosineWave, hc]
      have : ((j : ℝ) + 1 / 2) * Real.pi * x = -((-(j : ℝ) - 1 + 1 / 2) * Real.pi * x) := by
        ring
      rw [this, Real.cos_neg]
    · refine Or.inr ⟨Sum.inl j.toNat, 2, fun x => ?_⟩
      have hc : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
        have : ((j.toNat : ℕ) : ℤ) = j := by omega
        exact_mod_cast this
      rw [fourierDiff_odd, constantModelFun, Sum.elim_inl, cosineWave, hc]

theorem continuous_fourierDiff (k : ℤ) : Continuous (fourierDiff k) := by
  unfold fourierDiff; fun_prop

theorem integrable_continuous_mul (u : ℝ → ℂ) (hu : Continuous u) (f : IntervalL2) :
    Integrable (fun x => u x * f x) intervalMeasure :=
  (continuous_memLp_interval u hu).integrable_mul (Lp.memLp f)

theorem integral_fourierDiff_mul_eq_zero (f : IntervalL2)
    (hf : ∀ i, inner ℂ (constantModelVector i) f = 0) (k : ℤ) :
    ∫ x, fourierDiff k x * f x ∂intervalMeasure = 0 := by
  rcases fourierDiff_mode k with h | ⟨i, c, h⟩
  · simp [h]
  · have hi := hf i
    rw [L2.inner_def] at hi
    have hi' : ∫ x, constantModelFun i x * f x ∂intervalMeasure = 0 := by
      rw [← hi]
      refine integral_congr_ae ?_
      filter_upwards [constantModelVector_ae i] with x hx
      rw [hx]
      simp [RCLike.inner_apply, conj_constantModelFun, mul_comm]
    simp_rw [h, mul_assoc]
    rw [integral_const_mul, hi', mul_zero]

/-- Нечётное отражение относительно `x = 1` функции, заданной на `(-1, 1)`. -/
def oddReflectExt (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  Set.indicator (Set.Ioo (-1) 1) F x - Set.indicator (Set.Ioo 1 3) (fun y => F (2 - y)) x

theorem reflectTwo_measurePreserving :
    MeasurePreserving (fun x : ℝ => 2 - x) (volume.restrict (Set.Ioo 1 3)) intervalMeasure := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℝ) 2).restrict_preimage
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (-1 : ℝ) 1))
  have hpre : (fun x : ℝ => 2 - x) ⁻¹' Set.Ioo (-1) 1 = Set.Ioo 1 3 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simpa only [hpre, intervalMeasure] using h

theorem memLp_oddReflectExt (f : IntervalL2) :
    MemLp (oddReflectExt f) 2 (volume.restrict (Set.Ioc (-1) 3)) := by
  refine MemLp.sub ?_ ?_
  · rw [memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet,
      Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr
        (Set.Ioo_subset_Ioc_self.trans (Set.Ioc_subset_Ioc_right (by norm_num)))]
    exact Lp.memLp f
  · rw [memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet,
      Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr
        (Set.Ioo_subset_Ioc_self.trans (Set.Ioc_subset_Ioc_left (by norm_num)))]
    exact (Lp.memLp f).comp_measurePreserving reflectTwo_measurePreserving

theorem fourierCoeffOn_oddReflectExt (f : IntervalL2) (k : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 3) (oddReflectExt f) k =
      (1 / 4 : ℂ) * ∫ x, fourierDiff k x * f x ∂intervalMeasure := by
  set E : ℝ → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x / 4)
    with hEdef
  have hE : ∀ x : ℝ, fourier (-k) (x : AddCircle (3 - (-1) : ℝ)) = E x := by
    intro x; rw [fourier_coe_apply, hEdef]; norm_num
  have hEc : Continuous E := by rw [hEdef]; fun_prop
  rw [fourierCoeffOn_eq_integral]
  simp_rw [hE, smul_eq_mul]
  have hint : IntervalIntegrable (fun x => E x * oddReflectExt f x) volume (-1) 3 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    have hEm : MemLp E 2 (volume.restrict (Set.Ioc (-1) 3)) := by
      apply (memLp_two_iff_integrable_sq_norm hEc.aestronglyMeasurable).mpr
      have hc : Continuous (fun x => ‖E x‖ ^ 2) := hEc.norm.pow 2
      exact hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    exact hEm.integrable_mul (memLp_oddReflectExt f)
  have hsub1 : Set.uIcc (-1 : ℝ) 1 ⊆ Set.uIcc (-1) 3 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hsub2 : Set.uIcc (1 : ℝ) 3 ⊆ Set.uIcc (-1) 3 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hint.mono_set hsub1)
    (hint.mono_set hsub2)]
  have h1 : ∫ x in (-1 : ℝ)..1, E x * oddReflectExt f x =
      ∫ x, E x * f x ∂intervalMeasure := by
    rw [integral_intervalMeasure_eq]
    refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
    have hx' : x ∉ Set.Ioo (1 : ℝ) 3 := fun h => by linarith [hx.2, h.1]
    simp [oddReflectExt, Set.indicator_of_mem hx, Set.indicator_of_notMem hx']
  have h2 : ∫ x in (1 : ℝ)..3, E x * oddReflectExt f x =
      -∫ x, E (2 - x) * f x ∂intervalMeasure := by
    rw [integral_intervalMeasure_eq]
    have : ∫ x in (1 : ℝ)..3, E x * oddReflectExt f x =
        ∫ x in (1 : ℝ)..3, -((fun y => E (2 - y) * f y) (2 - x)) := by
      refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
      have hx' : x ∉ Set.Ioo (-1 : ℝ) 1 := fun h => by linarith [hx.1, h.2]
      simp [oddReflectExt, Set.indicator_of_mem hx, Set.indicator_of_notMem hx']
    rw [this, intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_sub_left (f := fun y => E (2 - y) * f y) 2]
    norm_num
  rw [h1, h2, ← sub_eq_add_neg, ← integral_sub (integrable_continuous_mul E hEc f)
    (integrable_continuous_mul (fun x => E (2 - x)) (by fun_prop) f)]
  have hD : ∀ x, fourierDiff k x * f x = E x * f x - E (2 - x) * f x := by
    intro x; rw [← sub_mul]; rfl
  simp_rw [hD]
  rw [Complex.real_smul]
  norm_num

theorem eq_zero_of_orthogonal_constantModel (f : IntervalL2)
    (hf : ∀ i, inner ℂ (constantModelVector i) f = 0) : f = 0 := by
  have hab : (-1 : ℝ) < 3 := by norm_num
  have hL2 := memLp_oddReflectExt f
  have hsum := tsum_sq_fourierCoeffOn hab hL2
  have hcoeff : ∀ k : ℤ, fourierCoeffOn hab (oddReflectExt f) k = 0 := by
    intro k
    rw [fourierCoeffOn_oddReflectExt, integral_fourierDiff_mul_eq_zero f hf, mul_zero]
  simp only [hcoeff, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    tsum_zero] at hsum
  have hint0 : ∫ x in (-1 : ℝ)..3, ‖oddReflectExt f x‖ ^ 2 = 0 := by
    have h4 : (3 - (-1) : ℝ)⁻¹ ≠ 0 := by norm_num
    exact (smul_eq_zero.mp hsum.symm).resolve_left h4
  rw [intervalIntegral.integral_of_le hab.le] at hint0
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity)
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2)).mp hint0
  have hae' : ∀ᵐ x ∂intervalMeasure, ‖oddReflectExt f x‖ ^ 2 = 0 :=
    ae_restrict_of_ae_restrict_of_subset
      (Set.Ioo_subset_Ioc_self.trans (Set.Ioc_subset_Ioc_right (by norm_num))) hae
  apply Lp.ext
  filter_upwards [hae', Lp.coeFn_zero ℂ 2 intervalMeasure,
    ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Set.Ioo (-1 : ℝ) 1))]
    with x hx hz hmem
  rw [hz]
  have hx' : x ∉ Set.Ioo (1 : ℝ) 3 := fun h => by linarith [hmem.2, h.1]
  simpa [oddReflectExt, Set.indicator_of_mem hmem, Set.indicator_of_notMem hx'] using hx

theorem constantModel_dense_span :
    (Submodule.span ℂ (Set.range constantModelVector)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  exact eq_zero_of_orthogonal_constantModel f fun i =>
    hf _ (Submodule.subset_span (Set.mem_range_self i))

/-! ### Гильбертов базис и базис Рисса -/

def constantModelHilbertBasis : HilbertBasis (ℕ ⊕ ℕ) ℂ IntervalL2 :=
  HilbertBasis.mk constantModel_orthonormal constantModel_dense_span.ge

theorem constantModelHilbertBasis_coe :
    ⇑constantModelHilbertBasis = constantModelVector :=
  HilbertBasis.coe_mk _ _

def constantModelRieszBasis : RieszBasis (ℕ ⊕ ℕ) IntervalL2 :=
  rieszBasisOfHilbertBasis constantModelHilbertBasis (ContinuousLinearEquiv.refl ℂ IntervalL2)

theorem constantModelRieszBasis_vector (i : ℕ ⊕ ℕ) :
    constantModelRieszBasis.vector i = constantModelVector i := by
  rw [constantModelRieszBasis, rieszBasisOfHilbertBasis_vector, constantModelHilbertBasis_coe]
  rfl

end Involution

