module

public import Involution.Setup.WeakDerivative
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! H²(-1,1; ℂ) задано через две слабые производные в L².
Все три компоненты являются классами п.в. равенства; выбор представителей
не влияет на слабое дифференцирование. Граничные следы — в `Involution.Setup.IntervalTrace`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Involution

def HasL2WeakDeriv (f g : IntervalL2) : Prop := HasIntervalWeakDeriv f g

namespace HasL2WeakDeriv

theorem unique {f g h : IntervalL2} (hg : HasL2WeakDeriv f g)
    (hh : HasL2WeakDeriv f h) : g = h :=
  Lp.ext (HasWeakDerivOn.unique isOpen_Ioo hg hh)

theorem neg {f g : IntervalL2} (h : HasL2WeakDeriv f g) :
    HasL2WeakDeriv (-f) (-g) :=
  (HasWeakDerivOn.neg h).congr (Lp.coeFn_neg f).symm (Lp.coeFn_neg g).symm

theorem add {f g f₁ g₁ : IntervalL2} (h : HasL2WeakDeriv f g)
    (h₁ : HasL2WeakDeriv f₁ g₁) : HasL2WeakDeriv (f + f₁) (g + g₁) :=
  (HasWeakDerivOn.add h h₁).congr (Lp.coeFn_add f f₁).symm (Lp.coeFn_add g g₁).symm

theorem reflect {f g : IntervalL2} (h : HasL2WeakDeriv f g) :
    HasL2WeakDeriv (l2Reflect f) (-l2Reflect g) := by
  apply (HasWeakDerivOn.reflect h).congr (l2Reflect_ae f).symm
  filter_upwards [Lp.coeFn_neg (l2Reflect g), l2Reflect_ae g] with x hx hy
  exact (hx.trans (congrArg Neg.neg hy)).symm

end HasL2WeakDeriv

def MemIntervalH2 (f : IntervalL2) : Prop :=
  ∃ g h : IntervalL2, HasL2WeakDeriv f g ∧ HasL2WeakDeriv g h

theorem MemIntervalH2.reflect {f : IntervalL2} (hf : MemIntervalH2 f) :
    MemIntervalH2 (l2Reflect f) := by
  obtain ⟨g, h, hfg, hgh⟩ := hf
  refine ⟨-l2Reflect g, l2Reflect h, hfg.reflect, ?_⟩
  simpa only [neg_neg] using hgh.reflect.neg

theorem memIntervalH2_reflect_iff (f : IntervalL2) :
    MemIntervalH2 (l2Reflect f) ↔ MemIntervalH2 f :=
  ⟨fun h => by simpa only [l2Reflect_involution] using h.reflect, MemIntervalH2.reflect⟩

theorem MemIntervalH2.derivatives_unique {f g h g₁ h₁ : IntervalL2}
    (hfg : HasL2WeakDeriv f g) (hgh : HasL2WeakDeriv g h)
    (hfg₁ : HasL2WeakDeriv f g₁) (hgh₁ : HasL2WeakDeriv g₁ h₁) :
    g = g₁ ∧ h = h₁ := by
  have hg := hfg.unique hfg₁
  exact ⟨hg, hgh.unique (hg.symm ▸ hgh₁)⟩

theorem continuous_memLp_interval (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 intervalMeasure := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hc : Continuous (fun x => ‖f x‖ ^ 2) := hf.norm.pow 2
  exact hc.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

theorem hasIntervalWeakDeriv_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    HasIntervalWeakDeriv f (deriv f) := by
  have hfc := hf.continuous
  have hgc := hf.continuous_deriv_one
  refine ⟨hfc.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self,
    hgc.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self, ?_⟩
  intro φ hφ
  have hleft : φ (-1) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    have hi := hφ.2.2 hx
    simp only [Set.mem_Ioo, lt_self_iff_false, false_and] at hi)
  have hright : φ 1 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    have hi := hφ.2.2 hx
    simp only [Set.mem_Ioo, lt_self_iff_false, and_false] at hi)
  have hint := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := (-1 : ℝ)) (b := 1)
    (fun x _ => (hφ.1.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    (hφ.deriv.1.continuous.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
  simp only [hleft, hright, zero_smul, sub_self, zero_sub] at hint
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hint
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hint
  exact (neg_eq_iff_eq_neg.mpr hint).symm

theorem hasL2WeakDeriv_toLp {f g : ℝ → ℂ}
    (hf : MemLp f 2 intervalMeasure) (hg : MemLp g 2 intervalMeasure)
    (hfg : HasIntervalWeakDeriv f g) :
    HasL2WeakDeriv (hf.toLp f) (hg.toLp g) :=
  hfg.congr hf.coeFn_toLp.symm hg.coeFn_toLp.symm

theorem memIntervalH2_of_contDiff (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    MemIntervalH2 ((continuous_memLp_interval f hf.continuous).toLp f) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg₁ : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' hf
  have hg := continuous_memLp_interval (deriv f) hg₁.continuous
  have hh := continuous_memLp_interval (deriv (deriv f)) hg₁.continuous_deriv_one
  exact ⟨hg.toLp (deriv f), hh.toLp (deriv (deriv f)),
    hasL2WeakDeriv_toLp _ hg (hasIntervalWeakDeriv_of_contDiff hf₁),
    hasL2WeakDeriv_toLp hg hh (hasIntervalWeakDeriv_of_contDiff hg₁)⟩

end Involution
