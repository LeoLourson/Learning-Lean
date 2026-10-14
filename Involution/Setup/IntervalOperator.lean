module

public import Involution.Setup.IntervalTrace
public import Involution.Setup.ClassicalModes

/-! Однозначные слабые производные и постоянная модель оператора в L².
Выбор свидетелей существования не влияет на результат благодаря единственности.
Область Дирихле задаётся отдельно через MemDirichletH2.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Involution

def firstWeakDeriv (f : IntervalL2) (hf : MemIntervalH2 f) : IntervalL2 := hf.choose

def secondWeakDeriv (f : IntervalL2) (hf : MemIntervalH2 f) : IntervalL2 :=
  hf.choose_spec.choose

theorem firstWeakDeriv_spec (f : IntervalL2) (hf : MemIntervalH2 f) :
    HasL2WeakDeriv f (firstWeakDeriv f hf) := hf.choose_spec.choose_spec.1

theorem secondWeakDeriv_spec (f : IntervalL2) (hf : MemIntervalH2 f) :
    HasL2WeakDeriv (firstWeakDeriv f hf) (secondWeakDeriv f hf) :=
  hf.choose_spec.choose_spec.2

theorem weakDerivatives_eq (f : IntervalL2) (hf : MemIntervalH2 f)
    {g h : IntervalL2} (hfg : HasL2WeakDeriv f g) (hgh : HasL2WeakDeriv g h) :
    firstWeakDeriv f hf = g ∧ secondWeakDeriv f hf = h :=
  MemIntervalH2.derivatives_unique (firstWeakDeriv_spec f hf)
    (secondWeakDeriv_spec f hf) hfg hgh

theorem firstWeakDeriv_reflect (f : IntervalL2) (hf : MemIntervalH2 f) :
    firstWeakDeriv (l2Reflect f) hf.reflect = -l2Reflect (firstWeakDeriv f hf) :=
  (firstWeakDeriv_spec _ _).unique (firstWeakDeriv_spec f hf).reflect

theorem secondWeakDeriv_reflect (f : IntervalL2) (hf : MemIntervalH2 f) :
    secondWeakDeriv (l2Reflect f) hf.reflect = l2Reflect (secondWeakDeriv f hf) := by
  have hfirst := firstWeakDeriv_reflect f hf
  have hsecond : HasL2WeakDeriv (-l2Reflect (firstWeakDeriv f hf))
      (l2Reflect (secondWeakDeriv f hf)) := by
    simpa only [neg_neg] using (secondWeakDeriv_spec f hf).reflect.neg
  exact (secondWeakDeriv_spec _ _).unique (hfirst.symm ▸ hsecond)

theorem secondWeakDeriv_smooth_ae (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    secondWeakDeriv ((continuous_memLp_interval f hf.continuous).toLp f)
      (memIntervalH2_of_contDiff f hf) =ᵐ[intervalMeasure] deriv (deriv f) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg₁ : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' hf
  have hg := continuous_memLp_interval (deriv f) hg₁.continuous
  have hh := continuous_memLp_interval (deriv (deriv f)) hg₁.continuous_deriv_one
  have heq := weakDerivatives_eq _ (memIntervalH2_of_contDiff f hf)
    (hasL2WeakDeriv_toLp _ hg (hasIntervalWeakDeriv_of_contDiff hf₁))
    (hasL2WeakDeriv_toLp hg hh (hasIntervalWeakDeriv_of_contDiff hg₁))
  rw [heq.2]
  exact hh.coeFn_toLp

def constantSobolevOperator (c : ℝ) (f : IntervalL2) (hf : MemIntervalH2 f) : IntervalL2 :=
  -secondWeakDeriv f hf - (c : ℂ) • l2Reflect (secondWeakDeriv f hf)

theorem constantSobolevOperator_smooth_ae (c : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) :
    constantSobolevOperator c ((continuous_memLp_interval f hf.continuous).toLp f)
      (memIntervalH2_of_contDiff f hf) =ᵐ[intervalMeasure] classicalOperator (fun _ => c) f := by
  let F := (continuous_memLp_interval f hf.continuous).toLp f
  let D := secondWeakDeriv F (memIntervalH2_of_contDiff f hf)
  have hD : D =ᵐ[intervalMeasure] deriv (deriv f) := secondWeakDeriv_smooth_ae f hf
  have hRD := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp hD
  change ⇑(-D - (c : ℂ) • l2Reflect D) =ᵐ[intervalMeasure] _
  filter_upwards [Lp.coeFn_sub (-D) ((c : ℂ) • l2Reflect D), Lp.coeFn_neg D,
    Lp.coeFn_smul (c : ℂ) (l2Reflect D), l2Reflect_ae D, hD, hRD] with x hsub hneg hsmul href hd hrd
  change (-D - (c : ℂ) • l2Reflect D) x =
    -deriv (deriv f) x - (c : ℂ) * deriv (deriv f) (-x)
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hneg, hsmul]
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [href, hd]
  exact congrArg (fun z : ℂ => -deriv (deriv f) x - (c : ℂ) * z) hrd

end Involution
