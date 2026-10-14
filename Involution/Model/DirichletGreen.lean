module

public import Involution.Setup.DirichletEnergy
public import Involution.Folding.IntervalGluing

/-! Явное решение слабой задачи `-y''=f`, `y(-1)=y(1)=0`.
Две первообразные и линейная поправка обеспечивают существование решения
для каждого класса `L₂`; единственность следует из энергетического тождества. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

def greenPrimitive (f : IntervalL2) (x : ℝ) : ℂ := ∫ t in (-1 : ℝ)..x, f t

def greenFirst (f : IntervalL2) (x : ℝ) : ℂ :=
  (∫ t in (-1 : ℝ)..1, greenPrimitive f t) / 2 - greenPrimitive f x

def greenFunction (f : IntervalL2) (x : ℝ) : ℂ := ∫ t in (-1 : ℝ)..x, greenFirst f t

theorem greenFunction_data (f : IntervalL2) :
    ContinuousOn (greenFunction f) (Icc (-1) 1) ∧
      ContinuousOn (greenFirst f) (Icc (-1) 1) ∧
      HasIntervalWeakDeriv (greenFunction f) (greenFirst f) ∧
      HasIntervalWeakDeriv (greenFirst f) (-f) ∧
      greenFunction f (-1) = 0 ∧ greenFunction f 1 = 0 := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1))
    infer_instance
  have hfi : IntegrableOn f (Ioo (-1 : ℝ) 1) :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hP : ContinuousOn (greenPrimitive f) (Icc (-1) 1) := by
    change ContinuousOn (fun x => ∫ t in (-1 : ℝ)..x, f t) (Icc (-1) 1)
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      (complex_primitive_absolutelyContinuous (by norm_num)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le
          (by norm_num : (-1 : ℝ) ≤ 1)).mpr hfi)).continuousOn
  have hG : ContinuousOn (greenFirst f) (Icc (-1) 1) := continuousOn_const.sub hP
  have hGi : IntegrableOn (greenFirst f) (Ioo (-1 : ℝ) 1) :=
    hG.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hF : ContinuousOn (greenFunction f) (Icc (-1) 1) := by
    change ContinuousOn (fun x => ∫ t in (-1 : ℝ)..x, greenFirst f t) (Icc (-1) 1)
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      (complex_primitive_absolutelyContinuous (by norm_num)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le
          (by norm_num : (-1 : ℝ) ≤ 1)).mpr hGi)).continuousOn
  have hFG : HasIntervalWeakDeriv (greenFunction f) (greenFirst f) :=
    hasWeakDerivOn_primitive (by norm_num) hGi
  have hGf : HasIntervalWeakDeriv (greenFirst f) (-f) := by
    convert hasWeakDerivOn_const_add_primitive (by norm_num : (-1 : ℝ) ≤ 1)
      hfi.neg ((∫ t in (-1 : ℝ)..1, greenPrimitive f t) / 2) using 1
    funext x
    simp only [greenFirst, greenPrimitive, Pi.neg_apply, intervalIntegral.integral_neg,
      sub_eq_add_neg]
  refine ⟨hF, hG, hFG, hGf, by simp [greenFunction], ?_⟩
  change (∫ t in (-1 : ℝ)..1,
    ((∫ s in (-1 : ℝ)..1, greenPrimitive f s) / 2 - greenPrimitive f t)) = 0
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (hP.intervalIntegrable_of_Icc (by norm_num)), intervalIntegral.integral_const]
  norm_num
  ring

theorem negativeSecondWeakDeriv_surjective (f : IntervalL2) :
    ∃ (y : IntervalL2) (hy : MemDirichletH2 y), -secondWeakDeriv y hy.1 = f := by
  obtain ⟨hF, hG, hFG, hGf, hleft, hright⟩ := greenFunction_data f
  let hFmem := continuousOn_memLp_interval hF
  let hGmem := continuousOn_memLp_interval hG
  let hHmem : MemLp (-f : ℝ → ℂ) 2 intervalMeasure := (Lp.memLp f).neg
  let y := hFmem.toLp (greenFunction f)
  let g := hGmem.toLp (greenFirst f)
  let h := hHmem.toLp (- (f : ℝ → ℂ))
  have hyg : HasL2WeakDeriv y g := hasL2WeakDeriv_toLp hFmem hGmem hFG
  have hgh : HasL2WeakDeriv g h := hasL2WeakDeriv_toLp hGmem hHmem hGf
  have hy : MemDirichletH2 y := ⟨⟨g, h, hyg, hgh⟩,
    greenFunction f, ⟨hF, hFmem.coeFn_toLp.symm⟩, hleft, hright⟩
  have hh : h = -f := Lp.ext (hHmem.coeFn_toLp.trans (Lp.coeFn_neg f).symm)
  refine ⟨y, hy, ?_⟩
  rw [(weakDerivatives_eq y hy.1 hyg hgh).2, hh, neg_neg]

theorem negativeSecondWeakDeriv_unique_solution (f y z : IntervalL2)
    (hy : MemDirichletH2 y) (hz : MemDirichletH2 z)
    (hyf : -secondWeakDeriv y hy.1 = f) (hzf : -secondWeakDeriv z hz.1 = f) : y = z :=
  secondWeakDeriv_dirichlet_injective y z hy hz (neg_injective (hyf.trans hzf.symm))

end Involution
