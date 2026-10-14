module

public import Involution.Setup.IntervalSobolev
public import Involution.Setup.IntervalTrace
public import Involution.Setup.IntervalOperator
public import Involution.Setup.ClassicalModes

/-! Принадлежность явных мод соболевскому H², заданному слабыми производными.
Граничные значения вычисляются на явно заданных гладких представителях.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace Involution

theorem contDiff_cosineWave (k : ℝ) : ContDiff ℝ 2 (cosineWave k) := by
  have hk : ContDiff ℝ 2 (fun x : ℝ => k * x) := contDiff_const.mul contDiff_id
  exact Complex.ofRealCLM.contDiff.comp hk.cos

theorem contDiff_sineWave (k : ℝ) : ContDiff ℝ 2 (sineWave k) := by
  have hk : ContDiff ℝ 2 (fun x : ℝ => k * x) := contDiff_const.mul contDiff_id
  exact Complex.ofRealCLM.contDiff.comp hk.sin

def cosineWaveL2 (k : ℝ) : IntervalL2 :=
  (continuous_memLp_interval (cosineWave k) (contDiff_cosineWave k).continuous).toLp
    (cosineWave k)

def sineWaveL2 (k : ℝ) : IntervalL2 :=
  (continuous_memLp_interval (sineWave k) (contDiff_sineWave k).continuous).toLp
    (sineWave k)

theorem cosineWaveL2_ae (k : ℝ) : cosineWaveL2 k =ᵐ[intervalMeasure] cosineWave k :=
  MemLp.coeFn_toLp _

theorem sineWaveL2_ae (k : ℝ) : sineWaveL2 k =ᵐ[intervalMeasure] sineWave k :=
  MemLp.coeFn_toLp _

theorem cosineWave_memIntervalH2 (k : ℝ) : MemIntervalH2 (cosineWaveL2 k) :=
  memIntervalH2_of_contDiff _ (contDiff_cosineWave k)

theorem sineWave_memIntervalH2 (k : ℝ) : MemIntervalH2 (sineWaveL2 k) :=
  memIntervalH2_of_contDiff _ (contDiff_sineWave k)

theorem cosineMode_memDirichletH2 (n : ℕ) :
    MemDirichletH2 (cosineWaveL2 (((n : ℝ) + 1 / 2) * Real.pi)) :=
  ⟨cosineWave_memIntervalH2 _, cosineWave _,
    ⟨(contDiff_cosineWave _).continuous.continuousOn, (cosineWaveL2_ae _).symm⟩,
    cosine_dirichlet_boundary n⟩

theorem sineMode_memDirichletH2 (n : ℕ) :
    MemDirichletH2 (sineWaveL2 ((n : ℝ) * Real.pi)) :=
  ⟨sineWave_memIntervalH2 _, sineWave _,
    ⟨(contDiff_sineWave _).continuous.continuousOn, (sineWaveL2_ae _).symm⟩,
    sine_dirichlet_boundary n⟩

theorem cosineWaveL2_ne_zero (k : ℝ) : cosineWaveL2 k ≠ 0 := by
  intro hz
  have hrep : HasIntervalRepresentative (cosineWaveL2 k) (cosineWave k) :=
    ⟨(contDiff_cosineWave k).continuous.continuousOn, (cosineWaveL2_ae k).symm⟩
  have hzero : HasIntervalRepresentative (cosineWaveL2 k) (fun _ => 0) := by
    rw [hz]
    exact ⟨continuous_const.continuousOn, (Lp.coeFn_zero ℂ 2 intervalMeasure).symm⟩
  have hx := hrep.unique hzero (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1)
  simp [cosineWave] at hx

theorem sineModeL2_ne_zero (n : ℕ) (hn : 0 < n) : sineWaveL2 ((n : ℝ) * Real.pi) ≠ 0 := by
  intro hz
  have hrep : HasIntervalRepresentative (sineWaveL2 ((n : ℝ) * Real.pi))
      (sineWave ((n : ℝ) * Real.pi)) :=
    ⟨(contDiff_sineWave _).continuous.continuousOn, (sineWaveL2_ae _).symm⟩
  have hzero : HasIntervalRepresentative (sineWaveL2 ((n : ℝ) * Real.pi)) (fun _ => 0) := by
    rw [hz]
    exact ⟨continuous_const.continuousOn, (Lp.coeFn_zero ℂ 2 intervalMeasure).symm⟩
  have heq : sineWave ((n : ℝ) * Real.pi) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)] with x hx
    exact hrep.unique hzero (Set.Ioo_subset_Icc_self hx)
  have hd := heq.deriv_eq
  rw [(hasDerivAt_sineWave ((n : ℝ) * Real.pi) 0).deriv] at hd
  have hnzero : n = 0 := by simpa [cosineWave] using hd
  exact hn.ne' hnzero

theorem cosineWaveL2_eigen_equation (c k : ℝ) :
    constantSobolevOperator c (cosineWaveL2 k) (cosineWave_memIntervalH2 k) =
      (((1 + c : ℝ) : ℂ) * (k : ℂ) ^ 2) • cosineWaveL2 k := by
  apply Lp.ext
  filter_upwards [constantSobolevOperator_smooth_ae c (cosineWave k) (contDiff_cosineWave k),
    Lp.coeFn_smul ((((1 + c : ℝ) : ℂ) * (k : ℂ) ^ 2)) (cosineWaveL2 k),
    cosineWaveL2_ae k] with x hx hsmul hmode
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmode]
  simpa only [cosineWaveL2, Complex.ofReal_mul, Complex.ofReal_pow] using
    hx.trans (constant_cosine_eigen_equation c k x)

theorem sineWaveL2_eigen_equation (c k : ℝ) :
    constantSobolevOperator c (sineWaveL2 k) (sineWave_memIntervalH2 k) =
      (((1 - c : ℝ) : ℂ) * (k : ℂ) ^ 2) • sineWaveL2 k := by
  apply Lp.ext
  filter_upwards [constantSobolevOperator_smooth_ae c (sineWave k) (contDiff_sineWave k),
    Lp.coeFn_smul ((((1 - c : ℝ) : ℂ) * (k : ℂ) ^ 2)) (sineWaveL2 k),
    sineWaveL2_ae k] with x hx hsmul hmode
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmode]
  simpa only [sineWaveL2, Complex.ofReal_mul, Complex.ofReal_pow] using
    hx.trans (constant_sine_eigen_equation c k x)

theorem constant_cosine_eigenpair (c : ℝ) (n : ℕ) :
    let k := ((n : ℝ) + 1 / 2) * Real.pi
    MemDirichletH2 (cosineWaveL2 k) ∧ cosineWaveL2 k ≠ 0 ∧
      constantSobolevOperator c (cosineWaveL2 k) (cosineWave_memIntervalH2 k) =
        ((((1 + c) * k ^ 2 : ℝ) : ℂ)) • cosineWaveL2 k := by
  refine ⟨cosineMode_memDirichletH2 n, cosineWaveL2_ne_zero _, ?_⟩
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
    cosineWaveL2_eigen_equation c (((n : ℝ) + 1 / 2) * Real.pi)

theorem constant_sine_eigenpair (c : ℝ) (n : ℕ) (hn : 0 < n) :
    let k := (n : ℝ) * Real.pi
    MemDirichletH2 (sineWaveL2 k) ∧ sineWaveL2 k ≠ 0 ∧
      constantSobolevOperator c (sineWaveL2 k) (sineWave_memIntervalH2 k) =
        ((((1 - c) * k ^ 2 : ℝ) : ℂ)) • sineWaveL2 k := by
  refine ⟨sineMode_memDirichletH2 n, sineModeL2_ne_zero n hn, ?_⟩
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
    sineWaveL2_eigen_equation c ((n : ℝ) * Real.pi)

end Involution
