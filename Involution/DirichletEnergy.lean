module

public import Involution.ComplexAC
public import Involution.IntervalRegularity
public import Involution.IntervalOperator
public import Involution.DirichletDomain

/-! Энергетическое тождество слабого оператора Дирихле.
Интегрирование по частям производится на абсолютно непрерывных
представителях; результат сформулирован на классах `L₂`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

theorem integral_complex_intervalMeasure (F : ℝ → ℂ) :
    (∫ x, F x ∂intervalMeasure) = ∫ x in (-1 : ℝ)..1, F x := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  rfl

theorem l2_inner_integral (f g : IntervalL2) :
    inner ℂ f g = ∫ x, star (f x) * g x ∂intervalMeasure := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply']
  rfl

theorem dirichlet_energy_identity (f u : IntervalL2)
    (hf : MemDirichletH2 f) (hu : MemIntervalH2 u) :
    inner ℂ f (secondWeakDeriv u hu) =
      -inner ℂ (firstWeakDeriv f hf.1) (firstWeakDeriv u hu) := by
  let g := firstWeakDeriv f hf.1
  let v := firstWeakDeriv u hu
  let h := secondWeakDeriv u hu
  have hfg := firstWeakDeriv_spec f hf.1
  have hvh := secondWeakDeriv_spec u hu
  obtain ⟨F, hF, hFac, hdF⟩ := hfg.exists_ac_representative
  obtain ⟨V, hV, hVac, hdV⟩ := hvh.exists_ac_representative
  have hgi : IntervalIntegrable g volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr hfg.2.1
  have hhi : IntervalIntegrable h volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr hvh.2.1
  have hparts := complex_ac_green_identity hFac hVac hgi hhi
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdF)
    (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdV)
  obtain ⟨hleft, hright⟩ := hf.2.boundary hF
  simp only [hleft, hright, star_zero, zero_mul, sub_self, zero_sub] at hparts
  change inner ℂ f h = -inner ℂ g v
  rw [l2_inner_integral, l2_inner_integral]
  calc
    _ = ∫ x, star (F x) * h x ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [hF.2] with x hx
      rw [hx]
    _ = -(∫ x, star (g x) * V x ∂intervalMeasure) := by
      rw [integral_complex_intervalMeasure, integral_complex_intervalMeasure]
      exact hparts
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hV.2] with x hx
      rw [hx]

theorem negativeSecondWeakDeriv_energy (f u : IntervalL2)
    (hf : MemDirichletH2 f) (hu : MemIntervalH2 u) :
    inner ℂ f (-secondWeakDeriv u hu) =
      inner ℂ (firstWeakDeriv f hf.1) (firstWeakDeriv u hu) := by
  rw [inner_neg_right, dirichlet_energy_identity f u hf hu, neg_neg]

theorem negativeSecondWeakDeriv_symmetric (f u : IntervalL2)
    (hf : MemDirichletH2 f) (hu : MemDirichletH2 u) :
    inner ℂ (-secondWeakDeriv f hf.1) u = inner ℂ f (-secondWeakDeriv u hu.1) := by
  rw [← inner_conj_symm, negativeSecondWeakDeriv_energy u f hu hf.1,
    inner_conj_symm, negativeSecondWeakDeriv_energy f u hf hu.1]

theorem negativeSecondWeakDeriv_nonnegative (f : IntervalL2) (hf : MemDirichletH2 f) :
    0 ≤ (inner ℂ f (-secondWeakDeriv f hf.1)).re := by
  change 0 ≤ RCLike.re (inner ℂ f (-secondWeakDeriv f hf.1))
  rw [negativeSecondWeakDeriv_energy f f hf hf.1]
  exact inner_self_nonneg

theorem dirichlet_eq_zero_of_firstWeakDeriv_eq_zero (f : IntervalL2)
    (hf : MemDirichletH2 f) (hg : firstWeakDeriv f hf.1 = 0) : f = 0 := by
  have hfg := firstWeakDeriv_spec f hf.1
  rw [hg] at hfg
  have hweak : HasIntervalWeakDeriv f (fun _ => 0) :=
    hfg.congr Filter.EventuallyEq.rfl (Lp.coeFn_zero ℂ 2 intervalMeasure)
  obtain ⟨c, hc⟩ := hweak.ae_eq_const_of_zero (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨F, hF, hleft, _⟩ := hf.2
  have hFc : EqOn F (fun _ => c) (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_Ioo_of_ae_eq volume (hF.2.trans hc)
      (hF.1.mono Ioo_subset_Icc_self) continuousOn_const
  have hclosed : EqOn F (fun _ => c) (Icc (-1 : ℝ) 1) :=
    hFc.of_subset_closure hF.1 continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  have hc0 : c = 0 := (hclosed (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)).symm.trans hleft
  apply Lp.ext
  exact (hc.trans (Filter.Eventually.of_forall fun _ => hc0)).trans
    (Lp.coeFn_zero ℂ 2 intervalMeasure).symm

theorem dirichlet_eq_zero_of_secondWeakDeriv_eq_zero (f : IntervalL2)
    (hf : MemDirichletH2 f) (hh : secondWeakDeriv f hf.1 = 0) : f = 0 := by
  have henergy := dirichlet_energy_identity f f hf hf.1
  rw [hh, inner_zero_right] at henergy
  have hg : firstWeakDeriv f hf.1 = 0 := inner_self_eq_zero.mp
    (neg_eq_zero.mp henergy.symm)
  exact dirichlet_eq_zero_of_firstWeakDeriv_eq_zero f hf hg

theorem negativeSecondWeakDeriv_positive (f : IntervalL2) (hf : MemDirichletH2 f)
    (hne : f ≠ 0) : 0 < (inner ℂ f (-secondWeakDeriv f hf.1)).re := by
  have hg : firstWeakDeriv f hf.1 ≠ 0 := fun h =>
    hne (dirichlet_eq_zero_of_firstWeakDeriv_eq_zero f hf h)
  change 0 < RCLike.re (inner ℂ f (-secondWeakDeriv f hf.1))
  rw [negativeSecondWeakDeriv_energy f f hf hf.1]
  exact re_inner_self_pos.mpr hg

theorem secondWeakDeriv_dirichlet_injective (f u : IntervalL2)
    (hf : MemDirichletH2 f) (hu : MemDirichletH2 u)
    (heq : secondWeakDeriv f hf.1 = secondWeakDeriv u hu.1) : f = u := by
  have hsub := hf.sub hu
  have hzero : secondWeakDeriv (f - u) hsub.1 = 0 := by
    rw [secondWeakDeriv_sub f u hf.1 hu.1 hsub.1, heq, sub_self]
  exact sub_eq_zero.mp (dirichlet_eq_zero_of_secondWeakDeriv_eq_zero (f - u) hsub hzero)

end Involution
