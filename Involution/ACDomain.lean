module

public import Involution.IntervalRegularity
public import Involution.IntervalOperator

/-! Характеризация слабой области Дирихле абсолютно непрерывными представителями.
Равенство с `H₀¹`, определённым замыканием гладких функций, здесь не доказывается. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

/-- Два абсолютно непрерывных представителя с производными в L₂ и нулевыми концами. -/
def MemACDirichletH2 (f : IntervalL2) : Prop :=
  ∃ (g h : IntervalL2) (F G : ℝ → ℂ), HasIntervalRepresentative f F ∧
    HasIntervalRepresentative g G ∧
    AbsolutelyContinuousOnInterval F (-1) 1 ∧ AbsolutelyContinuousOnInterval G (-1) 1 ∧
    (∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (g x) x) ∧
    (∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt G (h x) x) ∧
    F (-1) = 0 ∧ F 1 = 0

theorem MemDirichletH2.acRealization {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemACDirichletH2 f := by
  obtain ⟨g, h, hfg, hgh⟩ := hf.1
  obtain ⟨F, hF, hFac, hdF⟩ := hfg.exists_ac_representative
  obtain ⟨G, hG, hGac, hdG⟩ := hgh.exists_ac_representative
  obtain ⟨hl, hr⟩ := hf.2.boundary hF
  exact ⟨g, h, F, G, hF, hG, hFac, hGac, hdF, hdG, hl, hr⟩

theorem intervalL2_integrable (f : IntervalL2) : Integrable f intervalMeasure := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1))
    infer_instance
  exact (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)

theorem MemACDirichletH2.weakRealization {f : IntervalL2} (hf : MemACDirichletH2 f) :
    MemDirichletH2 f := by
  obtain ⟨g, h, F, G, hF, hG, hFac, hGac, hdF, hdG, hl, hr⟩ := hf
  have hfgF : HasIntervalWeakDeriv F g :=
    hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hFac (intervalL2_integrable g)
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdF)
  have hghG : HasIntervalWeakDeriv G h :=
    hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hGac (intervalL2_integrable h)
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdG)
  have hfg : HasL2WeakDeriv f g := hfgF.congr hF.2 Filter.EventuallyEq.rfl
  have hgh : HasL2WeakDeriv g h := hghG.congr hG.2 Filter.EventuallyEq.rfl
  exact ⟨⟨g, h, hfg, hgh⟩, F, hF, hl, hr⟩

theorem memDirichletH2_iff_acRealization (f : IntervalL2) :
    MemDirichletH2 f ↔ MemACDirichletH2 f :=
  ⟨MemDirichletH2.acRealization, MemACDirichletH2.weakRealization⟩

theorem acRealization_derivatives_eq (f g h : IntervalL2) (F G : ℝ → ℂ)
    (hf : MemDirichletH2 f) (hF : HasIntervalRepresentative f F)
    (hG : HasIntervalRepresentative g G) (hFac : AbsolutelyContinuousOnInterval F (-1) 1)
    (hGac : AbsolutelyContinuousOnInterval G (-1) 1)
    (hdF : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (g x) x)
    (hdG : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt G (h x) x) :
    firstWeakDeriv f hf.1 = g ∧ secondWeakDeriv f hf.1 = h := by
  apply weakDerivatives_eq
  · exact (hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hFac (intervalL2_integrable g)
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdF)).congr
        hF.2 Filter.EventuallyEq.rfl
  · exact (hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hGac (intervalL2_integrable h)
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdG)).congr
        hG.2 Filter.EventuallyEq.rfl

theorem acRealization_first_derivative (f g : IntervalL2) (F G : ℝ → ℂ)
    (hf : MemDirichletH2 f) (hF : HasIntervalRepresentative f F)
    (hG : HasIntervalRepresentative g G) (hFac : AbsolutelyContinuousOnInterval F (-1) 1)
    (hdF : ∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (g x) x) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (G x) x := by
  have hfg : HasL2WeakDeriv f g :=
    (hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hFac (intervalL2_integrable g)
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdF)).congr
        hF.2 Filter.EventuallyEq.rfl
  obtain ⟨g', F', G', hfg', hF', hG', _, _, hd⟩ := hf.1.exists_regular_pair
  have hgeq := hfg.unique hfg'
  subst g'
  have hFeq := hF.unique hF'
  have hGeq := hG.unique hG'
  intro x hx
  have hEq : F =ᶠ[nhds x] F' := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact hFeq hy
  have hder := (hd x hx).congr_of_eventuallyEq hEq
  rw [← hGeq (Ioo_subset_Icc_self hx)] at hder
  exact hder

end Involution
