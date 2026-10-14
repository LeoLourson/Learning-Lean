module

public import Involution.Setup.WeakConstant
public import Involution.Setup.WeakPrimitive
public import Involution.Setup.IntervalTrace

/-! Регулярные представители функций со слабыми производными.
Постоянство при нулевой слабой производной соединяется с первообразной. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

theorem HasWeakDerivOn.eq_const_add_primitive {l r : ℝ} (hlr : l < r)
    {f g : ℝ → ℂ} (hfg : HasWeakDerivOn (Ioo l r) f g) :
    ∃ c : ℂ, f =ᵐ[volume.restrict (Ioo l r)] (fun x => c + ∫ t in l..x, g t) := by
  obtain ⟨c, hc⟩ := (hfg.sub_primitive hlr.le).ae_eq_const_of_zero hlr
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change f x - (∫ t in l..x, g t) = c at hx
  exact (sub_eq_iff_eq_add.mp hx)

theorem HasWeakDerivOn.exists_ac_representative {l r : ℝ} (hlr : l < r)
    {f g : ℝ → ℂ} (hfg : HasWeakDerivOn (Ioo l r) f g) :
    ∃ F : ℝ → ℂ, AbsolutelyContinuousOnInterval F l r ∧
      F =ᵐ[volume.restrict (Ioo l r)] f ∧
      (∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (g x) x) := by
  obtain ⟨c, hc⟩ := hfg.eq_const_add_primitive hlr
  refine ⟨fun x => c + ∫ t in l..x, g t,
    complex_const_add_primitive_absolutelyContinuous hlr.le hfg.2.1 c, hc.symm, ?_⟩
  have hgi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr.le).mpr hfg.2.1
  filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hi
  exact (hx hi l left_mem_uIcc).const_add c

theorem HasL2WeakDeriv.exists_ac_representative {f g : IntervalL2}
    (hfg : HasL2WeakDeriv f g) :
    ∃ F : ℝ → ℂ, HasIntervalRepresentative f F ∧
      AbsolutelyContinuousOnInterval F (-1) 1 ∧
      (∀ᵐ x, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt F (g x) x) := by
  obtain ⟨F, hF, heq, hd⟩ := HasWeakDerivOn.exists_ac_representative
    (by norm_num : (-1 : ℝ) < 1) hfg
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hF.continuousOn
  exact ⟨F, ⟨hFc, heq⟩, hF, by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hd⟩

theorem MemIntervalH2.exists_continuous_representative {f : IntervalL2}
    (hf : MemIntervalH2 f) : ∃ F : ℝ → ℂ, HasIntervalRepresentative f F := by
  obtain ⟨g, h, hfg, hgh⟩ := hf
  obtain ⟨F, hF, _, _⟩ := hfg.exists_ac_representative
  exact ⟨F, hF⟩

theorem MemIntervalH2.exists_regular_pair {f : IntervalL2} (hf : MemIntervalH2 f) :
    ∃ (g : IntervalL2) (F G : ℝ → ℂ), HasL2WeakDeriv f g ∧
      HasIntervalRepresentative f F ∧ HasIntervalRepresentative g G ∧
      AbsolutelyContinuousOnInterval F (-1) 1 ∧
      AbsolutelyContinuousOnInterval G (-1) 1 ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (G x) x) := by
  obtain ⟨g, h, hfg, hgh⟩ := hf
  obtain ⟨G, hG, hGac, _⟩ := hgh.exists_ac_representative
  have hfG : HasIntervalWeakDeriv f G :=
    HasWeakDerivOn.congr hfg Filter.EventuallyEq.rfl hG.2.symm
  obtain ⟨c, hc⟩ := hfG.eq_const_add_primitive (by norm_num : (-1 : ℝ) < 1)
  let F : ℝ → ℂ := fun x => c + ∫ t in (-1 : ℝ)..x, G t
  have hFac : AbsolutelyContinuousOnInterval F (-1) 1 :=
    complex_const_add_primitive_absolutelyContinuous (by norm_num) hfG.2.1 c
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hFac.continuousOn
  refine ⟨g, F, G, hfg, ⟨hFc, hc.symm⟩, hG, hFac, hGac, ?_⟩
  intro x hx
  have hGx : ContinuousAt G x := hG.1.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hGwhole : IntervalIntegrable G volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr
      (hG.1.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  have hGi : IntervalIntegrable G volume (-1) x := by
    apply hGwhole.mono_set'
    rw [uIoc_of_le hx.1.le, uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact fun t ht => ⟨ht.1, ht.2.trans hx.2.le⟩
  exact (intervalIntegral.integral_hasDerivAt_right hGi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hG.1.mono Ioo_subset_Icc_self) x hx) hGx).const_add c

theorem regular_pair_representatives_unique {f g₁ g₂ : IntervalL2}
    {F₁ F₂ G₁ G₂ : ℝ → ℂ} (hfg₁ : HasL2WeakDeriv f g₁) (hfg₂ : HasL2WeakDeriv f g₂)
    (hF₁ : HasIntervalRepresentative f F₁) (hF₂ : HasIntervalRepresentative f F₂)
    (hG₁ : HasIntervalRepresentative g₁ G₁) (hG₂ : HasIntervalRepresentative g₂ G₂) :
    EqOn F₁ F₂ (Icc (-1 : ℝ) 1) ∧ EqOn G₁ G₂ (Icc (-1 : ℝ) 1) := by
  have hg := hfg₁.unique hfg₂
  subst g₂
  exact ⟨hF₁.unique hF₂, hG₁.unique hG₂⟩

end Involution
