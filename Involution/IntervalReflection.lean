module

public import Involution.IntervalGluing

/-! Отражение слабых производных между произвольными интервалами.
Знак первой производной меняется; знак второй сохраняется. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

theorem neg_preimage_Ioo (l r : ℝ) :
    (fun x : ℝ => -x) ⁻¹' Ioo l r = Ioo (-r) (-l) := by
  ext x
  simp only [mem_preimage, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem interval_reflect_measurePreserving (l r : ℝ) :
    MeasurePreserving (fun x : ℝ => -x)
      (volume.restrict (Ioo (-r) (-l))) (volume.restrict (Ioo l r)) := by
  simpa only [neg_preimage_Ioo] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Ioo : MeasurableSet (Ioo l r))

theorem IsSmoothTestOn.reflect_interval {l r : ℝ} {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn (Ioo l r) φ) :
    IsSmoothTestOn (Ioo (-r) (-l)) (Involution.reflect φ) := by
  refine ⟨hφ.1.comp contDiff_neg, hφ.2.1.comp_homeomorph (Homeomorph.neg ℝ), ?_⟩
  change tsupport (φ ∘ (Homeomorph.neg ℝ)) ⊆ Ioo (-r) (-l)
  rw [tsupport_comp_eq_preimage]
  intro x hx
  have h := hφ.2.2 hx
  change l < -x ∧ -x < r at h
  constructor <;> linarith [h.1, h.2]

theorem integral_reflect_pair_interval (l r : ℝ) (φ : ℝ → ℝ) (f : ℝ → ℂ) :
    (∫ x in Ioo (-r) (-l), φ x • reflect f x) =
      ∫ x in Ioo l r, reflect φ x • f x := by
  have h := (interval_reflect_measurePreserving l r).integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding (fun x => φ (-x) • f x)
  simpa only [reflect_apply, neg_neg] using h

theorem HasWeakDerivOn.reflect_interval {l r : ℝ} {f g : ℝ → ℂ}
    (h : HasWeakDerivOn (Ioo l r) f g) :
    HasWeakDerivOn (Ioo (-r) (-l)) (Involution.reflect f) (-Involution.reflect g) := by
  have hf : IntegrableOn (Involution.reflect f) (Ioo (-r) (-l)) :=
    ((interval_reflect_measurePreserving l r).integrable_comp
      h.1.aestronglyMeasurable).mpr h.1
  have hg : IntegrableOn (Involution.reflect g) (Ioo (-r) (-l)) :=
    ((interval_reflect_measurePreserving l r).integrable_comp
      h.2.1.aestronglyMeasurable).mpr h.2.1
  refine ⟨hf, hg.neg, ?_⟩
  intro φ hφ
  have htestφ : IsSmoothTestOn (Ioo l r) (Involution.reflect φ) := by
    simpa only [neg_neg] using hφ.reflect_interval
  have htest := h.2.2 (Involution.reflect φ) htestφ
  simp only [deriv_reflect, Pi.neg_apply, neg_smul, integral_neg] at htest
  have hpair := neg_injective htest
  change (∫ x in Ioo l r, Involution.reflect (deriv φ) x • f x) =
    ∫ x in Ioo l r, Involution.reflect φ x • g x at hpair
  calc
    _ = ∫ x in Ioo l r, Involution.reflect (deriv φ) x • f x :=
      integral_reflect_pair_interval l r (deriv φ) f
    _ = ∫ x in Ioo l r, Involution.reflect φ x • g x := hpair
    _ = ∫ x in Ioo (-r) (-l), φ x • Involution.reflect g x :=
      (integral_reflect_pair_interval l r φ g).symm
    _ = _ := by simp only [Pi.neg_apply, smul_neg, integral_neg, neg_neg]

theorem memLp_reflect_interval {l r : ℝ} {p : ENNReal} {f : ℝ → ℂ}
    (hf : MemLp f p (volume.restrict (Ioo l r))) :
    MemLp (reflect f) p (volume.restrict (Ioo (-r) (-l))) :=
  hf.comp_measurePreserving (interval_reflect_measurePreserving l r)

theorem continuousOn_reflect_interval {l r : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc l r)) : ContinuousOn (reflect f) (Icc (-r) (-l)) := by
  apply hf.comp continuous_neg.continuousOn
  intro x hx
  change l ≤ -x ∧ -x ≤ r
  constructor <;> linarith [hx.1, hx.2]

/-! Обратная склейка компонент `u(x)=y(x)`, `v(x)=y(-x)`.
Условия в нуле относятся к непрерывным представителям `u,v,u₁,v₁`;
для вторых производных достаточно принадлежности `L₂`. -/

theorem weak_derivatives_fold {F G H : ℝ → ℂ}
    (hFG : HasIntervalWeakDeriv F G) (hGH : HasIntervalWeakDeriv G H) :
    HasWeakDerivOn (Ioo 0 1) F G ∧
      HasWeakDerivOn (Ioo 0 1) G H ∧
      HasWeakDerivOn (Ioo 0 1) (reflect F) (-reflect G) ∧
      HasWeakDerivOn (Ioo 0 1) (-reflect G) (reflect H) := by
  have hpos : Ioo (0 : ℝ) 1 ⊆ Ioo (-1) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hneg : Ioo (-1 : ℝ) 0 ⊆ Ioo (-1) 1 := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  refine ⟨hFG.restrict hpos, hGH.restrict hpos, ?_, ?_⟩
  · simpa only [neg_zero, neg_neg] using (hFG.restrict hneg).reflect_interval
  · simpa only [neg_zero, neg_neg] using (hGH.restrict hneg).reflect_interval.neg

theorem folded_matching_traces (F G : ℝ → ℂ) :
    F 0 = reflect F 0 ∧ G 0 + (-reflect G) 0 = 0 := by
  simp only [reflect_apply, Pi.neg_apply, neg_zero, add_neg_cancel, and_self]

theorem memDirichletH2_reflectedJoin
    {u v u₁ v₁ u₂ v₂ : ℝ → ℂ}
    (hu : HasWeakDerivOn (Ioo 0 1) u u₁)
    (hv : HasWeakDerivOn (Ioo 0 1) v v₁)
    (hu₁ : HasWeakDerivOn (Ioo 0 1) u₁ u₂)
    (hv₁ : HasWeakDerivOn (Ioo 0 1) v₁ v₂)
    (huc : ContinuousOn u (Icc 0 1)) (hvc : ContinuousOn v (Icc 0 1))
    (hu₁c : ContinuousOn u₁ (Icc 0 1)) (hv₁c : ContinuousOn v₁ (Icc 0 1))
    (hmatch : u 0 = v 0) (hmatch₁ : u₁ 0 + v₁ 0 = 0)
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo 0 1)))
    (hv₂ : MemLp v₂ 2 (volume.restrict (Ioo 0 1)))
    (huend : u 1 = 0) (hvend : v 1 = 0) :
    ∃ hf : MemLp (intervalJoin 0 (reflect v) u) 2 intervalMeasure,
      MemDirichletH2 (hf.toLp (intervalJoin 0 (reflect v) u)) := by
  have hvR : HasWeakDerivOn (Ioo (-1) 0) (reflect v) (-reflect v₁) := by
    simpa only [neg_zero] using hv.reflect_interval
  have hv₁R : HasWeakDerivOn (Ioo (-1) 0) (-reflect v₁) (reflect v₂) := by
    simpa only [neg_zero, neg_neg] using hv₁.reflect_interval.neg
  have hvRc : ContinuousOn (reflect v) (Icc (-1) 0) := by
    simpa only [neg_zero] using continuousOn_reflect_interval hvc
  have hv₁Rc : ContinuousOn (-reflect v₁) (Icc (-1) 0) := by
    simpa only [neg_zero] using (continuousOn_reflect_interval hv₁c).neg
  have hmatchR : reflect v 0 = u 0 := by
    simpa only [reflect_apply, neg_zero] using hmatch.symm
  have hmatch₁R : (-reflect v₁) 0 = u₁ 0 := by
    simpa only [Pi.neg_apply, reflect_apply, neg_zero] using
      (eq_neg_of_add_eq_zero_left hmatch₁).symm
  have hv₂R : MemLp (reflect v₂) 2 (volume.restrict (Ioo (-1) 0)) := by
    simpa only [neg_zero] using memLp_reflect_interval hv₂
  obtain ⟨hf, hH2⟩ := memIntervalH2_intervalJoin hvR hu hv₁R hu₁
    hvRc huc hv₁Rc hu₁c hmatchR hmatch₁R hv₂R hu₂
  have hFc := intervalJoin_continuousOn (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1) hvR hu hvRc huc hmatchR
  refine ⟨hf, hH2, hasDirichletTrace_intervalJoin hf hFc ?_ huend⟩
  simpa only [reflect_apply, neg_neg] using hvend

end Involution
