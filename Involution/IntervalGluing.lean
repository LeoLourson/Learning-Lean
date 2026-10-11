module

public import Involution.IntervalRegularity

/-! Склеивание через первообразную слабой производной.
Значения в точке склейки относятся к непрерывным представителям.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

theorem HasWeakDerivOn.eqOn_primitive_of_continuousOn {l r : ℝ} (hlr : l < r)
    {F g : ℝ → ℂ} (hFg : HasWeakDerivOn (Ioo l r) F g)
    (hF : ContinuousOn F (Icc l r)) :
    EqOn F (fun x => F l + ∫ t in l..x, g t) (Icc l r) := by
  obtain ⟨c, hc⟩ := hFg.eq_const_add_primitive hlr
  have hP : ContinuousOn (fun x => c + ∫ t in l..x, g t) (Icc l r) := by
    simpa only [uIcc_of_le hlr.le] using
      (complex_const_add_primitive_absolutelyContinuous hlr.le hFg.2.1 c).continuousOn
  have heq : EqOn F (fun x => c + ∫ t in l..x, g t) (Ioo l r) :=
    Measure.eqOn_Ioo_of_ae_eq volume hc (hF.mono Ioo_subset_Icc_self)
      (hP.mono Ioo_subset_Icc_self)
  have heqc : EqOn F (fun x => c + ∫ t in l..x, g t) (Icc l r) :=
    heq.of_subset_closure hF hP Ioo_subset_Icc_self (by rw [closure_Ioo hlr.ne])
  have hcl : F l = c := by
    have h := heqc (left_mem_Icc.mpr hlr.le)
    simpa only [intervalIntegral.integral_same, add_zero] using h
  simpa only [← hcl] using heqc

def intervalJoin (m : ℝ) (fL fR : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x ≤ m then fL x else fR x

theorem intervalJoin_of_le {m x : ℝ} {fL fR : ℝ → ℂ} (hx : x ≤ m) :
    intervalJoin m fL fR x = fL x := by simp only [intervalJoin, ite_eq_left hx]

theorem intervalJoin_of_lt {m x : ℝ} {fL fR : ℝ → ℂ} (hx : m < x) :
    intervalJoin m fL fR x = fR x := by
  simp only [intervalJoin, ite_eq_right (not_le.mpr hx)]

theorem intervalJoin_intervalIntegrable {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    {gL gR : ℝ → ℂ} (hgL : IntegrableOn gL (Ioo l m))
    (hgR : IntegrableOn gR (Ioo m r)) :
    IntervalIntegrable (intervalJoin m gL gR) volume l r := by
  have hL : IntegrableOn (intervalJoin m gL gR) (Ioo l m) := by
    apply hgL.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (intervalJoin_of_le hx.2.le).symm
  have hR : IntegrableOn (intervalJoin m gL gR) (Ioo m r) := by
    apply hgR.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (intervalJoin_of_lt hx.1).symm
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlm.le).mpr hL).trans
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hmr.le).mpr hR)

theorem intervalJoin_eqOn_primitive {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    {FL FR gL gR : ℝ → ℂ}
    (hL : HasWeakDerivOn (Ioo l m) FL gL) (hR : HasWeakDerivOn (Ioo m r) FR gR)
    (hFL : ContinuousOn FL (Icc l m)) (hFR : ContinuousOn FR (Icc m r))
    (hmatch : FL m = FR m) :
    EqOn (intervalJoin m FL FR)
      (fun x => FL l + ∫ t in l..x, intervalJoin m gL gR t) (Icc l r) := by
  have hLp := hL.eqOn_primitive_of_continuousOn hlm hFL
  have hRp := hR.eqOn_primitive_of_continuousOn hmr hFR
  have hGi := intervalJoin_intervalIntegrable hlm hmr hL.2.1 hR.2.1
  intro x hx
  change intervalJoin m FL FR x = FL l + ∫ t in l..x, intervalJoin m gL gR t
  by_cases hxm : x ≤ m
  · have hI : (∫ t in l..x, intervalJoin m gL gR t) = ∫ t in l..x, gL t := by
      apply intervalIntegral.integral_congr_Ioo_of_le hx.1
      exact fun t ht => intervalJoin_of_le (ht.2.le.trans hxm)
    rw [intervalJoin_of_le hxm, hI]
    exact hLp ⟨hx.1, hxm⟩
  · have hmx : m < x := lt_of_not_ge hxm
    have hLm : IntervalIntegrable (intervalJoin m gL gR) volume l m := by
      apply hGi.mono_set'
      rw [uIoc_of_le hlm.le, uIoc_of_le (hlm.trans hmr).le]
      exact fun t ht => ⟨ht.1, ht.2.trans hmr.le⟩
    have hMx : IntervalIntegrable (intervalJoin m gL gR) volume m x := by
      apply hGi.mono_set'
      rw [uIoc_of_le hmx.le, uIoc_of_le (hlm.trans hmr).le]
      exact fun t ht => ⟨hlm.trans ht.1, ht.2.trans hx.2⟩
    have hIL : (∫ t in l..m, intervalJoin m gL gR t) = ∫ t in l..m, gL t := by
      apply intervalIntegral.integral_congr_Ioo_of_le hlm.le
      exact fun t ht => intervalJoin_of_le ht.2.le
    have hIR : (∫ t in m..x, intervalJoin m gL gR t) = ∫ t in m..x, gR t := by
      apply intervalIntegral.integral_congr_Ioo_of_le hmx.le
      exact fun t ht => intervalJoin_of_lt ht.1
    calc
      intervalJoin m FL FR x = FR x := intervalJoin_of_lt hmx
      _ = FR m + ∫ t in m..x, gR t := hRp ⟨hmx.le, hx.2⟩
      _ = FL l + ((∫ t in l..m, gL t) + ∫ t in m..x, gR t) := by
        rw [← hmatch, hLp (right_mem_Icc.mpr hlm.le), add_assoc]
      _ = FL l + ∫ t in l..x, intervalJoin m gL gR t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hLm hMx, hIL, hIR]

theorem hasWeakDerivOn_intervalJoin {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    {FL FR gL gR : ℝ → ℂ}
    (hL : HasWeakDerivOn (Ioo l m) FL gL) (hR : HasWeakDerivOn (Ioo m r) FR gR)
    (hFL : ContinuousOn FL (Icc l m)) (hFR : ContinuousOn FR (Icc m r))
    (hmatch : FL m = FR m) :
    HasWeakDerivOn (Ioo l r) (intervalJoin m FL FR) (intervalJoin m gL gR) := by
  have hGi : IntegrableOn (intervalJoin m gL gR) (Ioo l r) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hlm.trans hmr).le).mp
      (intervalJoin_intervalIntegrable hlm hmr hL.2.1 hR.2.1)
  have hP := hasWeakDerivOn_const_add_primitive (hlm.trans hmr).le hGi (FL l)
  have heq := intervalJoin_eqOn_primitive hlm hmr hL hR hFL hFR hmatch
  apply hP.congr ?_ Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (heq (Ioo_subset_Icc_self hx)).symm

theorem intervalJoin_memLp {l m r : ℝ} {p : ENNReal} (hlm : l < m) (hmr : m < r)
    {gL gR : ℝ → ℂ} (hgL : MemLp gL p (volume.restrict (Ioo l m)))
    (hgR : MemLp gR p (volume.restrict (Ioo m r))) :
    MemLp (intervalJoin m gL gR) p (volume.restrict (Ioo l r)) := by
  have hL : MemLp (intervalJoin m gL gR) p (volume.restrict (Ioo l m)) := by
    apply MemLp.ae_eq ?_ hgL
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (intervalJoin_of_le hx.2.le).symm
  have hR : MemLp (intervalJoin m gL gR) p (volume.restrict (Ioo m r)) := by
    apply MemLp.ae_eq ?_ hgR
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (intervalJoin_of_lt hx.1).symm
  have hdis : Disjoint (Ioc l m) (Ioc m r) := disjoint_left.mpr fun _ hL hR =>
    (not_lt_of_ge hL.2) hR.1
  rw [restrict_Ioo_eq_restrict_Ioc] at hL hR ⊢
  rw [← Ioc_union_Ioc_eq_Ioc hlm.le hmr.le, Measure.restrict_union hdis measurableSet_Ioc]
  exact hL.add_measure hR

theorem intervalJoin_continuousOn {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    {FL FR gL gR : ℝ → ℂ}
    (hL : HasWeakDerivOn (Ioo l m) FL gL) (hR : HasWeakDerivOn (Ioo m r) FR gR)
    (hFL : ContinuousOn FL (Icc l m)) (hFR : ContinuousOn FR (Icc m r))
    (hmatch : FL m = FR m) : ContinuousOn (intervalJoin m FL FR) (Icc l r) := by
  have hGi : IntegrableOn (intervalJoin m gL gR) (Ioo l r) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hlm.trans hmr).le).mp
      (intervalJoin_intervalIntegrable hlm hmr hL.2.1 hR.2.1)
  have hP : ContinuousOn (fun x => FL l + ∫ t in l..x, intervalJoin m gL gR t) (Icc l r) := by
    simpa only [uIcc_of_le (hlm.trans hmr).le] using
      (complex_const_add_primitive_absolutelyContinuous (hlm.trans hmr).le hGi (FL l)).continuousOn
  exact hP.congr (intervalJoin_eqOn_primitive hlm hmr hL hR hFL hFR hmatch)

theorem continuousOn_memLp_interval {l r : ℝ} {F : ℝ → ℂ}
    (hF : ContinuousOn F (Icc l r)) : MemLp F 2 (volume.restrict (Ioo l r)) := by
  have hFi : IntegrableOn F (Ioo l r) volume :=
    hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  apply (memLp_two_iff_integrable_sq_norm hFi.aestronglyMeasurable).mpr
  exact (hF.norm.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem memIntervalH2_intervalJoin
    {FL FR gLeft gRight hL hR : ℝ → ℂ}
    (hFLG : HasWeakDerivOn (Ioo (-1) 0) FL gLeft)
    (hFRG : HasWeakDerivOn (Ioo 0 1) FR gRight)
    (hGLh : HasWeakDerivOn (Ioo (-1) 0) gLeft hL)
    (hGRh : HasWeakDerivOn (Ioo 0 1) gRight hR)
    (hFLc : ContinuousOn FL (Icc (-1) 0)) (hFRc : ContinuousOn FR (Icc 0 1))
    (hGLc : ContinuousOn gLeft (Icc (-1) 0)) (hGRc : ContinuousOn gRight (Icc 0 1))
    (hmatchF : FL 0 = FR 0) (hmatchG : gLeft 0 = gRight 0)
    (hhL : MemLp hL 2 (volume.restrict (Ioo (-1) 0)))
    (hhR : MemLp hR 2 (volume.restrict (Ioo 0 1))) :
    ∃ hf : MemLp (intervalJoin 0 FL FR) 2 intervalMeasure,
      MemIntervalH2 (hf.toLp (intervalJoin 0 FL FR)) := by
  have hF : ContinuousOn (intervalJoin 0 FL FR) (Icc (-1) 1) :=
    intervalJoin_continuousOn (by norm_num) (by norm_num) hFLG hFRG hFLc hFRc hmatchF
  have hG : ContinuousOn (intervalJoin 0 gLeft gRight) (Icc (-1) 1) :=
    intervalJoin_continuousOn (by norm_num) (by norm_num) hGLh hGRh hGLc hGRc hmatchG
  have hf : MemLp (intervalJoin 0 FL FR) 2 intervalMeasure := continuousOn_memLp_interval hF
  have hg : MemLp (intervalJoin 0 gLeft gRight) 2 intervalMeasure := continuousOn_memLp_interval hG
  have hh : MemLp (intervalJoin 0 hL hR) 2 intervalMeasure :=
    intervalJoin_memLp (by norm_num) (by norm_num) hhL hhR
  have hfg : HasIntervalWeakDeriv (intervalJoin 0 FL FR) (intervalJoin 0 gLeft gRight) :=
    hasWeakDerivOn_intervalJoin (by norm_num) (by norm_num) hFLG hFRG hFLc hFRc hmatchF
  have hgh : HasIntervalWeakDeriv (intervalJoin 0 gLeft gRight) (intervalJoin 0 hL hR) :=
    hasWeakDerivOn_intervalJoin (by norm_num) (by norm_num) hGLh hGRh hGLc hGRc hmatchG
  exact ⟨hf, hg.toLp (intervalJoin 0 gLeft gRight), hh.toLp (intervalJoin 0 hL hR),
    hasL2WeakDeriv_toLp hf hg hfg, hasL2WeakDeriv_toLp hg hh hgh⟩

theorem hasDirichletTrace_intervalJoin {FL FR : ℝ → ℂ}
    (hf : MemLp (intervalJoin 0 FL FR) 2 intervalMeasure)
    (hFc : ContinuousOn (intervalJoin 0 FL FR) (Icc (-1) 1))
    (hleft : FL (-1) = 0) (hright : FR 1 = 0) :
    HasDirichletTrace (hf.toLp (intervalJoin 0 FL FR)) := by
  refine ⟨intervalJoin 0 FL FR, ⟨hFc, hf.coeFn_toLp.symm⟩, ?_, ?_⟩
  · exact (intervalJoin_of_le (by norm_num : (-1 : ℝ) ≤ 0)).trans hleft
  · exact (intervalJoin_of_lt (by norm_num : (0 : ℝ) < 1)).trans hright

end Involution
