module

public import Involution.Folding.L2Folding
public import Involution.Setup.IntervalRegularity

/-! Область Дирихле после унитарного складывания.
Определение хранит непрерывные представители функции и первой производной;
вторая производная задаётся только почти всюду. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

structure FoldedDirichletData (U : FoldedL2) where
  u : ℝ → ℂ
  v : ℝ → ℂ
  u₁ : ℝ → ℂ
  v₁ : ℝ → ℂ
  u₂ : ℝ → ℂ
  v₂ : ℝ → ℂ
  hu : HasWeakDerivOn (Ioo 0 1) u u₁
  hv : HasWeakDerivOn (Ioo 0 1) v v₁
  hu₁ : HasWeakDerivOn (Ioo 0 1) u₁ u₂
  hv₁ : HasWeakDerivOn (Ioo 0 1) v₁ v₂
  huc : ContinuousOn u (Icc 0 1)
  hvc : ContinuousOn v (Icc 0 1)
  hu₁c : ContinuousOn u₁ (Icc 0 1)
  hv₁c : ContinuousOn v₁ (Icc 0 1)
  hu_rep : u =ᵐ[halfIntervalMeasure] U.fst
  hv_rep : v =ᵐ[halfIntervalMeasure] U.snd
  hmatch : u 0 = v 0
  hmatch₁ : u₁ 0 + v₁ 0 = 0
  hu₂ : MemLp u₂ 2 halfIntervalMeasure
  hv₂ : MemLp v₂ 2 halfIntervalMeasure
  huend : u 1 = 0
  hvend : v 1 = 0

def MemFoldedDirichletH2 (U : FoldedL2) : Prop := Nonempty (FoldedDirichletData U)

theorem FoldedDirichletData.derivatives_unique {U : FoldedL2}
    (d e : FoldedDirichletData U) :
    d.u₁ =ᵐ[halfIntervalMeasure] e.u₁ ∧
      d.v₁ =ᵐ[halfIntervalMeasure] e.v₁ ∧
      d.u₂ =ᵐ[halfIntervalMeasure] e.u₂ ∧
      d.v₂ =ᵐ[halfIntervalMeasure] e.v₂ := by
  have hu₁ : d.u₁ =ᵐ[halfIntervalMeasure] e.u₁ := HasWeakDerivOn.unique isOpen_Ioo
    (d.hu.congr (d.hu_rep.trans e.hu_rep.symm) Filter.EventuallyEq.rfl) e.hu
  have hv₁ : d.v₁ =ᵐ[halfIntervalMeasure] e.v₁ := HasWeakDerivOn.unique isOpen_Ioo
    (d.hv.congr (d.hv_rep.trans e.hv_rep.symm) Filter.EventuallyEq.rfl) e.hv
  exact ⟨hu₁, hv₁,
    HasWeakDerivOn.unique isOpen_Ioo (d.hu₁.congr hu₁ Filter.EventuallyEq.rfl) e.hu₁,
    HasWeakDerivOn.unique isOpen_Ioo (d.hv₁.congr hv₁ Filter.EventuallyEq.rfl) e.hv₁⟩

theorem MemDirichletH2.fold {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemFoldedDirichletH2 (l2Fold f) := by
  obtain ⟨g, h, hfg, hgh⟩ := hf.1
  obtain ⟨g', F, G, hfg', hF, hG, _, _, _⟩ := hf.1.exists_regular_pair
  have hg : g' = g := hfg'.unique hfg
  subst g'
  have hFG : HasIntervalWeakDeriv F G := hfg.congr hF.2.symm hG.2.symm
  have hGH : HasIntervalWeakDeriv G h := hgh.congr hG.2.symm Filter.EventuallyEq.rfl
  obtain ⟨hu, hu₁, hv, hv₁⟩ := weak_derivatives_fold hFG hGH
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hRF : Involution.reflect F =ᵐ[halfIntervalMeasure] Involution.reflect f :=
    (interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp hF.2).filter_mono
      (ae_mono halfIntervalMeasure_le)
  have hRcF : ContinuousOn (Involution.reflect F) (Icc (-1) 1) := by
    simpa only [neg_neg] using continuousOn_reflect_interval hF.1
  have hRcG : ContinuousOn (Involution.reflect G) (Icc (-1) 1) := by
    simpa only [neg_neg] using continuousOn_reflect_interval hG.1
  have hh : MemLp (Involution.reflect h) 2 halfIntervalMeasure := by
    have hR := MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp (l2Reflect h))
    exact MemLp.ae_eq ((l2Reflect_ae h).filter_mono (ae_mono halfIntervalMeasure_le)) hR
  have hend := hf.2.boundary hF
  refine ⟨{
    u := F, v := Involution.reflect F, u₁ := G, v₁ := -Involution.reflect G
    u₂ := h, v₂ := Involution.reflect h
    hu := hu, hv := hv, hu₁ := hu₁, hv₁ := hv₁
    huc := hF.1.mono hsub, hvc := hRcF.mono hsub
    hu₁c := hG.1.mono hsub, hv₁c := (hRcG.mono hsub).neg
    hu_rep := (hF.2.filter_mono (ae_mono halfIntervalMeasure_le)).trans
      (l2Fold_fst_ae f).symm
    hv_rep := hRF.trans (l2Fold_snd_ae f).symm
    hmatch := (folded_matching_traces F G).1
    hmatch₁ := (folded_matching_traces F G).2
    hu₂ := MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp h)
    hv₂ := hh, huend := hend.2, hvend := ?_ }⟩
  simpa only [reflect_apply] using hend.1

theorem MemFoldedDirichletH2.unfold {U : FoldedL2} (hU : MemFoldedDirichletH2 U) :
    MemDirichletH2 (l2Unfold U) := by
  obtain ⟨d⟩ := hU
  obtain ⟨hf, hH2⟩ := memDirichletH2_reflectedJoin d.hu d.hv d.hu₁ d.hv₁
    d.huc d.hvc d.hu₁c d.hv₁c d.hmatch d.hmatch₁ d.hu₂ d.hv₂ d.huend d.hvend
  have hjoin : intervalJoin 0 (reflect d.v) d.u =ᵐ[intervalMeasure]
      intervalJoin 0 (reflect U.snd) U.fst := by
    have hleft : reflect d.v =ᵐ[volume.restrict (Ioo (-1 : ℝ) 0)] reflect U.snd := by
      have h := (interval_reflect_measurePreserving 0 1).quasiMeasurePreserving.ae_eq_comp
        d.hv_rep
      change (fun x => d.v (-x)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 0)]
        (fun x => U.snd (-x))
      simpa only [neg_zero, Function.comp_def] using h
    have hL : ∀ᵐ x ∂volume, x ∈ Ioo (-1 : ℝ) 0 → reflect d.v x = reflect U.snd x :=
      (ae_restrict_iff' measurableSet_Ioo).mp hleft
    have hR : ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 → d.u x = U.fst x :=
      (ae_restrict_iff' measurableSet_Ioo).mp d.hu_rep
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hL, hR, volume.ae_ne (0 : ℝ)] with x hxL hxR hx0 hx
    by_cases hxneg : x ≤ 0
    · rw [intervalJoin_of_le hxneg, intervalJoin_of_le hxneg]
      exact hxL ⟨hx.1, lt_of_le_of_ne hxneg hx0⟩
    · have hxpos : 0 < x := lt_of_not_ge hxneg
      rw [intervalJoin_of_lt hxpos, intervalJoin_of_lt hxpos]
      exact hxR ⟨hxpos, hx.2⟩
  have heq : hf.toLp (intervalJoin 0 (reflect d.v) d.u) = l2Unfold U :=
    Lp.ext ((hf.coeFn_toLp.trans hjoin).trans (l2Unfold_ae U).symm)
  exact heq ▸ hH2

theorem memDirichletH2_iff_fold (f : IntervalL2) :
    MemDirichletH2 f ↔ MemFoldedDirichletH2 (l2Fold f) := by
  refine ⟨MemDirichletH2.fold, fun hf => ?_⟩
  simpa only [l2Unfold_l2Fold] using hf.unfold

theorem memFoldedDirichletH2_iff_unfold (U : FoldedL2) :
    MemFoldedDirichletH2 U ↔ MemDirichletH2 (l2Unfold U) := by
  refine ⟨MemFoldedDirichletH2.unfold, fun hf => ?_⟩
  simpa only [l2Fold_l2Unfold] using hf.fold

end Involution
