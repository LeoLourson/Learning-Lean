module

public import Involution.IntervalReflection
public import Involution.FoldingIntegral
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-! Унитарное складывание интервала в две скалярные компоненты.
Пространство пар снабжено евклидовой нормой `WithLp 2`, а не максимумом
норм компонент. Все отображения определены на классах п.в. равенства. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

def halfIntervalMeasure : Measure ℝ := volume.restrict (Ioo 0 1)
abbrev HalfIntervalL2 := Lp ℂ 2 halfIntervalMeasure
abbrev FoldedL2 := WithLp 2 (HalfIntervalL2 × HalfIntervalL2)

theorem halfIntervalMeasure_le : halfIntervalMeasure ≤ intervalMeasure := by
  apply Measure.restrict_mono_set
  intro x hx
  exact ⟨by linarith [hx.1], hx.2⟩

def l2RestrictHalf (f : IntervalL2) : HalfIntervalL2 :=
  (MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp f)).toLp f

theorem l2RestrictHalf_ae (f : IntervalL2) :
    l2RestrictHalf f =ᵐ[halfIntervalMeasure] f := MemLp.coeFn_toLp _

def l2RestrictHalfLinear : IntervalL2 →ₗ[ℂ] HalfIntervalL2 where
  toFun := l2RestrictHalf
  map_add' f g := by
    apply Lp.ext
    have hfg := (Lp.coeFn_add f g).filter_mono (ae_mono halfIntervalMeasure_le)
    filter_upwards [l2RestrictHalf_ae (f + g), l2RestrictHalf_ae f,
      l2RestrictHalf_ae g, Lp.coeFn_add (l2RestrictHalf f) (l2RestrictHalf g), hfg]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁, h₄, h₅, h₂, h₃]
  map_smul' c f := by
    change l2RestrictHalf (c • f) = c • l2RestrictHalf f
    apply Lp.ext
    have hcf := (Lp.coeFn_smul c f).filter_mono (ae_mono halfIntervalMeasure_le)
    filter_upwards [l2RestrictHalf_ae (c • f), l2RestrictHalf_ae f,
      Lp.coeFn_smul c (l2RestrictHalf f), hcf] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply] at h₃ h₄
    rw [h₁, h₃, h₄, h₂]

def l2FoldLinear : IntervalL2 →ₗ[ℂ] FoldedL2 :=
  (WithLp.linearEquiv 2 ℂ (HalfIntervalL2 × HalfIntervalL2)).symm.toLinearMap.comp
    (l2RestrictHalfLinear.prod (l2RestrictHalfLinear.comp l2Reflect.toLinearMap))

theorem l2Fold_fst_ae (f : IntervalL2) :
    (l2FoldLinear f).fst =ᵐ[halfIntervalMeasure] f := l2RestrictHalf_ae f

theorem l2Fold_snd_ae (f : IntervalL2) :
    (l2FoldLinear f).snd =ᵐ[halfIntervalMeasure] reflect f :=
  (l2RestrictHalf_ae (l2Reflect f)).trans
    ((l2Reflect_ae f).filter_mono (ae_mono halfIntervalMeasure_le))

theorem l2_norm_sq_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  have hself : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f
  rw [← hself, L2.inner_def]
  have hcast := integral_ofReal (𝕜 := ℂ) (μ := μ) (f := fun x => ‖f x‖ ^ 2)
  calc
    _ = ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        push_cast
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f x)
    _ = _ := hcast

theorem integral_restrict_Ioo_eq_interval (l r : ℝ) (hlr : l ≤ r) (f : ℝ → ℝ) :
    (∫ x in Ioo l r, f x) = ∫ x in l..r, f x := by
  rw [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo]

theorem l2Fold_norm (f : IntervalL2) : ‖l2FoldLinear f‖ = ‖f‖ := by
  have hf : Integrable (fun x => ‖f x‖ ^ 2) halfIntervalMeasure :=
    (memLp_two_iff_integrable_sq_norm
      (MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp f)).aestronglyMeasurable).mp
      (MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp f))
  have hRf : Integrable (fun x => ‖reflect f x‖ ^ 2) halfIntervalMeasure := by
    have h := MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp (l2Reflect f))
    have h' : MemLp (reflect f) 2 halfIntervalMeasure := MemLp.ae_eq
      ((l2Reflect_ae f).filter_mono (ae_mono halfIntervalMeasure_le)) h
    exact (memLp_two_iff_integrable_sq_norm h'.aestronglyMeasurable).mp h'
  have hsq : ‖l2FoldLinear f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, l2_norm_sq_integral, l2_norm_sq_integral,
      l2_norm_sq_integral]
    have hfst : (∫ x, ‖(l2FoldLinear f).fst x‖ ^ 2 ∂halfIntervalMeasure) =
        ∫ x, ‖f x‖ ^ 2 ∂halfIntervalMeasure :=
      integral_congr_ae ((l2Fold_fst_ae f).mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)
    have hsnd : (∫ x, ‖(l2FoldLinear f).snd x‖ ^ 2 ∂halfIntervalMeasure) =
        ∫ x, ‖reflect f x‖ ^ 2 ∂halfIntervalMeasure :=
      integral_congr_ae ((l2Fold_snd_ae f).mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)
    rw [hfst, hsnd, ← integral_add hf hRf]
    change (∫ x in Ioo (0 : ℝ) 1, (‖f x‖ ^ 2 + ‖f (-x)‖ ^ 2)) =
      ∫ x in Ioo (-1 : ℝ) 1, ‖f x‖ ^ 2
    rw [integral_restrict_Ioo_eq_interval 0 1 (by norm_num),
      integral_restrict_Ioo_eq_interval (-1) 1 (by norm_num)]
    exact (l2_folding_sq_norm f).symm
  nlinarith [norm_nonneg (l2FoldLinear f), norm_nonneg f]

def l2Fold : IntervalL2 →ₗᵢ[ℂ] FoldedL2 where
  toLinearMap := l2FoldLinear
  norm_map' := l2Fold_norm

theorem negativeHalfMeasure_le : volume.restrict (Ioo (-1 : ℝ) 0) ≤ intervalMeasure := by
  apply Measure.restrict_mono_set
  intro x hx
  exact ⟨hx.1, by linarith [hx.2]⟩

theorem reflectedHalf_measurePreserving :
    MeasurePreserving (fun x : ℝ => -x) halfIntervalMeasure
      (volume.restrict (Ioo (-1 : ℝ) 0)) := by
  simpa only [neg_zero, neg_neg, halfIntervalMeasure] using
    interval_reflect_measurePreserving (-1) 0

theorem reflectedJoin_memLp (U : FoldedL2) :
    MemLp (intervalJoin 0 (reflect U.snd) U.fst) 2 intervalMeasure := by
  have hv : MemLp (reflect U.snd) 2 (volume.restrict (Ioo (-1 : ℝ) 0)) := by
    simpa only [neg_zero] using memLp_reflect_interval (Lp.memLp U.snd)
  exact intervalJoin_memLp (by norm_num) (by norm_num) hv (Lp.memLp U.fst)

def l2Unfold (U : FoldedL2) : IntervalL2 :=
  (reflectedJoin_memLp U).toLp (intervalJoin 0 (reflect U.snd) U.fst)

theorem l2Unfold_ae (U : FoldedL2) :
    l2Unfold U =ᵐ[intervalMeasure] intervalJoin 0 (reflect U.snd) U.fst :=
  MemLp.coeFn_toLp _

theorem l2Fold_l2Unfold (U : FoldedL2) : l2Fold (l2Unfold U) = U := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply Lp.ext
    have hU := (l2Unfold_ae U).filter_mono (ae_mono halfIntervalMeasure_le)
    filter_upwards [l2Fold_fst_ae (l2Unfold U), hU,
      ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))]
      with x hx hux hxpos
    exact hx.trans (hux.trans (intervalJoin_of_lt hxpos.1))
  · apply Lp.ext
    have hU := reflectedHalf_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      ((l2Unfold_ae U).filter_mono (ae_mono negativeHalfMeasure_le))
    filter_upwards [l2Fold_snd_ae (l2Unfold U), hU,
      ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))]
      with x hx hux hxpos
    change l2Unfold U (-x) = intervalJoin 0 (reflect U.snd) U.fst (-x) at hux
    change (l2FoldLinear (l2Unfold U)).snd x = U.snd x
    rw [hx, reflect_apply, hux, intervalJoin_of_le (by linarith [hxpos.1])]
    simp only [reflect_apply, neg_neg]

def l2FoldingEquiv : IntervalL2 ≃ₗᵢ[ℂ] FoldedL2 :=
  LinearIsometryEquiv.ofSurjective l2Fold (fun U => ⟨l2Unfold U, l2Fold_l2Unfold U⟩)

theorem l2FoldingEquiv_symm_apply (U : FoldedL2) :
    l2FoldingEquiv.symm U = l2Unfold U := by
  apply l2Fold.injective
  exact (l2FoldingEquiv.apply_symm_apply U).trans (l2Fold_l2Unfold U).symm

theorem l2Unfold_l2Fold (f : IntervalL2) : l2Unfold (l2Fold f) = f := by
  apply l2Fold.injective
  exact l2Fold_l2Unfold (l2Fold f)

end Involution
