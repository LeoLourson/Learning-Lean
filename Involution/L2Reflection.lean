module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Отражение в L²(-1,1; ℂ), определённое на классах равенства почти всюду. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

def intervalMeasure : Measure ℝ := volume.restrict (Set.Ioo (-1) 1)

abbrev IntervalL2 := Lp ℂ 2 intervalMeasure

theorem neg_preimage_interval :
    (fun x : ℝ => -x) ⁻¹' Set.Ioo (-1) 1 = Set.Ioo (-1) 1 := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem interval_neg_measurePreserving :
    MeasurePreserving (fun x : ℝ => -x) intervalMeasure intervalMeasure := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (-1 : ℝ) 1))
  simpa only [neg_preimage_interval, intervalMeasure] using h

def l2Reflect : IntervalL2 →ₗᵢ[ℂ] IntervalL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) interval_neg_measurePreserving

theorem l2Reflect_ae (f : IntervalL2) :
    l2Reflect f =ᵐ[intervalMeasure] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f interval_neg_measurePreserving

theorem l2Reflect_norm (f : IntervalL2) : ‖l2Reflect f‖ = ‖f‖ :=
  l2Reflect.norm_map f

@[simp] theorem l2Reflect_involution (f : IntervalL2) : l2Reflect (l2Reflect f) = f := by
  apply Lp.ext
  have h := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp (l2Reflect_ae f)
  filter_upwards [l2Reflect_ae (l2Reflect f), h] with x hx hy
  exact hx.trans (by simpa only [Function.comp_def, neg_neg] using hy)

def l2ReflectionEquiv : IntervalL2 ≃ₗᵢ[ℂ] IntervalL2 :=
  LinearIsometryEquiv.ofSurjective l2Reflect (fun f => ⟨l2Reflect f, l2Reflect_involution f⟩)

end Involution
