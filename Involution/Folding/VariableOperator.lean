module

public import Involution.Setup.IntervalOperator
public import Involution.Folding.L2Folding
public import Mathlib.MeasureTheory.Function.Holder

/-! Переменный оператор с коэффициентом класса `L∞`.
Библиотечное умножение Гёльдера задаётся на классах п.в. равенства;
непрерывные представители коэффициента и его следы здесь не нужны. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

abbrev IntervalLInfinity := Lp ℂ ∞ intervalMeasure

def realIntervalCoefficient (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure) :
    IntervalLInfinity := ha.ofReal.toLp (fun x => (a x : ℂ))

theorem realIntervalCoefficient_ae (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure) :
    realIntervalCoefficient a ha =ᵐ[intervalMeasure] fun x => (a x : ℂ) :=
  MemLp.coeFn_toLp _

def boundedMultiplierLinear {μ : Measure ℝ} (a : Lp ℂ ∞ μ) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := a • f
  map_add' f g := Lp.add_smul a f g
  map_smul' c f := by
    change a • (c • f) = c • (a • f)
    exact (Lp.smul_comm c a f).symm

def boundedMultiplier {μ : Measure ℝ} (a : Lp ℂ ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (boundedMultiplierLinear a).mkContinuous ‖a‖ (fun f => Lp.norm_smul_le a f)

theorem boundedMultiplier_ae {μ : Measure ℝ} (a : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    boundedMultiplier a f =ᵐ[μ] fun x => a x * f x := by
  change (a • f : Lp ℂ 2 μ) =ᵐ[μ] fun x => a x * f x
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ENNReal)) a f] with x hx
  exact hx

theorem boundedMultiplier_norm_le {μ : Measure ℝ} (a : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    ‖boundedMultiplier a f‖ ≤ ‖a‖ * ‖f‖ := Lp.norm_smul_le a f

def variableSobolevOperator (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemIntervalH2 f) : IntervalL2 :=
  -secondWeakDeriv f hf - boundedMultiplier a (l2Reflect (secondWeakDeriv f hf))

theorem variableSobolevOperator_ae (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemIntervalH2 f) :
    variableSobolevOperator a f hf =ᵐ[intervalMeasure] fun x =>
      -secondWeakDeriv f hf x - a x * secondWeakDeriv f hf (-x) := by
  let D := secondWeakDeriv f hf
  filter_upwards [Lp.coeFn_sub (-D) (boundedMultiplier a (l2Reflect D)),
    Lp.coeFn_neg D, boundedMultiplier_ae a (l2Reflect D), l2Reflect_ae D]
    with x hx hn hm hr
  change (-D - boundedMultiplier a (l2Reflect D)) x = -D x - a x * D (-x)
  simp only [Pi.sub_apply] at hx
  rw [hx, hn, hm, hr]
  rfl

theorem variableSobolevOperator_norm_le (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemIntervalH2 f) :
    ‖variableSobolevOperator a f hf‖ ≤ (1 + ‖a‖) * ‖secondWeakDeriv f hf‖ := by
  let D := secondWeakDeriv f hf
  change ‖-D - boundedMultiplier a (l2Reflect D)‖ ≤ (1 + ‖a‖) * ‖D‖
  have hb := boundedMultiplier_norm_le a (l2Reflect D)
  rw [l2Reflect_norm] at hb
  calc
    _ ≤ ‖-D‖ + ‖boundedMultiplier a (l2Reflect D)‖ := norm_sub_le (-D) _
    _ ≤ ‖D‖ + ‖a‖ * ‖D‖ := by
      rw [norm_neg]
      exact add_le_add_right hb ‖D‖
    _ = _ := by ring

def coefficientHalf (a : IntervalLInfinity) : Lp ℂ ∞ halfIntervalMeasure :=
  (MemLp.mono_measure halfIntervalMeasure_le (Lp.memLp a)).toLp a

def coefficientReflectedHalf (a : IntervalLInfinity) : Lp ℂ ∞ halfIntervalMeasure :=
  (MemLp.mono_measure halfIntervalMeasure_le
    ((Lp.memLp a).comp_measurePreserving interval_neg_measurePreserving)).toLp (reflect a)

theorem coefficientHalf_ae (a : IntervalLInfinity) :
    coefficientHalf a =ᵐ[halfIntervalMeasure] a := MemLp.coeFn_toLp _

theorem coefficientReflectedHalf_ae (a : IntervalLInfinity) :
    coefficientReflectedHalf a =ᵐ[halfIntervalMeasure] reflect a := MemLp.coeFn_toLp _

def foldedPrincipal (a : IntervalLInfinity) (U : FoldedL2) : FoldedL2 :=
  WithLp.toLp 2
    (U.fst + boundedMultiplier (coefficientHalf a) U.snd,
      boundedMultiplier (coefficientReflectedHalf a) U.fst + U.snd)

theorem foldedPrincipal_fst_ae (a : IntervalLInfinity) (U : FoldedL2) :
    (foldedPrincipal a U).fst =ᵐ[halfIntervalMeasure]
      fun x => U.fst x + a x * U.snd x := by
  filter_upwards [Lp.coeFn_add U.fst (boundedMultiplier (coefficientHalf a) U.snd),
    boundedMultiplier_ae (coefficientHalf a) U.snd, coefficientHalf_ae a] with x hx hm ha
  change (U.fst + boundedMultiplier (coefficientHalf a) U.snd) x = _
  simp only [Pi.add_apply] at hx
  rw [hx, hm, ha]

theorem foldedPrincipal_snd_ae (a : IntervalLInfinity) (U : FoldedL2) :
    (foldedPrincipal a U).snd =ᵐ[halfIntervalMeasure]
      fun x => a (-x) * U.fst x + U.snd x := by
  filter_upwards [Lp.coeFn_add (boundedMultiplier (coefficientReflectedHalf a) U.fst) U.snd,
    boundedMultiplier_ae (coefficientReflectedHalf a) U.fst,
    coefficientReflectedHalf_ae a] with x hx hm ha
  change (boundedMultiplier (coefficientReflectedHalf a) U.fst + U.snd) x = _
  simp only [Pi.add_apply] at hx
  rw [hx, hm, ha]
  rfl

theorem variableSobolevOperator_fold (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemIntervalH2 f) :
    l2Fold (variableSobolevOperator a f hf) =
      -foldedPrincipal a (l2Fold (secondWeakDeriv f hf)) := by
  let D := secondWeakDeriv f hf
  let L := variableSobolevOperator a f hf
  let U := l2Fold D
  have hL := (variableSobolevOperator_ae a f hf).filter_mono (ae_mono halfIntervalMeasure_le)
  have hRL := (interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (variableSobolevOperator_ae a f hf)).filter_mono (ae_mono halfIntervalMeasure_le)
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [l2Fold_fst_ae L, hL, foldedPrincipal_fst_ae a U,
      l2Fold_fst_ae D, l2Fold_snd_ae D, Lp.coeFn_neg (foldedPrincipal a U).fst]
      with x hx hl hp hd hrd hn
    change (l2FoldLinear L).fst x = (-(foldedPrincipal a U).fst) x
    simp only [Pi.neg_apply] at hn
    change U.fst x = D x at hd
    change U.snd x = reflect D x at hrd
    rw [hx, hn, hp, hd, hrd]
    change L x = -(D x + a x * D (-x))
    change L x = -D x - a x * D (-x) at hl
    rw [hl]
    ring
  · apply Lp.ext
    filter_upwards [l2Fold_snd_ae L, hRL, foldedPrincipal_snd_ae a U,
      l2Fold_fst_ae D, l2Fold_snd_ae D, Lp.coeFn_neg (foldedPrincipal a U).snd]
      with x hx hl hp hd hrd hn
    change (l2FoldLinear L).snd x = (-(foldedPrincipal a U).snd) x
    simp only [Pi.neg_apply] at hn
    change U.fst x = D x at hd
    change U.snd x = reflect D x at hrd
    rw [hx, hn, hp, hd, hrd]
    change L (-x) = -(a (-x) * D x + D (-x))
    change L (-x) = -D (-x) - a (-x) * D (-(-x)) at hl
    rw [neg_neg] at hl
    rw [hl]
    ring

end Involution
