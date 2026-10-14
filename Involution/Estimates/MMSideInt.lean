module

public import Involution.Estimates.MMContour

/-! Integrals of real functions along the four sides of a rectangle. -/

@[expose] public noncomputable section

open Complex Set intervalIntegral

namespace Involution

/-- The sum of the integrals of `g` along the four sides of `[a, b] × [c, d]`. -/
def sideInt (g : ℂ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ x in a..b, g (x + c * I)) + (∫ x in a..b, g (x + d * I)) +
    (∫ y in c..d, g (b + y * I)) + ∫ y in c..d, g (a + y * I)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_rint_le_sideInt {f : ℂ → E} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ‖rint f a b c d‖ ≤ sideInt (fun ω => ‖f ω‖) a b c d :=
  norm_rint_le hab hcd

section real

variable {g h : ℂ → ℝ} {a b c d : ℝ}

theorem ii_real_bottom (hab : a ≤ b) (hg : ContinuousOn g (bdry a b c d)) :
    IntervalIntegrable (fun x : ℝ => g (x + c * I)) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact hg.comp (continuous_horiz c).continuousOn fun x hx => mem_bdry_bottom hx

theorem ii_real_top (hab : a ≤ b) (hg : ContinuousOn g (bdry a b c d)) :
    IntervalIntegrable (fun x : ℝ => g (x + d * I)) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact hg.comp (continuous_horiz d).continuousOn fun x hx => mem_bdry_top hx

theorem ii_real_right (hcd : c ≤ d) (hg : ContinuousOn g (bdry a b c d)) :
    IntervalIntegrable (fun y : ℝ => g (b + y * I)) MeasureTheory.volume c d := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hcd]
  exact hg.comp (continuous_vert b).continuousOn fun y hy => mem_bdry_right hy

theorem ii_real_left (hcd : c ≤ d) (hg : ContinuousOn g (bdry a b c d)) :
    IntervalIntegrable (fun y : ℝ => g (a + y * I)) MeasureTheory.volume c d := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hcd]
  exact hg.comp (continuous_vert a).continuousOn fun y hy => mem_bdry_left hy

theorem sideInt_mono (hab : a ≤ b) (hcd : c ≤ d) (hg : ContinuousOn g (bdry a b c d))
    (hh : ContinuousOn h (bdry a b c d)) (hle : ∀ ω ∈ bdry a b c d, g ω ≤ h ω) :
    sideInt g a b c d ≤ sideInt h a b c d := by
  unfold sideInt
  gcongr ?_ + ?_ + ?_ + ?_
  · exact integral_mono_on hab (ii_real_bottom hab hg) (ii_real_bottom hab hh)
      fun x hx => hle _ (mem_bdry_bottom hx)
  · exact integral_mono_on hab (ii_real_top hab hg) (ii_real_top hab hh)
      fun x hx => hle _ (mem_bdry_top hx)
  · exact integral_mono_on hcd (ii_real_right hcd hg) (ii_real_right hcd hh)
      fun y hy => hle _ (mem_bdry_right hy)
  · exact integral_mono_on hcd (ii_real_left hcd hg) (ii_real_left hcd hh)
      fun y hy => hle _ (mem_bdry_left hy)

theorem sideInt_sum {ι : Type*} (s : Finset ι) (cs : ι → ℝ) (hs : ι → ℂ → ℝ) (hab : a ≤ b)
    (hcd : c ≤ d) (hc : ∀ i ∈ s, ContinuousOn (hs i) (bdry a b c d)) :
    sideInt (fun ω => ∑ i ∈ s, cs i * hs i ω) a b c d = ∑ i ∈ s, cs i * sideInt (hs i) a b c d := by
  unfold sideInt
  rw [integral_finsetSum (fun i hi => (ii_real_bottom hab (hc i hi)).const_mul _),
    integral_finsetSum (fun i hi => (ii_real_top hab (hc i hi)).const_mul _),
    integral_finsetSum (fun i hi => (ii_real_right hcd (hc i hi)).const_mul _),
    integral_finsetSum (fun i hi => (ii_real_left hcd (hc i hi)).const_mul _)]
  simp only [integral_const_mul, ← Finset.sum_add_distrib, mul_add]

end real

end Involution
