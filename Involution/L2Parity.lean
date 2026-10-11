module

public import Involution.L2Reflection
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Module

/-! Ортогональное разложение L² на собственные подпространства отражения. -/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace Involution

def l2EvenPart (f : IntervalL2) : IntervalL2 := (2 : ℂ)⁻¹ • (f + l2Reflect f)

def l2OddPart (f : IntervalL2) : IntervalL2 := (2 : ℂ)⁻¹ • (f - l2Reflect f)

theorem l2EvenPart_fixed (f : IntervalL2) : l2Reflect (l2EvenPart f) = l2EvenPart f := by
  simp only [l2EvenPart, map_smul, map_add, l2Reflect_involution]
  rw [add_comm]

theorem l2OddPart_neg (f : IntervalL2) : l2Reflect (l2OddPart f) = -l2OddPart f := by
  simp only [l2OddPart, map_smul, map_sub, l2Reflect_involution]
  module

theorem l2EvenPart_add_l2OddPart (f : IntervalL2) : l2EvenPart f + l2OddPart f = f := by
  simp only [l2EvenPart, l2OddPart]
  module

theorem l2Parity_unique (f e o : IntervalL2)
    (he : l2Reflect e = e) (ho : l2Reflect o = -o) (h : f = e + o) :
    e = l2EvenPart f ∧ o = l2OddPart f := by
  subst f
  simp only [l2EvenPart, l2OddPart, map_add, he, ho]
  constructor <;> module

theorem l2Reflect_inner (f g : IntervalL2) :
    ⟪l2Reflect f, l2Reflect g⟫_ℂ = ⟪f, g⟫_ℂ :=
  l2Reflect.inner_map_map f g

theorem l2Parity_orthogonal (e o : IntervalL2)
    (he : l2Reflect e = e) (ho : l2Reflect o = -o) : ⟪e, o⟫_ℂ = 0 := by
  have h := l2Reflect_inner e o
  rw [he, ho, inner_neg_right] at h
  have hsum : ⟪e, o⟫_ℂ + ⟪e, o⟫_ℂ = 0 := by
    calc
      ⟪e, o⟫_ℂ + ⟪e, o⟫_ℂ = -⟪e, o⟫_ℂ + ⟪e, o⟫_ℂ :=
        congrArg (fun z : ℂ => z + ⟪e, o⟫_ℂ) h.symm
      _ = 0 := neg_add_cancel _
  have hmul : (2 : ℂ) * ⟪e, o⟫_ℂ = 0 := by simpa only [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

theorem l2EvenPart_orthogonal_l2OddPart (f g : IntervalL2) :
    ⟪l2EvenPart f, l2OddPart g⟫_ℂ = 0 :=
  l2Parity_orthogonal _ _ (l2EvenPart_fixed f) (l2OddPart_neg g)

end Involution
