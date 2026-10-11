module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Отражение и разложение по чётности на уровне функций.
Производные здесь классические; слабые — в `WeakDerivative.lean`. -/

@[expose] public noncomputable section

namespace Involution

def reflect {E : Type*} (f : ℝ → E) : ℝ → E := fun x => f (-x)

@[simp] theorem reflect_apply {E : Type*} (f : ℝ → E) (x : ℝ) :
    reflect f x = f (-x) := rfl

@[simp] theorem reflect_reflect {E : Type*} (f : ℝ → E) :
    reflect (reflect f) = f := by
  funext x
  simp [reflect]

theorem reflect_eq_self_iff {E : Type*} (f : ℝ → E) :
    reflect f = f ↔ Function.Even f := by
  exact funext_iff

theorem reflect_eq_neg_iff {E : Type*} [Neg E] (f : ℝ → E) :
    reflect f = -f ↔ Function.Odd f := by
  exact funext_iff

def evenPart (f : ℝ → ℂ) : ℝ → ℂ := fun x => (f x + f (-x)) / 2

def oddPart (f : ℝ → ℂ) : ℝ → ℂ := fun x => (f x - f (-x)) / 2

theorem evenPart_even (f : ℝ → ℂ) : Function.Even (evenPart f) := by
  intro x
  simp [evenPart, add_comm]

theorem oddPart_odd (f : ℝ → ℂ) : Function.Odd (oddPart f) := by
  intro x
  simp only [oddPart, neg_neg]
  ring

theorem evenPart_add_oddPart (f : ℝ → ℂ) : evenPart f + oddPart f = f := by
  funext x
  change (f x + f (-x)) / 2 + (f x - f (-x)) / 2 = f x
  ring

theorem parity_decomposition_unique (f e o : ℝ → ℂ)
    (he : Function.Even e) (ho : Function.Odd o) (h : f = e + o) :
    e = evenPart f ∧ o = oddPart f := by
  subst f
  constructor <;> funext x <;> simp only [evenPart, oddPart, Pi.add_apply, he x, ho x] <;> ring

theorem evenPart_idempotent (f : ℝ → ℂ) : evenPart (evenPart f) = evenPart f := by
  funext x
  simp only [evenPart, neg_neg]
  ring

theorem oddPart_idempotent (f : ℝ → ℂ) : oddPart (oddPart f) = oddPart f := by
  funext x
  simp only [oddPart, neg_neg]
  ring

theorem evenPart_oddPart (f : ℝ → ℂ) : evenPart (oddPart f) = 0 := by
  funext x
  simp only [evenPart, oddPart, neg_neg, Pi.zero_apply]
  ring

theorem oddPart_evenPart (f : ℝ → ℂ) : oddPart (evenPart f) = 0 := by
  funext x
  simp only [evenPart, oddPart, neg_neg, Pi.zero_apply]
  ring

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_reflect {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' (-x)) : HasDerivAt (reflect f) (-f') x := by
  change HasDerivAt (fun t => f (-t)) (-f') x
  simpa only [zero_sub] using
    (HasDerivAt.comp_const_sub 0 x (by simpa only [zero_sub] using hf))

theorem deriv_reflect (f : ℝ → E) : deriv (reflect f) = -reflect (deriv f) := by
  funext x
  exact deriv_comp_neg f x

theorem second_deriv_reflect (f : ℝ → E) :
    deriv (deriv (reflect f)) = reflect (deriv (deriv f)) := by
  rw [deriv_reflect]
  funext x
  rw [deriv.neg, congrFun (deriv_reflect (deriv f)) x]
  simp

theorem deriv_even_is_odd {f : ℝ → E} (hf : Function.Even f) :
    Function.Odd (deriv f) := by
  have h := deriv_reflect f
  rw [(reflect_eq_self_iff f).2 hf] at h
  intro x
  have hx := congrFun h x
  change deriv f x = -deriv f (-x) at hx
  exact (neg_eq_iff_eq_neg.mpr hx).symm

theorem deriv_odd_is_even {f : ℝ → E} (hf : Function.Odd f) :
    Function.Even (deriv f) := by
  have h := deriv_reflect f
  rw [(reflect_eq_neg_iff f).2 hf] at h
  intro x
  have hx := congrFun h x
  simpa only [deriv.neg, Pi.neg_apply, reflect_apply, neg_inj] using hx.symm

end Derivatives

end Involution
