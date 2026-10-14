module

public import Involution.Setup.Reflection
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-! Явные собственные пары постоянного коэффициента на уровне классических функций.
Принадлежность области `H²` доказана в `Involution.Model.SobolevModes`, полнота — в
`Involution.Model.ModelBasis`. -/

@[expose] public noncomputable section

namespace Involution

def cosineWave (k : ℝ) (x : ℝ) : ℂ := Real.cos (k * x)
def sineWave (k : ℝ) (x : ℝ) : ℂ := Real.sin (k * x)

theorem cosineWave_even (k : ℝ) : Function.Even (cosineWave k) := by
  intro x
  simp [cosineWave]

theorem sineWave_odd (k : ℝ) : Function.Odd (sineWave k) := by
  intro x
  simp [sineWave]

theorem hasDerivAt_cosineWave (k x : ℝ) :
    HasDerivAt (cosineWave k) (-(k : ℂ) * sineWave k x) x := by
  change HasDerivAt (fun y : ℝ => (Real.cos (k * y) : ℂ))
    (-(k : ℂ) * (Real.sin (k * x) : ℂ)) x
  simpa only [id_eq, Complex.ofReal_one, mul_one, Complex.ofReal_neg,
    Complex.ofReal_mul, mul_neg, neg_mul, mul_comm] using
    (((hasDerivAt_id x).const_mul k).cos).ofReal_comp

theorem hasDerivAt_sineWave (k x : ℝ) :
    HasDerivAt (sineWave k) ((k : ℂ) * cosineWave k x) x := by
  change HasDerivAt (fun y : ℝ => (Real.sin (k * y) : ℂ))
    ((k : ℂ) * (Real.cos (k * x) : ℂ)) x
  simpa only [id_eq, Complex.ofReal_one, mul_one, Complex.ofReal_mul, mul_comm] using
    (((hasDerivAt_id x).const_mul k).sin).ofReal_comp

theorem second_deriv_cosineWave (k : ℝ) :
    deriv (deriv (cosineWave k)) = fun x => -(k : ℂ) ^ 2 * cosineWave k x := by
  have hfirst : deriv (cosineWave k) = fun x => -(k : ℂ) * sineWave k x :=
    funext fun x => (hasDerivAt_cosineWave k x).deriv
  rw [hfirst]
  funext x
  rw [((hasDerivAt_sineWave k x).const_mul (-(k : ℂ))).deriv]
  ring

theorem second_deriv_sineWave (k : ℝ) :
    deriv (deriv (sineWave k)) = fun x => -(k : ℂ) ^ 2 * sineWave k x := by
  have hfirst : deriv (sineWave k) = fun x => (k : ℂ) * cosineWave k x :=
    funext fun x => (hasDerivAt_sineWave k x).deriv
  rw [hfirst]
  funext x
  rw [((hasDerivAt_cosineWave k x).const_mul (k : ℂ)).deriv]
  ring

def classicalOperator (a : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv f) x - (a x : ℂ) * deriv (deriv f) (-x)

theorem constant_cosine_eigen_equation (c k x : ℝ) :
    classicalOperator (fun _ => c) (cosineWave k) x =
      (((1 + c) * k ^ 2 : ℝ) : ℂ) * cosineWave k x := by
  simp only [classicalOperator, second_deriv_cosineWave, cosineWave_even k x,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  ring

theorem constant_sine_eigen_equation (c k x : ℝ) :
    classicalOperator (fun _ => c) (sineWave k) x =
      (((1 - c) * k ^ 2 : ℝ) : ℂ) * sineWave k x := by
  simp only [classicalOperator, second_deriv_sineWave, sineWave_odd k x,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  ring

theorem cosine_dirichlet_boundary (n : ℕ) :
    cosineWave (((n : ℝ) + 1 / 2) * Real.pi) (-1) = 0 ∧
    cosineWave (((n : ℝ) + 1 / 2) * Real.pi) 1 = 0 := by
  have hangle : ((n : ℝ) + 1 / 2) * Real.pi = (n : ℝ) * Real.pi + Real.pi / 2 := by ring
  have hright : cosineWave (((n : ℝ) + 1 / 2) * Real.pi) 1 = 0 := by
    change (Real.cos ((((n : ℝ) + 1 / 2) * Real.pi) * 1) : ℂ) = 0
    rw [mul_one, hangle, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
    simp
  exact ⟨by simpa only [cosineWave_even _ 1] using hright, hright⟩

theorem sine_dirichlet_boundary (n : ℕ) :
    sineWave ((n : ℝ) * Real.pi) (-1) = 0 ∧
    sineWave ((n : ℝ) * Real.pi) 1 = 0 := by
  simp [sineWave, Real.sin_nat_mul_pi]

theorem cosineWave_ne_zero (k : ℝ) : cosineWave k ≠ 0 := by
  intro h
  have hx := congrFun h 0
  simp [cosineWave] at hx

theorem sineMode_ne_zero (n : ℕ) (hn : 0 < n) : sineWave ((n : ℝ) * Real.pi) ≠ 0 := by
  intro h
  have hd := congrArg (fun f : ℝ → ℂ => deriv f 0) h
  rw [(hasDerivAt_sineWave ((n : ℝ) * Real.pi) 0).deriv] at hd
  have hnzero : n = 0 := by simpa [cosineWave] using hd
  exact hn.ne' hnzero

end Involution
