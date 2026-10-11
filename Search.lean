import Involution.Reduction

-- An intentionally interactive search example from this project's subject.
example (a b : ℝ) : (Involution.principalMatrix a b).det = 1 - a * b := by
  exact?
