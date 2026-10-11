module

public import Involution.ModelBasis

/-! Модельный базис состоит из собственных векторов постоянного оператора.
Полнота и базис Рисса взяты из `ModelBasis.lean`, собственные уравнения — из
`SobolevModes.lean`. -/

@[expose] public noncomputable section

namespace Involution

def constantModelEigenvalue (c : ℝ) : ℕ ⊕ ℕ → ℝ :=
  Sum.elim
    (fun n => (1 + c) * ((((n : ℝ) + 1 / 2) * Real.pi) ^ 2))
    (fun n => (1 - c) * ((((n : ℝ) + 1) * Real.pi) ^ 2))

theorem constantModelVector_memDirichletH2 (i : ℕ ⊕ ℕ) :
    MemDirichletH2 (constantModelVector i) := by
  cases i with
  | inl n => exact cosineMode_memDirichletH2 n
  | inr n =>
    simpa only [constantModelVector, Sum.elim_inr, Nat.cast_add, Nat.cast_one] using
      sineMode_memDirichletH2 (n + 1)

theorem constantModel_eigen_equation (c : ℝ) (i : ℕ ⊕ ℕ) :
    constantSobolevOperator c (constantModelVector i)
      (constantModelVector_memDirichletH2 i).1 =
      ((constantModelEigenvalue c i : ℝ) : ℂ) • constantModelVector i := by
  cases i with
  | inl n =>
    simpa only [constantModelVector, constantModelEigenvalue, Sum.elim_inl] using
      (constant_cosine_eigenpair c n).2.2
  | inr n =>
    simpa only [constantModelVector, constantModelEigenvalue, Sum.elim_inr,
      Nat.cast_add, Nat.cast_one] using
      (constant_sine_eigenpair c (n + 1) (Nat.succ_pos n)).2.2

theorem constantModelRieszBasis_eigen_equation (c : ℝ) (i : ℕ ⊕ ℕ) :
    ∃ hf : MemDirichletH2 (constantModelRieszBasis.vector i),
      constantSobolevOperator c (constantModelRieszBasis.vector i) hf.1 =
        ((constantModelEigenvalue c i : ℝ) : ℂ) • constantModelRieszBasis.vector i := by
  rw [constantModelRieszBasis_vector]
  exact ⟨constantModelVector_memDirichletH2 i, constantModel_eigen_equation c i⟩

end Involution
