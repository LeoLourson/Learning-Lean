import Involution.Folding.Reduction
/-! First completed target. The isolated exercise for Aristotle is in `tasks/A4/package/`. -/

namespace Involution

/-- The real folded system is equivalent to its explicit inverse under a product bound. -/
theorem reduction_under_product_bound (a b κ u v f g : ℝ)
    (hκ : κ < 1) (hab : |a * b| ≤ κ) :
    (u + a * v = f ∧ b * u + v = g) ↔
      (u = (f - a * g) / (1 - a * b) ∧
       v = (g - b * f) / (1 - a * b)) := by
  exact solve_system a b u v f g (ne_of_gt (determinant_pos a b κ hκ hab))

end Involution

#print axioms Involution.reduction_under_product_bound
