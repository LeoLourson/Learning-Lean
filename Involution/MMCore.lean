module

public import Involution.MMEstimates
public import Involution.MMTotal
public import Involution.MMGoodCut
public import Involution.MMRieszBasis

/-! The core case of the Markus–Matsaev theorem: `b₀ = 0` and all eigenvalues large. -/

@[expose] public noncomputable section

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CutData

variable {D : MMData ι H} (C : CutData D)

theorem Q_sum_sq (t : Finset ℕ) (u : H) : ∑ k ∈ t, ‖C.Q k u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  simp only [C.Q_eq]
  refine sum_norm_sq_proj_le D.b C.blk t ?_ u
  intro j _ k _ hjk
  rw [Set.disjoint_left]
  rintro i ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases lt_or_gt_of_ne hjk with h | h
  · have := C.ξ_mono (Nat.succ_le_of_lt h); linarith
  · have := C.ξ_mono (Nat.succ_le_of_lt h); linarith

theorem Q_symm (k : ℕ) (x y : H) : inner ℂ (C.Q k x) y = inner ℂ x (C.Q k y) := by
  rw [C.Q_eq, inner_diagOp_left D.b _ 1 (norm_indicator_one_le _)]
  have : (fun i => (starRingEnd ℂ) ((C.blk k).indicator (1 : ι → ℂ) i)) =
      (C.blk k).indicator 1 := by
    funext i
    by_cases h : i ∈ C.blk k <;> simp [h]
  rw [this]

/-- The ranges of the Riesz projections form a Riesz basis of subspaces. -/
def rieszBasis : RieszBasisWithBrackets C.V where
  lower := ((1 + C.estimates.choose) ^ 2)⁻¹
  upper := (1 + C.estimates.choose) ^ 2
  lower_pos := by have := C.estimates.choose_spec.1; positivity
  upper_pos := by have := C.estimates.choose_spec.1; positivity
  finite := C.V_finite
  total := C.total
  bounds := fun t v => by
    have hc0 := C.estimates.choose_spec.1
    have h := riesz_bounds_of_estimates C.P C.Q _ hc0 (fun j k h => C.P_mul_ne h)
      C.Q_sum_sq C.Q_symm C.estimates.choose_spec.2.1 C.estimates.choose_spec.2.2 t
      (fun k => (v k : H)) (fun k => C.P_apply_of_mem (v k).2)
    have hpos : 0 < (1 + C.estimates.choose) ^ 2 := by positivity
    refine ⟨?_, h.2⟩
    rw [inv_mul_le_iff₀ hpos]
    exact h.1

end CutData

namespace MMData

/-- Core theorem: for a given bound `β` and counting constants, once the spectrum of `G`
lies above a sufficiently large threshold, `T = G + S` has a Riesz basis of finite-dimensional
invariant subspaces. -/
theorem core (β c₂ C₀ : ℝ) (hβ : 0 ≤ β) (hc₂ : 0 < c₂) (hC₀ : 0 ≤ C₀) :
    ∃ M : ℝ, ∀ D : MMData ι H, D.b₁ = β →
      (∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, D.ω i ≤ t) → (s.card : ℝ) ≤ c₂ * t + C₀) →
      M ≤ D.m →
      ∃ V : ℕ → Submodule ℂ H, Nonempty (RieszBasisWithBrackets V) ∧
        ∀ k, ∀ v ∈ V k, ∃ g : H, D.K₀ g = v ∧ g + D.B g ∈ V k := by
  obtain ⟨M, hM⟩ := exists_cuts (ι := ι) (H := H) β c₂ C₀ hβ hc₂ hC₀
  refine ⟨M, fun D hD hcount hm => ?_⟩
  obtain ⟨C⟩ := hM D hD hcount hm
  exact ⟨C.V, ⟨C.rieszBasis⟩, C.V_invariant⟩

end MMData

end Involution
