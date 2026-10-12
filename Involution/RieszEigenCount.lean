module

public import Involution.RieszBasis
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Счёт больших собственных значений для базиса Рисса из собственных векторов.
Если `K = F + E`, образ `F` лежит в подпространстве размерности не больше `n`, а
`C_b ‖E‖ < θ`, где `C_b = ‖b.repr.symm‖ ‖b.repr‖`, то собственных векторов базиса
с `θ ≤ ‖μ i‖` не больше `n`. -/

@[expose] public noncomputable section

namespace Involution

open scoped lp

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open Classical in
theorem RieszBasis.repr_finsum_apply (b : RieszBasis ι E) (s : Finset ι) (c : s → ℂ) (i : s) :
    b.repr (∑ j : s, c j • b.vector j) i = c i := by
  rw [map_sum]
  simp only [map_smul, RieszBasis.repr_vector]
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (i : ι) ≠ j := fun h => hji (Subtype.ext h.symm)
    simp [Pi.single_eq_of_ne hne]
  · simp

open Classical in
theorem RieszBasis.repr_finsum_apply_of_notMem (b : RieszBasis ι E) (s : Finset ι)
    (c : s → ℂ) (i : ι) (hi : i ∉ s) :
    b.repr (∑ j : s, c j • b.vector j) i = 0 := by
  rw [map_sum]
  simp only [map_smul, RieszBasis.repr_vector]
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : i ≠ j := fun h => hi (h ▸ j.2)
  simp [Pi.single_eq_of_ne hne]

/-- Счёт собственных векторов базиса Рисса через приближение конечного ранга. -/
theorem RieszBasis.card_le_of_finiteRank_approx (b : RieszBasis ι E) (K F G : E →L[ℂ] E)
    (hK : K = F + G) (W : Submodule ℂ E) [FiniteDimensional ℂ W] (n : ℕ)
    (hW : Module.finrank ℂ W ≤ n) (hF : ∀ x, F x ∈ W) (μ : ι → ℂ)
    (hKu : ∀ i, K (b.vector i) = μ i • b.vector i) (θ : ℝ)
    (hG : (‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr.toContinuousLinearMap‖) * ‖G‖ < θ)
    (s : Finset ι) (hs : ∀ i ∈ s, θ ≤ ‖μ i‖) : s.card ≤ n := by
  classical
  by_contra hcon
  push Not at hcon
  have hθ : 0 < θ := lt_of_le_of_lt (by positivity) hG
  let L0 : (s → ℂ) →ₗ[ℂ] E :=
    { toFun := fun c => ∑ i, c i • b.vector i
      map_add' := fun a c => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  let L : (s → ℂ) →ₗ[ℂ] W := ((F : E →ₗ[ℂ] E).comp L0).codRestrict W (fun c => hF _)
  have hker : L.ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    omega
  obtain ⟨c, hcL, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set x := ∑ i, c i • b.vector i with hx
  have hFx : F x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hcL)
  have hKx : K x = ∑ i : s, (μ i * c i) • b.vector i := by
    simp [hx, map_sum, map_smul, hKu, smul_smul, mul_comm]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hc0
    funext i
    have := b.repr_finsum_apply s c i
    rw [← hx, h0, map_zero] at this
    simpa using this.symm
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hcoord : ‖((θ : ℂ) • b.repr x)‖ ≤ ‖b.repr (K x)‖ := by
    apply lp.norm_le_of_forall_sum_le hp (norm_nonneg _)
    intro t
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (lp.sum_rpow_le_norm_rpow hp _ t)
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hθ.le]
    by_cases hi : i ∈ s
    · have h1 := b.repr_finsum_apply s c ⟨i, hi⟩
      have h2 := b.repr_finsum_apply s (fun j => μ j * c j) ⟨i, hi⟩
      rw [← hx] at h1
      rw [← hKx] at h2
      rw [h1, h2, norm_mul]
      exact mul_le_mul_of_nonneg_right (hs i hi) (norm_nonneg _)
    · rw [hx, b.repr_finsum_apply_of_notMem s c i hi]
      simp
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hθ.le] at hcoord
  have hyx : ‖x‖ ≤ ‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr x‖ := by
    have h := b.repr.symm.toContinuousLinearMap.le_opNorm (b.repr x)
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using h
  have hzK : ‖b.repr (K x)‖ ≤ ‖b.repr.toContinuousLinearMap‖ * ‖K x‖ :=
    b.repr.toContinuousLinearMap.le_opNorm _
  have hKG : ‖K x‖ ≤ ‖G‖ * ‖x‖ := by
    rw [hK, add_apply, hFx, zero_add]
    exact G.le_opNorm x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have key : θ * ‖x‖ ≤
      (‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr.toContinuousLinearMap‖ * ‖G‖) * ‖x‖ := by
    calc
      θ * ‖x‖ ≤ θ * (‖b.repr.symm.toContinuousLinearMap‖ * ‖b.repr x‖) :=
        mul_le_mul_of_nonneg_left hyx hθ.le
      _ = ‖b.repr.symm.toContinuousLinearMap‖ * (θ * ‖b.repr x‖) := by ring
      _ ≤ ‖b.repr.symm.toContinuousLinearMap‖ *
          (‖b.repr.toContinuousLinearMap‖ * (‖G‖ * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hcoord.trans (hzK.trans
          (mul_le_mul_of_nonneg_left hKG (norm_nonneg _)))) (norm_nonneg _)
      _ = _ := by ring
  have := mul_lt_mul_of_pos_right hG hxpos
  linarith

end Involution
