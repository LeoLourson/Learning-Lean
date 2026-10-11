module

public import Involution.ScalarDomain

/-! Симметричность исходного оператора во взвешенном канале и исключение
цепочки (L-λ)g=f, (L-λ)f=0. Все условия на вес понимаются почти всюду. -/

@[expose] public noncomputable section

open MeasureTheory InnerProductSpace

namespace Involution

theorem boundedMultiplier_comm (a w : IntervalLInfinity) (f : IntervalL2) :
    boundedMultiplier a (boundedMultiplier w f) = boundedMultiplier w (boundedMultiplier a f) := by
  apply Lp.ext
  filter_upwards [boundedMultiplier_ae a (boundedMultiplier w f), boundedMultiplier_ae w f,
    boundedMultiplier_ae w (boundedMultiplier a f), boundedMultiplier_ae a f] with x ha hw hw' ha'
  rw [ha, hw, hw', ha']
  ring

theorem channelPrincipal_multiplier_comm (a w : IntervalLInfinity) (s : ℂ) (f : IntervalL2) :
    channelPrincipal a s (boundedMultiplier w f) =
      boundedMultiplier w (channelPrincipal a s f) := by
  simp only [channelPrincipal, add_apply, ContinuousLinearMap.id_apply, smul_apply,
    map_add, map_smul, boundedMultiplier_comm]

theorem multiplier_channelPrincipal_inverse (a w : IntervalLInfinity) (s : ℂ)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1) (f : IntervalL2) :
    boundedMultiplier w (boundedMultiplier w (channelPrincipal a s f)) = f := by
  rw [← channelPrincipal_multiplier_comm, ← channelPrincipal_multiplier_comm,
    channelPrincipal_weight_inverse a w s hinv]

theorem weighted_channel_inner (a w : IntervalLInfinity) (s : ℂ)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (f g : IntervalL2) (hg : MemIntervalH2 g) (hpar : l2Reflect g = s • g) :
    inner ℂ (boundedMultiplier w f) (boundedMultiplier w (variableSobolevOperator a g hg)) =
      inner ℂ f (-secondWeakDeriv g hg) := by
  calc
    _ = inner ℂ f (boundedMultiplier w (boundedMultiplier w (variableSobolevOperator a g hg))) :=
      boundedMultiplier_symmetric w hr _ _
    _ = _ := by rw [variableSobolevOperator_channel a g hg s hpar,
      multiplier_channelPrincipal_inverse a w s hinv]

theorem weighted_channel_symmetric (a w : IntervalLInfinity) (s : ℂ)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (f g : IntervalL2) (hf : MemDirichletH2 f) (hg : MemDirichletH2 g)
    (hpf : l2Reflect f = s • f) (hpg : l2Reflect g = s • g) :
    inner ℂ (boundedMultiplier w (variableSobolevOperator a f hf.1)) (boundedMultiplier w g) =
      inner ℂ (boundedMultiplier w f) (boundedMultiplier w (variableSobolevOperator a g hg.1)) := by
  calc
    _ = star (inner ℂ (boundedMultiplier w g)
        (boundedMultiplier w (variableSobolevOperator a f hf.1))) := (inner_conj_symm _ _).symm
    _ = star (inner ℂ g (-secondWeakDeriv f hf.1)) :=
      congrArg star (weighted_channel_inner a w s hr hinv g f hf.1 hpf)
    _ = inner ℂ (-secondWeakDeriv f hf.1) g := inner_conj_symm _ _
    _ = inner ℂ f (-secondWeakDeriv g hg.1) := negativeSecondWeakDeriv_symmetric f g hf hg
    _ = _ := (weighted_channel_inner a w s hr hinv f g hg.1 hpg).symm

theorem symmetric_pair_noJordan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v Fu Fv : E) (lam : ℂ)
    (hself : inner ℂ Fu u = inner ℂ u Fu) (hpair : inner ℂ Fu v = inner ℂ u Fv)
    (hFu : Fu = lam • u) (hFv : Fv = lam • v + u) : u = 0 := by
  by_cases hu : u = 0
  · exact hu
  have hn : inner ℂ u u ≠ 0 := fun h => hu (inner_self_eq_zero.mp h)
  have hreal : starRingEnd ℂ lam = lam := by
    rw [hFu, inner_smul_left, inner_smul_right] at hself
    exact mul_right_cancel₀ hn hself
  rw [hFu, hFv, inner_smul_left, inner_add_right, inner_smul_right, hreal] at hpair
  have hzero : inner ℂ u u = 0 := by
    exact (add_left_cancel (a := lam * inner ℂ u v) (by simpa only [add_zero] using hpair.symm))
  exact (hn hzero).elim

theorem weighted_channel_noJordan (a w : IntervalLInfinity) (s lam : ℂ)
    (hr : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (hnz : ∀ᵐ x ∂intervalMeasure, w x ≠ 0)
    (f g : IntervalL2) (hf : MemDirichletH2 f) (hg : MemDirichletH2 g)
    (hpf : l2Reflect f = s • f) (hpg : l2Reflect g = s • g)
    (he : variableSobolevOperator a f hf.1 = lam • f)
    (hj : variableSobolevOperator a g hg.1 = lam • g + f) : f = 0 := by
  have hzero := symmetric_pair_noJordan (boundedMultiplier w f) (boundedMultiplier w g)
    (boundedMultiplier w (variableSobolevOperator a f hf.1))
    (boundedMultiplier w (variableSobolevOperator a g hg.1)) lam
    (weighted_channel_symmetric a w s hr hinv f f hf hf hpf hpf)
    (weighted_channel_symmetric a w s hr hinv f g hf hg hpf hpg)
    (by rw [he, map_smul]) (by rw [hj, map_add, map_smul])
  exact boundedMultiplier_injective w hnz (by simpa only [map_zero] using hzero)

end Involution
