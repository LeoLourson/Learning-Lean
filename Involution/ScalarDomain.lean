module

public import Involution.DirichletDomain
public import Involution.WeightedGreen

/-! Умножение слабой области Дирихле на комплексную константу.
Линейность слабых производных и оператора не использует точечных значений L₂. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

theorem HasWeakDerivOn.smul {s : Set ℝ} {f g : ℝ → ℂ}
    (h : HasWeakDerivOn s f g) (c : ℂ) : HasWeakDerivOn s (c • f) (c • g) := by
  refine ⟨h.1.smul c, h.2.1.smul c, ?_⟩
  intro phi hphi
  change (∫ x in s, deriv phi x • (c • f x)) = -(∫ x in s, phi x • (c • g x))
  simp_rw [smul_comm (deriv phi _) c, smul_comm (phi _) c]
  rw [integral_smul, integral_smul, h.2.2 phi hphi, smul_neg]

theorem HasL2WeakDeriv.smul {f g : IntervalL2} (h : HasL2WeakDeriv f g) (c : ℂ) :
    HasL2WeakDeriv (c • f) (c • g) :=
  (HasWeakDerivOn.smul h c).congr (Lp.coeFn_smul c f).symm (Lp.coeFn_smul c g).symm

theorem MemIntervalH2.smul {f : IntervalL2} (hf : MemIntervalH2 f) (c : ℂ) :
    MemIntervalH2 (c • f) := by
  obtain ⟨g, h, hfg, hgh⟩ := hf
  exact ⟨c • g, c • h, hfg.smul c, hgh.smul c⟩

theorem MemDirichletH2.smul {f : IntervalL2} (hf : MemDirichletH2 f) (c : ℂ) :
    MemDirichletH2 (c • f) := by
  refine ⟨hf.1.smul c, ?_⟩
  obtain ⟨F, hF, hl, hr⟩ := hf.2
  refine ⟨c • F, ⟨hF.1.const_smul c, ?_⟩, ?_, ?_⟩
  · filter_upwards [hF.2, Lp.coeFn_smul c f] with x hx hc
    change c • F x = (c • f) x
    simp only [Pi.smul_apply] at hc
    rw [hx, hc]
  · simp only [Pi.smul_apply, hl, smul_zero]
  · simp only [Pi.smul_apply, hr, smul_zero]

theorem MemDirichletH2.add {f g : IntervalL2} (hf : MemDirichletH2 f)
    (hg : MemDirichletH2 g) : MemDirichletH2 (f + g) := by
  simpa only [neg_one_smul, sub_neg_eq_add] using hf.sub (hg.smul (-1))

theorem secondWeakDeriv_add (f g : IntervalL2) (hf : MemIntervalH2 f)
    (hg : MemIntervalH2 g) (hfg : MemIntervalH2 (f + g)) :
    secondWeakDeriv (f + g) hfg = secondWeakDeriv f hf + secondWeakDeriv g hg :=
  (weakDerivatives_eq (f + g) hfg ((firstWeakDeriv_spec f hf).add (firstWeakDeriv_spec g hg))
    ((secondWeakDeriv_spec f hf).add (secondWeakDeriv_spec g hg))).2

theorem variableSobolevOperator_add (a : IntervalLInfinity) (f g : IntervalL2)
    (hf : MemIntervalH2 f) (hg : MemIntervalH2 g) (hfg : MemIntervalH2 (f + g)) :
    variableSobolevOperator a (f + g) hfg = variableSobolevOperator a f hf +
      variableSobolevOperator a g hg := by
  simp only [variableSobolevOperator, secondWeakDeriv_add f g hf hg hfg, map_add, neg_add]
  abel

theorem secondWeakDeriv_smul (c : ℂ) (f : IntervalL2) (hf : MemIntervalH2 f)
    (hcf : MemIntervalH2 (c • f)) :
    secondWeakDeriv (c • f) hcf = c • secondWeakDeriv f hf :=
  (weakDerivatives_eq (c • f) hcf ((firstWeakDeriv_spec f hf).smul c)
    ((secondWeakDeriv_spec f hf).smul c)).2

theorem variableSobolevOperator_smul (a : IntervalLInfinity) (c : ℂ) (f : IntervalL2)
    (hf : MemIntervalH2 f) (hcf : MemIntervalH2 (c • f)) :
    variableSobolevOperator a (c • f) hcf = c • variableSobolevOperator a f hf := by
  simp only [variableSobolevOperator, secondWeakDeriv_smul c f hf hcf,
    map_smul, smul_neg, smul_sub]

theorem variableSobolevOperator_congr (a : IntervalLInfinity) (f g : IntervalL2)
    (hf : MemIntervalH2 f) (hg : MemIntervalH2 g) (he : f = g) :
    variableSobolevOperator a f hf = variableSobolevOperator a g hg := by
  subst g
  rfl

theorem secondWeakDeriv_congr (f g : IntervalL2) (hf : MemIntervalH2 f)
    (hg : MemIntervalH2 g) (he : f = g) : secondWeakDeriv f hf = secondWeakDeriv g hg := by
  subst g
  rfl

theorem secondWeakDeriv_parity (f : IntervalL2) (hf : MemIntervalH2 f) (s : ℂ)
    (hpar : l2Reflect f = s • f) : l2Reflect (secondWeakDeriv f hf) = s • secondWeakDeriv f hf := by
  rw [← secondWeakDeriv_reflect f hf]
  exact (secondWeakDeriv_congr _ _ hf.reflect (hf.smul s) hpar).trans
    (secondWeakDeriv_smul s f hf (hf.smul s))

theorem variableSobolevOperator_channel (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemIntervalH2 f) (s : ℂ) (hpar : l2Reflect f = s • f) :
    variableSobolevOperator a f hf = channelPrincipal a s (-secondWeakDeriv f hf) := by
  simp only [variableSobolevOperator, secondWeakDeriv_parity f hf s hpar, channelPrincipal,
    add_apply, ContinuousLinearMap.id_apply, smul_apply, map_smul, map_neg,
    sub_eq_add_neg, neg_add]

end Involution
