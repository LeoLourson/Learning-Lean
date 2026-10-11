module

public import Involution.IntervalOperator

/-! Разность элементов слабой области Дирихле и линейность
второй слабой производной для этой операции. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

theorem HasL2WeakDeriv.sub {f g u v : IntervalL2}
    (hfg : HasL2WeakDeriv f g) (huv : HasL2WeakDeriv u v) :
    HasL2WeakDeriv (f - u) (g - v) := by
  simpa only [sub_eq_add_neg] using hfg.add huv.neg

theorem MemDirichletH2.sub {f u : IntervalL2} (hf : MemDirichletH2 f)
    (hu : MemDirichletH2 u) : MemDirichletH2 (f - u) := by
  obtain ⟨g, h, hfg, hgh⟩ := hf.1
  obtain ⟨v, w, huv, hvw⟩ := hu.1
  refine ⟨⟨g - v, h - w, hfg.sub huv, hgh.sub hvw⟩, ?_⟩
  obtain ⟨F, hF, hFl, hFr⟩ := hf.2
  obtain ⟨U, hU, hUl, hUr⟩ := hu.2
  refine ⟨F - U, ⟨hF.1.sub hU.1, ?_⟩, ?_, ?_⟩
  · filter_upwards [hF.2, hU.2, Lp.coeFn_sub f u] with x hxF hxU hxu
    change F x - U x = (f - u) x
    simp only [Pi.sub_apply] at hxu
    rw [hxF, hxU, hxu]
  · simp only [Pi.sub_apply, hFl, hUl, sub_self]
  · simp only [Pi.sub_apply, hFr, hUr, sub_self]

theorem secondWeakDeriv_sub (f u : IntervalL2) (hf : MemIntervalH2 f)
    (hu : MemIntervalH2 u) (hsub : MemIntervalH2 (f - u)) :
    secondWeakDeriv (f - u) hsub = secondWeakDeriv f hf - secondWeakDeriv u hu :=
  (weakDerivatives_eq (f - u) hsub ((firstWeakDeriv_spec f hf).sub
    (firstWeakDeriv_spec u hu)) ((secondWeakDeriv_spec f hf).sub
    (secondWeakDeriv_spec u hu))).2

end Involution
