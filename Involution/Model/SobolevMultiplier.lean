module

public import Involution.Setup.ACDomain
public import Involution.Model.ScalarDomain
public import Involution.Model.MultiplicationEquiv

/-! Правило произведения для ограниченных коэффициентов со слабой производной.
Точечные значения используются только у абсолютно непрерывного представителя. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

theorem interval_ae_closed {P : ℝ → Prop} (h : ∀ᵐ x ∂intervalMeasure, P x) :
    ∀ᵐ x ∂volume, x ∈ Icc (-1 : ℝ) 1 → P x := by
  have hc : ∀ᵐ x ∂volume.restrict (Icc (-1 : ℝ) 1), P x := by
    change ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1), P x at h
    rwa [restrict_Ioo_eq_restrict_Icc] at h
  exact (ae_restrict_iff' measurableSet_Icc).mp hc

/-- Представление коэффициента W¹∞: производная задаётся классом L∞. -/
def HasACMultiplierDerivative (a a' : IntervalLInfinity) : Prop :=
  ∃ A : ℝ → ℂ, AbsolutelyContinuousOnInterval A (-1) 1 ∧
    A =ᵐ[intervalMeasure] a ∧
    (∀ᵐ x ∂volume, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt A (a' x) x)

theorem HasACMultiplierDerivative.of_weak {a a' : IntervalLInfinity}
    (h : HasIntervalWeakDeriv a a') : HasACMultiplierDerivative a a' := by
  obtain ⟨A, hA, heq, hd⟩ := HasWeakDerivOn.exists_ac_representative
    (by norm_num : (-1 : ℝ) < 1) h
  exact ⟨A, hA, heq, by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hd⟩

/-- Две слабые производные коэффициента принадлежат L∞. -/
def MemIntervalW2Infinity (a : IntervalLInfinity) : Prop :=
  ∃ a' a'' : IntervalLInfinity, HasIntervalWeakDeriv a a' ∧ HasIntervalWeakDeriv a' a''

theorem HasL2WeakDeriv.mul_coefficient {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') {f g : IntervalL2} (hfg : HasL2WeakDeriv f g) :
    HasL2WeakDeriv (boundedMultiplier a f)
      (boundedMultiplier a' f + boundedMultiplier a g) := by
  obtain ⟨A, hAac, hA, hdA⟩ := ha
  obtain ⟨F, hF, hFac, hdF⟩ := hfg.exists_ac_representative
  let H := boundedMultiplier a' f + boundedMultiplier a g
  have hH : H =ᵐ[intervalMeasure] fun x => a' x * F x + A x * g x := by
    filter_upwards [Lp.coeFn_add (boundedMultiplier a' f) (boundedMultiplier a g),
      boundedMultiplier_ae a' f, boundedMultiplier_ae a g, hF.2, hA] with x hx h1 h0 hf ha
    change H x = boundedMultiplier a' f x + boundedMultiplier a g x at hx
    rw [hx, h1, h0, hf, ha]
  have hAFac : AbsolutelyContinuousOnInterval (fun x => A x * F x) (-1) 1 := by
    convert hAac.smul hFac using 1
  have hdAF : ∀ᵐ x ∂volume, x ∈ Icc (-1 : ℝ) 1 →
      HasDerivAt (fun t => A t * F t) (H x) x := by
    filter_upwards [hdA, hdF, interval_ae_closed hH] with x ha hf hh hx
    rw [hh hx]
    exact (ha hx).mul (hf hx)
  have hw : HasIntervalWeakDeriv (fun x => A x * F x) H :=
    hasWeakDerivOn_of_absolutelyContinuous (by norm_num) hAFac (intervalL2_integrable H)
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hdAF)
  apply hw.congr _ Filter.EventuallyEq.rfl
  filter_upwards [hA, hF.2, boundedMultiplier_ae a f] with x ha hf hm
  exact (by rw [ha, hf, hm])

theorem MemIntervalH2.mul_coefficient {a a' a'' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (ha' : HasACMultiplierDerivative a' a'')
    {f : IntervalL2} (hf : MemIntervalH2 f) : MemIntervalH2 (boundedMultiplier a f) := by
  obtain ⟨g, h, hfg, hgh⟩ := hf
  exact ⟨boundedMultiplier a' f + boundedMultiplier a g,
    (boundedMultiplier a'' f + boundedMultiplier a' g) +
      (boundedMultiplier a' g + boundedMultiplier a h),
    hfg.mul_coefficient ha, (hfg.mul_coefficient ha').add (hgh.mul_coefficient ha)⟩

theorem HasDirichletTrace.mul_coefficient {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') {f : IntervalL2} (hf : HasDirichletTrace f) :
    HasDirichletTrace (boundedMultiplier a f) := by
  obtain ⟨A, hAac, hA, _⟩ := ha
  obtain ⟨F, hF, hl, hr⟩ := hf
  have hAc : ContinuousOn A (Icc (-1 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hAac.continuousOn
  refine ⟨fun x => A x * F x, ⟨hAc.mul hF.1, ?_⟩, by simp [hl], by simp [hr]⟩
  filter_upwards [hA, hF.2, boundedMultiplier_ae a f] with x ha hf hm
  rw [ha, hf, hm]

theorem MemDirichletH2.mul_coefficient {a a' a'' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (ha' : HasACMultiplierDerivative a' a'')
    {f : IntervalL2} (hf : MemDirichletH2 f) : MemDirichletH2 (boundedMultiplier a f) :=
  ⟨hf.1.mul_coefficient ha ha', hf.2.mul_coefficient ha⟩

theorem MemIntervalW2Infinity.mul_dirichlet {a : IntervalLInfinity}
    (ha : MemIntervalW2Infinity a) {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemDirichletH2 (boundedMultiplier a f) := by
  obtain ⟨a', a'', h0, h1⟩ := ha
  exact hf.mul_coefficient (HasACMultiplierDerivative.of_weak h0)
    (HasACMultiplierDerivative.of_weak h1)

theorem memDirichletH2_mul_iff (a b : IntervalLInfinity)
    (ha : MemIntervalW2Infinity a) (hb : MemIntervalW2Infinity b)
    (hab : ∀ᵐ x ∂intervalMeasure, a x * b x = 1) (f : IntervalL2) :
    MemDirichletH2 (boundedMultiplier a f) ↔ MemDirichletH2 f := by
  constructor
  · intro hf
    have h := hb.mul_dirichlet hf
    rwa [boundedMultiplier_inverse b a (hab.mono fun x hx => by rwa [mul_comm])] at h
  · exact ha.mul_dirichlet

theorem secondWeakDeriv_mul_coefficient {a a' a'' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (ha' : HasACMultiplierDerivative a' a'')
    (f : IntervalL2) (hf : MemIntervalH2 f) (haf : MemIntervalH2 (boundedMultiplier a f)) :
    secondWeakDeriv (boundedMultiplier a f) haf =
      (boundedMultiplier a'' f + boundedMultiplier a' (firstWeakDeriv f hf)) +
        (boundedMultiplier a' (firstWeakDeriv f hf) + boundedMultiplier a (secondWeakDeriv f hf)) :=
  (weakDerivatives_eq _ haf ((firstWeakDeriv_spec f hf).mul_coefficient ha)
    (((firstWeakDeriv_spec f hf).mul_coefficient ha').add
      ((secondWeakDeriv_spec f hf).mul_coefficient ha))).2

theorem firstWeakDeriv_mul_coefficient {a a' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (f : IntervalL2) (hf : MemIntervalH2 f)
    (haf : MemIntervalH2 (boundedMultiplier a f)) :
    firstWeakDeriv (boundedMultiplier a f) haf =
      boundedMultiplier a' f + boundedMultiplier a (firstWeakDeriv f hf) :=
  (firstWeakDeriv_spec _ haf).unique ((firstWeakDeriv_spec f hf).mul_coefficient ha)

theorem secondWeakDeriv_mul_coefficient_norm_le {a a' a'' : IntervalLInfinity}
    (ha : HasACMultiplierDerivative a a') (ha' : HasACMultiplierDerivative a' a'')
    (f : IntervalL2) (hf : MemIntervalH2 f) (haf : MemIntervalH2 (boundedMultiplier a f)) :
    ‖secondWeakDeriv (boundedMultiplier a f) haf‖ ≤
      ‖a''‖ * ‖f‖ + 2 * ‖a'‖ * ‖firstWeakDeriv f hf‖ + ‖a‖ * ‖secondWeakDeriv f hf‖ := by
  rw [secondWeakDeriv_mul_coefficient ha ha' f hf haf]
  have h0 := boundedMultiplier_norm_le a (secondWeakDeriv f hf)
  have h1 := boundedMultiplier_norm_le a' (firstWeakDeriv f hf)
  have h2 := boundedMultiplier_norm_le a'' f
  have hl := norm_add_le (boundedMultiplier a'' f) (boundedMultiplier a' (firstWeakDeriv f hf))
  have hr := norm_add_le (boundedMultiplier a' (firstWeakDeriv f hf))
    (boundedMultiplier a (secondWeakDeriv f hf))
  have hs := norm_add_le
    (boundedMultiplier a'' f + boundedMultiplier a' (firstWeakDeriv f hf))
    (boundedMultiplier a' (firstWeakDeriv f hf) + boundedMultiplier a (secondWeakDeriv f hf))
  nlinarith

end Involution
