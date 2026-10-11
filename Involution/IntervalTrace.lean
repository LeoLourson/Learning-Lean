module

public import Involution.IntervalSobolev
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Следы непрерывного представителя класса L² на замкнутом интервале.
Значения не зависят от представителя. Существование представителя для элементов
`H²` — в `IntervalRegularity.lean`. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Involution

def HasIntervalRepresentative (f : IntervalL2) (F : ℝ → ℂ) : Prop :=
  ContinuousOn F (Set.Icc (-1) 1) ∧ F =ᵐ[intervalMeasure] f

theorem HasIntervalRepresentative.unique {f : IntervalL2} {F G : ℝ → ℂ}
    (hF : HasIntervalRepresentative f F) (hG : HasIntervalRepresentative f G) :
    Set.EqOn F G (Set.Icc (-1) 1) := by
  have heq : Set.EqOn F G (Set.Ioo (-1) 1) :=
    Measure.eqOn_Ioo_of_ae_eq volume (hF.2.trans hG.2.symm)
      (hF.1.mono Set.Ioo_subset_Icc_self) (hG.1.mono Set.Ioo_subset_Icc_self)
  exact heq.of_subset_closure hF.1 hG.1 Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])

theorem HasIntervalRepresentative.reflect {f : IntervalL2} {F : ℝ → ℂ}
    (hF : HasIntervalRepresentative f F) :
    HasIntervalRepresentative (l2Reflect f) (reflect F) := by
  refine ⟨hF.1.comp continuous_neg.continuousOn ?_, ?_⟩
  · intro x hx
    change -1 ≤ -x ∧ -x ≤ 1
    constructor <;> linarith [hx.1, hx.2]
  · have heq := interval_neg_measurePreserving.quasiMeasurePreserving.ae_eq_comp hF.2
    exact heq.trans (l2Reflect_ae f).symm

def HasDirichletTrace (f : IntervalL2) : Prop :=
  ∃ F : ℝ → ℂ, HasIntervalRepresentative f F ∧ F (-1) = 0 ∧ F 1 = 0

theorem HasDirichletTrace.boundary {f : IntervalL2} (hf : HasDirichletTrace f)
    {F : ℝ → ℂ} (hF : HasIntervalRepresentative f F) : F (-1) = 0 ∧ F 1 = 0 := by
  obtain ⟨G, hG, hleft, hright⟩ := hf
  have heq := hF.unique hG
  exact ⟨(heq (by norm_num)).trans hleft, (heq (by norm_num)).trans hright⟩

theorem HasDirichletTrace.reflect {f : IntervalL2} (hf : HasDirichletTrace f) :
    HasDirichletTrace (l2Reflect f) := by
  obtain ⟨F, hF, hleft, hright⟩ := hf
  exact ⟨Involution.reflect F, hF.reflect, by simpa only [reflect_apply, neg_neg] using hright,
    by simpa only [reflect_apply] using hleft⟩

def MemDirichletH2 (f : IntervalL2) : Prop := MemIntervalH2 f ∧ HasDirichletTrace f

theorem MemDirichletH2.reflect {f : IntervalL2} (hf : MemDirichletH2 f) :
    MemDirichletH2 (l2Reflect f) := ⟨hf.1.reflect, hf.2.reflect⟩

end Involution
