module

public import Involution.Setup.Reflection
public import Involution.Setup.L2Reflection
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Слабые производные комплексных функций на открытом интервале.
Определение использует все гладкие вещественные пробные функции с компактным
носителем внутри области. Производные определены с точностью до п.в. равенства.
Следы — в `Involution.Setup.IntervalTrace`, абсолютно непрерывные представители —
в `Involution.Setup.IntervalRegularity`. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Involution

def IsSmoothTestOn (s : Set ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ s

def HasWeakDerivOn (s : Set ℝ) (f g : ℝ → ℂ) : Prop :=
  IntegrableOn f s ∧ IntegrableOn g s ∧
    ∀ φ : ℝ → ℝ, IsSmoothTestOn s φ →
      (∫ x in s, deriv φ x • f x) = -(∫ x in s, φ x • g x)

abbrev HasIntervalWeakDeriv := HasWeakDerivOn (Set.Ioo (-1) 1)

theorem IsSmoothTestOn.deriv {s : Set ℝ} {φ : ℝ → ℝ} (hφ : IsSmoothTestOn s φ) :
    IsSmoothTestOn s (deriv φ) := by
  refine ⟨?_, hφ.2.1.deriv, tsupport_deriv_subset.trans hφ.2.2⟩
  exact ContDiff.deriv' (by simpa using hφ.1)

theorem IsSmoothTestOn.integrable_smul {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn s φ) {f : ℝ → ℂ} (hf : IntegrableOn f s) :
    IntegrableOn (fun x => φ x • f x) s := by
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  exact hf.bdd_smul C hφ.1.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem IsSmoothTestOn.setIntegral_eq_integral {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn s φ) (f : ℝ → ℂ) :
    (∫ x in s, φ x • f x) = ∫ x, φ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
  rw [hzero, zero_smul]

theorem IsSmoothTestOn.reflect {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn (Set.Ioo (-1) 1) φ) :
    IsSmoothTestOn (Set.Ioo (-1) 1) (reflect φ) := by
  refine ⟨hφ.1.comp contDiff_neg, hφ.2.1.comp_homeomorph (Homeomorph.neg ℝ), ?_⟩
  change tsupport (φ ∘ (Homeomorph.neg ℝ)) ⊆ Set.Ioo (-1) 1
  rw [tsupport_comp_eq_preimage]
  intro x hx
  have h := hφ.2.2 hx
  change -1 < -x ∧ -x < 1 at h
  constructor <;> linarith [h.1, h.2]

theorem integral_reflect_pair (φ : ℝ → ℝ) (f : ℝ → ℂ) :
    (∫ x, φ x • reflect f x ∂intervalMeasure) =
      ∫ x, reflect φ x • f x ∂intervalMeasure := by
  have h := interval_neg_measurePreserving.integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding (fun x => φ (-x) • f x)
  simpa only [reflect_apply, neg_neg] using h

namespace HasWeakDerivOn

theorem unique {s : Set ℝ} (hs : IsOpen s) {f g g₁ : ℝ → ℂ}
    (h : HasWeakDerivOn s f g) (h₁ : HasWeakDerivOn s f g₁) :
    g =ᵐ[volume.restrict s] g₁ := by
  have hzero : ∀ᵐ x ∂volume, x ∈ s → g x - g₁ x = 0 := by
    apply hs.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (h.2.1.sub h₁.2.1).locallyIntegrableOn
    intro φ hdiff hcompact hsupp
    have hφ : IsSmoothTestOn s φ := ⟨hdiff, hcompact, hsupp⟩
    change (∫ x, φ x • (g x - g₁ x)) = 0
    rw [← hφ.setIntegral_eq_integral (fun x => g x - g₁ x)]
    simp only [smul_sub]
    rw [integral_sub (hφ.integrable_smul h.2.1) (hφ.integrable_smul h₁.2.1)]
    have heq := neg_injective ((h.2.2 φ hφ).symm.trans (h₁.2.2 φ hφ))
    exact sub_eq_zero.mpr heq
  apply (ae_restrict_iff' hs.measurableSet).mpr
  exact hzero.mono (fun x hx hsx => sub_eq_zero.mp (hx hsx))

theorem congr {s : Set ℝ} {f g f₁ g₁ : ℝ → ℂ}
    (h : HasWeakDerivOn s f g)
    (hf : f =ᵐ[volume.restrict s] f₁) (hg : g =ᵐ[volume.restrict s] g₁) :
    HasWeakDerivOn s f₁ g₁ := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, ?_⟩
  intro φ hφ
  calc
    (∫ x in s, deriv φ x • f₁ x) = ∫ x in s, deriv φ x • f x :=
      integral_congr_ae (hf.symm.mono (fun x hx => congrArg _ hx))
    _ = -(∫ x in s, φ x • g x) := h.2.2 φ hφ
    _ = -(∫ x in s, φ x • g₁ x) := by
      congr 1
      exact integral_congr_ae (hg.mono (fun x hx => congrArg _ hx))

theorem neg {s : Set ℝ} {f g : ℝ → ℂ} (h : HasWeakDerivOn s f g) :
    HasWeakDerivOn s (-f) (-g) := by
  refine ⟨h.1.neg, h.2.1.neg, ?_⟩
  intro φ hφ
  simpa only [Pi.neg_apply, smul_neg, integral_neg, neg_neg] using
    congrArg Neg.neg (h.2.2 φ hφ)

theorem add {s : Set ℝ} {f g f₁ g₁ : ℝ → ℂ}
    (h : HasWeakDerivOn s f g) (h₁ : HasWeakDerivOn s f₁ g₁) :
    HasWeakDerivOn s (f + f₁) (g + g₁) := by
  refine ⟨h.1.add h₁.1, h.2.1.add h₁.2.1, ?_⟩
  intro φ hφ
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (hφ.deriv.integrable_smul h.1) (hφ.deriv.integrable_smul h₁.1),
    integral_add (hφ.integrable_smul h.2.1) (hφ.integrable_smul h₁.2.1),
    h.2.2 φ hφ, h₁.2.2 φ hφ, neg_add]

theorem restrict {s t : Set ℝ} {f g : ℝ → ℂ} (h : HasWeakDerivOn s f g)
    (hts : t ⊆ s) : HasWeakDerivOn t f g := by
  refine ⟨h.1.mono_set hts, h.2.1.mono_set hts, ?_⟩
  intro φ hφ
  have hφs : IsSmoothTestOn s φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hts⟩
  rw [hφ.deriv.setIntegral_eq_integral f, hφ.setIntegral_eq_integral g]
  rw [← hφs.deriv.setIntegral_eq_integral f, ← hφs.setIntegral_eq_integral g]
  exact h.2.2 φ hφs

theorem reflect {f g : ℝ → ℂ} (h : HasIntervalWeakDeriv f g) :
    HasIntervalWeakDeriv (Involution.reflect f) (-Involution.reflect g) := by
  have hf : Integrable (Involution.reflect f) intervalMeasure :=
    (interval_neg_measurePreserving.integrable_comp h.1.aestronglyMeasurable).mpr h.1
  have hg : Integrable (Involution.reflect g) intervalMeasure :=
    (interval_neg_measurePreserving.integrable_comp h.2.1.aestronglyMeasurable).mpr h.2.1
  refine ⟨hf, hg.neg, ?_⟩
  intro φ hφ
  have htest := h.2.2 (Involution.reflect φ) hφ.reflect
  simp only [deriv_reflect, Pi.neg_apply, neg_smul, integral_neg] at htest
  have hpair := neg_injective htest
  change (∫ x, Involution.reflect (deriv φ) x • f x ∂intervalMeasure) =
    ∫ x, Involution.reflect φ x • g x ∂intervalMeasure at hpair
  change (∫ x, deriv φ x • Involution.reflect f x ∂intervalMeasure) =
    -(∫ x, φ x • (-Involution.reflect g) x ∂intervalMeasure)
  calc
    _ = ∫ x, Involution.reflect (deriv φ) x • f x ∂intervalMeasure :=
      integral_reflect_pair (deriv φ) f
    _ = ∫ x, Involution.reflect φ x • g x ∂intervalMeasure := hpair
    _ = ∫ x, φ x • Involution.reflect g x ∂intervalMeasure :=
      (integral_reflect_pair φ g).symm
    _ = _ := by simp only [Pi.neg_apply, smul_neg, integral_neg, neg_neg]

end HasWeakDerivOn

theorem weak_second_derivative_reflect {f g h : ℝ → ℂ}
    (hfg : HasIntervalWeakDeriv f g) (hgh : HasIntervalWeakDeriv g h) :
    HasIntervalWeakDeriv (reflect f) (-reflect g) ∧
      HasIntervalWeakDeriv (-reflect g) (reflect h) := by
  exact ⟨hfg.reflect, by simpa only [neg_neg] using hgh.reflect.neg⟩

end Involution
