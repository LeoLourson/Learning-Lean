module

public import Involution.Model.WeightedGreen
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! Весь класс постановки: факторизация `L_a = (I + a R) (-D²)` и компактный обратный.
Чётность и гладкость коэффициента здесь не используются: достаточно класса `L∞`
и ограниченной обратимости определителя `1 - a(x) a(-x)` почти всюду.
Спектральная задача сводится к компактному оператору; базисность отсюда не следует. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

/-- Отражение с последующим умножением: `(A f)(x) = a(x) f(-x)`. -/
def reflectedMultiplier (a : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  (boundedMultiplier a).comp l2Reflect.toContinuousLinearMap

theorem reflectedMultiplier_ae (a : IntervalLInfinity) (f : IntervalL2) :
    reflectedMultiplier a f =ᵐ[intervalMeasure] fun x => a x * f (-x) := by
  filter_upwards [boundedMultiplier_ae a (l2Reflect f), l2Reflect_ae f] with x hm hr
  change boundedMultiplier a (l2Reflect f) x = a x * f (-x)
  rw [hm, hr]

/-- Главный множитель `I + a R`. -/
def principalOperator (a : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  ContinuousLinearMap.id ℂ IntervalL2 + reflectedMultiplier a

/-- Присоединённый множитель `I - a R`. -/
def principalCofactor (a : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  ContinuousLinearMap.id ℂ IntervalL2 - reflectedMultiplier a

theorem principalOperator_ae (a : IntervalLInfinity) (f : IntervalL2) :
    principalOperator a f =ᵐ[intervalMeasure] fun x => f x + a x * f (-x) := by
  filter_upwards [Lp.coeFn_add f (reflectedMultiplier a f), reflectedMultiplier_ae a f]
    with x hadd hm
  change (f + reflectedMultiplier a f) x = f x + a x * f (-x)
  rw [hadd, Pi.add_apply, hm]

theorem principalCofactor_ae (a : IntervalLInfinity) (f : IntervalL2) :
    principalCofactor a f =ᵐ[intervalMeasure] fun x => f x - a x * f (-x) := by
  filter_upwards [Lp.coeFn_sub f (reflectedMultiplier a f), reflectedMultiplier_ae a f]
    with x hsub hm
  change (f - reflectedMultiplier a f) x = f x - a x * f (-x)
  rw [hsub, Pi.sub_apply, hm]

theorem variableSobolevOperator_eq_principal (a : IntervalLInfinity) (f : IntervalL2)
    (hf : MemIntervalH2 f) :
    variableSobolevOperator a f hf = principalOperator a (-secondWeakDeriv f hf) := by
  change -secondWeakDeriv f hf - boundedMultiplier a (l2Reflect (secondWeakDeriv f hf)) =
    -secondWeakDeriv f hf + boundedMultiplier a (l2Reflect (-secondWeakDeriv f hf))
  rw [map_neg, map_neg, sub_eq_add_neg]

/-- Кандидат в обратный: `d (I - a R)`, где `d (1 - a(x) a(-x)) = 1` почти всюду. -/
def principalOperatorInverse (a d : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  (boundedMultiplier d).comp (principalCofactor a)

theorem principalOperatorInverse_left (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f : IntervalL2) :
    principalOperatorInverse a d (principalOperator a f) = f := by
  apply Lp.ext
  have hneg : ∀ᵐ x ∂intervalMeasure,
      principalOperator a f (-x) = f (-x) + a (-x) * f x := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (principalOperator_ae a f)] with x hx
    simpa only [neg_neg] using hx
  filter_upwards [boundedMultiplier_ae d (principalCofactor a (principalOperator a f)),
    principalCofactor_ae a (principalOperator a f), principalOperator_ae a f, hneg, hd]
    with x hm hc hg hgn hx
  change boundedMultiplier d (principalCofactor a (principalOperator a f)) x = f x
  rw [hm, hc, hg, hgn]
  calc
    _ = (d x * (1 - a x * a (-x))) * f x := by ring
    _ = f x := by rw [hx, one_mul]

theorem principalOperatorInverse_right (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f : IntervalL2) :
    principalOperator a (principalOperatorInverse a d f) = f := by
  apply Lp.ext
  have hdn : ∀ᵐ x ∂intervalMeasure, d (-x) * (1 - a (-x) * a x) = 1 := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hd] with x hx
    simpa only [neg_neg] using hx
  have hcn : ∀ᵐ x ∂intervalMeasure,
      principalCofactor a f (-x) = f (-x) - a (-x) * f x := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (principalCofactor_ae a f)] with x hx
    simpa only [neg_neg] using hx
  have hmn : ∀ᵐ x ∂intervalMeasure,
      boundedMultiplier d (principalCofactor a f) (-x) =
        d (-x) * principalCofactor a f (-x) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (boundedMultiplier_ae d (principalCofactor a f))] with x hx
    exact hx
  filter_upwards [principalOperator_ae a (boundedMultiplier d (principalCofactor a f)),
    boundedMultiplier_ae d (principalCofactor a f), principalCofactor_ae a f,
    hmn, hcn, hd, hdn] with x hp hm hc hmx hcx hx hxn
  change principalOperator a (boundedMultiplier d (principalCofactor a f)) x = f x
  rw [hp, hm, hc, hmx, hcx]
  have hde : d (-x) = d x := by
    calc
      d (-x) = d (-x) * (d x * (1 - a x * a (-x))) := by rw [hx, mul_one]
      _ = d x * (d (-x) * (1 - a (-x) * a x)) := by ring
      _ = d x := by rw [hxn, mul_one]
  rw [hde]
  calc
    _ = (d x * (1 - a x * a (-x))) * f x := by ring
    _ = f x := by rw [hx, one_mul]

/-- Ограниченно обратимый главный множитель. -/
def principalEquiv (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) :
    IntervalL2 ≃L[ℂ] IntervalL2 :=
  ContinuousLinearEquiv.equivOfInverse (principalOperator a) (principalOperatorInverse a d)
    (principalOperatorInverse_left a d hd) (principalOperatorInverse_right a d hd)

theorem principalOperatorInverse_injective (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) :
    Function.Injective (principalOperatorInverse a d) := by
  intro f g hfg
  rw [← principalOperatorInverse_right a d hd f, ← principalOperatorInverse_right a d hd g, hfg]

/-- Обратный к `L_a`: `G (I + a R)⁻¹`, где `G` — обратный к `-D²` с условиями Дирихле. -/
def variableGreen (a d : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  spectralGreen.comp (principalOperatorInverse a d)

theorem variableGreen_compact (a d : IntervalLInfinity) :
    IsCompactOperator (variableGreen a d) :=
  spectralGreen_compact.comp_clm (principalOperatorInverse a d)

theorem variableGreen_memDirichletH2 (a d : IntervalLInfinity) (g : IntervalL2) :
    MemDirichletH2 (variableGreen a d g) :=
  spectralGreen_memDirichletH2 (principalOperatorInverse a d g)

theorem variableGreen_injective (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) :
    Function.Injective (variableGreen a d) :=
  spectralGreen_injective.comp (principalOperatorInverse_injective a d hd)

theorem variableGreen_right_inverse (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (g : IntervalL2) :
    variableSobolevOperator a (variableGreen a d g) (variableGreen_memDirichletH2 a d g).1 = g := by
  have h := spectralGreen_right_inverse (principalOperatorInverse a d g)
  rw [variableSobolevOperator_eq_principal]
  exact (congrArg (principalOperator a) h).trans (principalOperatorInverse_right a d hd g)

theorem variableGreen_left_inverse (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f : IntervalL2)
    (hf : MemDirichletH2 f) :
    variableGreen a d (variableSobolevOperator a f hf.1) = f := by
  change spectralGreen (principalOperatorInverse a d (variableSobolevOperator a f hf.1)) = f
  rw [variableSobolevOperator_eq_principal, principalOperatorInverse_left a d hd]
  exact spectralGreen_left_inverse f hf

theorem variableSobolevOperator_of_eq_green (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f g : IntervalL2)
    (h : f = variableGreen a d g) (hf : MemIntervalH2 f) :
    variableSobolevOperator a f hf = g := by
  subst h
  exact variableGreen_right_inverse a d hd g

/-- Разрешимость: `L_a f = g` на области Дирихле тогда и только тогда, когда `f = K g`. -/
theorem variableOperator_solution_iff (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f g : IntervalL2) :
    (∃ hf : MemDirichletH2 f, variableSobolevOperator a f hf.1 = g) ↔
      f = variableGreen a d g := by
  constructor
  · rintro ⟨hf, he⟩
    rw [← he, variableGreen_left_inverse a d hd f hf]
  · intro h
    have hf : MemDirichletH2 f := h ▸ variableGreen_memDirichletH2 a d g
    exact ⟨hf, variableSobolevOperator_of_eq_green a d hd f g h hf.1⟩

/-- Нуль не является собственным значением. -/
theorem variableOperator_kernel_trivial (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f : IntervalL2)
    (hf : MemDirichletH2 f) (h : variableSobolevOperator a f hf.1 = 0) : f = 0 := by
  rw [← variableGreen_left_inverse a d hd f hf, h, map_zero]

/-- Собственные пары `L_a` — это в точности собственные пары компактного обратного. -/
theorem variableOperator_eigen_iff (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f : IntervalL2)
    (lam : ℂ) (hlam : lam ≠ 0) :
    (∃ hf : MemDirichletH2 f, variableSobolevOperator a f hf.1 = lam • f) ↔
      variableGreen a d f = lam⁻¹ • f := by
  rw [variableOperator_solution_iff a d hd f (lam • f), map_smul]
  constructor
  · intro h
    rw [eq_inv_smul_iff₀ hlam]
    exact h.symm
  · intro h
    rw [h, smul_inv_smul₀ hlam]

theorem variableOperator_eigenvalue_ne_zero (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (f : IntervalL2)
    (hf : MemDirichletH2 f) (hne : f ≠ 0) (lam : ℂ)
    (he : variableSobolevOperator a f hf.1 = lam • f) : lam ≠ 0 := by
  rintro rfl
  rw [zero_smul] at he
  exact hne (variableOperator_kernel_trivial a d hd f hf he)

/-- Собственные подпространства конечномерны. -/
theorem variableOperator_finiteDimensional_eigenspace (a d : IntervalLInfinity) (lam : ℂ)
    (hlam : lam ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace (variableGreen a d).toLinearMap lam⁻¹) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (variableGreen_compact a d) lam⁻¹
    (inv_ne_zero hlam)

/-- Альтернатива Фредгольма для `L_a`: каждое комплексное число либо собственное значение,
либо неоднородная задача `(L_a - λ) f = g` однозначно разрешима для каждой правой части. -/
theorem variableOperator_fredholm (a d : IntervalLInfinity)
    (hd : ∀ᵐ x ∂intervalMeasure, d x * (1 - a x * a (-x)) = 1) (lam : ℂ) :
    (∃ f : IntervalL2, f ≠ 0 ∧
      ∃ hf : MemDirichletH2 f, variableSobolevOperator a f hf.1 = lam • f) ∨
    (∀ g : IntervalL2, ∃! f : IntervalL2,
      ∃ hf : MemDirichletH2 f, variableSobolevOperator a f hf.1 = lam • f + g) := by
  by_cases hlam : lam = 0
  · right
    subst hlam
    intro g
    refine ⟨variableGreen a d g, ?_, ?_⟩
    · exact (variableOperator_solution_iff a d hd _ _).mpr (by rw [zero_smul, zero_add])
    · intro f hf
      have h := (variableOperator_solution_iff a d hd f _).mp hf
      rwa [zero_smul, zero_add] at h
  · have hmu : lam⁻¹ ≠ 0 := inv_ne_zero hlam
    rcases (variableGreen_compact a d).hasEigenvalue_or_mem_resolventSet hmu with he | hr
    · left
      obtain ⟨f, hf⟩ := he.exists_hasEigenvector
      refine ⟨f, hf.2, ?_⟩
      exact (variableOperator_eigen_iff a d hd f lam hlam).mpr
        (Module.End.mem_eigenspace_iff.mp hf.1)
    · right
      obtain ⟨u, hu⟩ := (spectrum.mem_resolventSet_iff.mp hr)
      let S : IntervalL2 →L[ℂ] IntervalL2 := (↑u⁻¹ : IntervalL2 →L[ℂ] IntervalL2)
      have hSu : ∀ f : IntervalL2, S (lam⁻¹ • f - variableGreen a d f) = f := by
        intro f
        have h := congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T f) u.inv_mul
        rw [hu] at h
        exact h
      have huS : ∀ f : IntervalL2, lam⁻¹ • S f - variableGreen a d (S f) = f := by
        intro f
        have h := congrArg (fun T : IntervalL2 →L[ℂ] IntervalL2 => T f) u.mul_inv
        rw [hu] at h
        exact h
      have hkey : ∀ f g : IntervalL2, f = variableGreen a d (lam • f + g) ↔
          lam⁻¹ • f - variableGreen a d f = lam⁻¹ • variableGreen a d g := by
        intro f g
        rw [map_add, map_smul]
        constructor
        · intro h
          have h2 : lam⁻¹ • f = variableGreen a d f + lam⁻¹ • variableGreen a d g := by
            conv_lhs => rw [h]
            rw [smul_add, inv_smul_smul₀ hlam]
          rw [h2, add_sub_cancel_left]
        · intro h
          have h2 : lam⁻¹ • f = variableGreen a d f + lam⁻¹ • variableGreen a d g := by
            rw [← h, add_sub_cancel]
          have h3 := congrArg (fun v : IntervalL2 => lam • v) h2
          simp only [smul_inv_smul₀ hlam, smul_add] at h3
          exact h3
      intro g
      refine ⟨S (lam⁻¹ • variableGreen a d g), ?_, ?_⟩
      · exact (variableOperator_solution_iff a d hd _ _).mpr ((hkey _ g).mpr (huS _))
      · intro f hf
        have h := (hkey f g).mp ((variableOperator_solution_iff a d hd f _).mp hf)
        rw [← h, hSu]

theorem determinantInverse_memLp (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    MemLp (fun x => (1 - a x * a (-x))⁻¹) ∞ intervalMeasure := by
  have hm : AEMeasurable a intervalMeasure := ha.aestronglyMeasurable.aemeasurable
  have hn : AEMeasurable (fun x => a (-x)) intervalMeasure :=
    hm.comp_quasiMeasurePreserving interval_neg_measurePreserving.quasiMeasurePreserving
  apply memLp_top_of_bound ((hm.mul hn).const_sub 1).inv.aestronglyMeasurable (1 - kappa)⁻¹
  filter_upwards [hproduct] with x hx
  have hpos : 0 < 1 - kappa := by linarith
  have hle : 1 - kappa ≤ 1 - a x * a (-x) := by linarith [le_abs_self (a x * a (-x))]
  have hp : 0 < 1 - a x * a (-x) := lt_of_lt_of_le hpos hle
  change ‖(1 - a x * a (-x))⁻¹‖ ≤ (1 - kappa)⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact (inv_le_inv₀ hp hpos).mpr hle

/-- Класс `L∞` функции `1 / (1 - a(x) a(-x))`. -/
def determinantInverse (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) : IntervalLInfinity :=
  realIntervalCoefficient (fun x => (1 - a x * a (-x))⁻¹)
    (determinantInverse_memLp a ha kappa hkappa1 hproduct)

theorem determinantInverse_identity (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∀ᵐ x ∂intervalMeasure, determinantInverse a ha kappa hkappa1 hproduct x *
      (1 - realIntervalCoefficient a ha x * realIntervalCoefficient a ha (-x)) = 1 := by
  have hn : ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient a ha (-x) = (a (-x) : ℂ) := by
    filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
      (realIntervalCoefficient_ae a ha)] with x hx
    exact hx
  filter_upwards [realIntervalCoefficient_ae _
    (determinantInverse_memLp a ha kappa hkappa1 hproduct),
    realIntervalCoefficient_ae a ha, hn, hproduct] with x hdx hax hanx hx
  change realIntervalCoefficient _ (determinantInverse_memLp a ha kappa hkappa1 hproduct) x *
    (1 - realIntervalCoefficient a ha x * realIntervalCoefficient a ha (-x)) = 1
  rw [hdx, hax, hanx]
  have hne : 1 - a x * a (-x) ≠ 0 := by
    have : 0 < 1 - a x * a (-x) := by linarith [le_abs_self (a x * a (-x))]
    exact ne_of_gt this
  have h := inv_mul_cancel₀ hne
  exact_mod_cast h

theorem realIntervalCoefficient_real (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure) :
    ∀ᵐ x ∂intervalMeasure, star (realIntervalCoefficient a ha x) =
      realIntervalCoefficient a ha x := by
  filter_upwards [realIntervalCoefficient_ae a ha] with x hx
  rw [hx]
  simp

/-- Главный множитель `I + a R` симметричен в `L₂` тогда и только тогда, когда `a` чётна
почти всюду. Поэтому взвешенная симметризация случая C5 применима только к чётным `a`;
отсутствие базиса для остальных коэффициентов отсюда не следует. -/
theorem principalOperator_isSymmetric_iff (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure) :
    (principalOperator (realIntervalCoefficient a ha)).IsSymmetric ↔
      ∀ᵐ x ∂intervalMeasure, a (-x) = a x := by
  let A := realIntervalCoefficient a ha
  have hM : (boundedMultiplier A).IsSymmetric :=
    boundedMultiplier_symmetric A (realIntervalCoefficient_real a ha)
  have hadj : ∀ f g : IntervalL2, inner ℂ (reflectedMultiplier A f) g =
      inner ℂ f (l2Reflect (boundedMultiplier A g)) := by
    intro f g
    calc
      inner ℂ (boundedMultiplier A (l2Reflect f)) g =
          inner ℂ (l2Reflect f) (boundedMultiplier A g) := hM _ _
      _ = inner ℂ (l2Reflect (l2Reflect f)) (l2Reflect (boundedMultiplier A g)) :=
        (l2Reflect.inner_map_map _ _).symm
      _ = _ := by rw [l2Reflect_involution]
  constructor
  · intro hsym
    have hcomm : ∀ g : IntervalL2,
        reflectedMultiplier A g = l2Reflect (boundedMultiplier A g) := by
      intro g
      apply ext_inner_left ℂ
      intro f
      have h1 : inner ℂ (f + reflectedMultiplier A f) g =
          inner ℂ f (g + reflectedMultiplier A g) := hsym f g
      rw [inner_add_left, inner_add_right, hadj] at h1
      exact (add_left_cancel h1).symm
    let : IsFiniteMeasure intervalMeasure := by
      change IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1))
      infer_instance
    let one : IntervalL2 := (memLp_const (1 : ℂ)).toLp (fun _ => (1 : ℂ))
    have hone : one =ᵐ[intervalMeasure] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
    have honen : ∀ᵐ x ∂intervalMeasure, one (-x) = 1 := by
      filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae hone] with x hx
      exact hx
    have hmn : ∀ᵐ x ∂intervalMeasure,
        boundedMultiplier A one (-x) = A (-x) * one (-x) := by
      filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
        (boundedMultiplier_ae A one)] with x hx
      exact hx
    have han : ∀ᵐ x ∂intervalMeasure, A (-x) = (a (-x) : ℂ) := by
      filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
        (realIntervalCoefficient_ae a ha)] with x hx
      exact hx
    filter_upwards [reflectedMultiplier_ae A one, l2Reflect_ae (boundedMultiplier A one),
      hmn, honen, realIntervalCoefficient_ae a ha, han] with x hl hr hm h1 hax hanx
    have hx : reflectedMultiplier A one x = l2Reflect (boundedMultiplier A one) x := by
      rw [hcomm one]
    rw [hl, hr, hm, h1, mul_one, mul_one] at hx
    change A x = A (-x) at hx
    have hax' : A x = (a x : ℂ) := hax
    rw [hax', hanx] at hx
    exact_mod_cast hx.symm
  · intro heven
    have hA : ∀ᵐ x ∂intervalMeasure, A (-x) = A x := by
      have han : ∀ᵐ x ∂intervalMeasure, A (-x) = (a (-x) : ℂ) := by
        filter_upwards [interval_neg_measurePreserving.quasiMeasurePreserving.ae
          (realIntervalCoefficient_ae a ha)] with x hx
        exact hx
      filter_upwards [realIntervalCoefficient_ae a ha, han, heven] with x hx hn he
      have hx' : A x = (a x : ℂ) := hx
      rw [hn, hx', he]
    intro f g
    change inner ℂ (f + reflectedMultiplier A f) g = inner ℂ f (g + reflectedMultiplier A g)
    rw [inner_add_left, inner_add_right, hadj]
    change _ = _ + inner ℂ f (boundedMultiplier A (l2Reflect g))
    rw [boundedMultiplier_reflect A hA]

/-- Итог для всего класса постановки: при `|a(x) a(-x)| ≤ κ < 1` почти всюду оператор
`L_a` на слабой области Дирихле имеет компактный инъективный двусторонний обратный. -/
theorem productBound_compact_inverse (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ K : IntervalL2 →L[ℂ] IntervalL2, IsCompactOperator K ∧ Function.Injective K ∧
      (∀ g : IntervalL2, ∃ hf : MemDirichletH2 (K g),
        variableSobolevOperator (realIntervalCoefficient a ha) (K g) hf.1 = g) ∧
      (∀ (f : IntervalL2) (hf : MemDirichletH2 f),
        K (variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) = f) := by
  let A := realIntervalCoefficient a ha
  let d := determinantInverse a ha kappa hkappa1 hproduct
  have hd := determinantInverse_identity a ha kappa hkappa1 hproduct
  exact ⟨variableGreen A d, variableGreen_compact A d, variableGreen_injective A d hd,
    fun g => ⟨variableGreen_memDirichletH2 A d g, variableGreen_right_inverse A d hd g⟩,
    fun f hf => variableGreen_left_inverse A d hd f hf⟩

/-- Дискретность спектра во всём классе постановки в форме альтернативы Фредгольма. -/
theorem productBound_fredholm (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (kappa : ℝ) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) (lam : ℂ) :
    (∃ f : IntervalL2, f ≠ 0 ∧ ∃ hf : MemDirichletH2 f,
      variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 = lam • f) ∨
    (∀ g : IntervalL2, ∃! f : IntervalL2, ∃ hf : MemDirichletH2 f,
      variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 = lam • f + g) :=
  variableOperator_fredholm (realIntervalCoefficient a ha)
    (determinantInverse a ha kappa hkappa1 hproduct)
    (determinantInverse_identity a ha kappa hkappa1 hproduct) lam

end Involution
