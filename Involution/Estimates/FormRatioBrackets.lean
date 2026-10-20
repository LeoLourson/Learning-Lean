module

public import Involution.Estimates.FormEnergy
public import Involution.Estimates.GeneralBrackets
public import Involution.Estimates.PositiveRatioBrackets

/-! Положительное отношение `a(x)/a(-x)` класса `W¹∞` (утверждение C22).

Калибровка `r = ρ^(1/8)`, `ρ(x) = q(x)/q(-x)`, как в C20, переводит `a` в чётный `b`.
Вместо возмущения оператора используется возмущение формы: в энергетической модели
`T = V (-D²) V` оператора `L_b` форма `∫ (r u)' conj (w v)'` отличается от формы `T`
на `𝔟`, подчинённую `T` с `p = 1/2`; порядок `T` равен `2`. Теорема 6.9 обзора S3
(`FormMarkusMatsaevStatement`) входит гипотезой. Вторая производная веса не нужна. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace Involution

/-- Коэффициент класса `W¹∞`: слабая производная лежит в `L∞`. -/
def MemIntervalW1Infinity (a : IntervalLInfinity) : Prop :=
  ∃ a' : IntervalLInfinity, HasIntervalWeakDeriv a a'

/-- Диагонализованная модель чётного коэффициента: `W = T_b^{-1/2}` в каналах отражения,
`V = W⁻¹`, `W G W eᵢ = λᵢ⁻¹ eᵢ` и линейная оценка счётной функции частот. -/
theorem evenModel_diagonal_data (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (kappa : ℝ)
    (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1) (heven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x)
    (hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa) :
    ∃ (Wm Vm : IntervalL2 →L[ℂ] IntervalL2) (ι : Type) (e : HilbertBasis ι ℂ IntervalL2)
      (lam : ι → ℝ) (ν : ℝ), 0 < ν ∧ Wm.IsSymmetric ∧ (∀ z, Vm (Wm z) = z) ∧
      (∀ z, Wm (Vm z) = z) ∧
      (∀ g, principalOperator (realIntervalCoefficient b hb) (Wm g) = Vm g) ∧
      (∀ i, 0 < lam i) ∧
      (∀ i, Wm (spectralGreen (Wm (e i))) = (((lam i)⁻¹ : ℝ) : ℂ) • e i) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t ^ 2) →
        (s.card : ℝ) ≤ 2 * ν / Real.pi * t + 2) := by
  obtain ⟨ve, we, hve, hwe, hree, hive, hpe, hweb, hveb⟩ :=
    evenCoefficient_channel_weights_bounded b hb kappa hkappa hkappa1 heven hbprod 1
      (by norm_num)
  obtain ⟨vo, wo, hvo, hwo, hreo, hivo, hpo, hwob, hvob⟩ :=
    evenCoefficient_channel_weights_bounded b hb kappa hkappa hkappa1 heven hbprod (-1)
      (by norm_num)
  simp only [Complex.ofReal_one] at hpe
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hpo
  set Bc := realIntervalCoefficient b hb with hBc
  -- постоянные
  have hsk : Real.sqrt kappa < 1 :=
    (Real.sqrt_lt hkappa (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hkappa1)
  have hsk0 : 0 ≤ Real.sqrt kappa := Real.sqrt_nonneg _
  have hq : 0 < 1 - Real.sqrt kappa := by linarith
  set ν := (Real.sqrt (1 - Real.sqrt kappa))⁻¹ with hν
  have hν0 : 0 < ν := inv_pos.mpr (Real.sqrt_pos.mpr hq)
  have hν2 : ν * ν = (1 - Real.sqrt kappa)⁻¹ := by
    rw [hν, ← mul_inv, Real.mul_self_sqrt hq.le]
  -- операторы
  let Wm : IntervalL2 →L[ℂ] IntervalL2 := parityMultiplierSum we wo
  let Vm : IntervalL2 →L[ℂ] IntervalL2 := parityMultiplierSum ve vo
  let T : IntervalL2 →L[ℂ] IntervalL2 := principalOperator Bc
  let Kt : IntervalL2 →L[ℂ] IntervalL2 := Wm ∘L spectralGreen ∘L Wm
  have hWnorm : ‖Wm‖ ≤ ν := parityMultiplierSum_norm_le we wo ν hν0.le hwe hwo hweb hwob
  have hVnorm : ‖Vm‖ ≤ Real.sqrt (1 + Real.sqrt kappa) :=
    parityMultiplierSum_norm_le ve vo _ (Real.sqrt_nonneg _) hve hvo hveb hvob
  have hWsym : Wm.IsSymmetric := parityMultiplierSum_symmetric we wo hwe hwo hree hreo
  have hVW : ∀ z : IntervalL2, Vm (Wm z) = z :=
    parityMultiplierSum_inverse we wo ve vo hwe hwo hive hivo
  have hbabs : ∀ᵐ x ∂intervalMeasure, ‖Bc x‖ ≤ Real.sqrt kappa := by
    filter_upwards [evenCoefficient_abs_bound b kappa hkappa heven hbprod,
      realIntervalCoefficient_ae b hb] with x hx hbx
    change ‖realIntervalCoefficient b hb x‖ ≤ _
    rw [hbx, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hTnorm : ‖T‖ ≤ 1 + Real.sqrt kappa := principalOperator_norm_le Bc _ hsk0 hbabs
  have hTW : ∀ g : IntervalL2, T (Wm g) = Vm g := by
    intro g
    change principalOperator Bc (boundedMultiplier we (l2EvenPart g) +
      boundedMultiplier wo (l2OddPart g)) =
        boundedMultiplier ve (l2EvenPart g) + boundedMultiplier vo (l2OddPart g)
    rw [map_add,
      principalOperator_weight Bc ve we 1 hwe hive hpe (l2EvenPart g)
        (by rw [l2EvenPart_fixed, one_smul]),
      principalOperator_weight Bc vo wo (-1) hwo hivo hpo (l2OddPart g)
        (by rw [l2OddPart_neg, neg_one_smul])]
  -- собственный базис
  let be := weightedChannelEigenbasis we hwe hree 1
  let bo := weightedChannelEigenbasis wo hwo hreo (-1)
  let bH := parityHilbertBasis be bo
  have hKe : ∀ i, Kt (bH (Sum.inl i)) = i.1 • bH (Sum.inl i) := by
    intro i
    have hbi : bH (Sum.inl i) = (be i : IntervalL2) := parityHilbertBasis_apply be bo _
    rw [hbi]
    have hz : spectralGreen (boundedMultiplier we (be i : IntervalL2)) ∈ parityL2Submodule 1 :=
      spectralGreen_parity_invariant 1 _
        (boundedMultiplier_parity_invariant we hwe 1 _ (be i).property)
    change Wm (spectralGreen (Wm (be i : IntervalL2))) = _
    rw [show Wm (be i : IntervalL2) = boundedMultiplier we (be i : IntervalL2) from
      parityMultiplierSum_even we wo (be i)]
    rw [show Wm (spectralGreen (boundedMultiplier we (be i : IntervalL2))) =
      boundedMultiplier we (spectralGreen (boundedMultiplier we (be i : IntervalL2))) from
      parityMultiplierSum_even we wo ⟨_, hz⟩]
    exact congrArg Subtype.val (weightedChannelEigenbasis_equation we hwe hree 1 i)
  have hKo : ∀ i, Kt (bH (Sum.inr i)) = i.1 • bH (Sum.inr i) := by
    intro i
    have hbi : bH (Sum.inr i) = (bo i : IntervalL2) := parityHilbertBasis_apply be bo _
    rw [hbi]
    have hz : spectralGreen (boundedMultiplier wo (bo i : IntervalL2)) ∈
        parityL2Submodule (-1) :=
      spectralGreen_parity_invariant (-1) _
        (boundedMultiplier_parity_invariant wo hwo (-1) _ (bo i).property)
    change Wm (spectralGreen (Wm (bo i : IntervalL2))) = _
    rw [show Wm (bo i : IntervalL2) = boundedMultiplier wo (bo i : IntervalL2) from
      parityMultiplierSum_odd we wo (bo i)]
    rw [show Wm (spectralGreen (boundedMultiplier wo (bo i : IntervalL2))) =
      boundedMultiplier wo (spectralGreen (boundedMultiplier wo (bo i : IntervalL2))) from
      parityMultiplierSum_odd we wo ⟨_, hz⟩]
    exact congrArg Subtype.val (weightedChannelEigenbasis_equation wo hwo hreo (-1) i)
  let mu : CompactEigenbasisIndex (weightedParityGreen we hwe 1) ⊕
      CompactEigenbasisIndex (weightedParityGreen wo hwo (-1)) → ℂ :=
    Sum.elim (fun i => i.1) (fun i => i.1)
  have hKmu : ∀ i, Kt (bH i) = mu i • bH i := by
    intro i
    cases i with
    | inl i => exact hKe i
    | inr i => exact hKo i
  have hmu0 : ∀ i, mu i ≠ 0 := by
    intro i
    cases i with
    | inl i => exact weightedChannelEigenvalue_ne_zero ve we hwe hree hive 1 i
    | inr i => exact weightedChannelEigenvalue_ne_zero vo wo hwo hreo hivo (-1) i
  have hmuE : ∀ i, mu i = ((‖greenDeriv (Wm (bH i))‖ ^ 2 : ℝ) : ℂ) := fun i =>
    sandwich_eigenvalue_eq_energy Wm hWsym (bH i) (bH.orthonormal.norm_eq_one i) (mu i)
      (hKmu i)
  let lam := fun i => (‖greenDeriv (Wm (bH i))‖ ^ 2)⁻¹
  have hEpos : ∀ i, 0 < ‖greenDeriv (Wm (bH i))‖ ^ 2 := by
    intro i
    refine lt_of_le_of_ne (sq_nonneg _) fun h0 => hmu0 i ?_
    rw [hmuE i, ← h0, Complex.ofReal_zero]
  have hlam : ∀ i, 0 < lam i := fun i => inv_pos.mpr (hEpos i)
  have hK₀ : ∀ i, Kt (bH i) = (((lam i)⁻¹ : ℝ) : ℂ) • bH i := by
    intro i
    rw [hKmu i, hmuE i]
    change _ = ((((‖greenDeriv (Wm (bH i))‖ ^ 2)⁻¹)⁻¹ : ℝ) : ℂ) • bH i
    rw [inv_inv]
  -- оценка счётной функции
  have hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset _, (∀ i ∈ s, lam i ≤ t ^ 2) →
      (s.card : ℝ) ≤ 2 * ν / Real.pi * t + 2 := fun t ht s hs =>
    green_sandwich_eigen_count Wm Wm ν hν0 hWnorm hWnorm bH bH.orthonormal lam hlam hK₀ t ht
      s hs
  have hWV : ∀ z : IntervalL2, Wm (Vm z) = z :=
    parityMultiplierSum_inverse ve vo we wo hve hvo
      (hive.mono fun x hx => by rwa [mul_comm]) (hivo.mono fun x hx => by rwa [mul_comm])
  exact ⟨Wm, Vm, _, bH, lam, ν, hν0, hWsym, hVW, hWV, hTW, hlam, hK₀, hcount⟩

/-- Отношение `ρ(x) = q(x)/q(-x)` положительного коэффициента `q ∈ W¹∞` лежит в `W¹∞`. -/
theorem positiveRatio_hasACDerivative (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW1Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hρ : MemLp (fun x => q x / q (-x)) ∞ intervalMeasure) :
    ∃ ρ' : IntervalLInfinity,
      HasACMultiplierDerivative (realIntervalCoefficient (fun x => q x / q (-x)) hρ) ρ' := by
  obtain ⟨a', h0⟩ := hreg
  let Q := realIntervalCoefficient q hq
  have hA0 := HasACMultiplierDerivative.of_weak h0
  let R := reflectCoefficient Q
  have hR0 : HasACMultiplierDerivative R (-reflectCoefficient a') := hA0.reflect
  have hlown : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q (-x) :=
    interval_neg_measurePreserving.quasiMeasurePreserving.ae hlow
  have hRae : ∀ᵐ x ∂intervalMeasure, R x = ((q (-x) : ℝ) : ℂ) := by
    filter_upwards [reflectCoefficient_ae Q,
      interval_neg_measurePreserving.quasiMeasurePreserving.ae
        (realIntervalCoefficient_ae q hq)] with x h1 h2
    rw [h1]
    exact h2
  have hRlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ ‖R x‖ := by
    filter_upwards [hRae, hlown] with x h1 h2
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hq₀ h2)]
    exact h2
  let Ri := inverseCoefficient R q₀ hq₀ hRlow
  have hRi0 := hR0.coeff_inv q₀ hq₀ hRlow
  have hQ0 := hA0.coeff_mul hRi0
  have hQeq : realIntervalCoefficient (fun x => q x / q (-x)) hρ = coefficientProduct Q Ri := by
    apply Lp.ext
    filter_upwards [realIntervalCoefficient_ae _ hρ, coefficientProduct_ae Q Ri,
      realIntervalCoefficient_ae q hq, inverseCoefficient_ae R q₀ hq₀ hRlow, hRae]
      with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
    push_cast
    rw [div_eq_mul_inv]
  rw [hQeq]
  exact ⟨_, hQ0⟩

/-- Обратный квадратный корень веса `W¹∞`, отделённого от нуля, лежит в `W¹∞`. -/
theorem inverseSqrtWeight_hasACDerivative (p : ℝ → ℝ) (hp : MemLp p ∞ intervalMeasure)
    (m M : ℝ) (hm : 0 < m) (hlower : ∀ᵐ x ∂intervalMeasure, m ≤ p x)
    (hupper : ∀ᵐ x ∂intervalMeasure, p x ≤ M) (a' : IntervalLInfinity)
    (ha : HasACMultiplierDerivative (realIntervalCoefficient p hp) a') :
    ∃ w' : IntervalLInfinity,
      HasACMultiplierDerivative (inverseSqrtWeight p hp m hm hlower) w' := by
  let S := sqrtWeight p hp M hupper
  let W := inverseSqrtWeight p hp m hm hlower
  have hS := sqrtWeight_hasACDerivative p hp m M hm hlower hupper a' ha
  have hslow : ∀ᵐ x ∂intervalMeasure, Real.sqrt m ≤ ‖S x‖ :=
    sqrtWeight_norm_lower p hp m M hlower hupper
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hW := hS.coeff_inv (Real.sqrt m) hsm hslow
  have heq : inverseCoefficient S (Real.sqrt m) hsm hslow = W := by
    apply Lp.ext
    filter_upwards [inverseCoefficient_reciprocal S (Real.sqrt m) hsm hslow,
      sqrtWeight_inverseSqrtWeight p hp m M hm hlower hupper, hslow] with x hi hw hl
    exact mul_left_cancel₀ (norm_pos_iff.mp (lt_of_lt_of_le hsm hl)) (hi.trans hw.symm)
  rw [heq] at hW
  exact ⟨_, hW⟩

/-- Данные калибровки `r = (q(x)/q(-x))^(1/8)` для `q ∈ W¹∞`: вещественные `r`, `w = 1/r`
класса `W¹∞` и чётный коэффициент `b` с `b r = a r(-·)`. -/
theorem positiveRatio_gauge_data_W1 (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW1Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hratio : ∀ᵐ x ∂intervalMeasure, a x = q x * a (-x)) (kappa : ℝ)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (r wg r' wg' : IntervalLInfinity),
      (∀ᵐ x ∂intervalMeasure, b (-x) = b x) ∧
      (∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa) ∧
      (∀ᵐ x ∂intervalMeasure, r x * wg x = 1) ∧
      (∀ᵐ x ∂intervalMeasure, star (r x) = r x) ∧
      (∀ᵐ x ∂intervalMeasure, star (wg x) = wg x) ∧
      HasACMultiplierDerivative r r' ∧ HasACMultiplierDerivative wg wg' ∧
      (∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x =
        realIntervalCoefficient a ha x * r (-x)) := by
  have hneg := interval_neg_measurePreserving.quasiMeasurePreserving
  set Mq := ‖realIntervalCoefficient q hq‖ + q₀ with hMqdef
  have hMq : 0 < Mq := by positivity
  have hup : ∀ᵐ x ∂intervalMeasure, q x ≤ Mq := by
    filter_upwards [intervalLInfinity_ae_norm_le (realIntervalCoefficient q hq),
      realIntervalCoefficient_ae q hq] with x h1 h2
    rw [h2, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [le_abs_self (q x)]
  have hlown : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q (-x) := hneg.ae hlow
  have hupn : ∀ᵐ x ∂intervalMeasure, q (-x) ≤ Mq := hneg.ae hup
  have hration : ∀ᵐ x ∂intervalMeasure, a (-x) = q (-x) * a (- -x) := hneg.ae hratio
  let ρ : ℝ → ℝ := fun x => q x / q (-x)
  have hqm : AEMeasurable q intervalMeasure := hq.aestronglyMeasurable.aemeasurable
  have hqmn : AEMeasurable (fun x => q (-x)) intervalMeasure :=
    hqm.comp_quasiMeasurePreserving hneg
  have hρm : AEMeasurable ρ intervalMeasure := hqm.div hqmn
  have hρlow : ∀ᵐ x ∂intervalMeasure, q₀ / Mq ≤ ρ x := by
    filter_upwards [hlow, hupn, hlown] with x h1 h2 h3
    exact div_le_div₀ (lt_of_lt_of_le hq₀ h1).le h1 (lt_of_lt_of_le hq₀ h3) h2
  have hρup : ∀ᵐ x ∂intervalMeasure, ρ x ≤ Mq / q₀ := by
    filter_upwards [hup, hlown] with x h1 h2
    exact div_le_div₀ hMq.le h1 hq₀ h2
  have hm1 : 0 < q₀ / Mq := div_pos hq₀ hMq
  have hρ : MemLp ρ ∞ intervalMeasure := by
    apply memLp_top_of_bound hρm.aestronglyMeasurable (Mq / q₀)
    filter_upwards [hρup, hρlow] with x h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (hm1.le.trans h2)]
    exact h1
  obtain ⟨ρ', hρW⟩ := positiveRatio_hasACDerivative q hq hreg q₀ hq₀ hlow hρ
  -- первый корень
  let s1 : ℝ → ℝ := fun x => Real.sqrt (ρ x)
  have hs1 : MemLp s1 ∞ intervalMeasure := sqrt_memLp_of_upper_bound ρ hρ _ hρup
  have hs1W := sqrtWeight_hasACDerivative ρ hρ _ _ hm1 hρlow hρup ρ' hρW
  have hs1low : ∀ᵐ x ∂intervalMeasure, Real.sqrt (q₀ / Mq) ≤ s1 x :=
    hρlow.mono fun x hx => Real.sqrt_le_sqrt hx
  have hs1up : ∀ᵐ x ∂intervalMeasure, s1 x ≤ Real.sqrt (Mq / q₀) :=
    hρup.mono fun x hx => Real.sqrt_le_sqrt hx
  have hm2 : 0 < Real.sqrt (q₀ / Mq) := Real.sqrt_pos.mpr hm1
  -- второй корень
  let s2 : ℝ → ℝ := fun x => Real.sqrt (s1 x)
  have hs2 : MemLp s2 ∞ intervalMeasure := sqrt_memLp_of_upper_bound s1 hs1 _ hs1up
  have hs2W := sqrtWeight_hasACDerivative s1 hs1 _ _ hm2 hs1low hs1up _ hs1W
  have hs2low : ∀ᵐ x ∂intervalMeasure, Real.sqrt (Real.sqrt (q₀ / Mq)) ≤ s2 x :=
    hs1low.mono fun x hx => Real.sqrt_le_sqrt hx
  have hs2up : ∀ᵐ x ∂intervalMeasure, s2 x ≤ Real.sqrt (Real.sqrt (Mq / q₀)) :=
    hs1up.mono fun x hx => Real.sqrt_le_sqrt hx
  have hm3 : 0 < Real.sqrt (Real.sqrt (q₀ / Mq)) := Real.sqrt_pos.mpr hm2
  -- вес `r = √s2`
  let r := sqrtWeight s2 hs2 _ hs2up
  let wg := inverseSqrtWeight s2 hs2 _ hm3 hs2low
  have hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1 :=
    sqrtWeight_inverseSqrtWeight s2 hs2 _ _ hm3 hs2low hs2up
  have hr := sqrtWeight_hasACDerivative s2 hs2 _ _ hm3 hs2low hs2up _ hs2W
  obtain ⟨wg', hw⟩ := inverseSqrtWeight_hasACDerivative s2 hs2 _ _ hm3 hs2low hs2up _ hs2W
  have hrreal : ∀ᵐ x ∂intervalMeasure, star (r x) = r x := by
    filter_upwards [sqrtWeight_ae s2 hs2 _ hs2up] with x hx
    change star (sqrtWeight s2 hs2 _ hs2up x) = sqrtWeight s2 hs2 _ hs2up x
    rw [hx]
    simp
  let t : ℝ → ℝ := fun x => Real.sqrt (s2 x)
  have ht : ∀ᵐ x ∂intervalMeasure, 0 < t x ∧ t x ^ 8 = q x / q (-x) := by
    filter_upwards [hρlow] with x hx
    have hρx : 0 ≤ ρ x := hm1.le.trans hx
    exact ⟨Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le hm1 hx))),
      sqrt_sqrt_sqrt_pow_eight _ hρx⟩
  have htn : ∀ᵐ x ∂intervalMeasure, 0 < t (-x) ∧ t (-x) ^ 8 = q (-x) / q x := by
    filter_upwards [hneg.ae ht] with x hx
    simpa only [neg_neg] using hx
  let b : ℝ → ℝ := fun x => a x * t (-x) / t x
  have hbeven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x := by
    filter_upwards [ht, htn, hlow, hlown, hratio, hration] with x h1 h2 h3 h4 h5 h6
    rw [neg_neg] at h6
    have := positiveRatio_gauge_point (q x) (q (-x)) (a x) (a (-x)) (t x) (t (-x))
      (lt_of_lt_of_le hq₀ h3) h1.1 h2.1 h1.2 h2.2 h5 h6
    change a (-x) * t (- -x) / t (-x) = a x * t (-x) / t x
    rw [neg_neg, this]
  have hbmul : ∀ᵐ x ∂intervalMeasure, b x * b (-x) = a x * a (-x) := by
    filter_upwards [ht, htn] with x h1 h2
    change a x * t (-x) / t x * (a (-x) * t (- -x) / t (-x)) = _
    rw [neg_neg]
    field_simp [h1.1.ne', h2.1.ne']
  have hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa := by
    filter_upwards [hbmul, hproduct] with x h1 h2
    rwa [h1]
  have hb : MemLp b ∞ intervalMeasure := by
    have ham : AEMeasurable a intervalMeasure := ha.aestronglyMeasurable.aemeasurable
    have htm : AEMeasurable t intervalMeasure := hρm.sqrt.sqrt.sqrt
    have htmn : AEMeasurable (fun x => t (-x)) intervalMeasure :=
      htm.comp_quasiMeasurePreserving hneg
    apply memLp_top_of_bound ((ham.mul htmn).div htm).aestronglyMeasurable (Real.sqrt kappa)
    filter_upwards [hbeven, hbprod] with x h1 h2
    rw [h1, abs_mul_self] at h2
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by rw [sq]; exact h2)
  refine ⟨b, hb, r, wg, _, wg', hbeven, hbprod, hrw, hrreal,
    inverseSqrtWeight_real s2 hs2 _ hm3 hs2low, hr, hw, ?_⟩
  have hrn : ∀ᵐ x ∂intervalMeasure, r (-x) = ((t (-x) : ℝ) : ℂ) :=
    hneg.ae (sqrtWeight_ae s2 hs2 _ hs2up)
  filter_upwards [realIntervalCoefficient_ae b hb, realIntervalCoefficient_ae a ha,
    sqrtWeight_ae s2 hs2 _ hs2up, hrn, ht] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4]
  change ((a x * t (-x) / t x : ℝ) : ℂ) * ((t x : ℝ) : ℂ) = _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, div_mul_cancel₀ _ h5.1.ne']

theorem inner_boundedMultiplier_real (r : IntervalLInfinity)
    (hr : ∀ᵐ x ∂intervalMeasure, star (r x) = r x) (f g : IntervalL2) :
    inner ℂ (boundedMultiplier r f) g = inner ℂ f (boundedMultiplier r g) := by
  rw [l2_inner_integral, l2_inner_integral]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_ae r f, boundedMultiplier_ae r g, hr] with x h1 h2 h3
  rw [h1, h2, star_mul, h3]
  ring

theorem inner_boundedMultiplier_cancel (w r : IntervalLInfinity)
    (hw : ∀ᵐ x ∂intervalMeasure, star (w x) = w x)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * w x = 1) (f g : IntervalL2) :
    inner ℂ (boundedMultiplier w f) (boundedMultiplier r g) = inner ℂ f g := by
  rw [l2_inner_integral, l2_inner_integral]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_ae w f, boundedMultiplier_ae r g, hw, hrw]
    with x h1 h2 h3 h4
  rw [h1, h2, star_mul, h3]
  calc
    star (f x) * w x * (r x * g x) = star (f x) * (r x * w x) * g x := by ring
    _ = _ := by rw [h4, mul_one]

/-- Пробная функция и её производная образуют пару `H₀¹`. -/
theorem test_isH01Pair (φ : ℝ → ℝ) (hφ : IsSmoothTestOn (Set.Ioo (-1) 1) φ) :
    IsH01Pair ((continuous_memLp_interval (fun x => (φ x : ℂ))
        (Complex.continuous_ofReal.comp hφ.1.continuous)).toLp _)
      ((continuous_memLp_interval (fun x => ((deriv φ x : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp hφ.deriv.1.continuous)).toLp _) := by
  set u : ℝ → ℂ := fun x => (φ x : ℂ) with hu_def
  have hd : ∀ x, HasDerivAt u ((deriv φ x : ℝ) : ℂ) x := fun x =>
    ((hφ.1.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have hderiv : deriv u = fun x => ((deriv φ x : ℝ) : ℂ) := funext fun x => (hd x).deriv
  have hu : ContDiff ℝ 1 u :=
    (Complex.ofRealCLM.contDiff.comp hφ.1).of_le (by exact_mod_cast le_top)
  have hw := hasIntervalWeakDeriv_of_contDiff hu
  rw [hderiv] at hw
  have hleft : φ (-1) = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    have hi := hφ.2.2 hx
    simp only [Set.mem_Ioo, lt_self_iff_false, false_and] at hi)
  have hright : φ 1 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    have hi := hφ.2.2 hx
    simp only [Set.mem_Ioo, lt_self_iff_false, and_false] at hi)
  refine ⟨hasL2WeakDeriv_toLp _ _ hw, u, ⟨hu.continuous.continuousOn,
    (MemLp.coeFn_toLp _).symm⟩, ?_, ?_⟩
  · simp [hu_def, hleft]
  · simp [hu_def, hright]

/-- **Калибровка к чётному коэффициенту весом `W¹∞` при гипотезе
`FormMarkusMatsaevStatement`.** Пусть вещественный вес `r` класса `W¹∞` с вещественным
обратным `wg` класса `W¹∞` переводит коэффициент `A` в чётный `b`:
`b(x) r(x) = A(x) r(-x)`, `|b(x) b(-x)| ≤ κ < 1`. Тогда существует базис Рисса со скобками
из конечномерных подпространств слабой области Дирихле, инвариантных относительно `L_A`. -/
theorem bracket_basis_of_form_gauge (hF : FormMarkusMatsaevStatement)
    (A : IntervalLInfinity) (b : ℝ → ℝ) (hb : MemLp b ∞ intervalMeasure) (kappa : ℝ)
    (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (heven : ∀ᵐ x ∂intervalMeasure, b (-x) = b x)
    (hbprod : ∀ᵐ x ∂intervalMeasure, |b x * b (-x)| ≤ kappa)
    (r wg r' wg' : IntervalLInfinity)
    (hrw : ∀ᵐ x ∂intervalMeasure, r x * wg x = 1)
    (hrreal : ∀ᵐ x ∂intervalMeasure, star (r x) = r x)
    (hwreal : ∀ᵐ x ∂intervalMeasure, star (wg x) = wg x)
    (hr : HasACMultiplierDerivative r r') (hw : HasACMultiplierDerivative wg wg')
    (hg : ∀ᵐ x ∂intervalMeasure, realIntervalCoefficient b hb x * r x = A x * r (-x)) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f, variableSobolevOperator A f hf.1 ∈ W k := by
  obtain ⟨Wm, Vm, ι, e, lam, ν, hν, hWsym, hVW, hWV, hTW, hlam, hK, hcount⟩ :=
    evenModel_diagonal_data b hb kappa hkappa hkappa1 heven hbprod
  have hwr : ∀ᵐ x ∂intervalMeasure, wg x * r x = 1 := hrw.mono fun x hx => by
    rwa [mul_comm]
  have hpair : ∀ x ∈ formDomain e lam, IsH01Pair (Vm x) (formDeriv Wm e lam x) :=
    fun x hx => formDeriv_isH01Pair hlam hWsym hVW hWV hK hx
  -- производная `(V x)'` как линейное отображение на области формы
  let ΦL : formDomain e lam →ₗ[ℂ] IntervalL2 :=
    { toFun := fun x => formDeriv Wm e lam x
      map_add' := fun x y => by
        have h := (hpair x x.2).1.add (hpair y y.2).1
        rw [← map_add] at h
        exact (hpair _ (x + y).2).1.unique h
      map_smul' := fun c x => by
        have h := (hpair x x.2).1.smul c
        rw [← map_smul] at h
        exact (hpair _ (c • x).2).1.unique h }
  let XL : formDomain e lam →ₗ[ℂ] IntervalL2 := Vm.toLinearMap ∘ₗ (formDomain e lam).subtype
  let DwL : formDomain e lam →ₗ[ℂ] IntervalL2 :=
    (boundedMultiplier wg').toLinearMap ∘ₗ XL + (boundedMultiplier wg).toLinearMap ∘ₗ ΦL
  let DrL : formDomain e lam →ₗ[ℂ] IntervalL2 :=
    (boundedMultiplier r').toLinearMap ∘ₗ XL + (boundedMultiplier r).toLinearMap ∘ₗ ΦL
  -- форма возмущения `𝔟[y, x] = ⟨(w V y)', (r V x)'⟩ - ⟨(V y)', (V x)'⟩`
  let 𝔟 : formDomain e lam →ₗ⋆[ℂ] formDomain e lam →ₗ[ℂ] ℂ :=
    ((innerₛₗ ℂ).comp DwL).compl₂ DrL - ((innerₛₗ ℂ).comp ΦL).compl₂ ΦL
  have h𝔟 : ∀ y x : formDomain e lam, 𝔟 y x =
      inner ℂ (boundedMultiplier wg' (Vm y) + boundedMultiplier wg (formDeriv Wm e lam y))
        (boundedMultiplier r' (Vm x) + boundedMultiplier r (formDeriv Wm e lam x)) -
      inner ℂ (formDeriv Wm e lam y) (formDeriv Wm e lam x) := fun _ _ => rfl
  -- подчинённость с `p = 1/2`
  set bb := (‖wg'‖ * ‖r‖ + ‖wg‖ * ‖r'‖) * ‖Vm‖ with hbb
  set MM := ‖wg'‖ * ‖r'‖ * ‖Vm‖ ^ 2 with hMM
  have hbound : ∀ x : formDomain e lam, ‖𝔟 x x‖ ≤
      bb * formEnergy e lam x ^ (1 / 2 : ℝ) * (‖(x : IntervalL2)‖ ^ 2) ^ (1 - 1 / 2 : ℝ) +
        MM * ‖(x : IntervalL2)‖ ^ 2 := by
    intro x
    set X := Vm x with hX
    set P := formDeriv Wm e lam x with hP
    rw [formEnergy_eq hlam hWsym hVW hWV hK x.2, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    have hexp : 𝔟 x x = inner ℂ (boundedMultiplier wg' X) (boundedMultiplier r' X) +
        inner ℂ (boundedMultiplier wg' X) (boundedMultiplier r P) +
        inner ℂ (boundedMultiplier wg P) (boundedMultiplier r' X) := by
      rw [h𝔟, inner_add_left, inner_add_right, inner_add_right,
        inner_boundedMultiplier_cancel wg r hwreal hrw]
      ring
    have hXn : ‖X‖ ≤ ‖Vm‖ * ‖(x : IntervalL2)‖ := Vm.le_opNorm _
    have hm : ∀ (u : IntervalLInfinity) (f : IntervalL2), ‖boundedMultiplier u f‖ ≤ ‖u‖ * ‖f‖ :=
      fun u f => boundedMultiplier_norm_le u f
    have hin : ∀ (u v : IntervalLInfinity) (f g : IntervalL2),
        ‖inner ℂ (boundedMultiplier u f) (boundedMultiplier v g)‖ ≤ ‖u‖ * ‖v‖ * (‖f‖ * ‖g‖) := by
      intro u v f g
      calc
        _ ≤ ‖boundedMultiplier u f‖ * ‖boundedMultiplier v g‖ := norm_inner_le_norm _ _
        _ ≤ (‖u‖ * ‖f‖) * (‖v‖ * ‖g‖) :=
          mul_le_mul (hm u f) (hm v g) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc
      ‖𝔟 x x‖ ≤ ‖wg'‖ * ‖r'‖ * (‖X‖ * ‖X‖) + ‖wg'‖ * ‖r‖ * (‖X‖ * ‖P‖) +
          ‖wg‖ * ‖r'‖ * (‖P‖ * ‖X‖) := by
        rw [hexp]
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (hin _ _ _ _) (hin _ _ _ _))) (hin _ _ _ _))
      _ = ‖wg'‖ * ‖r'‖ * ‖X‖ ^ 2 + (‖wg'‖ * ‖r‖ + ‖wg‖ * ‖r'‖) * ‖X‖ * ‖P‖ := by ring
      _ ≤ ‖wg'‖ * ‖r'‖ * (‖Vm‖ * ‖(x : IntervalL2)‖) ^ 2 +
          (‖wg'‖ * ‖r‖ + ‖wg‖ * ‖r'‖) * (‖Vm‖ * ‖(x : IntervalL2)‖) * ‖P‖ := by
        gcongr
      _ = _ := by rw [hbb, hMM]; ring
  -- порядок `T` равен `2`
  have hcount' : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t) →
      (s.card : ℝ) ≤ 2 * ν / Real.pi * t ^ (2 : ℝ)⁻¹ + 2 := by
    intro t ht s hs
    have h := hcount (Real.sqrt t) (Real.sqrt_nonneg t) s
      (fun i hi => by rw [Real.sq_sqrt ht]; exact hs i hi)
    rwa [Real.sqrt_eq_rpow, one_div] at h
  obtain ⟨V, ⟨BV⟩, hinv⟩ := hF ι IntervalL2 e lam hlam 2 (2 * ν / Real.pi) 2 (by norm_num)
    hcount' (1 / 2) bb MM (by norm_num) (by norm_num) (by norm_num) (by positivity)
    (by positivity) 𝔟 hbound
  -- перенос на исходный оператор
  let Ψ : IntervalL2 ≃L[ℂ] IntervalL2 :=
    (ContinuousLinearEquiv.equivOfInverse Vm Wm hWV hVW).trans (multiplicationEquiv r wg hrw)
  refine ⟨fun k => (V k).map (Ψ : IntervalL2 →L[ℂ] IntervalL2).toLinearMap, ⟨BV.map Ψ⟩, ?_⟩
  rintro k _ ⟨v, hv, rfl⟩
  obtain ⟨hvD, z, hz, hform⟩ := hinv k v hv
  have hvp := hpair v hvD
  set X := Vm v with hX
  set P := formDeriv Wm e lam v with hP
  have hF1 : HasL2WeakDeriv (boundedMultiplier r X)
      (boundedMultiplier r' X + boundedMultiplier r P) := hvp.1.mul_coefficient hr
  have hFtr : HasDirichletTrace (boundedMultiplier r X) := hvp.2.mul_coefficient hr
  have key : HasL2WeakDeriv (boundedMultiplier r' X + boundedMultiplier r P)
      (-boundedMultiplier r (Wm z)) := by
    refine ⟨intervalL2_integrable _, intervalL2_integrable _, fun φ hφ => ?_⟩
    have hφp := test_isH01Pair φ hφ
    set φL := (continuous_memLp_interval (fun x => (φ x : ℂ))
      (Complex.continuous_ofReal.comp hφ.1.continuous)).toLp _ with hφL
    set φ'L := (continuous_memLp_interval (fun x => ((deriv φ x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hφ.deriv.1.continuous)).toLp _ with hφ'L
    have hYp : IsH01Pair (boundedMultiplier r φL)
        (boundedMultiplier r' φL + boundedMultiplier r φ'L) :=
      ⟨hφp.1.mul_coefficient hr, hφp.2.mul_coefficient hr⟩
    set y := Wm (boundedMultiplier r φL) with hy
    have hyV : Vm y = boundedMultiplier r φL := hVW _
    have hyD : y ∈ formDomain e lam :=
      mem_formDomain_of_isH01Pair hlam hWsym hVW hWV hK (by rw [hyV]; exact hYp)
    have hDw : boundedMultiplier wg' (Vm y) + boundedMultiplier wg (formDeriv Wm e lam y) =
        φ'L := by
      have h1 := (hpair y hyD).1.mul_coefficient hw
      rw [hyV, boundedMultiplier_inverse wg r hwr] at h1
      rw [hyV]
      exact h1.unique hφp.1
    have hf := hform ⟨y, hyD⟩
    have hp := inner_formDeriv hlam hWsym hVW hWV hK hvD hyD
    rw [← hp, h𝔟] at hf
    change inner ℂ (formDeriv Wm e lam y) P +
      (inner ℂ (boundedMultiplier wg' (Vm y) + boundedMultiplier wg (formDeriv Wm e lam y))
        (boundedMultiplier r' X + boundedMultiplier r P) -
        inner ℂ (formDeriv Wm e lam y) P) = inner ℂ y z at hf
    rw [add_sub_cancel, hDw] at hf
    have hyz : inner ℂ y z = inner ℂ φL (boundedMultiplier r (Wm z)) := by
      rw [hy]
      exact (hWsym _ z).trans (inner_boundedMultiplier_real r hrreal _ _)
    rw [setIntegral_real_smul_eq_inner _ hφ.deriv.1.continuous,
      setIntegral_real_smul_eq_inner _ hφ.1.continuous, inner_neg_right, neg_neg]
    exact hf.trans hyz
  have hFD : MemDirichletH2 (boundedMultiplier r X) := ⟨⟨_, _, hF1, key⟩, hFtr⟩
  rw [show (Ψ : IntervalL2 →L[ℂ] IntervalL2).toLinearMap v = boundedMultiplier r X from rfl]
  refine ⟨hFD, ?_⟩
  rw [variableSobolevOperator_eq_principal, (weakDerivatives_eq _ hFD.1 hF1 key).2, neg_neg,
    principalOperator_gauge A (realIntervalCoefficient b hb) r hg, hTW]
  exact ⟨z, hz, rfl⟩

/-- **Положительное отношение `a(x)/a(-x)` класса `W¹∞`: базис Рисса со скобками (C22).**
Условия: вещественный `a ∈ L∞`, `|a(x) a(-x)| ≤ κ < 1` почти всюду; вещественная
`q ∈ W¹∞`, `q ≥ q₀ > 0` почти всюду, `a(x) = q(x) a(-x)` почти всюду; теорема 6.9 обзора
S3 (`FormMarkusMatsaevStatement`). Существует последовательность конечномерных
подпространств слабой области Дирихле, инвариантных относительно `L_a` и образующих
базис Рисса со скобками. -/
theorem bracketBasis_of_positiveRatio_W1 (hF : FormMarkusMatsaevStatement)
    (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW1Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hratio : ∀ᵐ x ∂intervalMeasure, a x = q x * a (-x))
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∀ f ∈ W k, ∃ hf : MemDirichletH2 f,
        variableSobolevOperator (realIntervalCoefficient a ha) f hf.1 ∈ W k := by
  obtain ⟨b, hb, r, wg, r', wg', hbeven, hbprod, hrw, hrreal, hwreal, hr, hw, hg⟩ :=
    positiveRatio_gauge_data_W1 a ha q hq hreg q₀ hq₀ hlow hratio kappa hproduct
  exact bracket_basis_of_form_gauge hF (realIntervalCoefficient a ha) b hb kappa hkappa hkappa1
    hbeven hbprod r wg r' wg' hrw hrreal hwreal hr hw hg

/-- Блоки базиса со скобками из `bracketBasis_of_positiveRatio_W1` порождены корневыми
векторами `L_a`. -/
theorem bracketRootVectors_of_positiveRatio_W1 (hF : FormMarkusMatsaevStatement)
    (a : ℝ → ℝ) (ha : MemLp a ∞ intervalMeasure)
    (q : ℝ → ℝ) (hq : MemLp q ∞ intervalMeasure)
    (hreg : MemIntervalW1Infinity (realIntervalCoefficient q hq)) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hlow : ∀ᵐ x ∂intervalMeasure, q₀ ≤ q x)
    (hratio : ∀ᵐ x ∂intervalMeasure, a x = q x * a (-x))
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hkappa1 : kappa < 1)
    (hproduct : ∀ᵐ x ∂intervalMeasure, |a x * a (-x)| ≤ kappa) :
    ∃ W : ℕ → Submodule ℂ IntervalL2, Nonempty (RieszBasisWithBrackets W) ∧
      ∀ k, ∃ N : Module.End ℂ (W k),
        (∀ f : W k, ∃ hf : MemDirichletH2 (f : IntervalL2),
          ((N f : W k) : IntervalL2) =
            variableSobolevOperator (realIntervalCoefficient a ha) f hf.1) ∧
        ⨆ μ : ℂ, N.maxGenEigenspace μ = ⊤ := by
  obtain ⟨W, ⟨B⟩, hW⟩ := bracketBasis_of_positiveRatio_W1 hF a ha q hq hreg q₀ hq₀ hlow
    hratio kappa hkappa hkappa1 hproduct
  refine ⟨W, ⟨B⟩, fun k => ?_⟩
  have := B.finite k
  exact invariant_block_rootVectors (realIntervalCoefficient a ha) (W k) (hW k)

end Involution
