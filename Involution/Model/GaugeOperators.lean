module

public import Involution.Model.GaugeSimilarity
public import Involution.Model.ParityMultiplier

/-! Ограниченные операторы для калибровочного возмущения.
`greenDeriv` — оператор `h ↦ (G h)'`, где `G` — обратный оператор Дирихле;
`gaugeLowerOp` — младшие члены калибровки, применённые к `G h`. Здесь же собраны
оценки нормы и симметричность оператора умножения с разными весами в каналах. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Involution

theorem intervalLInfinity_norm_le (f : IntervalLInfinity) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂intervalMeasure, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  let : IsFiniteMeasure intervalMeasure := by
    change IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1))
    infer_instance
  have hn := Lp.norm_le_of_ae_bound hC h
  simpa using hn

theorem boundedMultiplier_norm_le_of_ae (w : IntervalLInfinity) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂intervalMeasure, ‖w x‖ ≤ C) (f : IntervalL2) :
    ‖boundedMultiplier w f‖ ≤ C * ‖f‖ :=
  (boundedMultiplier_norm_le w f).trans
    (mul_le_mul_of_nonneg_right (intervalLInfinity_norm_le w C hC h) (norm_nonneg f))

/-- Линейное отображение `h ↦ (G h)'`. -/
def greenDerivLinear : IntervalL2 →ₗ[ℂ] IntervalL2 where
  toFun h := firstWeakDeriv (spectralGreen h) (spectralGreen_memDirichletH2 h).1
  map_add' f g := by
    apply HasL2WeakDeriv.unique (firstWeakDeriv_spec _ _)
    rw [map_add]
    exact (firstWeakDeriv_spec _ _).add (firstWeakDeriv_spec _ _)
  map_smul' c f := by
    apply HasL2WeakDeriv.unique (firstWeakDeriv_spec _ _)
    rw [map_smul, RingHom.id_apply]
    exact (firstWeakDeriv_spec _ _).smul c

/-- Энергетическое тождество: `⟨G h, h⟩ = ⟨(G h)', (G h)'⟩`. -/
theorem greenDerivLinear_inner (h : IntervalL2) :
    inner ℂ (spectralGreen h) h = inner ℂ (greenDerivLinear h) (greenDerivLinear h) := by
  have he := negativeSecondWeakDeriv_energy (spectralGreen h) (spectralGreen h)
    (spectralGreen_memDirichletH2 h) (spectralGreen_memDirichletH2 h).1
  rwa [spectralGreen_right_inverse h] at he

theorem greenDerivLinear_norm_sq (h : IntervalL2) :
    ‖greenDerivLinear h‖ ^ 2 = RCLike.re (inner ℂ (spectralGreen h) h) := by
  rw [greenDerivLinear_inner]
  exact (inner_self_eq_norm_sq _).symm

theorem greenDerivLinear_norm_le (h : IntervalL2) :
    ‖greenDerivLinear h‖ ≤ Real.sqrt ‖spectralGreen‖ * ‖h‖ := by
  have h1 : ‖greenDerivLinear h‖ ^ 2 ≤ ‖spectralGreen‖ * ‖h‖ ^ 2 := by
    rw [greenDerivLinear_norm_sq]
    calc
      RCLike.re (inner ℂ (spectralGreen h) h) ≤ ‖spectralGreen h‖ * ‖h‖ := re_inner_le_norm _ _
      _ ≤ ‖spectralGreen‖ * ‖h‖ * ‖h‖ :=
        mul_le_mul_of_nonneg_right (spectralGreen.le_opNorm h) (norm_nonneg h)
      _ = _ := by ring
  calc
    ‖greenDerivLinear h‖ = Real.sqrt (‖greenDerivLinear h‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖spectralGreen‖ * ‖h‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := by rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg h)]

/-- Ограниченный оператор `h ↦ (G h)'`. -/
def greenDeriv : IntervalL2 →L[ℂ] IntervalL2 :=
  greenDerivLinear.mkContinuous (Real.sqrt ‖spectralGreen‖) greenDerivLinear_norm_le

theorem greenDeriv_apply (h : IntervalL2) :
    greenDeriv h = firstWeakDeriv (spectralGreen h) (spectralGreen_memDirichletH2 h).1 := rfl

theorem greenDeriv_inner (h : IntervalL2) :
    inner ℂ (spectralGreen h) h = inner ℂ (greenDeriv h) (greenDeriv h) :=
  greenDerivLinear_inner h

theorem greenDeriv_norm_sq (h : IntervalL2) :
    ‖greenDeriv h‖ ^ 2 = RCLike.re (inner ℂ (spectralGreen h) h) :=
  greenDerivLinear_norm_sq h

/-- Младшие члены калибровки как ограниченный оператор от правой части `h`. -/
def gaugeLowerOp (wg r' r'' : IntervalLInfinity) : IntervalL2 →L[ℂ] IntervalL2 :=
  -((2 : ℂ) • (boundedMultiplier wg ∘L boundedMultiplier r' ∘L greenDeriv) +
    boundedMultiplier wg ∘L boundedMultiplier r'' ∘L spectralGreen)

theorem gaugeLowerOp_apply (wg r' r'' : IntervalLInfinity) (h : IntervalL2) :
    gaugeLowerOp wg r' r'' h =
      gaugeLowerOrder wg r' r'' (spectralGreen h) (spectralGreen_memDirichletH2 h).1 := rfl

theorem boundedMultiplier_comp_norm_le_of_ae (u v : IntervalLInfinity) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂intervalMeasure, ‖u x * v x‖ ≤ C) (f : IntervalL2) :
    ‖boundedMultiplier u (boundedMultiplier v f)‖ ≤ C * ‖f‖ := by
  have he : boundedMultiplier u (boundedMultiplier v f) =
      boundedMultiplier (coefficientProduct u v) f := by
    apply Lp.ext
    filter_upwards [boundedMultiplier_ae u (boundedMultiplier v f), boundedMultiplier_ae v f,
      boundedMultiplier_ae (coefficientProduct u v) f, coefficientProduct_ae u v]
      with x h1 h2 h3 h4
    rw [h1, h2, h3, h4, mul_assoc]
  rw [he]
  refine boundedMultiplier_norm_le_of_ae _ C hC ?_ f
  filter_upwards [coefficientProduct_ae u v, h] with x hx hb
  rwa [hx]

theorem gaugeLowerOp_norm_le (wg r' r'' : IntervalLInfinity) (c1 c2 : ℝ)
    (h1 : ∀ f : IntervalL2, ‖boundedMultiplier wg (boundedMultiplier r' f)‖ ≤ c1 * ‖f‖)
    (h2 : ∀ f : IntervalL2, ‖boundedMultiplier wg (boundedMultiplier r'' f)‖ ≤ c2 * ‖f‖)
    (h : IntervalL2) :
    ‖gaugeLowerOp wg r' r'' h‖ ≤ 2 * c1 * ‖greenDeriv h‖ + c2 * ‖spectralGreen h‖ := by
  have htwo : ‖(2 : ℂ)‖ = 2 := by simp
  change ‖-((2 : ℂ) • boundedMultiplier wg (boundedMultiplier r' (greenDeriv h)) +
    boundedMultiplier wg (boundedMultiplier r'' (spectralGreen h)))‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ ‖(2 : ℂ) • boundedMultiplier wg (boundedMultiplier r' (greenDeriv h))‖ +
        ‖boundedMultiplier wg (boundedMultiplier r'' (spectralGreen h))‖ := norm_add_le _ _
    _ ≤ 2 * (c1 * ‖greenDeriv h‖) + c2 * ‖spectralGreen h‖ := by
      rw [norm_smul, htwo]
      exact add_le_add (mul_le_mul_of_nonneg_left (h1 _) (by norm_num)) (h2 _)
    _ = _ := by ring

/-- Чётная и нечётная функции ортогональны: теорема Пифагора. -/
theorem norm_sq_even_add_odd (e o : IntervalL2) (he : l2Reflect e = e)
    (ho : l2Reflect o = -o) : ‖e + o‖ ^ 2 = ‖e‖ ^ 2 + ‖o‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero e o
    (l2Parity_orthogonal e o he ho)
  rw [sq, sq, sq]
  exact h

theorem norm_sq_parity_parts (f : IntervalL2) :
    ‖f‖ ^ 2 = ‖l2EvenPart f‖ ^ 2 + ‖l2OddPart f‖ ^ 2 := by
  have h := norm_sq_even_add_odd (l2EvenPart f) (l2OddPart f) (l2EvenPart_fixed f)
    (l2OddPart_neg f)
  rwa [l2EvenPart_add_l2OddPart] at h

/-- Оценка нормы умножения с разными весами в каналах отражения. -/
theorem parityMultiplierSum_norm_le (we wo : IntervalLInfinity) (ν : ℝ) (hν : 0 ≤ ν)
    (hwe : ∀ᵐ x ∂intervalMeasure, we (-x) = we x) (hwo : ∀ᵐ x ∂intervalMeasure, wo (-x) = wo x)
    (hbe : ∀ᵐ x ∂intervalMeasure, ‖we x‖ ≤ ν) (hbo : ∀ᵐ x ∂intervalMeasure, ‖wo x‖ ≤ ν) :
    ‖parityMultiplierSum we wo‖ ≤ ν := by
  refine ContinuousLinearMap.opNorm_le_bound _ hν fun f => ?_
  have he : l2Reflect (boundedMultiplier we (l2EvenPart f)) =
      boundedMultiplier we (l2EvenPart f) := by
    rw [← boundedMultiplier_reflect we hwe, l2EvenPart_fixed]
  have ho : l2Reflect (boundedMultiplier wo (l2OddPart f)) =
      -boundedMultiplier wo (l2OddPart f) := by
    rw [← boundedMultiplier_reflect wo hwo, l2OddPart_neg, map_neg]
  have h1 := boundedMultiplier_norm_le_of_ae we ν hν hbe (l2EvenPart f)
  have h2 := boundedMultiplier_norm_le_of_ae wo ν hν hbo (l2OddPart f)
  have hsq : ‖parityMultiplierSum we wo f‖ ^ 2 ≤ (ν * ‖f‖) ^ 2 := by
    rw [parityMultiplierSum_apply, norm_sq_even_add_odd _ _ he ho, mul_pow,
      norm_sq_parity_parts f, mul_add]
    exact add_le_add
      ((pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (mul_pow _ _ _).le)
      ((pow_le_pow_left₀ (norm_nonneg _) h2 2).trans (mul_pow _ _ _).le)
  exact le_of_sq_le_sq hsq (mul_nonneg hν (norm_nonneg f))

/-- Умножение с вещественными чётными весами в каналах симметрично. -/
theorem parityMultiplierSum_symmetric (we wo : IntervalLInfinity)
    (hwe : ∀ᵐ x ∂intervalMeasure, we (-x) = we x) (hwo : ∀ᵐ x ∂intervalMeasure, wo (-x) = wo x)
    (hre : ∀ᵐ x ∂intervalMeasure, star (we x) = we x)
    (hro : ∀ᵐ x ∂intervalMeasure, star (wo x) = wo x) :
    (parityMultiplierSum we wo).IsSymmetric := by
  intro f g
  have key : ∀ f g : IntervalL2, inner ℂ (parityMultiplierSum we wo f) g =
      inner ℂ (boundedMultiplier we (l2EvenPart f)) (l2EvenPart g) +
        inner ℂ (boundedMultiplier wo (l2OddPart f)) (l2OddPart g) := by
    intro f g
    have he : l2Reflect (boundedMultiplier we (l2EvenPart f)) =
        boundedMultiplier we (l2EvenPart f) := by
      rw [← boundedMultiplier_reflect we hwe, l2EvenPart_fixed]
    have ho : l2Reflect (boundedMultiplier wo (l2OddPart f)) =
        -boundedMultiplier wo (l2OddPart f) := by
      rw [← boundedMultiplier_reflect wo hwo, l2OddPart_neg, map_neg]
    have h1 : inner ℂ (boundedMultiplier we (l2EvenPart f)) (l2OddPart g) = 0 :=
      l2Parity_orthogonal _ _ he (l2OddPart_neg g)
    have h2 : inner ℂ (boundedMultiplier wo (l2OddPart f)) (l2EvenPart g) = 0 :=
      inner_eq_zero_symm.mp (l2Parity_orthogonal _ _ (l2EvenPart_fixed g) ho)
    calc
      inner ℂ (parityMultiplierSum we wo f) g =
          inner ℂ (boundedMultiplier we (l2EvenPart f) + boundedMultiplier wo (l2OddPart f))
            (l2EvenPart g + l2OddPart g) := by
        rw [parityMultiplierSum_apply, l2EvenPart_add_l2OddPart]
      _ = _ := by
        rw [inner_add_left, inner_add_right, inner_add_right, h1, h2, add_zero, zero_add]
  have key' : ∀ f g : IntervalL2, inner ℂ f (parityMultiplierSum we wo g) =
      inner ℂ (l2EvenPart f) (boundedMultiplier we (l2EvenPart g)) +
        inner ℂ (l2OddPart f) (boundedMultiplier wo (l2OddPart g)) := by
    intro f g
    have h := key g f
    have hc := congrArg (starRingEnd ℂ) h
    rw [inner_conj_symm, map_add, inner_conj_symm, inner_conj_symm] at hc
    exact hc
  change inner ℂ (parityMultiplierSum we wo f) g = inner ℂ f (parityMultiplierSum we wo g)
  rw [key f g, key' f g]
  exact congrArg₂ (· + ·) (boundedMultiplier_symmetric we hre _ _)
    (boundedMultiplier_symmetric wo hro _ _)

theorem principalOperator_channel (a : IntervalLInfinity) (s : ℂ) (f : IntervalL2)
    (hf : l2Reflect f = s • f) : principalOperator a f = channelPrincipal a s f := by
  change f + boundedMultiplier a (l2Reflect f) = f + s • boundedMultiplier a f
  rw [hf, map_smul]

/-- На канале отражения главный множитель переводит вес `w` в обратный вес `v`. -/
theorem principalOperator_weight (a v w : IntervalLInfinity) (s : ℂ)
    (hw : ∀ᵐ x ∂intervalMeasure, w (-x) = w x)
    (hvw : ∀ᵐ x ∂intervalMeasure, v x * w x = 1)
    (hinv : ∀ᵐ x ∂intervalMeasure, (1 + s * a x) * (w x * w x) = 1)
    (f : IntervalL2) (hf : l2Reflect f = s • f) :
    principalOperator a (boundedMultiplier w f) = boundedMultiplier v f := by
  have hpar : l2Reflect (boundedMultiplier w f) = s • boundedMultiplier w f := by
    rw [← boundedMultiplier_reflect w hw, hf, map_smul]
  rw [principalOperator_channel a s _ hpar]
  have h := channelPrincipal_weight_inverse a w s hinv (boundedMultiplier v f)
  rwa [boundedMultiplier_inverse w v (hvw.mono fun x hx => by rwa [mul_comm])] at h

theorem principalOperator_norm_le (a : IntervalLInfinity) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂intervalMeasure, ‖a x‖ ≤ C) : ‖principalOperator a‖ ≤ 1 + C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun f => ?_
  change ‖f + boundedMultiplier a (l2Reflect f)‖ ≤ (1 + C) * ‖f‖
  have h1 := boundedMultiplier_norm_le_of_ae a C hC h (l2Reflect f)
  rw [l2Reflect_norm] at h1
  calc
    _ ≤ ‖f‖ + ‖boundedMultiplier a (l2Reflect f)‖ := norm_add_le _ _
    _ ≤ ‖f‖ + C * ‖f‖ := by linarith
    _ = _ := by ring

end Involution
