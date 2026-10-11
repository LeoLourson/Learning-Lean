module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Три стандартных вспомогательных утверждения для теоремы о возмущениях:
неподвижная точка метода подобных операторов, разреженные разрезы спектра
с зазорами и оценка числа больших собственных значений через приближение
оператором конечного ранга. -/

@[expose] public noncomputable section

namespace Involution

open Finset

/-- Нелинейное уравнение метода подобных операторов. Отображение
`Φ X = S - S * G1 X + G0 X * J X` сжимает шар радиуса `2 ‖S‖`. -/
theorem exists_similarity_fixedPoint {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (G0 G1 J : A →ₗ[ℂ] A) (γ : ℝ) (hγ : 0 ≤ γ)
    (hG0 : ∀ X, ‖G0 X‖ ≤ γ * ‖X‖) (hG1 : ∀ X, ‖G1 X‖ ≤ γ * ‖X‖)
    (hJ : ∀ X, ‖J X‖ ≤ ‖X‖) (S : A) (hS : 10 * γ * ‖S‖ ≤ 1) :
    ∃ X : A, X = S - S * G1 X + G0 X * J X ∧ ‖X‖ ≤ 2 * ‖S‖ := by
  set s := ‖S‖ with hs
  have s0 : 0 ≤ s := norm_nonneg _
  have gs : 0 ≤ γ * s := mul_nonneg hγ s0
  set Φ : A → A := fun X => S - S * G1 X + G0 X * J X with hΦ
  set B := Metric.closedBall (0 : A) (2 * s) with hB
  have hmaps : Set.MapsTo Φ B B := by
    intro X hX
    rw [hB, mem_closedBall_zero_iff] at hX ⊢
    have h1 : ‖S * G1 X‖ ≤ s * (γ * (2 * s)) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((hG1 X).trans
        (mul_le_mul_of_nonneg_left hX hγ)) s0)
    have h2 : ‖G0 X * J X‖ ≤ (γ * (2 * s)) * (2 * s) :=
      (norm_mul_le _ _).trans (mul_le_mul ((hG0 X).trans (mul_le_mul_of_nonneg_left hX hγ))
        ((hJ X).trans hX) (norm_nonneg _) (by positivity))
    calc ‖Φ X‖ ≤ ‖S‖ + ‖S * G1 X‖ + ‖G0 X * J X‖ := by
          simp only [hΦ]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ 2 * s := by nlinarith
  have hlip : ∀ X ∈ B, ∀ Y ∈ B, ‖Φ X - Φ Y‖ ≤ (1/2) * ‖X - Y‖ := by
    intro X hX Y hY
    rw [hB, mem_closedBall_zero_iff] at hX hY
    have heq : Φ X - Φ Y = -(S * G1 (X - Y)) + (G0 (X - Y) * J X + G0 Y * J (X - Y)) := by
      simp only [hΦ, map_sub, mul_sub, sub_mul]; abel
    set d := ‖X - Y‖
    have d0 : 0 ≤ d := norm_nonneg _
    have h1 : ‖S * G1 (X - Y)‖ ≤ s * (γ * d) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hG1 _) s0)
    have h2 : ‖G0 (X - Y) * J X‖ ≤ (γ * d) * (2 * s) :=
      (norm_mul_le _ _).trans
        (mul_le_mul (hG0 _) ((hJ X).trans hX) (norm_nonneg _) (by positivity))
    have h3 : ‖G0 Y * J (X - Y)‖ ≤ (γ * (2 * s)) * d :=
      (norm_mul_le _ _).trans (mul_le_mul ((hG0 Y).trans (mul_le_mul_of_nonneg_left hY hγ))
        (hJ _) (norm_nonneg _) (by positivity))
    rw [heq]
    calc _ ≤ ‖S * G1 (X - Y)‖ + (‖G0 (X - Y) * J X‖ + ‖G0 Y * J (X - Y)‖) :=
          (norm_add_le _ _).trans (by rw [norm_neg]; gcongr; exact norm_add_le _ _)
      _ ≤ (1/2) * d := by nlinarith
  have hcontr : ContractingWith (1/2 : NNReal) (hmaps.restrict Φ B B) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun X Y => ?_
    simp only [Subtype.dist_eq, Set.MapsTo.val_restrict_apply, dist_eq_norm]
    push_cast
    exact hlip X X.2 Y Y.2
  have h0 : (0 : A) ∈ B := Metric.mem_closedBall_self (by positivity)
  obtain ⟨y, hyB, hy, -⟩ :=
    hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps h0 (edist_ne_top _ _)
  exact ⟨y, hy.symm, mem_closedBall_zero_iff.mp hyB⟩

/-- Window claim: above any level `T ≥ 0` there is a point `x ≥ T + δ` at distance
at least `δ = 1 / (4 c₂)` from every `ω i`. -/
theorem exists_gap_point {ι : Type*} (ω : ι → ℝ) (c₂ C₀ : ℝ) (hc₂ : 0 < c₂)
    (hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, ω i ≤ t) →
      (s.card : ℝ) ≤ c₂ * t + C₀) (T : ℝ) (hT : 0 ≤ T) :
    ∃ x, T + 1 / (4 * c₂) ≤ x ∧ ∀ i, 1 / (4 * c₂) ≤ |ω i - x| := by
  classical
  set δ := 1 / (4 * c₂) with hδ
  have δpos : 0 < δ := by positivity
  have hδc : c₂ * (2 * δ) = 1 / 2 := by rw [hδ]; field_simp; ring
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * c₂ * T + 2 * C₀)
  have hx : ∀ q : ℕ, ∃ i, |ω i - (T + δ * (2 * q + 1))| < δ := fun q =>
    hcon _ (by nlinarith [Nat.cast_nonneg (α := ℝ) q])
  choose f hf using hx
  have hinj : Set.InjOn f (range N : Set ℕ) := by
    intro p _ q _ hpq
    have h1 := hf p
    have h2 := hf q
    rw [hpq] at h1
    rw [abs_lt] at h1 h2
    have h3 : ((p : ℝ) - q) < 1 := by nlinarith
    have h4 : ((q : ℝ) - p) < 1 := by nlinarith
    have h3' : ((p : ℤ) - q) < 1 := by exact_mod_cast h3
    have h4' : ((q : ℤ) - p) < 1 := by exact_mod_cast h4
    omega
  have hcard := hcount (T + 2 * δ * N) (by positivity) ((range N).image f) (by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hi
    have := (abs_lt.mp (hf q)).2
    have hqN : (q : ℝ) + 1 ≤ N := by exact_mod_cast (mem_range.mp hq)
    nlinarith)
  rw [card_image_of_injOn hinj, card_range] at hcard
  nlinarith

/-- Разреженные разрезы. Если число точек `ω i ≤ t` не превосходит `c₂ t + C₀`,
то существует последовательность разрезов `ξ`, удваивающаяся на каждом шаге,
с зазором `δ = 1 / (4 c₂)` до всех точек, и нумерация блоков `blk`. -/
theorem exists_sparse_cuts {ι : Type*} (ω : ι → ℝ) (_hω : ∀ i, 0 < ω i) (c₂ C₀ : ℝ)
    (hc₂ : 0 < c₂) (_hC₀ : 0 ≤ C₀)
    (hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, ω i ≤ t) →
      (s.card : ℝ) ≤ c₂ * t + C₀) :
    ∃ (ξ : ℕ → ℝ) (blk : ι → ℕ),
      1 / (4 * c₂) ≤ ξ 1 ∧
      (∀ k, 1 ≤ k → 2 * ξ k ≤ ξ (k + 1)) ∧
      (∀ i, ω i + 1 / (4 * c₂) ≤ ξ (blk i + 1)) ∧
      (∀ i, 1 ≤ blk i → ξ (blk i) + 1 / (4 * c₂) ≤ ω i) ∧
      (∀ k, {i | blk i = k}.Finite) := by
  classical
  set δ := 1 / (4 * c₂) with hδ
  have δpos : 0 < δ := by positivity
  have hw := exists_gap_point ω c₂ C₀ hc₂ hcount
  obtain ⟨nxt, hnxt⟩ : ∃ nxt : ℝ → ℝ, ∀ T, 0 ≤ T → T + δ ≤ nxt T ∧ ∀ i, δ ≤ |ω i - nxt T| :=
    ⟨fun T => if h : 0 ≤ T then Classical.choose (hw T h) else 0, fun T h => by
      simp only [dite_eq_left, h]; exact Classical.choose_spec (hw T h)⟩
  obtain ⟨ξ, hξz, hξs⟩ : ∃ ξ : ℕ → ℝ, ξ 0 = 0 ∧ ∀ k, ξ (k + 1) = nxt (2 * ξ k) :=
    ⟨fun k => Nat.rec 0 (fun _ y => nxt (2 * y)) k, rfl, fun k => rfl⟩
  have hξ0 : ∀ k, 0 ≤ ξ k := by
    intro k; induction k with
    | zero => exact hξz.ge
    | succ k ih => rw [hξs]; have := (hnxt (2 * ξ k) (by linarith)).1; linarith
  have hstep : ∀ k, 2 * ξ k + δ ≤ ξ (k + 1) ∧ ∀ i, δ ≤ |ω i - ξ (k + 1)| := fun k => by
    rw [hξs]; exact hnxt _ (by linarith [hξ0 k])
  have hlin : ∀ k : ℕ, k * δ ≤ ξ k := by
    intro k; induction k with
    | zero => simp [hξz]
    | succ k ih => push_cast; linarith [(hstep k).1, hξ0 k]
  have hex : ∀ i, ∃ k, ω i < ξ (k + 1) := fun i => by
    obtain ⟨k, hk⟩ := exists_nat_gt (ω i / δ)
    refine ⟨k, ?_⟩
    have := hlin (k + 1)
    rw [div_lt_iff₀ δpos] at hk
    push_cast at this; linarith
  obtain ⟨blk, hb1, hb2⟩ : ∃ blk : ι → ℕ, (∀ i, ω i < ξ (blk i + 1)) ∧
      ∀ i m, m < blk i → ¬ ω i < ξ (m + 1) :=
    ⟨fun i => Nat.find (hex i), fun i => Nat.find_spec (hex i),
      fun i m hm => Nat.find_min (hex i) hm⟩
  refine ⟨ξ, blk, ?_, ?_, ?_, ?_, ?_⟩
  · have := (hstep 0).1; linarith [hξ0 0]
  · intro k _; linarith [(hstep k).1]
  · intro i
    have h1 := hb1 i
    have h2 := (hstep (blk i)).2 i
    rw [abs_sub_comm, abs_of_pos (by linarith)] at h2
    linarith
  · intro i hi
    obtain ⟨m, hm⟩ : ∃ m, blk i = m + 1 := ⟨blk i - 1, by omega⟩
    have h1 : ¬ ω i < ξ (m + 1) := hb2 i m (by omega)
    have h2 := (hstep m).2 i
    rw [hm]
    rcases (not_lt.mp h1).lt_or_eq with h | h
    · rw [abs_of_pos (by linarith)] at h2; linarith
    · rw [← h, sub_self, abs_zero] at h2; linarith
  · intro k
    refine Set.Finite.subset (s := {i | ω i ≤ ξ (k + 1)}) ?_ ?_
    · by_contra hinf
      obtain ⟨N, hN⟩ := exists_nat_gt (c₂ * ξ (k + 1) + C₀)
      obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf N
      have := hcount (ξ (k + 1)) (hξ0 (k + 1)) t (fun i hi => ht hi)
      rw [htc] at this; linarith
    · intro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      rw [← hi]; exact (hb1 i).le

/-- Счёт больших собственных значений. Если `K = F + E`, образ `F` лежит в
подпространстве размерности не больше `n`, а `‖E‖ < θ`, то ортонормированных
собственных векторов `K` с `θ ≤ ‖μ i‖` не больше `n`. -/
theorem card_le_of_finiteRank_approx {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K F E : H →L[ℂ] H) (hK : K = F + E)
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (n : ℕ) (hW : Module.finrank ℂ W ≤ n)
    (hF : ∀ x, F x ∈ W) (u : ι → H) (hu : Orthonormal ℂ u) (μ : ι → ℂ)
    (hKu : ∀ i, K (u i) = μ i • u i) (θ : ℝ) (hE : ‖E‖ < θ)
    (s : Finset ι) (hs : ∀ i ∈ s, θ ≤ ‖μ i‖) : s.card ≤ n := by
  by_contra hcon
  push Not at hcon
  have hθ : 0 < θ := lt_of_le_of_lt (norm_nonneg _) hE
  set v : s → H := fun i => u i.1 with hv
  have hvo : Orthonormal ℂ v := hu.comp _ Subtype.val_injective
  let L0 : (s → ℂ) →ₗ[ℂ] H :=
    { toFun := fun c => ∑ i, c i • v i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a b => by simp [Finset.smul_sum, smul_smul] }
  let L : (s → ℂ) →ₗ[ℂ] W := ((F : H →ₗ[ℂ] H).comp L0).codRestrict W (fun c => hF _)
  have hker : L.ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    omega
  obtain ⟨c, hcL, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set x := ∑ i, c i • v i with hx
  have hFx : F x = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hcL)
    exact this
  have hxx : ‖x‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have h := hvo.inner_sum c c Finset.univ
    rw [← hx, inner_self_eq_norm_sq_to_K] at h
    have h2 := congrArg RCLike.re h
    simp only [RCLike.re_to_complex] at h2
    rw [Complex.re_sum] at h2
    convert h2 using 1
    · norm_cast
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      norm_cast
  have hKx : K x = ∑ i, (c i * μ i) • v i := by
    simp [hx, map_sum, map_smul, hv, hKu, smul_smul]
  have hKxx : ‖K x‖ ^ 2 = ∑ i, ‖c i * μ i‖ ^ 2 := by
    have h := hvo.inner_sum (fun i => c i * μ i) (fun i => c i * μ i) Finset.univ
    rw [← hKx, inner_self_eq_norm_sq_to_K] at h
    have h2 := congrArg RCLike.re h
    simp only [RCLike.re_to_complex] at h2
    rw [Complex.re_sum] at h2
    convert h2 using 1
    · norm_cast
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      norm_cast
  have hlow : θ ^ 2 * ‖x‖ ^ 2 ≤ ‖K x‖ ^ 2 := by
    rw [hxx, hKxx, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_pow, mul_comm]
    have := hs i.1 i.2
    gcongr
  have hxpos : 0 < ‖x‖ := by
    rcases (norm_nonneg x).lt_or_eq with h | h
    · exact h
    · exfalso; apply hc0
      have : ∑ i, ‖c i‖ ^ 2 = 0 := by rw [← hxx, ← h]; ring
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp this i
        (Finset.mem_univ _)
      simpa using this
  have hup : ‖K x‖ ≤ ‖E‖ * ‖x‖ := by
    rw [hK, add_apply, hFx, zero_add]
    exact E.le_opNorm x
  have : ‖E‖ * ‖x‖ < θ * ‖x‖ := mul_lt_mul_of_pos_right hE hxpos
  nlinarith [norm_nonneg (K x), norm_nonneg E]

end Involution
