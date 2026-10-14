module

public import Involution.Model.BlockInvariant

/-! Теорема о малых подчинённых возмущениях порядка `1/2`.
Пусть `G` диагонален в гильбертовом базисе с собственными значениями `lam i > 0`,
число значений `lam i ≤ t²` не превосходит `c₂ t + C₀`, а возмущение `S` задано
ограниченным `B = S G⁻¹` с оценкой `‖B g‖ ≤ b₁ ⟨G⁻¹ g, g⟩^(1/2) + b₀ ‖G⁻¹ g‖`,
то есть `‖S u‖ ≤ b₁ ⟨G u, u⟩^(1/2) + b₀ ‖u‖`. Если `160 b₁ c₂ < 1`, то у `G + S`
есть базис Рисса со скобками из конечномерных инвариантных подпространств.
Доказательство: сдвиг `G + c`, разреженные разрезы и метод подобных операторов. -/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Скалярное произведение двух конечных комбинаций с вещественными весами. -/
theorem inner_weighted_slices (b : HilbertBasis ι ℂ H) (p q : ι → ℝ) (s : Finset ι) (x : H) :
    inner ℂ (∑ i ∈ s, ((p i : ℂ) * inner ℂ (b i) x) • b i)
      (∑ i ∈ s, ((q i : ℂ) * inner ℂ (b i) x) • b i) =
      ((∑ i ∈ s, p i * q i * ‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) := by
  rw [b.orthonormal.inner_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  have h := Complex.conj_mul' (inner ℂ (b i) x)
  push_cast
  calc
    (p i : ℂ) * conj (inner ℂ (b i) x) * ((q i : ℂ) * inner ℂ (b i) x) =
        (p i : ℂ) * (q i : ℂ) * (conj (inner ℂ (b i) x) * inner ℂ (b i) x) := by ring
    _ = _ := by rw [h]

omit [CompleteSpace H] in
theorem norm_sq_weighted_slice (b : HilbertBasis ι ℂ H) (p : ι → ℝ) (s : Finset ι) (x : H) :
    ‖∑ i ∈ s, ((p i : ℂ) * inner ℂ (b i) x) • b i‖ ^ 2 =
      ∑ i ∈ s, p i * p i * ‖inner ℂ (b i) x‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, ((p i : ℂ) * inner ℂ (b i) x) • b i‖ ^ 2 =
        RCLike.re (inner ℂ (∑ i ∈ s, ((p i : ℂ) * inner ℂ (b i) x) • b i)
          (∑ i ∈ s, ((p i : ℂ) * inner ℂ (b i) x) • b i)) := (inner_self_eq_norm_sq _).symm
    _ = _ := by
      rw [inner_weighted_slices]
      exact Complex.ofReal_re _

omit [CompleteSpace H] in
/-- Оценка на конечных срезах для оператора `S (G + c)^(-1/2)`. -/
theorem shifted_slice_bound (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (K₀ B : H →L[ℂ] H) (hK₀ : ∀ i, K₀ (b i) = (((lam i)⁻¹ : ℝ) : ℂ) • b i)
    (b₁ b₀ c : ℝ) (hb₁ : 0 ≤ b₁) (hb₀ : 0 ≤ b₀) (hc : 0 < c)
    (hB : ∀ g : H, ‖B g‖ ≤ b₁ * Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) + b₀ * ‖K₀ g‖)
    (s : Finset ι) (x : H) :
    ‖B (∑ i ∈ s, (((lam i / Real.sqrt (lam i + c) : ℝ) : ℂ) * inner ℂ (b i) x) • b i)‖ ≤
      (b₁ + b₀ / Real.sqrt c) * ‖x‖ := by
  set g := ∑ i ∈ s, (((lam i / Real.sqrt (lam i + c) : ℝ) : ℂ) * inner ℂ (b i) x) • b i with hg
  have hpos : ∀ i, 0 < lam i + c := fun i => add_pos (hlam i) hc
  have hsq : ∀ i, 0 < Real.sqrt (lam i + c) := fun i => Real.sqrt_pos.mpr (hpos i)
  have hK : K₀ g =
      ∑ i ∈ s, ((((Real.sqrt (lam i + c))⁻¹ : ℝ) : ℂ) * inner ℂ (b i) x) • b i := by
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hK₀, smul_smul]
    congr 1
    have h1 : (lam i / Real.sqrt (lam i + c)) * (lam i)⁻¹ = (Real.sqrt (lam i + c))⁻¹ := by
      field_simp [(hlam i).ne']
    rw [← h1]
    push_cast
    ring
  have hbessel : ∑ i ∈ s, ‖inner ℂ (b i) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    Orthonormal.sum_inner_products_le x b.orthonormal
  have hre : RCLike.re (inner ℂ (K₀ g) g) ≤ ‖x‖ ^ 2 := by
    rw [hK, hg, inner_weighted_slices]
    change (((∑ i ∈ s, (Real.sqrt (lam i + c))⁻¹ * (lam i / Real.sqrt (lam i + c)) *
      ‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ)).re ≤ ‖x‖ ^ 2
    rw [Complex.ofReal_re]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hbessel
    have hle : (Real.sqrt (lam i + c))⁻¹ * (lam i / Real.sqrt (lam i + c)) ≤ 1 := by
      have h2 : (Real.sqrt (lam i + c))⁻¹ * (lam i / Real.sqrt (lam i + c)) =
          lam i / (lam i + c) := by
        rw [inv_mul_eq_div, div_div, Real.mul_self_sqrt (hpos i).le]
      rw [h2, div_le_one (hpos i)]
      linarith
    calc
      _ ≤ 1 * ‖inner ℂ (b i) x‖ ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = _ := one_mul _
  have hnorm : ‖K₀ g‖ ^ 2 ≤ c⁻¹ * ‖x‖ ^ 2 := by
    rw [hK, norm_sq_weighted_slice]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hbessel (inv_nonneg.mpr hc.le))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hle : (Real.sqrt (lam i + c))⁻¹ * (Real.sqrt (lam i + c))⁻¹ ≤ c⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (hpos i).le]
      exact inv_anti₀ hc (by linarith [hlam i])
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  have h1 : Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) ≤ ‖x‖ :=
    (Real.sqrt_le_sqrt hre).trans (Real.sqrt_sq (norm_nonneg x)).le
  have h2 : ‖K₀ g‖ ≤ ‖x‖ / Real.sqrt c := by
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    rw [le_div_iff₀ hsc]
    have h3 : (‖K₀ g‖ * Real.sqrt c) ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      have := mul_le_mul_of_nonneg_right hnorm hc.le
      rwa [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one] at this
    exact le_of_sq_le_sq h3 (norm_nonneg x)
  calc
    ‖B g‖ ≤ b₁ * Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) + b₀ * ‖K₀ g‖ := hB g
    _ ≤ b₁ * ‖x‖ + b₀ * (‖x‖ / Real.sqrt c) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hb₁) (mul_le_mul_of_nonneg_left h2 hb₀)
    _ = _ := by ring

/-- Малое возмущение порядка `1/2` диагонального оператора с линейной оценкой
счётной функции частот: базис Рисса со скобками из инвариантных подпространств.
Инвариантность: для `v ∈ V k` найдётся `g` с `K₀ g = v` и `g + B g ∈ V k`. -/
theorem exists_bracket_basis_of_subordinate (b : HilbertBasis ι ℂ H) (lam : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (K₀ B : H →L[ℂ] H)
    (hK₀ : ∀ i, K₀ (b i) = (((lam i)⁻¹ : ℝ) : ℂ) • b i)
    (c₂ C₀ b₁ b₀ : ℝ) (hc₂ : 0 < c₂) (hC₀ : 0 ≤ C₀) (hb₁ : 0 ≤ b₁) (hb₀ : 0 ≤ b₀)
    (hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t ^ 2) →
      (s.card : ℝ) ≤ c₂ * t + C₀)
    (hB : ∀ g : H, ‖B g‖ ≤ b₁ * Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) + b₀ * ‖K₀ g‖)
    (hsmall : 160 * b₁ * c₂ < 1) :
    ∃ V : ℕ → Submodule ℂ H, Nonempty (RieszBasisWithBrackets V) ∧
      ∀ k, ∀ v ∈ V k, ∃ g : H, K₀ g = v ∧ g + B g ∈ V k := by
  -- выбор сдвига
  set η := 1 - 160 * b₁ * c₂ with hη
  have hη0 : 0 < η := by linarith
  set c := (160 * c₂ * b₀ / η) ^ 2 + 1 with hc
  have hc0 : 0 < c := by positivity
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hsqrtc : 160 * c₂ * b₀ / η ≤ Real.sqrt c := by
    have h0 : 0 ≤ 160 * c₂ * b₀ / η := by positivity
    calc
      160 * c₂ * b₀ / η = Real.sqrt ((160 * c₂ * b₀ / η) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt (by rw [hc]; linarith)
  have hC : 40 * (b₁ + b₀ / Real.sqrt c) ≤ 1 / (4 * c₂) := by
    have h1 : 160 * c₂ * b₀ ≤ η * Real.sqrt c := (div_le_iff₀' hη0).mp hsqrtc
    have h2 : b₀ / Real.sqrt c ≤ η / (160 * c₂) := by
      rw [div_le_div_iff₀ hsc (by positivity)]
      nlinarith
    have h3 : b₁ + η / (160 * c₂) = 1 / (160 * c₂) := by
      rw [hη]
      field_simp
      ring
    calc
      40 * (b₁ + b₀ / Real.sqrt c) ≤ 40 * (b₁ + η / (160 * c₂)) := by linarith
      _ = 40 * (1 / (160 * c₂)) := by rw [h3]
      _ = _ := by
        field_simp
        ring
  -- частоты сдвинутого оператора
  let ω : ι → ℝ := fun i => Real.sqrt (lam i + c)
  have hpos : ∀ i, 0 < lam i + c := fun i => add_pos (hlam i) hc0
  have hω : ∀ i, 0 < ω i := fun i => Real.sqrt_pos.mpr (hpos i)
  have hωge : ∀ i, Real.sqrt c ≤ ω i := fun i =>
    Real.sqrt_le_sqrt (by linarith [hlam i])
  have hcountω : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, ω i ≤ t) →
      (s.card : ℝ) ≤ c₂ * t + C₀ := by
    intro t ht s hs
    refine hcount t ht s fun i hi => ?_
    have h1 := hs i hi
    have h2 : lam i + c ≤ t ^ 2 := by
      have := Real.sqrt_le_left (x := lam i + c) (y := t) ht |>.mp h1
      exact this
    linarith
  obtain ⟨ξ, blk, hξ1, hξ2, hup, hlow, hfin⟩ :=
    exists_sparse_cuts ω hω c₂ C₀ hc₂ hC₀ hcountω
  let D : SpectralBlocks ι :=
    { ω := ω, blk := blk, ξ := ξ, δ := 1 / (4 * c₂), ω₀ := Real.sqrt c
      δ_pos := by positivity
      ω₀_pos := hsc
      ω_ge := hωge
      ξ_one := hξ1
      ξ_double := hξ2
      upper := hup
      lower := hlow }
  -- оператор `S (G + c)^(-1/2)`
  obtain ⟨S, hSnorm, hSb⟩ := exists_weighted_extension b B
    (fun i => ((lam i / Real.sqrt (lam i + c) : ℝ) : ℂ)) (b₁ + b₀ / Real.sqrt c)
    (by positivity)
    (shifted_slice_bound b lam hlam K₀ B hK₀ b₁ b₀ c hb₁ hb₀ hc0 hB)
  have hS : 40 * ‖S‖ ≤ D.δ := by
    change 40 * ‖S‖ ≤ 1 / (4 * c₂)
    linarith
  obtain ⟨V, hV, hinv⟩ := D.exists_bracket_basis b S hS hfin
  refine ⟨V, hV, ?_⟩
  -- возвращение к несдвинутому оператору
  let θ : ι → ℂ := fun i => ((lam i / (lam i + c) : ℝ) : ℂ)
  have hθ : ∀ i, ‖θ i‖ ≤ 1 := by
    intro i
    change ‖((lam i / (lam i + c) : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hlam i) (hpos i)),
      div_le_one (hpos i)]
    linarith
  have hρ : ∀ i, D.rho i = (((Real.sqrt (lam i + c))⁻¹ : ℝ) : ℂ) := fun i => rfl
  have hRb : ∀ i, D.invFreq b (b i) = (((Real.sqrt (lam i + c))⁻¹ : ℝ) : ℂ) • b i := fun i => by
    rw [D.invFreq_apply_basis b i, hρ i]
  have hΘb : ∀ i, diagOp b θ (b i) = θ i • b i := diagOp_apply_basis b θ 1 hθ
  have hmul : ∀ i, (Real.sqrt (lam i + c))⁻¹ * (Real.sqrt (lam i + c))⁻¹ = (lam i + c)⁻¹ :=
    fun i => by rw [← mul_inv, Real.mul_self_sqrt (hpos i).le]
  have hKΘ : K₀ * diagOp b θ = D.invFreq b * D.invFreq b := by
    apply clm_ext_basis b
    intro i
    change K₀ (diagOp b θ (b i)) = D.invFreq b (D.invFreq b (b i))
    rw [hΘb, map_smul, hK₀, hRb, map_smul, hRb, smul_smul, smul_smul]
    congr 1
    change ((lam i / (lam i + c) : ℝ) : ℂ) * (((lam i)⁻¹ : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hmul i]
    congr 1
    field_simp [(hlam i).ne']
  have hBΘ : B * diagOp b θ = S * D.invFreq b := by
    apply clm_ext_basis b
    intro i
    change B (diagOp b θ (b i)) = S (D.invFreq b (b i))
    rw [hΘb, map_smul, hRb, map_smul, hSb, smul_smul]
    congr 1
    change ((lam i / (lam i + c) : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul]
    congr 1
    rw [inv_mul_eq_div, div_div, Real.mul_self_sqrt (hpos i).le]
  have hΘ : diagOp b θ = 1 - (c : ℂ) • (D.invFreq b * D.invFreq b) := by
    apply clm_ext_basis b
    intro i
    change diagOp b θ (b i) = b i - (c : ℂ) • D.invFreq b (D.invFreq b (b i))
    rw [hΘb, hRb, map_smul, hRb, smul_smul, smul_smul]
    change ((lam i / (lam i + c) : ℝ) : ℂ) • b i = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_assoc, hmul i]
    have h1 : lam i / (lam i + c) = 1 - c * (lam i + c)⁻¹ := by
      field_simp [(hpos i).ne']
      ring
    rw [h1, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  intro k v hv
  obtain ⟨g, hg1, hg2⟩ := hinv k v hv
  refine ⟨diagOp b θ g, ?_, ?_⟩
  · have h := congrArg (fun T : H →L[ℂ] H => T g) hKΘ
    change K₀ (diagOp b θ g) = D.invFreq b (D.invFreq b g) at h
    rw [h, hg1]
  · have h := congrArg (fun T : H →L[ℂ] H => T g) hBΘ
    change B (diagOp b θ g) = S (D.invFreq b g) at h
    have h' := congrArg (fun T : H →L[ℂ] H => T g) hΘ
    change diagOp b θ g = g - (c : ℂ) • D.invFreq b (D.invFreq b g) at h'
    rw [h, h', hg1]
    have he : g - (c : ℂ) • v + S (D.invFreq b g) = (g + S (D.invFreq b g)) - (c : ℂ) • v := by
      abel
    rw [he]
    exact Submodule.sub_mem _ hg2 (Submodule.smul_mem _ _ hv)

end Involution
