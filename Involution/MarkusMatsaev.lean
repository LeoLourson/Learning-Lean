module

public import Involution.SubordinatePerturbation
public import Involution.MMCore

/-! Теорема Маркуса–Мацаева для возмущений порядка `1/2` без условия малости
(Wyss, arXiv:0906.2631v1, теорема 6.1, в диагональной форме).
Отличие от `exists_bracket_basis_of_subordinate`: нет гипотезы `160 b₁ c₂ < 1`.
Этот модуль и модули `MM*` получены от Aristotle
(проект c4fdbf81-6fdc-48c0-b18a-995935371d25). -/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Возмущение порядка `1/2` диагонального оператора с линейной оценкой счётной
функции частот: базис Рисса со скобками из конечномерных инвариантных подпространств.
Инвариантность: для `v ∈ V k` найдётся `g` с `K₀ g = v` и `g + B g ∈ V k`. -/
theorem exists_bracket_basis_of_subordinate_general (b : HilbertBasis ι ℂ H) (lam : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (K₀ B : H →L[ℂ] H)
    (hK₀ : ∀ i, K₀ (b i) = (((lam i)⁻¹ : ℝ) : ℂ) • b i)
    (c₂ C₀ b₁ b₀ : ℝ) (hc₂ : 0 < c₂) (hC₀ : 0 ≤ C₀) (hb₁ : 0 ≤ b₁) (hb₀ : 0 ≤ b₀)
    (hcount : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, lam i ≤ t ^ 2) →
      (s.card : ℝ) ≤ c₂ * t + C₀)
    (hB : ∀ g : H, ‖B g‖ ≤ b₁ * Real.sqrt (RCLike.re (inner ℂ (K₀ g) g)) + b₀ * ‖K₀ g‖) :
    ∃ V : ℕ → Submodule ℂ H, Nonempty (RieszBasisWithBrackets V) ∧
      ∀ k, ∀ v ∈ V k, ∃ g : H, K₀ g = v ∧ g + B g ∈ V k := by
  classical
  obtain ⟨M, hM⟩ := MMData.core (ι := ι) (H := H) (b₁ + 1) c₂ C₀ (by linarith) hc₂ hC₀
  set c : ℝ := b₀ ^ 2 + M ^ 2 + 1 with hc
  have hc0 : 0 < c := by positivity
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hb₀c : b₀ / Real.sqrt c ≤ 1 := by
    rw [div_le_one hsc]
    calc b₀ = Real.sqrt (b₀ ^ 2) := (Real.sqrt_sq hb₀).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt (by rw [hc]; nlinarith [sq_nonneg M])
  have hMc : M ≤ Real.sqrt c := by
    calc M ≤ |M| := le_abs_self M
      _ = Real.sqrt (M ^ 2) := (Real.sqrt_sq_eq_abs M).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt (by rw [hc]; nlinarith [sq_nonneg b₀])
  have hpos : ∀ i, 0 < lam i + c := fun i => add_pos (hlam i) hc0
  -- the shifted operators
  let θ : ι → ℂ := fun i => ((lam i / (lam i + c) : ℝ) : ℂ)
  have hθ : ∀ i, ‖θ i‖ ≤ 1 := by
    intro i
    change ‖((lam i / (lam i + c) : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hlam i) (hpos i)),
      div_le_one (hpos i)]
    linarith
  let κ : ι → ℂ := fun i => (((lam i + c)⁻¹ : ℝ) : ℂ)
  have hκ : ∀ i, ‖κ i‖ ≤ c⁻¹ := by
    intro i
    change ‖(((lam i + c)⁻¹ : ℝ) : ℂ)‖ ≤ c⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos i))]
    exact inv_anti₀ hc0 (by linarith [hlam i])
  set Θ := diagOp b θ with hΘdef
  set K' := diagOp b κ with hK'def
  set B' := B * Θ with hB'def
  have hΘb : ∀ i, Θ (b i) = θ i • b i := diagOp_apply_basis b θ 1 hθ
  have hK'b : ∀ i, K' (b i) = (((lam i + c)⁻¹ : ℝ) : ℂ) • b i := diagOp_apply_basis b κ _ hκ
  have hKΘ : K₀ * Θ = K' := by
    apply clm_ext_basis b
    intro i
    change K₀ (Θ (b i)) = K' (b i)
    rw [hΘb, map_smul, hK₀, hK'b, smul_smul]
    congr 1
    change ((lam i / (lam i + c) : ℝ) : ℂ) * (((lam i)⁻¹ : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [(hlam i).ne']
  have hΘ : Θ = 1 - (c : ℂ) • K' := by
    apply clm_ext_basis b
    intro i
    change Θ (b i) = b i - (c : ℂ) • K' (b i)
    rw [hΘb, hK'b, smul_smul]
    change ((lam i / (lam i + c) : ℝ) : ℂ) • b i = _
    rw [← Complex.ofReal_mul]
    have h1 : lam i / (lam i + c) = 1 - c * (lam i + c)⁻¹ := by
      field_simp [(hpos i).ne']
      ring
    rw [h1, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  -- the bound for `B'` on finite slices
  have hslice : ∀ (s : Finset ι) (x : H),
      ‖B' (∑ i ∈ s, (((1 : ℝ) : ℂ) * inner ℂ (b i) x) • b i)‖ ≤
        (b₁ + 1) * Real.sqrt (RCLike.re (inner ℂ (K' (∑ i ∈ s, (((1 : ℝ) : ℂ) *
          inner ℂ (b i) x) • b i)) (∑ i ∈ s, (((1 : ℝ) : ℂ) * inner ℂ (b i) x) • b i))) := by
    intro s x
    set g := ∑ i ∈ s, (((1 : ℝ) : ℂ) * inner ℂ (b i) x) • b i with hg
    have hΘg : Θ g = ∑ i ∈ s, (((lam i / (lam i + c) : ℝ) : ℂ) * inner ℂ (b i) x) • b i := by
      rw [hg, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hΘb, smul_smul]
      congr 1
      change _ * ((lam i / (lam i + c) : ℝ) : ℂ) = _
      push_cast; ring
    have hK'g : K' g = ∑ i ∈ s, ((((lam i + c)⁻¹ : ℝ) : ℂ) * inner ℂ (b i) x) • b i := by
      rw [hg, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hK'b, smul_smul]
      congr 1
      push_cast; ring
    have hKΘg : K₀ (Θ g) = K' g := by
      rw [← hKΘ]; rfl
    have hE : RCLike.re (inner ℂ (K' g) g) =
        ∑ i ∈ s, (lam i + c)⁻¹ * 1 * ‖inner ℂ (b i) x‖ ^ 2 := by
      rw [hK'g, hg, inner_weighted_slices]
      exact Complex.ofReal_re _
    have h1 : RCLike.re (inner ℂ (K₀ (Θ g)) (Θ g)) ≤ RCLike.re (inner ℂ (K' g) g) := by
      rw [hKΘg, hE, hK'g, hΘg, inner_weighted_slices]
      change (((∑ i ∈ s, (lam i + c)⁻¹ * (lam i / (lam i + c)) *
        ‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ)).re ≤ _
      rw [Complex.ofReal_re]
      refine Finset.sum_le_sum fun i _ => ?_
      gcongr
      · exact (inv_pos.mpr (hpos i)).le
      · rw [div_le_one (hpos i)]; linarith
    have h2 : ‖K₀ (Θ g)‖ ^ 2 ≤ c⁻¹ * RCLike.re (inner ℂ (K' g) g) := by
      rw [hE, hKΘg, hK'g, norm_sq_weighted_slice, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h3 : (lam i + c)⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 (by linarith [hlam i])
      have h4 := (inv_pos.mpr (hpos i)).le
      nlinarith [mul_le_mul_of_nonneg_right h3 (mul_nonneg h4 (sq_nonneg ‖inner ℂ (b i) x‖))]
    have hE0 : 0 ≤ RCLike.re (inner ℂ (K' g) g) := by
      rw [hE]; exact Finset.sum_nonneg fun i _ => by
        have := (inv_pos.mpr (hpos i)).le; positivity
    have h2' : ‖K₀ (Θ g)‖ ≤ Real.sqrt (RCLike.re (inner ℂ (K' g) g)) / Real.sqrt c := by
      rw [le_div_iff₀ hsc, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul (sq_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      have := mul_le_mul_of_nonneg_right h2 hc0.le
      rwa [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one] at this
    have hB0 := hB (Θ g)
    change ‖B (Θ g)‖ ≤ _
    set E := Real.sqrt (RCLike.re (inner ℂ (K' g) g))
    have hE1 : Real.sqrt (RCLike.re (inner ℂ (K₀ (Θ g)) (Θ g))) ≤ E := Real.sqrt_le_sqrt h1
    have hEn : 0 ≤ E := Real.sqrt_nonneg _
    calc ‖B (Θ g)‖ ≤ b₁ * E + b₀ * (E / Real.sqrt c) :=
          hB0.trans (add_le_add (mul_le_mul_of_nonneg_left hE1 hb₁)
            (mul_le_mul_of_nonneg_left h2' hb₀))
      _ = (b₁ + b₀ / Real.sqrt c) * E := by ring
      _ ≤ (b₁ + 1) * E := by gcongr
  have hB' : ∀ g : H, ‖B' g‖ ≤ (b₁ + 1) * Real.sqrt (RCLike.re (inner ℂ (K' g) g)) := by
    intro g
    have hs : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, (((1 : ℝ) : ℂ) * inner ℂ (b i) g) • b i)
        Filter.atTop (nhds g) := by
      have := (b.hasSum_repr g)
      simp only [HilbertBasis.repr_apply_apply] at this
      simp only [Complex.ofReal_one, one_mul]
      exact this
    have hcont1 : Continuous fun x : H => ‖B' x‖ := by fun_prop
    have hcont2 : Continuous fun x : H =>
        (b₁ + 1) * Real.sqrt (RCLike.re (inner ℂ (K' x) x)) := by fun_prop
    exact le_of_tendsto_of_tendsto' ((hcont1.tendsto g).comp hs) ((hcont2.tendsto g).comp hs)
      fun s => hslice s g
  -- the core data
  let D : MMData ι H :=
    { b := b, lam := fun i => lam i + c, m := Real.sqrt c, hm := hsc
      hlam := fun i => by rw [Real.sq_sqrt hc0.le]; linarith [hlam i]
      K₀ := K', B := B', hK := hK'b, b₁ := b₁ + 1, hb₁ := by linarith, hB := hB' }
  have hcountD : ∀ t : ℝ, 0 ≤ t → ∀ s : Finset ι, (∀ i ∈ s, D.ω i ≤ t) →
      (s.card : ℝ) ≤ c₂ * t + C₀ := by
    intro t ht s hs
    refine hcount t ht s fun i hi => ?_
    have h1 : Real.sqrt (lam i + c) ≤ t := hs i hi
    have h2 : lam i + c ≤ t ^ 2 := (Real.sqrt_le_left ht).mp h1
    linarith
  obtain ⟨V, hV, hinv⟩ := hM D rfl hcountD hMc
  refine ⟨V, hV, fun k v hv => ?_⟩
  obtain ⟨g, hg1, hg2⟩ := hinv k v hv
  change K' g = v at hg1
  change g + B' g ∈ V k at hg2
  refine ⟨Θ g, ?_, ?_⟩
  · rw [← hg1, ← hKΘ]; rfl
  · have e : Θ g + B (Θ g) = (g + B' g) - (c : ℂ) • v := by
      rw [← hg1]
      change Θ g + B (Θ g) = (g + B (Θ g)) - (c : ℂ) • K' g
      rw [hΘ]
      simp only [sub_apply, one_apply_eq_self, smul_apply]
      abel
    rw [e]
    exact Submodule.sub_mem _ hg2 (Submodule.smul_mem _ _ hv)

end Involution
