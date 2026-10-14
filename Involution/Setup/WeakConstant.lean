module

public import Involution.Setup.SmoothPrimitive
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Функция с нулевой слабой производной на интервале п.в. постоянна.
Доказательство получено от Aristotle (проект 94018f4e-bbff-42ca-b92b-d4529070e91a). -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Involution

/-- На непустом открытом интервале существует гладкая пробная функция с интегралом `1`. -/
theorem exists_isSmoothTestOn_integral_eq_one {l r : ℝ} (hlr : l < r) :
    ∃ η : ℝ → ℝ, IsSmoothTestOn (Ioo l r) η ∧ (∫ x, η x) = 1 := by
  let b : ContDiffBump ((l + r) / 2) := ⟨(r - l) / 4, (r - l) / 3, by linarith, by linarith⟩
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, ?_⟩,
    b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -((r - l) / 3) ≤ x - (l + r) / 2 ∧ x - (l + r) / 2 ≤ (r - l) / 3 at hx
  constructor <;> linarith [hx.1, hx.2]

theorem HasWeakDerivOn.ae_eq_const_of_zero
    {l r : ℝ} (hlr : l < r) {f : ℝ → ℂ}
    (hf : HasWeakDerivOn (Set.Ioo l r) f 0) :
    ∃ c : ℂ, f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo l r)]
      (fun _ => c) := by
  obtain ⟨η, hη, hη1⟩ := exists_isSmoothTestOn_integral_eq_one hlr
  set c : ℂ := ∫ x in Ioo l r, η x • f x
  refine ⟨c, ?_⟩
  -- Интеграл против пробной функции зависит только от её интеграла.
  have key : ∀ φ : ℝ → ℝ, IsSmoothTestOn (Ioo l r) φ →
      (∫ x in Ioo l r, φ x • f x) = (∫ x, φ x) • c := by
    intro φ hφ
    set χ : ℝ → ℝ := fun x => φ x - (∫ y, φ y) * η x with hχ
    have hχtest : IsSmoothTestOn (Ioo l r) χ := by
      refine ⟨hφ.1.sub (contDiff_const.mul hη.1), hφ.2.1.sub (hη.2.1.mul_left), ?_⟩
      refine (closure_minimal ?_ ((isClosed_tsupport φ).union (isClosed_tsupport η))).trans
        (union_subset hφ.2.2 hη.2.2)
      exact Function.support_sub _ _ |>.trans (union_subset_union
        (subset_tsupport _) (fun x hx => subset_tsupport η
          (Function.mem_support.mpr fun h => hx (by simp [h]))))
    have hχint : (∫ x, χ x) = 0 := by
      have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
      have hηi : Integrable η := hη.1.continuous.integrable_of_hasCompactSupport hη.2.1
      simp only [hχ]
      rw [integral_sub hφi (hηi.const_mul _), integral_const_mul, hη1, mul_one, sub_self]
    obtain ⟨ψ, hψ, hψd⟩ := hχtest.exists_primitive hχint
    have h := hf.2.2 ψ hψ
    simp only [Pi.zero_apply, smul_zero, integral_zero, neg_zero, hψd] at h
    have hsplit : (fun x => χ x • f x) =
        fun x => φ x • f x - (∫ y, φ y) • (η x • f x) := by
      funext x
      simp only [hχ, sub_smul, mul_smul]
    have hB : IntegrableOn (fun x => (∫ y, φ y) • (η x • f x)) (Ioo l r) :=
      by have := (hη.integrable_smul hf.1).smul (∫ y, φ y); exact this
    rw [hsplit, integral_sub (hφ.integrable_smul hf.1) hB, integral_smul] at h
    exact sub_eq_zero.mp h
  have hzero : ∀ᵐ x ∂volume, x ∈ Ioo l r → f x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.1.sub (integrableOn_const measure_Ioo_lt_top.ne)).locallyIntegrableOn
    intro φ hdiff hcompact hsupp
    have hφ : IsSmoothTestOn (Ioo l r) φ := ⟨hdiff, hcompact, hsupp⟩
    change (∫ x, φ x • (f x - c)) = 0
    rw [← hφ.setIntegral_eq_integral (fun x => f x - c)]
    simp only [smul_sub]
    rw [integral_sub (hφ.integrable_smul hf.1)
      (hφ.integrable_smul (integrableOn_const measure_Ioo_lt_top.ne)), key φ hφ,
      integral_smul_const, setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))), sub_self]
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  exact hzero.mono (fun x hx hsx => sub_eq_zero.mp (hx hsx))

end Involution
