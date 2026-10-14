module

public import Involution.Setup.WeakPrimitive

/-! Формула Ньютона–Лейбница и интегрирование по частям для комплексных
абсолютно непрерывных функций. Производные задаются почти всюду;
не предполагается поточечная дифференцируемость на концах отрезка. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Involution

theorem complex_ac_integral_eq_sub {l r : ℝ} {F g : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F l r)
    (hg : IntervalIntegrable g volume l r)
    (hd : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (g x) x) :
    (∫ x in l..r, g x) = F r - F l := by
  have hmap (L : ℂ →L[ℝ] ℝ) : L (∫ x in l..r, g x) = L (F r - F l) := by
    have hLF : AbsolutelyContinuousOnInterval (fun x => L (F x)) l r :=
      L.lipschitzWith.comp_absolutelyContinuousOnInterval hF
    have heq : (∫ x in l..r, L (g x)) = ∫ x in l..r, deriv (fun t => L (F t)) x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with x hx hi
      exact (L.hasFDerivAt.comp_hasDerivAt x (hx (uIoc_subset_uIcc hi))).deriv.symm
    rw [← L.intervalIntegral_comp_comm hg, heq, hLF.integral_deriv_eq_sub, L.map_sub]
  exact Complex.ext (hmap Complex.reCLM) (hmap Complex.imCLM)

theorem complex_ac_integral_product_derivative {l r : ℝ} {F G f g : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F l r)
    (hG : AbsolutelyContinuousOnInterval G l r)
    (hf : IntervalIntegrable f volume l r) (hg : IntervalIntegrable g volume l r)
    (hdF : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (f x) x)
    (hdG : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt G (g x) x) :
    (∫ x in l..r, (f x * G x + F x * g x)) = F r * G r - F l * G l := by
  have hi : IntervalIntegrable (fun x => f x * G x + F x * g x) volume l r :=
    (hf.mul_continuousOn hG.continuousOn).add (hg.continuousOn_mul hF.continuousOn)
  have hFG : AbsolutelyContinuousOnInterval (fun x => F x * G x) l r := by
    convert hF.smul hG using 1
  apply complex_ac_integral_eq_sub hFG hi
  filter_upwards [hdF, hdG] with x hfx hgx hx
  exact (hfx hx).mul (hgx hx)

theorem complex_ac_integration_by_parts {l r : ℝ} {F G f g : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F l r)
    (hG : AbsolutelyContinuousOnInterval G l r)
    (hf : IntervalIntegrable f volume l r) (hg : IntervalIntegrable g volume l r)
    (hdF : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (f x) x)
    (hdG : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt G (g x) x) :
    (∫ x in l..r, F x * g x) = F r * G r - F l * G l - ∫ x in l..r, f x * G x := by
  have hprod := complex_ac_integral_product_derivative hF hG hf hg hdF hdG
  rw [intervalIntegral.integral_add (hf.mul_continuousOn hG.continuousOn)
    (hg.continuousOn_mul hF.continuousOn)] at hprod
  exact eq_sub_of_add_eq' hprod

theorem complex_ac_green_identity {l r : ℝ} {F G f g : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F l r)
    (hG : AbsolutelyContinuousOnInterval G l r)
    (hf : IntervalIntegrable f volume l r) (hg : IntervalIntegrable g volume l r)
    (hdF : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (f x) x)
    (hdG : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt G (g x) x) :
    (∫ x in l..r, star (F x) * g x) =
      star (F r) * G r - star (F l) * G l - ∫ x in l..r, star (f x) * G x := by
  let C : ℂ →L[ℝ] ℂ := Complex.conjCLE
  have hCF : AbsolutelyContinuousOnInterval (fun x => C (F x)) l r :=
    C.lipschitzWith.comp_absolutelyContinuousOnInterval hF
  have hCf : IntervalIntegrable (fun x => C (f x)) volume l r :=
    intervalIntegrable_iff.mpr (C.integrable_comp hf.def')
  have hdCF : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt (fun t => C (F t)) (C (f x)) x := by
    filter_upwards [hdF] with x hx hi
    exact C.hasFDerivAt.comp_hasDerivAt x (hx hi)
  exact complex_ac_integration_by_parts hCF hG hCf hg hdCF hdG

end Involution
