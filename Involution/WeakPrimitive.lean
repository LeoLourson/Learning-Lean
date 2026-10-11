module

public import Involution.WeakDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Слабая производная первообразной интегрируемой функции.
Используются готовые теоремы Mathlib об абсолютной непрерывности первообразной,
дифференцировании интеграла почти всюду и интегрировании по частям.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Involution

theorem real_primitive_test_identity {l r : ℝ} (hlr : l ≤ r) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume l r) {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn (Ioo l r) φ) :
    (∫ x in Ioo l r, deriv φ x * (∫ t in l..x, g t)) =
      -(∫ x in Ioo l r, φ x * g x) := by
  let G : ℝ → ℝ := fun x => ∫ t in l..x, g t
  have hG : AbsolutelyContinuousOnInterval G l r :=
    hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hφac : AbsolutelyContinuousOnInterval φ l r :=
    (hφ.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hleft : φ l = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl l) (hφ.2.2 hx).1)
  have hright : φ r = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl r) (hφ.2.2 hx).2)
  have hd : ∀ᵐ x, x ∈ uIcc l r → deriv G x = g x := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hi
    exact (hx hi l left_mem_uIcc).deriv
  have hint := hφac.integral_mul_deriv_eq_deriv_mul hG
  have heq : (∫ x in l..r, φ x * deriv G x) = ∫ x in l..r, φ x * g x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with x hx hi
    rw [hx (uIoc_subset_uIcc hi)]
  rw [heq, hleft, hright, zero_mul, zero_mul, sub_self, zero_sub] at hint
  rw [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo] at hint
  exact (neg_eq_iff_eq_neg.mpr hint).symm

theorem complex_primitive_test_identity {l r : ℝ} (hlr : l ≤ r) {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume l r) {φ : ℝ → ℝ}
    (hφ : IsSmoothTestOn (Ioo l r) φ) :
    (∫ x in Ioo l r, deriv φ x • (∫ t in l..x, g t)) =
      -(∫ x in Ioo l r, φ x • g x) := by
  let G : ℝ → ℂ := fun x => ∫ t in l..x, g t
  have hGc : ContinuousOn G (Icc l r) := by
    simpa only [uIcc_of_le hlr] using
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have hGi : IntegrableOn G (Ioo l r) :=
    hGc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hgi : IntegrableOn g (Ioo l r) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mp hg
  have htestG := hφ.deriv.integrable_smul hGi
  have htestg := hφ.integrable_smul hgi
  have hmap (L : ℂ →L[ℝ] ℝ) :
      L (∫ x in Ioo l r, deriv φ x • G x) =
        L (-(∫ x in Ioo l r, φ x • g x)) := by
    have hgL : IntervalIntegrable (fun x => L (g x)) volume l r :=
      ⟨L.integrable_comp hg.1, L.integrable_comp hg.2⟩
    have hcomm : ∀ x ∈ Ioo l r, (∫ t in l..x, L (g t)) = L (G x) := by
      intro x hx
      apply L.intervalIntegral_comp_comm
      apply hg.mono_set'
      rw [uIoc_of_le hx.1.le, uIoc_of_le hlr]
      intro t ht
      exact ⟨ht.1, ht.2.trans hx.2.le⟩
    rw [L.map_neg, ← L.integral_comp_comm htestG, ← L.integral_comp_comm htestg]
    simp only [map_smul, smul_eq_mul]
    have hreal := real_primitive_test_identity hlr hgL hφ
    have heq : (∫ x in Ioo l r, deriv φ x * L (G x)) =
        ∫ x in Ioo l r, deriv φ x * (∫ t in l..x, L (g t)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact congrArg (fun y => deriv φ x * y) (hcomm x hx).symm
    rw [heq]
    exact hreal
  exact Complex.ext (hmap Complex.reCLM) (hmap Complex.imCLM)

theorem hasWeakDerivOn_primitive {l r : ℝ} (hlr : l ≤ r) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Ioo l r)) :
    HasWeakDerivOn (Ioo l r) (fun x => ∫ t in l..x, g t) g := by
  have hgi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mpr hg
  have hcont : ContinuousOn (fun x => ∫ t in l..x, g t) (Icc l r) := by
    simpa only [uIcc_of_le hlr] using
      intervalIntegral.continuousOn_primitive_interval' hgi left_mem_uIcc
  exact ⟨hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self, hg,
    fun _ hφ => complex_primitive_test_identity hlr hgi hφ⟩

theorem complex_primitive_absolutelyContinuous {l r : ℝ} (hlr : l ≤ r)
    {g : ℝ → ℂ} (hg : IntervalIntegrable g volume l r) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in l..x, g t) l r := by
  have hRe : IntervalIntegrable (fun x => Complex.reCLM (g x)) volume l r :=
    ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have hIm : IntervalIntegrable (fun x => Complex.imCLM (g x)) volume l r :=
    ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  have hReac := hRe.absolutelyContinuousOnInterval_intervalIntegral
    (c := l) left_mem_uIcc
  have hImac := hIm.absolutelyContinuousOnInterval_intervalIntegral
    (c := l) left_mem_uIcc
  have hReC := Complex.ofRealLI.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hReac
  have hImC := Complex.ofRealLI.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hImac
  apply (hReC.add (hImC.const_smul Complex.I)).congr
  intro x hx
  have hx' : x ∈ Icc l r := by simpa only [uIcc_of_le hlr] using hx
  have hgx : IntervalIntegrable g volume l x := by
    apply hg.mono_set'
    rw [uIoc_of_le hx'.1, uIoc_of_le hlr]
    exact fun t ht => ⟨ht.1, ht.2.trans hx'.2⟩
  simp only [Pi.add_apply, Function.comp_apply, Complex.ofRealLI_apply, smul_eq_mul]
  rw [Complex.reCLM.intervalIntegral_comp_comm hgx,
    Complex.imCLM.intervalIntegral_comp_comm hgx]
  apply Complex.ext <;> simp

theorem HasWeakDerivOn.sub_primitive {l r : ℝ} (hlr : l ≤ r) {f g : ℝ → ℂ}
    (hfg : HasWeakDerivOn (Ioo l r) f g) :
    HasWeakDerivOn (Ioo l r) (fun x => f x - ∫ t in l..x, g t) 0 := by
  have hfun : f + -(fun x => ∫ t in l..x, g t) =
      (fun x => f x - ∫ t in l..x, g t) := by
    funext x
    simp only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  simpa only [hfun, add_neg_cancel] using
    hfg.add (hasWeakDerivOn_primitive hlr hfg.2.1).neg

theorem hasWeakDerivOn_const {l r : ℝ} (hlr : l ≤ r) (c : ℂ) :
    HasWeakDerivOn (Ioo l r) (fun _ => c) 0 := by
  refine ⟨continuous_const.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self,
    integrable_zero _ _ _, ?_⟩
  intro φ hφ
  have hφac : AbsolutelyContinuousOnInterval φ l r :=
    (hφ.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hleft : φ l = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl l) (hφ.2.2 hx).1)
  have hright : φ r = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl r) (hφ.2.2 hx).2)
  have hint := hφac.integral_deriv_eq_sub
  rw [hleft, hright, sub_self, intervalIntegral.integral_of_le hlr,
    integral_Ioc_eq_integral_Ioo] at hint
  simp only [Pi.zero_apply, smul_zero, integral_zero, neg_zero]
  rw [integral_smul_const, hint, zero_smul]

theorem hasWeakDerivOn_const_add_primitive {l r : ℝ} (hlr : l ≤ r)
    {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo l r)) (c : ℂ) :
    HasWeakDerivOn (Ioo l r) (fun x => c + ∫ t in l..x, g t) g := by
  have hfun : (fun _ : ℝ => c) + (fun x => ∫ t in l..x, g t) =
      (fun x => c + ∫ t in l..x, g t) := by
    funext x
    rfl
  simpa only [hfun, zero_add] using
    (hasWeakDerivOn_const hlr c).add (hasWeakDerivOn_primitive hlr hg)

theorem complex_const_add_primitive_absolutelyContinuous {l r : ℝ} (hlr : l ≤ r)
    {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo l r)) (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun x => c + ∫ t in l..x, g t) l r := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) l r :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  exact hc.add (complex_primitive_absolutelyContinuous hlr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlr).mpr hg))

theorem real_ac_test_identity {l r : ℝ} (hlr : l ≤ r) {F g : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F l r)
    (hd : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (g x) x)
    {φ : ℝ → ℝ} (hφ : IsSmoothTestOn (Ioo l r) φ) :
    (∫ x in Ioo l r, deriv φ x * F x) = -(∫ x in Ioo l r, φ x * g x) := by
  have hφac : AbsolutelyContinuousOnInterval φ l r :=
    (hφ.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hleft : φ l = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl l) (hφ.2.2 hx).1)
  have hright : φ r = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl r) (hφ.2.2 hx).2)
  have hint := hφac.integral_mul_deriv_eq_deriv_mul hF
  have heq : (∫ x in l..r, φ x * deriv F x) = ∫ x in l..r, φ x * g x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with x hx hi
    rw [(hx (uIoc_subset_uIcc hi)).deriv]
  rw [heq, hleft, hright, zero_mul, zero_mul, sub_self, zero_sub] at hint
  rw [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo] at hint
  exact (neg_eq_iff_eq_neg.mpr hint).symm

theorem hasWeakDerivOn_of_absolutelyContinuous {l r : ℝ} (hlr : l ≤ r)
    {F g : ℝ → ℂ} (hF : AbsolutelyContinuousOnInterval F l r)
    (hg : IntegrableOn g (Ioo l r))
    (hd : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt F (g x) x) :
    HasWeakDerivOn (Ioo l r) F g := by
  have hFc : ContinuousOn F (Icc l r) := by
    simpa only [uIcc_of_le hlr] using hF.continuousOn
  have hFi : IntegrableOn F (Ioo l r) := hFc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine ⟨hFi, hg, ?_⟩
  intro φ hφ
  have htestF := hφ.deriv.integrable_smul hFi
  have htestg := hφ.integrable_smul hg
  have hmap (L : ℂ →L[ℝ] ℝ) :
      L (∫ x in Ioo l r, deriv φ x • F x) = L (-(∫ x in Ioo l r, φ x • g x)) := by
    have hLF : AbsolutelyContinuousOnInterval (fun x => L (F x)) l r :=
      L.lipschitzWith.comp_absolutelyContinuousOnInterval hF
    have hLd : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt (fun x => L (F x)) (L (g x)) x := by
      filter_upwards [hd] with x hx hi
      exact L.hasFDerivAt.comp_hasDerivAt x (hx hi)
    rw [L.map_neg, ← L.integral_comp_comm htestF, ← L.integral_comp_comm htestg]
    simp only [map_smul, smul_eq_mul]
    exact real_ac_test_identity hlr hLF hLd hφ
  exact Complex.ext (hmap Complex.reCLM) (hmap Complex.imCLM)

end Involution
