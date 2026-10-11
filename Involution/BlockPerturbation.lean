module

public import Involution.BlockMultiplier
public import Involution.SparseCuts
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Tactic.NoncommRing

/-! Метод подобных операторов на разреженных блоках.
Пусть `G = diag (ω i ^ 2)`, `R = G^(-1/2) = diag (1 / ω i)`, и возмущение задано
ограниченным `Ŝ = S G^(-1/2)` с `40 ‖Ŝ‖ ≤ δ`. Тогда существуют обратимый `U` и
блочно-диагональный `D̂`, для которых `(G + S) U = U (G + D̂ G^(1/2))`. Здесь это
записано тождествами для ограниченных операторов:
`U R² = R² M` и `(1 + Ŝ R) M = U (1 + D̂ R)`. -/

@[expose] public noncomputable section

namespace Involution

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Алгебраическая часть: уравнение неподвижной точки и соотношение Сильвестра
дают сплетающее тождество. -/
theorem similarity_algebra {A : Type*} [Ring A] (x s g0 g1 p r : A)
    (hfp : x = s - s * g1 + g0 * p) (h2 : g1 * r = r * g0 + r * (x - p) * r) :
    (1 + s * r) * (1 - g0 - (x - p) * r) = (1 - g0) * (1 + p * r) := by
  have key : s * r * g0 + s * r * (x - p) * r = s * g1 * r := by
    rw [mul_assoc s g1 r, h2]
    noncomm_ring
  have h3 : x - s + s * g1 = g0 * p := by
    have h : (s - s * g1 + g0 * p) - s + s * g1 = g0 * p := by abel
    rwa [← hfp] at h
  calc
    (1 + s * r) * (1 - g0 - (x - p) * r) =
        1 - g0 - (x - p) * r + s * r - (s * r * g0 + s * r * (x - p) * r) := by noncomm_ring
    _ = 1 - g0 - (x - p) * r + s * r - s * g1 * r := by rw [key]
    _ = 1 - g0 + p * r - (x - s + s * g1) * r := by noncomm_ring
    _ = 1 - g0 + p * r - g0 * p * r := by rw [h3]
    _ = (1 - g0) * (1 + p * r) := by noncomm_ring

theorem domain_algebra {A : Type*} [Ring A] (x g0 p r : A)
    (h1 : g0 * r * r = r * r * g0 + r * r * (x - p) * r) :
    (1 - g0) * (r * r) = r * r * (1 - g0 - (x - p) * r) := by
  calc
    (1 - g0) * (r * r) = r * r - g0 * r * r := by noncomm_ring
    _ = r * r - (r * r * g0 + r * r * (x - p) * r) := by rw [h1]
    _ = _ := by noncomm_ring

namespace SpectralBlocks

variable (D : SpectralBlocks ι) (b : HilbertBasis ι ℂ H)

/-- Мультипликатор `1 / (ω i - ω l)` вне диагональных блоков. -/
def gammaMinus : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  schurMap b (D.offMult 1) (4 * D.δ⁻¹) (D.offMult_bound b 1 (by simp))

/-- Мультипликатор `1 / (ω i + ω l)` вне диагональных блоков. -/
def gammaPlus : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  schurMap b (D.offMult (-1)) (4 * D.δ⁻¹) (D.offMult_bound b (-1) (by simp))

/-- Блочно-диагональная часть оператора. -/
def pinch : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  schurMap b D.diagMult 1 (D.diagMult_bound b)

/-- Решение уравнения Сильвестра с правой частью `X̂ G^(1/2)`: множитель
`ω l / (ω i ^ 2 - ω l ^ 2)`. -/
def gamma0 : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  (1 / 2 : ℂ) • (D.gammaMinus b - D.gammaPlus b)

/-- То же решение, сопряжённое с `G^(1/2)`: множитель `ω i / (ω i ^ 2 - ω l ^ 2)`. -/
def gamma1 : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  (1 / 2 : ℂ) • (D.gammaMinus b + D.gammaPlus b)

theorem gammaMinus_norm_le (X : H →L[ℂ] H) : ‖D.gammaMinus b X‖ ≤ 4 * D.δ⁻¹ * ‖X‖ :=
  schurMap_norm_le b _ _ _ X

theorem gammaPlus_norm_le (X : H →L[ℂ] H) : ‖D.gammaPlus b X‖ ≤ 4 * D.δ⁻¹ * ‖X‖ :=
  schurMap_norm_le b _ _ _ X

omit [CompleteSpace H] in
theorem pinch_norm_le (X : H →L[ℂ] H) : ‖D.pinch b X‖ ≤ ‖X‖ := by
  have h := schurMap_norm_le b D.diagMult 1 (D.diagMult_bound b) X
  rwa [one_mul] at h

theorem gamma0_norm_le (X : H →L[ℂ] H) : ‖D.gamma0 b X‖ ≤ 4 * D.δ⁻¹ * ‖X‖ := by
  have h1 := D.gammaMinus_norm_le b X
  have h2 := D.gammaPlus_norm_le b X
  have h3 := norm_sub_le (D.gammaMinus b X) (D.gammaPlus b X)
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  change ‖(1 / 2 : ℂ) • (D.gammaMinus b X - D.gammaPlus b X)‖ ≤ _
  rw [norm_smul, hhalf]
  linarith

theorem gamma1_norm_le (X : H →L[ℂ] H) : ‖D.gamma1 b X‖ ≤ 4 * D.δ⁻¹ * ‖X‖ := by
  have h1 := D.gammaMinus_norm_le b X
  have h2 := D.gammaPlus_norm_le b X
  have h3 := norm_add_le (D.gammaMinus b X) (D.gammaPlus b X)
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  change ‖(1 / 2 : ℂ) • (D.gammaMinus b X + D.gammaPlus b X)‖ ≤ _
  rw [norm_smul, hhalf]
  linarith

theorem gamma0_entry (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (D.gamma0 b X) i l =
      (1 / 2 : ℂ) * (D.offMult 1 i l - D.offMult (-1) i l) * opEntry b X i l := by
  change opEntry b ((1 / 2 : ℂ) • (D.gammaMinus b X - D.gammaPlus b X)) i l = _
  rw [opEntry_smul, opEntry_sub, gammaMinus, gammaPlus, schurMap_entry, schurMap_entry]
  ring

theorem gamma1_entry (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (D.gamma1 b X) i l =
      (1 / 2 : ℂ) * (D.offMult 1 i l + D.offMult (-1) i l) * opEntry b X i l := by
  change opEntry b ((1 / 2 : ℂ) • (D.gammaMinus b X + D.gammaPlus b X)) i l = _
  rw [opEntry_smul, opEntry_add, gammaMinus, gammaPlus, schurMap_entry, schurMap_entry]
  ring

omit [CompleteSpace H] in
theorem pinch_entry (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (D.pinch b X) i l = D.diagMult i l * opEntry b X i l :=
  schurMap_entry b _ _ _ X i l

/-- Символ оператора `G^(-1/2)`. -/
def rho (i : ι) : ℂ := ((D.ω i)⁻¹ : ℝ)

theorem rho_norm_le (i : ι) : ‖D.rho i‖ ≤ D.ω₀⁻¹ := by
  rw [rho, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.ω_pos i))]
  exact inv_anti₀ D.ω₀_pos (D.ω_ge i)

/-- Оператор `R = G^(-1/2)`. -/
def invFreq : H →L[ℂ] H := diagOp b D.rho

omit [CompleteSpace H] in
theorem opEntry_invFreq_mul (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (D.invFreq b * X) i l = D.rho i * opEntry b X i l :=
  opEntry_diagOp_comp b D.rho _ D.rho_norm_le X i l

omit [CompleteSpace H] in
theorem opEntry_mul_invFreq (X : H →L[ℂ] H) (i l : ι) :
    opEntry b (X * D.invFreq b) i l = opEntry b X i l * D.rho l :=
  opEntry_comp_diagOp b D.rho _ D.rho_norm_le X i l

theorem offMult_of_eq (s : ℝ) {i l : ι} (h : D.blk i = D.blk l) : D.offMult s i l = 0 := by
  unfold offMult
  exact ite_eq_right (by simpa using h)

theorem offMult_of_ne (s : ℝ) {i l : ι} (h : D.blk i ≠ D.blk l) :
    D.offMult s i l = (((D.ω i - s * D.ω l : ℝ) : ℂ))⁻¹ := by
  unfold offMult
  exact ite_eq_left h

theorem offMult_one_of_ne {i l : ι} (h : D.blk i ≠ D.blk l) :
    D.offMult 1 i l = ((D.ω i : ℂ) - D.ω l)⁻¹ := by
  rw [D.offMult_of_ne 1 h]
  push_cast
  rw [one_mul]

theorem offMult_neg_one_of_ne {i l : ι} (h : D.blk i ≠ D.blk l) :
    D.offMult (-1) i l = ((D.ω i : ℂ) + D.ω l)⁻¹ := by
  rw [D.offMult_of_ne (-1) h]
  push_cast
  rw [neg_one_mul, sub_neg_eq_add]

theorem rho_eq (i : ι) : D.rho i = (D.ω i : ℂ)⁻¹ := by
  rw [rho, Complex.ofReal_inv]

theorem diagMult_of_eq {i l : ι} (h : D.blk i = D.blk l) : D.diagMult i l = 1 := by
  unfold diagMult
  exact ite_eq_left h

theorem diagMult_of_ne {i l : ι} (h : D.blk i ≠ D.blk l) : D.diagMult i l = 0 := by
  unfold diagMult
  exact ite_eq_right h

/-- Соотношение Сильвестра в ограниченной форме:
`Γ₀ X̂ · R² = R² · Γ₀ X̂ + R² (X̂ - J X̂) R`. -/
theorem gamma0_sylvester (X : H →L[ℂ] H) :
    D.gamma0 b X * D.invFreq b * D.invFreq b =
      D.invFreq b * D.invFreq b * D.gamma0 b X +
        D.invFreq b * D.invFreq b * (X - D.pinch b X) * D.invFreq b := by
  apply opEntry_ext b
  intro i l
  rw [opEntry_add, opEntry_mul_invFreq, opEntry_mul_invFreq, opEntry_mul_invFreq,
    mul_assoc (D.invFreq b) (D.invFreq b) (D.gamma0 b X),
    mul_assoc (D.invFreq b) (D.invFreq b) (X - D.pinch b X),
    opEntry_invFreq_mul, opEntry_invFreq_mul, opEntry_invFreq_mul, opEntry_invFreq_mul,
    opEntry_sub, gamma0_entry, pinch_entry]
  by_cases hb : D.blk i = D.blk l
  · rw [D.offMult_of_eq 1 hb, D.offMult_of_eq (-1) hb, D.diagMult_of_eq hb]
    ring
  · rw [D.offMult_one_of_ne hb, D.offMult_neg_one_of_ne hb, D.diagMult_of_ne hb,
      D.rho_eq i, D.rho_eq l]
    have hi := (D.ω_pos i).ne'
    have hl := (D.ω_pos l).ne'
    have hne : D.ω i - D.ω l ≠ 0 := sub_ne_zero.mpr (D.ω_ne_of_blk_ne hb)
    have hpos : D.ω i + D.ω l ≠ 0 := (add_pos (D.ω_pos i) (D.ω_pos l)).ne'
    have hic : (D.ω i : ℂ) ≠ 0 := by exact_mod_cast hi
    have hlc : (D.ω l : ℂ) ≠ 0 := by exact_mod_cast hl
    have hnec : (D.ω i : ℂ) - D.ω l ≠ 0 := by exact_mod_cast hne
    have hposc : (D.ω i : ℂ) + D.ω l ≠ 0 := by exact_mod_cast hpos
    field_simp
    ring

/-- Связь двух решений: `Γ₁ X̂ · R = R · Γ₀ X̂ + R (X̂ - J X̂) R`. -/
theorem gamma1_invFreq (X : H →L[ℂ] H) :
    D.gamma1 b X * D.invFreq b =
      D.invFreq b * D.gamma0 b X + D.invFreq b * (X - D.pinch b X) * D.invFreq b := by
  apply opEntry_ext b
  intro i l
  rw [opEntry_add, opEntry_mul_invFreq, opEntry_mul_invFreq, opEntry_invFreq_mul,
    opEntry_invFreq_mul, opEntry_sub, gamma0_entry, gamma1_entry, pinch_entry]
  by_cases hb : D.blk i = D.blk l
  · rw [D.offMult_of_eq 1 hb, D.offMult_of_eq (-1) hb, D.diagMult_of_eq hb]
    ring
  · rw [D.offMult_one_of_ne hb, D.offMult_neg_one_of_ne hb, D.diagMult_of_ne hb,
      D.rho_eq i, D.rho_eq l]
    have hi := (D.ω_pos i).ne'
    have hl := (D.ω_pos l).ne'
    have hne : D.ω i - D.ω l ≠ 0 := sub_ne_zero.mpr (D.ω_ne_of_blk_ne hb)
    have hpos : D.ω i + D.ω l ≠ 0 := (add_pos (D.ω_pos i) (D.ω_pos l)).ne'
    have hic : (D.ω i : ℂ) ≠ 0 := by exact_mod_cast hi
    have hlc : (D.ω l : ℂ) ≠ 0 := by exact_mod_cast hl
    have hnec : (D.ω i : ℂ) - D.ω l ≠ 0 := by exact_mod_cast hne
    have hposc : (D.ω i : ℂ) + D.ω l ≠ 0 := by exact_mod_cast hpos
    field_simp
    ring

/-- Подобие блочно-диагональному оператору. `U` обратим, `Dg` не связывает разные
блоки, и выполнены два тождества: сохранение области `U R² = R² M` и сплетение
`(1 + Ŝ R) M = U (1 + Dg)`. -/
theorem exists_block_similarity (S : H →L[ℂ] H) (hS : 40 * ‖S‖ ≤ D.δ) :
    ∃ (U : (H →L[ℂ] H)ˣ) (M Dg : H →L[ℂ] H),
      (U : H →L[ℂ] H) * (D.invFreq b * D.invFreq b) = D.invFreq b * D.invFreq b * M ∧
      (1 + S * D.invFreq b) * M = (U : H →L[ℂ] H) * (1 + Dg) ∧
      ∀ i l, D.blk i ≠ D.blk l → opEntry b Dg i l = 0 := by
  have hδ := D.δ_pos
  have hγ : (0 : ℝ) ≤ 4 * D.δ⁻¹ := by positivity
  have hsmall : 10 * (4 * D.δ⁻¹) * ‖S‖ ≤ 1 := by
    have h : 40 * ‖S‖ * D.δ⁻¹ ≤ D.δ * D.δ⁻¹ :=
      mul_le_mul_of_nonneg_right hS (inv_nonneg.mpr hδ.le)
    rw [mul_inv_cancel₀ hδ.ne'] at h
    linarith
  obtain ⟨X, hfp, hX⟩ := exists_similarity_fixedPoint (D.gamma0 b) (D.gamma1 b) (D.pinch b)
    (4 * D.δ⁻¹) hγ (D.gamma0_norm_le b) (D.gamma1_norm_le b) (D.pinch_norm_le b) S hsmall
  have hY : ‖D.gamma0 b X‖ < 1 := by
    have h1 := D.gamma0_norm_le b X
    have h2 : 4 * D.δ⁻¹ * ‖X‖ ≤ 4 * D.δ⁻¹ * (2 * ‖S‖) := mul_le_mul_of_nonneg_left hX hγ
    nlinarith [norm_nonneg S]
  refine ⟨Units.oneSub (D.gamma0 b X) hY,
    1 - D.gamma0 b X - (X - D.pinch b X) * D.invFreq b, D.pinch b X * D.invFreq b, ?_, ?_, ?_⟩
  · rw [Units.val_oneSub]
    exact domain_algebra X (D.gamma0 b X) (D.pinch b X) (D.invFreq b) (D.gamma0_sylvester b X)
  · rw [Units.val_oneSub]
    exact similarity_algebra X S (D.gamma0 b X) (D.gamma1 b X) (D.pinch b X) (D.invFreq b)
      hfp (D.gamma1_invFreq b X)
  · intro i l hb
    rw [opEntry_mul_invFreq, pinch_entry, D.diagMult_of_ne hb, zero_mul, zero_mul]

end SpectralBlocks

end Involution
