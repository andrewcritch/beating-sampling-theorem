import BstLean.Part212Mixed

/-! The mixed moment uses one input weight and one shared distribution of network weights. -/
namespace BstLean.Part212
open MeasureTheory
open scoped ENNReal

theorem weighted_score80 {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (μ : Measure A) [SFinite μ] (ν : Measure X) [IsProbabilityMeasure ν]
    {Ψ : A → X → ℝ} (hΨ : Measurable (Function.uncurry Ψ)) (h0 : ∀ a x, 0 ≤ Ψ a x)
    {w : X → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hwpos : ∀ᵐ x ∂ν, 0 < w x)
    {S : ℝ≥0∞} (hS : ∫⁻ x, ENNReal.ofReal (w x ^ 12) ∂ν = S) (hS0 : S ≠ 0) (hSt : S ≠ ∞)
    {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ᵐ x ∂ν, ∫⁻ a, ENNReal.ofReal (Ψ a x ^ 80) ∂μ ≤
      ENNReal.ofReal ((B * w x) ^ 80)) :
    ∫⁻ a, (∫⁻ x, ENNReal.ofReal (Ψ a x ^ 12) ∂ν) ^ ((20 : ℝ) / 3) ∂μ ≤
      ENNReal.ofReal (B ^ 80) * S ^ ((20 : ℝ) / 3) := by
  let d := fun x => ENNReal.ofReal (w x ^ 12)
  let ρ := S⁻¹ • ν.withDensity d
  have hd : Measurable d := (hw.pow_const 12).ennreal_ofReal
  letI : IsProbabilityMeasure ρ := by
    constructor
    change (S⁻¹ • ν.withDensity d) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply d MeasurableSet.univ,
      setLIntegral_univ, hS, ENNReal.inv_mul_cancel hS0 hSt]
  let G := fun a x => Ψ a x / w x
  have hg : Measurable (Function.uncurry G) := hΨ.div (hw.comp measurable_snd)
  have hg0 : ∀ a x, 0 ≤ G a x := fun a x => div_nonneg (h0 a x) (hw0 x)
  have hgm (a : A) (p : ℕ) : Measurable (fun x => ENNReal.ofReal (G a x ^ p)) :=
    ((hg.comp (measurable_const.prodMk measurable_id)).pow_const p).ennreal_ofReal
  have hwint (a : A) (p : ℕ) :
      ∫⁻ x, ENNReal.ofReal (G a x ^ p) ∂ρ =
        S⁻¹ * ∫⁻ x, d x * ENNReal.ofReal (G a x ^ p) ∂ν := by
    rw [lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul ν hd (hgm a p)]
    rfl
  have h12 (a : A) : (∫⁻ x, ENNReal.ofReal (Ψ a x ^ 12) ∂ν) =
      S * ∫⁻ x, ENNReal.ofReal (G a x ^ 12) ∂ρ := by
    rw [hwint, ← mul_assoc, ENNReal.mul_inv_cancel hS0 hSt, one_mul]
    apply lintegral_congr_ae
    filter_upwards [hwpos] with x hx
    dsimp [d, G]
    rw [← ENNReal.ofReal_mul (pow_nonneg hx.le 12)]
    congr 1
    rw [← mul_pow]
    field_simp
  have hp (a : A) : (∫⁻ x, ENNReal.ofReal (Ψ a x ^ 12) ∂ν) ^ ((20 : ℝ) / 3) ≤
      S ^ ((20 : ℝ) / 3) * ∫⁻ x, ENNReal.ofReal (G a x ^ 80) ∂ρ := by
    rw [h12, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact mul_le_mul_right (field_score_le_moment80 ρ
      (hg.comp (measurable_const.prodMk measurable_id)) (hg0 a)) _
  have hpoint : ∀ᵐ x ∂ν, ∫⁻ a, d x * ENNReal.ofReal (G a x ^ 80) ∂μ ≤
      ENNReal.ofReal (B ^ 80) * d x := by
    filter_upwards [hwpos, hM] with x hx hMx
    have he (a : A) : d x * ENNReal.ofReal (G a x ^ 80) =
        ENNReal.ofReal (w x ^ 12 / w x ^ 80) * ENNReal.ofReal (Ψ a x ^ 80) := by
      dsimp [d, G]
      rw [← ENNReal.ofReal_mul (pow_nonneg hx.le 12),
        ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hx.le 12) (pow_nonneg hx.le 80))]
      congr 1
      rw [div_pow]
      ring
    simp_rw [he]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right hMx _).trans (le_of_eq ?_)
    dsimp [d]
    rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hx.le 12) (pow_nonneg hx.le 80)),
      ← ENNReal.ofReal_mul (pow_nonneg hB 80), mul_pow]
    congr 1
    field_simp
  have hsub : (∫⁻ a, ∫⁻ x, d x * ENNReal.ofReal (G a x ^ 80) ∂ν ∂μ) ≤
      ENNReal.ofReal (B ^ 80) * S := by
    rw [lintegral_lintegral_swap
      ((hd.comp measurable_snd).mul (hg.pow_const 80).ennreal_ofReal).aemeasurable]
    refine (lintegral_mono_ae hpoint).trans (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [hS]
  have hSr : S ^ ((20 : ℝ) / 3) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSt
  have hSi : S⁻¹ ≠ ∞ := by exact ENNReal.inv_ne_top.mpr hS0
  calc (∫⁻ a, (∫⁻ x, ENNReal.ofReal (Ψ a x ^ 12) ∂ν) ^ ((20 : ℝ) / 3) ∂μ)
      ≤ ∫⁻ a, S ^ ((20 : ℝ) / 3) * ∫⁻ x, ENNReal.ofReal (G a x ^ 80) ∂ρ ∂μ :=
        lintegral_mono hp
    _ = (S ^ ((20 : ℝ) / 3) * S⁻¹) *
        (∫⁻ a, ∫⁻ x, d x * ENNReal.ofReal (G a x ^ 80) ∂ν ∂μ) := by
      simp_rw [hwint]
      rw [lintegral_const_mul' _ _ hSr, lintegral_const_mul' _ _ hSi, mul_assoc]
    _ ≤ (S ^ ((20 : ℝ) / 3) * S⁻¹) * (ENNReal.ofReal (B ^ 80) * S) :=
      mul_le_mul_right hsub _
    _ = ENNReal.ofReal (B ^ 80) * S ^ ((20 : ℝ) / 3) := by
      calc _ = (ENNReal.ofReal (B ^ 80) * S ^ ((20 : ℝ) / 3)) * (S⁻¹ * S) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hS0 hSt, mul_one]
end BstLean.Part212
