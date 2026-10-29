import BstLean.Part254GaussianScalar
import BstLean.Part254Cells

namespace BstLean.Part254
open Real Set BstLean.Part199 BstLean.Part238 BstLean.Part251

theorem fixedGaussianCovariance_le_envelope {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100) (528 / 1000)) :
    fixedGaussianCovariance 12225 θ ≤ gaussianEnvelope θ := by
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  obtain ⟨hm, hc, hwide⟩ := envelope_denominators hw.2
  obtain ⟨hrw, hrc⟩ := radius_envelope hθ0
  have hwi : (1 - radiusMinus 12225 θ exampleWide)⁻¹ ≤
      (1 - radiusEnvelope θ true)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hwide (by linarith)
  have hci : (1 - radiusMinus 12225 θ exampleCore)⁻¹ ≤
      (1 - radiusEnvelope θ false)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hc (by linarith)
  have hk := mul_le_mul_of_nonneg_right fixedCore_enclosure.2
    (inv_nonneg.mpr hm.le)
  have hp := mul_le_mul
    (mul_le_mul_of_nonneg_left hci (by norm_num : (0 : ℝ) ≤ 67 / 100))
    gaussian_core_pair_upper (by exact gaussianTail_nonneg _)
    (by positivity : 0 ≤ (67 / 100 : ℝ) * (1 - radiusEnvelope θ false)⁻¹)
  have ho := mul_le_mul
    (mul_le_mul_of_nonneg_left hwi (by norm_num : (0 : ℝ) ≤ 67 / 100))
    gaussian_core_outside_upper (by exact add_nonneg (gaussianTail_nonneg _) (by positivity))
    (by positivity : 0 ≤ (67 / 100 : ℝ) * (1 - radiusEnvelope θ true)⁻¹)
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hk hp) ho) hθ0
  have he := mul_le_mul_of_nonneg_left
    (gaussian_exceptional_upper
      (BstLean.Part249.optionB_cutoff (by norm_num : 11883 ≤ 12225)))
    (by norm_num : (0 : ℝ) ≤ 13 / 10)
  unfold fixedGaussianCovariance gaussianScalar gaussianEnvelope
  simpa only [div_eq_mul_inv, Nat.cast_ofNat] using add_le_add hs he

theorem gaussianEnvelope_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 528 / 1000) : gaussianEnvelope a ≤ gaussianEnvelope b := by
  obtain ⟨hb0, hbc, hbw⟩ := envelope_denominators hb
  have hr0 : 1 - 4 * b / 12225 ≤ 1 - 4 * a / 12225 := by linarith
  have hrc : 1 - radiusEnvelope b false ≤ 1 - radiusEnvelope a false := by
    norm_num [radiusEnvelope]; linarith
  have hrw : 1 - radiusEnvelope b true ≤ 1 - radiusEnvelope a true := by
    norm_num [radiusEnvelope]; linarith
  have h0 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 598514915 / 10 ^ 9) hb0 hr0
  have hc := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 67 / 100) hbc hrc
  have hw := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 67 / 100) hbw hrw
  unfold gaussianEnvelope
  refine add_le_add ?_ le_rfl
  apply mul_le_mul hab
  · exact add_le_add
      (add_le_add h0 (mul_le_mul_of_nonneg_right hc (by norm_num)))
      (mul_le_mul_of_nonneg_right hw (by norm_num))
  · obtain ⟨h0a, hca, hwa⟩ := envelope_denominators (hab.trans hb)
    positivity
  · linarith

structure SharpGridCertificate (i : Fin 60) (cap : ℝ) : Prop where
  upper : gaussianEnvelope (cellUpper i) ≤ cap
  previous : cap - 1 / 10 ^ 9 < gaussianEnvelope (cellUpper i)
  nonneg : 0 ≤ cap
  source_gap : (rowCellAudit i).covarianceCap < cap

end BstLean.Part254
