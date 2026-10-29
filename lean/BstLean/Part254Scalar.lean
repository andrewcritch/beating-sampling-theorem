import BstLean.Part254Tails
import BstLean.Part251Obstruction

/-! A cell-dependent upper enclosure for the existing Option B scalar.
This retains the uniform TI coefficients and the existing covariance event. -/
namespace BstLean.Part254
open Real Set BstLean.Part199 BstLean.Part238 BstLean.Part251

noncomputable def radiusEnvelope (θ : ℝ) (wide : Bool) : ℝ :=
  if wide then 12 * (4522156317 / 10 ^ 12) + 2 * θ * (40447395714 / 10 ^ 12)
  else (56 / 10) * (4522156317 / 10 ^ 12) + 2 * θ * (24768870231 / 10 ^ 12)

noncomputable def scalarEnvelope (θ : ℝ) : ℝ :=
  θ * ((598514915 / 10 ^ 9) / (1 - 4 * θ / 12225) +
    (67 / 100) / (1 - radiusEnvelope θ false) * (11952045791 / 10 ^ 12) +
    (67 / 100) / (1 - radiusEnvelope θ true) * (40788358230 / 10 ^ 12)) +
    (13 / 10) * (1032 / 10 ^ 6)

theorem fixedCore_enclosure :
    (598514914 / 10 ^ 9 : ℝ) ≤ fixedCore ∧ fixedCore ≤ (598514915 / 10 ^ 9 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤
    ((595 / 1000 - 25 / 100) / 2) ^ 2 + (35 / 1000) ^ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (((595 / 1000 - 25 / 100) / 2) ^ 2 + (35 / 1000 : ℝ) ^ 2)
  constructor
  · apply le_min
    · unfold sharpK
      have := Real.sqrt_nonneg (51 / 100 : ℝ)
      nlinarith
    · unfold BstLean.Part182.ta_lam
      nlinarith
  · refine (min_le_right _ _).trans ?_
    unfold BstLean.Part182.ta_lam
    nlinarith

theorem radius_envelope {θ : ℝ} (hθ : 0 ≤ θ) :
    radiusMinus 12225 θ exampleWide ≤ radiusEnvelope θ true ∧
    radiusMinus 12225 θ exampleCore ≤ radiusEnvelope θ false := by
  have ha : √(θ * (1 - θ) / 12225) ≤ (4522156317 / 10 ^ 12 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hw : √(20 / 12225 : ℝ) ≤ 40447395714 / 10 ^ 12 :=
    BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hc : √((75 / 10) / 12225 : ℝ) ≤ 24768870231 / 10 ^ 12 :=
    BstLean.Part182.sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hwm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * θ by positivity)
  have hcm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * θ by positivity)
  constructor
  · change 2 * 6 * √(θ * (1 - θ) / (12225 : ℝ)) + 2 * θ * √(20 / 12225) ≤
      12 * (4522156317 / 10 ^ 12) + 2 * θ * (40447395714 / 10 ^ 12)
    nlinarith only [ha, hwm]
  · change 2 * (28 / 10) * √(θ * (1 - θ) / (12225 : ℝ)) +
      2 * θ * √((75 / 10) / 12225) ≤
      (56 / 10) * (4522156317 / 10 ^ 12) + 2 * θ * (24768870231 / 10 ^ 12)
    nlinarith only [ha, hcm]

theorem envelope_denominators {θ : ℝ} (hθ : θ ≤ 528 / 1000) :
    0 < 1 - 4 * θ / 12225 ∧
    0 < 1 - radiusEnvelope θ false ∧ 0 < 1 - radiusEnvelope θ true := by
  norm_num [radiusEnvelope]
  constructor
  · linarith
  constructor <;> linarith

theorem fixedCovariance_le_envelope {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100) (528 / 1000)) :
    fixedCovariance 12225 θ ≤ scalarEnvelope θ := by
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
    core_pair_upper (by unfold pairRowBound; positivity)
    (by positivity : 0 ≤ (67 / 100 : ℝ) * (1 - radiusEnvelope θ false)⁻¹)
  have ho := mul_le_mul
    (mul_le_mul_of_nonneg_left hwi (by norm_num : (0 : ℝ) ≤ 67 / 100))
    core_outside_upper (by unfold outsideBound; positivity)
    (by positivity : 0 ≤ (67 / 100 : ℝ) * (1 - radiusEnvelope θ true)⁻¹)
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hk hp) ho) hθ0
  have he := mul_le_mul_of_nonneg_left
    (BstLean.Part246.exceptional_bound_28
      (BstLean.Part249.optionB_cutoff (by norm_num : 11883 ≤ 12225)))
    (by norm_num : (0 : ℝ) ≤ 13 / 10)
  unfold fixedCovariance sharpScalar scalarEnvelope
  simpa only [div_eq_mul_inv, Nat.cast_ofNat] using add_le_add hs he

theorem scalarEnvelope_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 528 / 1000) : scalarEnvelope a ≤ scalarEnvelope b := by
  obtain ⟨hb0, hbc, hbw⟩ := envelope_denominators hb
  have hr0 : 1 - 4 * b / 12225 ≤ 1 - 4 * a / 12225 := by linarith
  have hrc : 1 - radiusEnvelope b false ≤ 1 - radiusEnvelope a false := by
    norm_num [radiusEnvelope]; linarith
  have hrw : 1 - radiusEnvelope b true ≤ 1 - radiusEnvelope a true := by
    norm_num [radiusEnvelope]; linarith
  have h0 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 598514915 / 10 ^ 9) hb0 hr0
  have hc := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 67 / 100) hbc hrc
  have hw := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 67 / 100) hbw hrw
  unfold scalarEnvelope
  refine add_le_add ?_ le_rfl
  apply mul_le_mul hab
  · exact add_le_add
      (add_le_add h0 (mul_le_mul_of_nonneg_right hc (by norm_num)))
      (mul_le_mul_of_nonneg_right hw (by norm_num))
  · obtain ⟨h0a, hca, hwa⟩ := envelope_denominators (hab.trans hb)
    positivity
  · linarith

end BstLean.Part254
