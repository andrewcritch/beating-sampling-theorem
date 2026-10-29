import BstLean.Part252TableCoefficients
import BstLean.Part252RadiusPolynomial
import BstLean.Part252FourTable

namespace BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12225 160 ∧
    0 ≤ (tableEnvelope C).f1 12225 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12225 160 ∧
    0 ≤ (tableEnvelope C).w1 12225 160 ∧ 0 ≤ (tableEnvelope C).w2 12225 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12225 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12225 160 ∧ 0 ≤ d.f1 12225 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12225 160 ∧ 0 ≤ d.w1 12225 160 ∧ 0 ≤ d.w2 12225 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12225 ≤ 2 * (228 / 100 : ℝ) / 12225 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12225 ≤ 2 * (370 / 100 : ℝ) / 12225 := by
  have hr : (1216070380 : ℝ) ^ (1 / 16 : ℝ) ≤ 370 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 1216070380)
      (by norm_num : (16 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold energyR16
  gcongr

theorem table_bias_prices {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    (completeRAData (tableEnvelope C) 12225 160).locationBound 12225 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12225 160).energyBound 12225 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12225 160) (d.f1 12225 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12225 160) (d.w1 12225 160)
      (d.w2 12225 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12225 160) (d.f1 12225 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12225 160) (d.f1 12225 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12225 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12225 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12225 160) (d.f1 12225 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12225 160) (d.w1 12225 160) (d.w2 12225 160)
  have hwexpr0 : 0 ≤ d.w0 12225 160 + d.w1 12225 160 * √(π / 2) +
      2 * d.w2 12225 160 + energyR16 12225 *
      radiusPolynomialRoot16 (d.w0 12225 160) (d.w1 12225 160) (d.w2 12225 160) := by
    positivity
  constructor
  · change (12225 : ℝ) ^ 8 * (mA 12225 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12225 160) (d.f1 12225 160) d.f2 + locationR16 12225 *
        radiusPolynomialRoot16 (d.f0 12225 160) (d.f1 12225 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12225 : ℝ) ^ 8 * (mA 12225 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12225) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12225 : ℝ) ^ 16 *
      (d.w0 12225 160 + d.w1 12225 160 * √(π / 2) + 2 * d.w2 12225 160 +
        energyR16 12225 * radiusPolynomialRoot16 (d.w0 12225 160) (d.w1 12225 160)
          (d.w2 12225 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12225 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12225) *
          (32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13))) ^ 16 := by
        gcongr <;> first
          | exact F.w0
          | exact F.w1
          | exact F.w2
          | exact hπ
          | exact table_energy_correction
          | exact htW
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]

theorem table_bias_charge_caps :
    (15 / 1000 : ℝ) ^ 16 / fourAllowances 1 ^ 16 +
      (10 / 1000 : ℝ) ^ 16 / fourAllowances 3 ^ 16 ≤ 6 / 10 ^ 6 := by
  norm_num [fourAllowances]

end BstLean.Part252
