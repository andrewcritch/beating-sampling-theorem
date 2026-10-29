import BstLean.Part276Stat
import BstLean.Part276Radius

/-! The four common-cap prices at dimension 12224, with the sharp node moment,
the sharp radius root and the paper's four allowances. -/
namespace BstLean.Part276
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part216 BstLean.Part220 BstLean.Part223

theorem sharp_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (sharpEnvelope C).f0 12224 160 ∧
    0 ≤ (sharpEnvelope C).f1 12224 160 ∧ 0 ≤ (sharpEnvelope C).f2 ∧
    0 ≤ (sharpEnvelope C).w0 12224 160 ∧
    0 ≤ (sharpEnvelope C).w1 12224 160 ∧ 0 ≤ (sharpEnvelope C).w2 12224 160 := by
  let d := sharpEnvelope C
  have hD : 0 ≤ d.D := (sharp_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (sharp_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (sharp_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12224 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, sharpEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12224 160 ∧ 0 ≤ d.f1 12224 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12224 160 ∧ 0 ≤ d.w1 12224 160 ∧ 0 ≤ d.w2 12224 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem sharp_location_correction : locationR16 12224 ≤ 2 * (228 / 100 : ℝ) / 12224 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem sharp_energy_correction : energyR16 12224 ≤ 2 * (370 / 100 : ℝ) / 12224 := by
  have hr : (1216070380 : ℝ) ^ (1 / 16 : ℝ) ≤ 370 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 1216070380)
      (by norm_num : (16 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold energyR16
  gcongr

theorem sharp_bias_prices {C : ℝ} (hCp : 0 < C) (hC4 : C ≤ 32 / 10) :
    (completeRAData (sharpEnvelope C) 12224 160).locationBound 12224 160 ≤
      (890 / 100000 : ℝ) ^ 16 ∧
    (completeRAData (sharpEnvelope C) 12224 160).energyBound 12224 160 ≤
      (600 / 100000 : ℝ) ^ 16 := by
  have hC := hCp.le
  let d := sharpEnvelope C
  have F := sharp_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := sharp_coefficient_nonneg hC hC4
  have hDp : 0 < d.D := by
    change 0 < envelopeD 12224 (61 / 100) * (C + C)
    exact mul_pos (by norm_num [envelopeD, tA, mA]) (by linarith)
  have hV0 : 0 ≤ d.V := (sharp_envelope_V hC hC4).1
  have hP0 : 0 ≤ d.P := (sharp_envelope_P hC hC4).1
  have hsm : 0 < √(17 / (100 * 12224) : ℝ) := by positivity
  have hf0p : 0 < d.f0 12224 160 := by
    change 0 < AF0 (√(17 / (100 * 12224) : ℝ)) (tA 12224 * 160 ^ 2 + 26 / (10 * 12224))
      d.D d.V d.P
    unfold AF0
    have t1 : 0 < phiG 0 / (2 * √(17 / (100 * 12224) : ℝ)) * d.D :=
      mul_pos (div_pos (phiG_pos 0) (by positivity)) hDp
    have t2 : 0 ≤ 1 / 2 * (phiG 0 / (√2 * √(17 / (100 * 12224) : ℝ) ^ 3) * d.V) :=
      mul_nonneg (by norm_num) (mul_nonneg (div_nonneg (phiG_pos 0).le (by positivity)) hV0)
    have t3 : 0 ≤ d.P * (3 / 2 * phiG 0 / √(17 / (100 * 12224) : ℝ) *
        (tA 12224 * 160 ^ 2 + 26 / (10 * 12224))) :=
      mul_nonneg hP0 (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (phiG_pos 0).le)
        hsm.le) (by norm_num [tA, mA]))
    linarith
  have hw0p : 0 < d.w0 12224 160 := by
    change 0 < AW0 (√(17 / (100 * 12224) : ℝ)) (tA 12224 * 160 ^ 2 + 26 / (10 * 12224))
      d.D d.V d.P
    unfold AW0
    have t2 : 0 ≤ phiG 1 / (2 * √(17 / (100 * 12224) : ℝ) ^ 2) * d.V :=
      mul_nonneg (div_nonneg (phiG_pos 1).le (by positivity)) hV0
    have t3 : 0 ≤ d.P * (4 * (tA 12224 * 160 ^ 2 + 26 / (10 * 12224))) :=
      mul_nonneg hP0 (by norm_num [tA, mA])
    linarith
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12224 160) (d.f1 12224 160) d.f2 ≤
      (405 / 10 ^ 11 : ℝ) + 14 / 5 * (135 / 10 ^ 11) + 14 * (325 / 10 ^ 12) :=
    (radius_polynomial_root_sharp hf0p hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12224 160) (d.w1 12224 160)
      (d.w2 12224 160) ≤
      (1650 / 10 ^ 14 : ℝ) + 14 / 5 * (1175 / 10 ^ 14) + 14 * (429 / 10 ^ 14) :=
    (radius_polynomial_root_sharp hw0p hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12224 160) (d.f1 12224 160) d.f2 ≤
      (405 / 10 ^ 11 : ℝ) ^ 2 + 2 * (405 / 10 ^ 11) * (135 / 10 ^ 11) * (126 / 100) +
      2 * ((135 / 10 ^ 11) ^ 2 + 2 * (405 / 10 ^ 11) * (325 / 10 ^ 12)) +
      6 * (135 / 10 ^ 11) * (325 / 10 ^ 12) * (126 / 100) + 8 * (325 / 10 ^ 12) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12224 160) (d.f1 12224 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12224 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12224 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12224 160) (d.f1 12224 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12224 160) (d.w1 12224 160) (d.w2 12224 160)
  have hwexpr0 : 0 ≤ d.w0 12224 160 + d.w1 12224 160 * √(π / 2) +
      2 * d.w2 12224 160 + energyR16 12224 *
      radiusPolynomialRoot16 (d.w0 12224 160) (d.w1 12224 160) (d.w2 12224 160) := by
    positivity
  constructor
  · change (12224 : ℝ) ^ 8 * (mA 12224 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12224 160) (d.f1 12224 160) d.f2 + locationR16 12224 *
        radiusPolynomialRoot16 (d.f0 12224 160) (d.f1 12224 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12224 : ℝ) ^ 8 * (mA 12224 : ℝ) ^ 8 *
        (((405 / 10 ^ 11 : ℝ) ^ 2 + 2 * (405 / 10 ^ 11) * (135 / 10 ^ 11) * (126 / 100) +
          2 * ((135 / 10 ^ 11) ^ 2 + 2 * (405 / 10 ^ 11) * (325 / 10 ^ 12)) +
          6 * (135 / 10 ^ 11) * (325 / 10 ^ 12) * (126 / 100) + 8 * (325 / 10 ^ 12) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12224) *
          ((405 / 10 ^ 11 : ℝ) + 14 / 5 * (135 / 10 ^ 11) + 14 * (325 / 10 ^ 12)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact sharp_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12224 : ℝ) ^ 16 *
      (d.w0 12224 160 + d.w1 12224 160 * √(π / 2) + 2 * d.w2 12224 160 +
        energyR16 12224 * radiusPolynomialRoot16 (d.w0 12224 160) (d.w1 12224 160)
          (d.w2 12224 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12224 : ℝ) ^ 16 *
        ((1650 / 10 ^ 14 : ℝ) + (1175 / 10 ^ 14) * (126 / 100) + 2 * (429 / 10 ^ 14) +
          (2 * (370 / 100 : ℝ) / 12224) *
          ((1650 / 10 ^ 14 : ℝ) + 14 / 5 * (1175 / 10 ^ 14) + 14 * (429 / 10 ^ 14))) ^ 16 := by
        gcongr <;> first
          | exact F.w0
          | exact F.w1
          | exact F.w2
          | exact hπ
          | exact sharp_energy_correction
          | exact htW
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]


noncomputable def sharpH : ℝ := 5435 / 10000

noncomputable def sharpPrices : Fin 4 → ℝ :=
  completeMomentPrices 12224 (61 / 100) 160 (17 / (100 * 12224)) (26 / (10 * 12224))
    (statisticsConstant (paperBound256 12224)) √((42 / 10 : ℝ) / 12224) sharpH

theorem sharp_location_fluctuation_price :
    (k24 * (√(12224 : ℝ) *
      √(tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) / 2) * √sharpH) ^ 24 ≤
      (105 / 10 ^ 6 : ℝ) * fourA 0 ^ 24 := by
  have hN : √(12224 : ℝ) ^ 24 = (12224 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) ^ 24 =
      (tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √sharpH ^ 24 = sharpH ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [sharpH])]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourA, sharpH, Nat.factorial]

theorem sharp_energy_coefficient :
    energyCoefficient18 12224 ≤ (2 * 12224 * (21165 / 10000 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 21165 / 10000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem sharp_energy_fluctuation_price :
    (√(tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) * √((42 / 10 : ℝ) / 12224) *
      energyCoefficient18 12224) ^ 18 * sharpH ^ 12 * (61 / 100 : ℝ) ^ 6 ≤
        (490 / 10 ^ 6 : ℝ) * fourA 2 ^ 18 := by
  have hlam : √(tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) ^ 18 =
      (tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 12224) ^ 18 = ((42 / 10 : ℝ) / 12224) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 12224 * ((160 : ℝ) ^ 2 / (12224 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 12224) ^ 9 *
        (2 * 12224 * (21165 / 10000 : ℝ) + (269 / 10) * 8) ^ 18 * sharpH ^ 12 *
          (61 / 100 : ℝ) ^ 6 := by
      gcongr <;> first
        | exact sharp_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourA, sharpH]

theorem sharp_four_price :
    sharpPrices 0 / fourA 0 ^ 24 + sharpPrices 1 / fourA 1 ^ 16 +
      sharpPrices 2 / fourA 2 ^ 18 + sharpPrices 3 / fourA 3 ^ 16 ≤ 667 / 10 ^ 6 := by
  have h0 : sharpPrices 0 ≤ (105 / 10 ^ 6 : ℝ) * fourA 0 ^ 24 :=
    sharp_location_fluctuation_price
  have h2 : sharpPrices 2 ≤ (490 / 10 ^ 6 : ℝ) * fourA 2 ^ 18 :=
    sharp_energy_fluctuation_price
  have hb := sharp_bias_prices statistics_constant_pos_12224 statistics_constant_12224
  have h1 : sharpPrices 1 ≤ (890 / 100000 : ℝ) ^ 16 := hb.1
  have h3 : sharpPrices 3 ≤ (600 / 100000 : ℝ) ^ 16 := hb.2
  have hd0 : sharpPrices 0 / fourA 0 ^ 24 ≤ (105 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourA])).mpr
    exact h0
  have hd2 : sharpPrices 2 / fourA 2 ^ 18 ≤ (490 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourA])).mpr
    exact h2
  have hd1 : sharpPrices 1 / fourA 1 ^ 16 ≤ (60 / 10 ^ 6 : ℝ) :=
    (div_le_div_of_nonneg_right h1 (by norm_num [fourA])).trans (by norm_num [fourA])
  have hd3 : sharpPrices 3 / fourA 3 ^ 16 ≤ (12 / 10 ^ 6 : ℝ) :=
    (div_le_div_of_nonneg_right h3 (by norm_num [fourA])).trans (by norm_num [fourA])
  linarith

end BstLean.Part276
