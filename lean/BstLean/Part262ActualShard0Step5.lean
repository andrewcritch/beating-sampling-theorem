import BstLean.Part262ActualShard0Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12225. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12223 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12223 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12223 128 ≤ (12477 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12477 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12225) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12225 : ℕ))
    (by norm_num : (12225 : ℕ) ≤ 16384)
  have ht : paperTail256 12225 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12225 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12225 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12225 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12225 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12225 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12223 128 * √(2 / (12225 : ℝ)) *
      (√(12225 : ℝ) + paperT0 12225 + paperTail256 12225) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12225 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12225 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12225 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12223 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12223 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12225 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12225

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12225 (61 / 100) 160 (17 / (100 * 12225)) (26 / (10 * 12225)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12225 (61 / 100) 160 (17 / (100 * 12225)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12225 / 12225 * (61 / 100)) ^ 4 * inverseRadius8 (12225 - 1) /
            envelopeGap 12225 (61 / 100) 160 (17 / (100 * 12225)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12225

namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12225 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12225 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12225 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12225 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12225 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12225) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12225) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12225) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12225) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12225) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12225 * (160 : ℝ) ^ 2 + 26 / (10 * 12225) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12225) : ℝ)) (tA 12225 * 160 ^ 2 + 26 / (10 * 12225)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12225) : ℝ)) d.D d.V d.P (√(tA 12225) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12225) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12225) : ℝ)) (tA 12225 * 160 ^ 2 + 26 / (10 * 12225)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12225) : ℝ)) (√(26 / (10 * 12225) : ℝ)) d.D d.V d.P (√(tA 12225) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12225) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12225

namespace BstLean.Part262.Row12225
open BstLean.Part252
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

end BstLean.Part262.Row12225

/-! A coarse bound on the actual paper statistics constant at dimension 12227. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12225 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12225 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12225 128 ≤ (12479 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12479 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12227) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12227 : ℕ))
    (by norm_num : (12227 : ℕ) ≤ 16384)
  have ht : paperTail256 12227 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12227 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12227 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12227 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12227 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12227 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12225 128 * √(2 / (12227 : ℝ)) *
      (√(12227 : ℝ) + paperT0 12227 + paperTail256 12227) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12227 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12227 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12227 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12225 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12225 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12227 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12227

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12227 (61 / 100) 160 (17 / (100 * 12227)) (26 / (10 * 12227)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12227 (61 / 100) 160 (17 / (100 * 12227)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12227 / 12227 * (61 / 100)) ^ 4 * inverseRadius8 (12227 - 1) /
            envelopeGap 12227 (61 / 100) 160 (17 / (100 * 12227)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12227

namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12227 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12227 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12227 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12227 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12227 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12227) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12227) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12227) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12227) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12227) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12227 * (160 : ℝ) ^ 2 + 26 / (10 * 12227) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12227) : ℝ)) (tA 12227 * 160 ^ 2 + 26 / (10 * 12227)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12227) : ℝ)) d.D d.V d.P (√(tA 12227) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12227) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12227) : ℝ)) (tA 12227 * 160 ^ 2 + 26 / (10 * 12227)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12227) : ℝ)) (√(26 / (10 * 12227) : ℝ)) d.D d.V d.P (√(tA 12227) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12227) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12227

namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12227 160 ∧
    0 ≤ (tableEnvelope C).f1 12227 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12227 160 ∧
    0 ≤ (tableEnvelope C).w1 12227 160 ∧ 0 ≤ (tableEnvelope C).w2 12227 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12227 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12227 160 ∧ 0 ≤ d.f1 12227 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12227 160 ∧ 0 ≤ d.w1 12227 160 ∧ 0 ≤ d.w2 12227 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12227 ≤ 2 * (228 / 100 : ℝ) / 12227 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12227 ≤ 2 * (370 / 100 : ℝ) / 12227 := by
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
    (completeRAData (tableEnvelope C) 12227 160).locationBound 12227 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12227 160).energyBound 12227 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12227 160) (d.f1 12227 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12227 160) (d.w1 12227 160)
      (d.w2 12227 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12227 160) (d.f1 12227 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12227 160) (d.f1 12227 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12227 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12227 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12227 160) (d.f1 12227 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12227 160) (d.w1 12227 160) (d.w2 12227 160)
  have hwexpr0 : 0 ≤ d.w0 12227 160 + d.w1 12227 160 * √(π / 2) +
      2 * d.w2 12227 160 + energyR16 12227 *
      radiusPolynomialRoot16 (d.w0 12227 160) (d.w1 12227 160) (d.w2 12227 160) := by
    positivity
  constructor
  · change (12227 : ℝ) ^ 8 * (mA 12227 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12227 160) (d.f1 12227 160) d.f2 + locationR16 12227 *
        radiusPolynomialRoot16 (d.f0 12227 160) (d.f1 12227 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12227 : ℝ) ^ 8 * (mA 12227 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12227) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12227 : ℝ) ^ 16 *
      (d.w0 12227 160 + d.w1 12227 160 * √(π / 2) + 2 * d.w2 12227 160 +
        energyR16 12227 * radiusPolynomialRoot16 (d.w0 12227 160) (d.w1 12227 160)
          (d.w2 12227 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12227 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12227) *
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

end BstLean.Part262.Row12227

/-! A coarse bound on the actual paper statistics constant at dimension 12228. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12226 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12226 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12226 128 ≤ (12480 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12480 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12228) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12228 : ℕ))
    (by norm_num : (12228 : ℕ) ≤ 16384)
  have ht : paperTail256 12228 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12228 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12228 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12228 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12228 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12228 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12226 128 * √(2 / (12228 : ℝ)) *
      (√(12228 : ℝ) + paperT0 12228 + paperTail256 12228) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12228 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12228 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12228 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12226 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12226 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12228 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12228

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12228 (61 / 100) 160 (17 / (100 * 12228)) (26 / (10 * 12228)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12228 (61 / 100) 160 (17 / (100 * 12228)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12228 / 12228 * (61 / 100)) ^ 4 * inverseRadius8 (12228 - 1) /
            envelopeGap 12228 (61 / 100) 160 (17 / (100 * 12228)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12228

namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12228 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12228 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12228 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12228 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12228 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12228) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12228) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12228) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12228) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12228) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12228 * (160 : ℝ) ^ 2 + 26 / (10 * 12228) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12228) : ℝ)) (tA 12228 * 160 ^ 2 + 26 / (10 * 12228)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12228) : ℝ)) d.D d.V d.P (√(tA 12228) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12228) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12228) : ℝ)) (tA 12228 * 160 ^ 2 + 26 / (10 * 12228)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12228) : ℝ)) (√(26 / (10 * 12228) : ℝ)) d.D d.V d.P (√(tA 12228) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12228) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12228

namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12228 160 ∧
    0 ≤ (tableEnvelope C).f1 12228 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12228 160 ∧
    0 ≤ (tableEnvelope C).w1 12228 160 ∧ 0 ≤ (tableEnvelope C).w2 12228 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12228 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12228 160 ∧ 0 ≤ d.f1 12228 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12228 160 ∧ 0 ≤ d.w1 12228 160 ∧ 0 ≤ d.w2 12228 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12228 ≤ 2 * (228 / 100 : ℝ) / 12228 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12228 ≤ 2 * (370 / 100 : ℝ) / 12228 := by
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
    (completeRAData (tableEnvelope C) 12228 160).locationBound 12228 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12228 160).energyBound 12228 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12228 160) (d.f1 12228 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12228 160) (d.w1 12228 160)
      (d.w2 12228 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12228 160) (d.f1 12228 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12228 160) (d.f1 12228 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12228 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12228 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12228 160) (d.f1 12228 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12228 160) (d.w1 12228 160) (d.w2 12228 160)
  have hwexpr0 : 0 ≤ d.w0 12228 160 + d.w1 12228 160 * √(π / 2) +
      2 * d.w2 12228 160 + energyR16 12228 *
      radiusPolynomialRoot16 (d.w0 12228 160) (d.w1 12228 160) (d.w2 12228 160) := by
    positivity
  constructor
  · change (12228 : ℝ) ^ 8 * (mA 12228 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12228 160) (d.f1 12228 160) d.f2 + locationR16 12228 *
        radiusPolynomialRoot16 (d.f0 12228 160) (d.f1 12228 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12228 : ℝ) ^ 8 * (mA 12228 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12228) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12228 : ℝ) ^ 16 *
      (d.w0 12228 160 + d.w1 12228 160 * √(π / 2) + 2 * d.w2 12228 160 +
        energyR16 12228 * radiusPolynomialRoot16 (d.w0 12228 160) (d.w1 12228 160)
          (d.w2 12228 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12228 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12228) *
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

end BstLean.Part262.Row12228

/-! A coarse bound on the actual paper statistics constant at dimension 12229. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12227 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12227 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12227 128 ≤ (12481 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12481 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12229) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12229 : ℕ))
    (by norm_num : (12229 : ℕ) ≤ 16384)
  have ht : paperTail256 12229 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12229 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12229 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12229 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12229 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12229 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12227 128 * √(2 / (12229 : ℝ)) *
      (√(12229 : ℝ) + paperT0 12229 + paperTail256 12229) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12229 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12229 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12229 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12227 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12227 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12229 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12229

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12229 (61 / 100) 160 (17 / (100 * 12229)) (26 / (10 * 12229)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12229 (61 / 100) 160 (17 / (100 * 12229)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12229 / 12229 * (61 / 100)) ^ 4 * inverseRadius8 (12229 - 1) /
            envelopeGap 12229 (61 / 100) 160 (17 / (100 * 12229)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12229

namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12229 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12229 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12229 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12229 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12229 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12229) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12229) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12229) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12229) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12229) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12229 * (160 : ℝ) ^ 2 + 26 / (10 * 12229) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12229) : ℝ)) (tA 12229 * 160 ^ 2 + 26 / (10 * 12229)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12229) : ℝ)) d.D d.V d.P (√(tA 12229) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12229) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12229) : ℝ)) (tA 12229 * 160 ^ 2 + 26 / (10 * 12229)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12229) : ℝ)) (√(26 / (10 * 12229) : ℝ)) d.D d.V d.P (√(tA 12229) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12229) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12229

namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12229 160 ∧
    0 ≤ (tableEnvelope C).f1 12229 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12229 160 ∧
    0 ≤ (tableEnvelope C).w1 12229 160 ∧ 0 ≤ (tableEnvelope C).w2 12229 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12229 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12229 160 ∧ 0 ≤ d.f1 12229 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12229 160 ∧ 0 ≤ d.w1 12229 160 ∧ 0 ≤ d.w2 12229 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12229 ≤ 2 * (228 / 100 : ℝ) / 12229 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12229 ≤ 2 * (370 / 100 : ℝ) / 12229 := by
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
    (completeRAData (tableEnvelope C) 12229 160).locationBound 12229 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12229 160).energyBound 12229 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12229 160) (d.f1 12229 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12229 160) (d.w1 12229 160)
      (d.w2 12229 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12229 160) (d.f1 12229 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12229 160) (d.f1 12229 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12229 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12229 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12229 160) (d.f1 12229 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12229 160) (d.w1 12229 160) (d.w2 12229 160)
  have hwexpr0 : 0 ≤ d.w0 12229 160 + d.w1 12229 160 * √(π / 2) +
      2 * d.w2 12229 160 + energyR16 12229 *
      radiusPolynomialRoot16 (d.w0 12229 160) (d.w1 12229 160) (d.w2 12229 160) := by
    positivity
  constructor
  · change (12229 : ℝ) ^ 8 * (mA 12229 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12229 160) (d.f1 12229 160) d.f2 + locationR16 12229 *
        radiusPolynomialRoot16 (d.f0 12229 160) (d.f1 12229 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12229 : ℝ) ^ 8 * (mA 12229 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12229) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12229 : ℝ) ^ 16 *
      (d.w0 12229 160 + d.w1 12229 160 * √(π / 2) + 2 * d.w2 12229 160 +
        energyR16 12229 * radiusPolynomialRoot16 (d.w0 12229 160) (d.w1 12229 160)
          (d.w2 12229 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12229 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12229) *
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

end BstLean.Part262.Row12229

/-! A coarse bound on the actual paper statistics constant at dimension 12230. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12228 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12228 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12228 128 ≤ (12482 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12482 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12230) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12230 : ℕ))
    (by norm_num : (12230 : ℕ) ≤ 16384)
  have ht : paperTail256 12230 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12230 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12230 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12230 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12230 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12230 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12228 128 * √(2 / (12230 : ℝ)) *
      (√(12230 : ℝ) + paperT0 12230 + paperTail256 12230) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12230 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12230 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12230 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12228 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12228 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12230 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12230

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12230 (61 / 100) 160 (17 / (100 * 12230)) (26 / (10 * 12230)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12230 (61 / 100) 160 (17 / (100 * 12230)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12230 / 12230 * (61 / 100)) ^ 4 * inverseRadius8 (12230 - 1) /
            envelopeGap 12230 (61 / 100) 160 (17 / (100 * 12230)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12230

namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12230 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12230 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12230 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12230 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12230 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12230) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12230) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12230) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12230) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12230) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12230 * (160 : ℝ) ^ 2 + 26 / (10 * 12230) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12230) : ℝ)) (tA 12230 * 160 ^ 2 + 26 / (10 * 12230)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12230) : ℝ)) d.D d.V d.P (√(tA 12230) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12230) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12230) : ℝ)) (tA 12230 * 160 ^ 2 + 26 / (10 * 12230)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12230) : ℝ)) (√(26 / (10 * 12230) : ℝ)) d.D d.V d.P (√(tA 12230) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12230) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12230

namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12230 160 ∧
    0 ≤ (tableEnvelope C).f1 12230 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12230 160 ∧
    0 ≤ (tableEnvelope C).w1 12230 160 ∧ 0 ≤ (tableEnvelope C).w2 12230 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12230 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12230 160 ∧ 0 ≤ d.f1 12230 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12230 160 ∧ 0 ≤ d.w1 12230 160 ∧ 0 ≤ d.w2 12230 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12230 ≤ 2 * (228 / 100 : ℝ) / 12230 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12230 ≤ 2 * (370 / 100 : ℝ) / 12230 := by
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
    (completeRAData (tableEnvelope C) 12230 160).locationBound 12230 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12230 160).energyBound 12230 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12230 160) (d.f1 12230 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12230 160) (d.w1 12230 160)
      (d.w2 12230 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12230 160) (d.f1 12230 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12230 160) (d.f1 12230 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12230 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12230 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12230 160) (d.f1 12230 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12230 160) (d.w1 12230 160) (d.w2 12230 160)
  have hwexpr0 : 0 ≤ d.w0 12230 160 + d.w1 12230 160 * √(π / 2) +
      2 * d.w2 12230 160 + energyR16 12230 *
      radiusPolynomialRoot16 (d.w0 12230 160) (d.w1 12230 160) (d.w2 12230 160) := by
    positivity
  constructor
  · change (12230 : ℝ) ^ 8 * (mA 12230 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12230 160) (d.f1 12230 160) d.f2 + locationR16 12230 *
        radiusPolynomialRoot16 (d.f0 12230 160) (d.f1 12230 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12230 : ℝ) ^ 8 * (mA 12230 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12230) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12230 : ℝ) ^ 16 *
      (d.w0 12230 160 + d.w1 12230 160 * √(π / 2) + 2 * d.w2 12230 160 +
        energyR16 12230 * radiusPolynomialRoot16 (d.w0 12230 160) (d.w1 12230 160)
          (d.w2 12230 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12230 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12230) *
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

end BstLean.Part262.Row12230

/-! A coarse bound on the actual paper statistics constant at dimension 12231. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12229 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12229 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12229 128 ≤ (12483 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12483 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12231) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12231 : ℕ))
    (by norm_num : (12231 : ℕ) ≤ 16384)
  have ht : paperTail256 12231 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12231 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12231 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12231 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12231 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12231 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12229 128 * √(2 / (12231 : ℝ)) *
      (√(12231 : ℝ) + paperT0 12231 + paperTail256 12231) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12231 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12231 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12231 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12229 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12229 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12231 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12231

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12231 (61 / 100) 160 (17 / (100 * 12231)) (26 / (10 * 12231)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12231 (61 / 100) 160 (17 / (100 * 12231)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12231 / 12231 * (61 / 100)) ^ 4 * inverseRadius8 (12231 - 1) /
            envelopeGap 12231 (61 / 100) 160 (17 / (100 * 12231)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12231

namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12231 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12231 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12231 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12231 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12231 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12231) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12231) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12231) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12231) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12231) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12231 * (160 : ℝ) ^ 2 + 26 / (10 * 12231) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12231) : ℝ)) (tA 12231 * 160 ^ 2 + 26 / (10 * 12231)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12231) : ℝ)) d.D d.V d.P (√(tA 12231) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12231) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12231) : ℝ)) (tA 12231 * 160 ^ 2 + 26 / (10 * 12231)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12231) : ℝ)) (√(26 / (10 * 12231) : ℝ)) d.D d.V d.P (√(tA 12231) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12231) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12231

namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12231 160 ∧
    0 ≤ (tableEnvelope C).f1 12231 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12231 160 ∧
    0 ≤ (tableEnvelope C).w1 12231 160 ∧ 0 ≤ (tableEnvelope C).w2 12231 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12231 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12231 160 ∧ 0 ≤ d.f1 12231 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12231 160 ∧ 0 ≤ d.w1 12231 160 ∧ 0 ≤ d.w2 12231 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12231 ≤ 2 * (228 / 100 : ℝ) / 12231 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12231 ≤ 2 * (370 / 100 : ℝ) / 12231 := by
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
    (completeRAData (tableEnvelope C) 12231 160).locationBound 12231 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12231 160).energyBound 12231 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12231 160) (d.f1 12231 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12231 160) (d.w1 12231 160)
      (d.w2 12231 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12231 160) (d.f1 12231 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12231 160) (d.f1 12231 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12231 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12231 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12231 160) (d.f1 12231 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12231 160) (d.w1 12231 160) (d.w2 12231 160)
  have hwexpr0 : 0 ≤ d.w0 12231 160 + d.w1 12231 160 * √(π / 2) +
      2 * d.w2 12231 160 + energyR16 12231 *
      radiusPolynomialRoot16 (d.w0 12231 160) (d.w1 12231 160) (d.w2 12231 160) := by
    positivity
  constructor
  · change (12231 : ℝ) ^ 8 * (mA 12231 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12231 160) (d.f1 12231 160) d.f2 + locationR16 12231 *
        radiusPolynomialRoot16 (d.f0 12231 160) (d.f1 12231 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12231 : ℝ) ^ 8 * (mA 12231 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12231) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12231 : ℝ) ^ 16 *
      (d.w0 12231 160 + d.w1 12231 160 * √(π / 2) + 2 * d.w2 12231 160 +
        energyR16 12231 * radiusPolynomialRoot16 (d.w0 12231 160) (d.w1 12231 160)
          (d.w2 12231 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12231 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12231) *
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

end BstLean.Part262.Row12231

/-! A coarse bound on the actual paper statistics constant at dimension 12232. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12230 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12230 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12230 128 ≤ (12484 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12484 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12232) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12232 : ℕ))
    (by norm_num : (12232 : ℕ) ≤ 16384)
  have ht : paperTail256 12232 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12232 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12232 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12232 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12232 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12232 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12230 128 * √(2 / (12232 : ℝ)) *
      (√(12232 : ℝ) + paperT0 12232 + paperTail256 12232) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12232 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12232 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12232 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12230 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12230 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12232 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12232

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12232 (61 / 100) 160 (17 / (100 * 12232)) (26 / (10 * 12232)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12232 (61 / 100) 160 (17 / (100 * 12232)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12232 / 12232 * (61 / 100)) ^ 4 * inverseRadius8 (12232 - 1) /
            envelopeGap 12232 (61 / 100) 160 (17 / (100 * 12232)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12232

namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12232 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12232 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12232 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12232 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12232 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12232) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12232) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12232) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12232) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12232) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12232 * (160 : ℝ) ^ 2 + 26 / (10 * 12232) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12232) : ℝ)) (tA 12232 * 160 ^ 2 + 26 / (10 * 12232)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12232) : ℝ)) d.D d.V d.P (√(tA 12232) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12232) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12232) : ℝ)) (tA 12232 * 160 ^ 2 + 26 / (10 * 12232)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12232) : ℝ)) (√(26 / (10 * 12232) : ℝ)) d.D d.V d.P (√(tA 12232) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12232) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12232

namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12232 160 ∧
    0 ≤ (tableEnvelope C).f1 12232 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12232 160 ∧
    0 ≤ (tableEnvelope C).w1 12232 160 ∧ 0 ≤ (tableEnvelope C).w2 12232 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12232 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12232 160 ∧ 0 ≤ d.f1 12232 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12232 160 ∧ 0 ≤ d.w1 12232 160 ∧ 0 ≤ d.w2 12232 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12232 ≤ 2 * (228 / 100 : ℝ) / 12232 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12232 ≤ 2 * (370 / 100 : ℝ) / 12232 := by
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
    (completeRAData (tableEnvelope C) 12232 160).locationBound 12232 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12232 160).energyBound 12232 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12232 160) (d.f1 12232 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12232 160) (d.w1 12232 160)
      (d.w2 12232 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12232 160) (d.f1 12232 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12232 160) (d.f1 12232 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12232 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12232 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12232 160) (d.f1 12232 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12232 160) (d.w1 12232 160) (d.w2 12232 160)
  have hwexpr0 : 0 ≤ d.w0 12232 160 + d.w1 12232 160 * √(π / 2) +
      2 * d.w2 12232 160 + energyR16 12232 *
      radiusPolynomialRoot16 (d.w0 12232 160) (d.w1 12232 160) (d.w2 12232 160) := by
    positivity
  constructor
  · change (12232 : ℝ) ^ 8 * (mA 12232 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12232 160) (d.f1 12232 160) d.f2 + locationR16 12232 *
        radiusPolynomialRoot16 (d.f0 12232 160) (d.f1 12232 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12232 : ℝ) ^ 8 * (mA 12232 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12232) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12232 : ℝ) ^ 16 *
      (d.w0 12232 160 + d.w1 12232 160 * √(π / 2) + 2 * d.w2 12232 160 +
        energyR16 12232 * radiusPolynomialRoot16 (d.w0 12232 160) (d.w1 12232 160)
          (d.w2 12232 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12232 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12232) *
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

end BstLean.Part262.Row12232

/-! A coarse bound on the actual paper statistics constant at dimension 12233. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12231 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12231 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12231 128 ≤ (12485 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12485 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12233) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12233 : ℕ))
    (by norm_num : (12233 : ℕ) ≤ 16384)
  have ht : paperTail256 12233 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12233 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12233 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12233 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12233 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12233 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12231 128 * √(2 / (12233 : ℝ)) *
      (√(12233 : ℝ) + paperT0 12233 + paperTail256 12233) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12233 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12233 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12233 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12231 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12231 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12233 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12233

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12233 (61 / 100) 160 (17 / (100 * 12233)) (26 / (10 * 12233)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12233 (61 / 100) 160 (17 / (100 * 12233)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12233 / 12233 * (61 / 100)) ^ 4 * inverseRadius8 (12233 - 1) /
            envelopeGap 12233 (61 / 100) 160 (17 / (100 * 12233)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12233

namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12233 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12233 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12233 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12233 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12233 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12233) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12233) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12233) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12233) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12233) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12233 * (160 : ℝ) ^ 2 + 26 / (10 * 12233) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12233) : ℝ)) (tA 12233 * 160 ^ 2 + 26 / (10 * 12233)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12233) : ℝ)) d.D d.V d.P (√(tA 12233) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12233) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12233) : ℝ)) (tA 12233 * 160 ^ 2 + 26 / (10 * 12233)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12233) : ℝ)) (√(26 / (10 * 12233) : ℝ)) d.D d.V d.P (√(tA 12233) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12233) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12233

namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12233 160 ∧
    0 ≤ (tableEnvelope C).f1 12233 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12233 160 ∧
    0 ≤ (tableEnvelope C).w1 12233 160 ∧ 0 ≤ (tableEnvelope C).w2 12233 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12233 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12233 160 ∧ 0 ≤ d.f1 12233 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12233 160 ∧ 0 ≤ d.w1 12233 160 ∧ 0 ≤ d.w2 12233 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12233 ≤ 2 * (228 / 100 : ℝ) / 12233 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12233 ≤ 2 * (370 / 100 : ℝ) / 12233 := by
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
    (completeRAData (tableEnvelope C) 12233 160).locationBound 12233 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12233 160).energyBound 12233 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12233 160) (d.f1 12233 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12233 160) (d.w1 12233 160)
      (d.w2 12233 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12233 160) (d.f1 12233 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12233 160) (d.f1 12233 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12233 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12233 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12233 160) (d.f1 12233 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12233 160) (d.w1 12233 160) (d.w2 12233 160)
  have hwexpr0 : 0 ≤ d.w0 12233 160 + d.w1 12233 160 * √(π / 2) +
      2 * d.w2 12233 160 + energyR16 12233 *
      radiusPolynomialRoot16 (d.w0 12233 160) (d.w1 12233 160) (d.w2 12233 160) := by
    positivity
  constructor
  · change (12233 : ℝ) ^ 8 * (mA 12233 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12233 160) (d.f1 12233 160) d.f2 + locationR16 12233 *
        radiusPolynomialRoot16 (d.f0 12233 160) (d.f1 12233 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12233 : ℝ) ^ 8 * (mA 12233 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12233) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12233 : ℝ) ^ 16 *
      (d.w0 12233 160 + d.w1 12233 160 * √(π / 2) + 2 * d.w2 12233 160 +
        energyR16 12233 * radiusPolynomialRoot16 (d.w0 12233 160) (d.w1 12233 160)
          (d.w2 12233 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12233 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12233) *
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

end BstLean.Part262.Row12233

/-! A coarse bound on the actual paper statistics constant at dimension 12234. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12232 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12232 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12232 128 ≤ (12486 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12486 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12234) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12234 : ℕ))
    (by norm_num : (12234 : ℕ) ≤ 16384)
  have ht : paperTail256 12234 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12234 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12234 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12234 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12234 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12234 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12232 128 * √(2 / (12234 : ℝ)) *
      (√(12234 : ℝ) + paperT0 12234 + paperTail256 12234) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12234 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12234 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12234 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12232 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12232 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12234 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12234

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12234 (61 / 100) 160 (17 / (100 * 12234)) (26 / (10 * 12234)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12234 (61 / 100) 160 (17 / (100 * 12234)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12234 / 12234 * (61 / 100)) ^ 4 * inverseRadius8 (12234 - 1) /
            envelopeGap 12234 (61 / 100) 160 (17 / (100 * 12234)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12234

namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12234 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12234 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12234 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12234 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12234 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12234) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12234) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12234) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12234) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12234) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12234 * (160 : ℝ) ^ 2 + 26 / (10 * 12234) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12234) : ℝ)) (tA 12234 * 160 ^ 2 + 26 / (10 * 12234)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12234) : ℝ)) d.D d.V d.P (√(tA 12234) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12234) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12234) : ℝ)) (tA 12234 * 160 ^ 2 + 26 / (10 * 12234)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12234) : ℝ)) (√(26 / (10 * 12234) : ℝ)) d.D d.V d.P (√(tA 12234) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12234) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12234

namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12234 160 ∧
    0 ≤ (tableEnvelope C).f1 12234 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12234 160 ∧
    0 ≤ (tableEnvelope C).w1 12234 160 ∧ 0 ≤ (tableEnvelope C).w2 12234 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12234 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12234 160 ∧ 0 ≤ d.f1 12234 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12234 160 ∧ 0 ≤ d.w1 12234 160 ∧ 0 ≤ d.w2 12234 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12234 ≤ 2 * (228 / 100 : ℝ) / 12234 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12234 ≤ 2 * (370 / 100 : ℝ) / 12234 := by
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
    (completeRAData (tableEnvelope C) 12234 160).locationBound 12234 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12234 160).energyBound 12234 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12234 160) (d.f1 12234 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12234 160) (d.w1 12234 160)
      (d.w2 12234 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12234 160) (d.f1 12234 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12234 160) (d.f1 12234 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12234 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12234 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12234 160) (d.f1 12234 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12234 160) (d.w1 12234 160) (d.w2 12234 160)
  have hwexpr0 : 0 ≤ d.w0 12234 160 + d.w1 12234 160 * √(π / 2) +
      2 * d.w2 12234 160 + energyR16 12234 *
      radiusPolynomialRoot16 (d.w0 12234 160) (d.w1 12234 160) (d.w2 12234 160) := by
    positivity
  constructor
  · change (12234 : ℝ) ^ 8 * (mA 12234 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12234 160) (d.f1 12234 160) d.f2 + locationR16 12234 *
        radiusPolynomialRoot16 (d.f0 12234 160) (d.f1 12234 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12234 : ℝ) ^ 8 * (mA 12234 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12234) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12234 : ℝ) ^ 16 *
      (d.w0 12234 160 + d.w1 12234 160 * √(π / 2) + 2 * d.w2 12234 160 +
        energyR16 12234 * radiusPolynomialRoot16 (d.w0 12234 160) (d.w1 12234 160)
          (d.w2 12234 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12234 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12234) *
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

end BstLean.Part262.Row12234

/-! A coarse bound on the actual paper statistics constant at dimension 12235. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12233 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12233 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12233 128 ≤ (12487 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12487 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12235) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12235 : ℕ))
    (by norm_num : (12235 : ℕ) ≤ 16384)
  have ht : paperTail256 12235 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12235 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12235 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12235 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12235 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12235 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12233 128 * √(2 / (12235 : ℝ)) *
      (√(12235 : ℝ) + paperT0 12235 + paperTail256 12235) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12235 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12235 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12235 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12233 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12233 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12235 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12235

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12235 (61 / 100) 160 (17 / (100 * 12235)) (26 / (10 * 12235)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12235 (61 / 100) 160 (17 / (100 * 12235)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12235 / 12235 * (61 / 100)) ^ 4 * inverseRadius8 (12235 - 1) /
            envelopeGap 12235 (61 / 100) 160 (17 / (100 * 12235)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12235

namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12235 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12235 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12235 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12235 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12235 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12235) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12235) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12235) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12235) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12235) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12235 * (160 : ℝ) ^ 2 + 26 / (10 * 12235) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12235) : ℝ)) (tA 12235 * 160 ^ 2 + 26 / (10 * 12235)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12235) : ℝ)) d.D d.V d.P (√(tA 12235) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12235) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12235) : ℝ)) (tA 12235 * 160 ^ 2 + 26 / (10 * 12235)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12235) : ℝ)) (√(26 / (10 * 12235) : ℝ)) d.D d.V d.P (√(tA 12235) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12235) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12235

namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12235 160 ∧
    0 ≤ (tableEnvelope C).f1 12235 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12235 160 ∧
    0 ≤ (tableEnvelope C).w1 12235 160 ∧ 0 ≤ (tableEnvelope C).w2 12235 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12235 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12235 160 ∧ 0 ≤ d.f1 12235 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12235 160 ∧ 0 ≤ d.w1 12235 160 ∧ 0 ≤ d.w2 12235 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12235 ≤ 2 * (228 / 100 : ℝ) / 12235 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12235 ≤ 2 * (370 / 100 : ℝ) / 12235 := by
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
    (completeRAData (tableEnvelope C) 12235 160).locationBound 12235 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12235 160).energyBound 12235 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12235 160) (d.f1 12235 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12235 160) (d.w1 12235 160)
      (d.w2 12235 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12235 160) (d.f1 12235 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12235 160) (d.f1 12235 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12235 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12235 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12235 160) (d.f1 12235 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12235 160) (d.w1 12235 160) (d.w2 12235 160)
  have hwexpr0 : 0 ≤ d.w0 12235 160 + d.w1 12235 160 * √(π / 2) +
      2 * d.w2 12235 160 + energyR16 12235 *
      radiusPolynomialRoot16 (d.w0 12235 160) (d.w1 12235 160) (d.w2 12235 160) := by
    positivity
  constructor
  · change (12235 : ℝ) ^ 8 * (mA 12235 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12235 160) (d.f1 12235 160) d.f2 + locationR16 12235 *
        radiusPolynomialRoot16 (d.f0 12235 160) (d.f1 12235 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12235 : ℝ) ^ 8 * (mA 12235 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12235) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12235 : ℝ) ^ 16 *
      (d.w0 12235 160 + d.w1 12235 160 * √(π / 2) + 2 * d.w2 12235 160 +
        energyR16 12235 * radiusPolynomialRoot16 (d.w0 12235 160) (d.w1 12235 160)
          (d.w2 12235 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12235 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12235) *
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

end BstLean.Part262.Row12235

/-! A coarse bound on the actual paper statistics constant at dimension 12236. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12234 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12234 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12234 128 ≤ (12488 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12488 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12236) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12236 : ℕ))
    (by norm_num : (12236 : ℕ) ≤ 16384)
  have ht : paperTail256 12236 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12236 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12236 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12236 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12236 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12236 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12234 128 * √(2 / (12236 : ℝ)) *
      (√(12236 : ℝ) + paperT0 12236 + paperTail256 12236) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12236 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12236 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12236 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12234 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12234 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12236 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12236

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12236 (61 / 100) 160 (17 / (100 * 12236)) (26 / (10 * 12236)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12236 (61 / 100) 160 (17 / (100 * 12236)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12236 / 12236 * (61 / 100)) ^ 4 * inverseRadius8 (12236 - 1) /
            envelopeGap 12236 (61 / 100) 160 (17 / (100 * 12236)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12236

namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12236 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12236 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12236 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12236 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12236 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12236) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12236) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12236) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12236) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12236) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12236 * (160 : ℝ) ^ 2 + 26 / (10 * 12236) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12236) : ℝ)) (tA 12236 * 160 ^ 2 + 26 / (10 * 12236)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12236) : ℝ)) d.D d.V d.P (√(tA 12236) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12236) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12236) : ℝ)) (tA 12236 * 160 ^ 2 + 26 / (10 * 12236)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12236) : ℝ)) (√(26 / (10 * 12236) : ℝ)) d.D d.V d.P (√(tA 12236) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12236) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12236

namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12236 160 ∧
    0 ≤ (tableEnvelope C).f1 12236 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12236 160 ∧
    0 ≤ (tableEnvelope C).w1 12236 160 ∧ 0 ≤ (tableEnvelope C).w2 12236 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12236 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12236 160 ∧ 0 ≤ d.f1 12236 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12236 160 ∧ 0 ≤ d.w1 12236 160 ∧ 0 ≤ d.w2 12236 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12236 ≤ 2 * (228 / 100 : ℝ) / 12236 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12236 ≤ 2 * (370 / 100 : ℝ) / 12236 := by
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
    (completeRAData (tableEnvelope C) 12236 160).locationBound 12236 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12236 160).energyBound 12236 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12236 160) (d.f1 12236 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12236 160) (d.w1 12236 160)
      (d.w2 12236 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12236 160) (d.f1 12236 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12236 160) (d.f1 12236 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12236 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12236 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12236 160) (d.f1 12236 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12236 160) (d.w1 12236 160) (d.w2 12236 160)
  have hwexpr0 : 0 ≤ d.w0 12236 160 + d.w1 12236 160 * √(π / 2) +
      2 * d.w2 12236 160 + energyR16 12236 *
      radiusPolynomialRoot16 (d.w0 12236 160) (d.w1 12236 160) (d.w2 12236 160) := by
    positivity
  constructor
  · change (12236 : ℝ) ^ 8 * (mA 12236 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12236 160) (d.f1 12236 160) d.f2 + locationR16 12236 *
        radiusPolynomialRoot16 (d.f0 12236 160) (d.f1 12236 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12236 : ℝ) ^ 8 * (mA 12236 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12236) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12236 : ℝ) ^ 16 *
      (d.w0 12236 160 + d.w1 12236 160 * √(π / 2) + 2 * d.w2 12236 160 +
        energyR16 12236 * radiusPolynomialRoot16 (d.w0 12236 160) (d.w1 12236 160)
          (d.w2 12236 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12236 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12236) *
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

end BstLean.Part262.Row12236

/-! A coarse bound on the actual paper statistics constant at dimension 12237. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12235 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12235 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12235 128 ≤ (12489 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12489 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12237) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12237 : ℕ))
    (by norm_num : (12237 : ℕ) ≤ 16384)
  have ht : paperTail256 12237 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12237 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12237 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12237 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12237 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12237 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12235 128 * √(2 / (12237 : ℝ)) *
      (√(12237 : ℝ) + paperT0 12237 + paperTail256 12237) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12237 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12237 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12237 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12235 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12235 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12237 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12237

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12237 (61 / 100) 160 (17 / (100 * 12237)) (26 / (10 * 12237)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12237 (61 / 100) 160 (17 / (100 * 12237)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12237 / 12237 * (61 / 100)) ^ 4 * inverseRadius8 (12237 - 1) /
            envelopeGap 12237 (61 / 100) 160 (17 / (100 * 12237)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12237

namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12237 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12237 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12237 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12237 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12237 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12237) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12237) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12237) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12237) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12237) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12237 * (160 : ℝ) ^ 2 + 26 / (10 * 12237) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12237) : ℝ)) (tA 12237 * 160 ^ 2 + 26 / (10 * 12237)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12237) : ℝ)) d.D d.V d.P (√(tA 12237) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12237) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12237) : ℝ)) (tA 12237 * 160 ^ 2 + 26 / (10 * 12237)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12237) : ℝ)) (√(26 / (10 * 12237) : ℝ)) d.D d.V d.P (√(tA 12237) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12237) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12237

namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12237 160 ∧
    0 ≤ (tableEnvelope C).f1 12237 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12237 160 ∧
    0 ≤ (tableEnvelope C).w1 12237 160 ∧ 0 ≤ (tableEnvelope C).w2 12237 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12237 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12237 160 ∧ 0 ≤ d.f1 12237 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12237 160 ∧ 0 ≤ d.w1 12237 160 ∧ 0 ≤ d.w2 12237 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12237 ≤ 2 * (228 / 100 : ℝ) / 12237 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12237 ≤ 2 * (370 / 100 : ℝ) / 12237 := by
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
    (completeRAData (tableEnvelope C) 12237 160).locationBound 12237 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12237 160).energyBound 12237 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12237 160) (d.f1 12237 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12237 160) (d.w1 12237 160)
      (d.w2 12237 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12237 160) (d.f1 12237 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12237 160) (d.f1 12237 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12237 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12237 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12237 160) (d.f1 12237 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12237 160) (d.w1 12237 160) (d.w2 12237 160)
  have hwexpr0 : 0 ≤ d.w0 12237 160 + d.w1 12237 160 * √(π / 2) +
      2 * d.w2 12237 160 + energyR16 12237 *
      radiusPolynomialRoot16 (d.w0 12237 160) (d.w1 12237 160) (d.w2 12237 160) := by
    positivity
  constructor
  · change (12237 : ℝ) ^ 8 * (mA 12237 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12237 160) (d.f1 12237 160) d.f2 + locationR16 12237 *
        radiusPolynomialRoot16 (d.f0 12237 160) (d.f1 12237 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12237 : ℝ) ^ 8 * (mA 12237 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12237) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12237 : ℝ) ^ 16 *
      (d.w0 12237 160 + d.w1 12237 160 * √(π / 2) + 2 * d.w2 12237 160 +
        energyR16 12237 * radiusPolynomialRoot16 (d.w0 12237 160) (d.w1 12237 160)
          (d.w2 12237 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12237 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12237) *
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

end BstLean.Part262.Row12237

/-! A coarse bound on the actual paper statistics constant at dimension 12238. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12236 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12236 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12236 128 ≤ (12490 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12490 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12238) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12238 : ℕ))
    (by norm_num : (12238 : ℕ) ≤ 16384)
  have ht : paperTail256 12238 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12238 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12238 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12238 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12238 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12238 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12236 128 * √(2 / (12238 : ℝ)) *
      (√(12238 : ℝ) + paperT0 12238 + paperTail256 12238) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12238 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12238 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12238 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12236 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12236 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12238 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12238

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12238 (61 / 100) 160 (17 / (100 * 12238)) (26 / (10 * 12238)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12238 (61 / 100) 160 (17 / (100 * 12238)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12238 / 12238 * (61 / 100)) ^ 4 * inverseRadius8 (12238 - 1) /
            envelopeGap 12238 (61 / 100) 160 (17 / (100 * 12238)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12238

namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12238 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12238 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12238 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12238 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12238 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12238) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12238) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12238) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12238) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12238) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12238 * (160 : ℝ) ^ 2 + 26 / (10 * 12238) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12238) : ℝ)) (tA 12238 * 160 ^ 2 + 26 / (10 * 12238)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12238) : ℝ)) d.D d.V d.P (√(tA 12238) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12238) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12238) : ℝ)) (tA 12238 * 160 ^ 2 + 26 / (10 * 12238)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12238) : ℝ)) (√(26 / (10 * 12238) : ℝ)) d.D d.V d.P (√(tA 12238) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12238) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12238

namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12238 160 ∧
    0 ≤ (tableEnvelope C).f1 12238 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12238 160 ∧
    0 ≤ (tableEnvelope C).w1 12238 160 ∧ 0 ≤ (tableEnvelope C).w2 12238 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12238 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12238 160 ∧ 0 ≤ d.f1 12238 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12238 160 ∧ 0 ≤ d.w1 12238 160 ∧ 0 ≤ d.w2 12238 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12238 ≤ 2 * (228 / 100 : ℝ) / 12238 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12238 ≤ 2 * (370 / 100 : ℝ) / 12238 := by
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
    (completeRAData (tableEnvelope C) 12238 160).locationBound 12238 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12238 160).energyBound 12238 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12238 160) (d.f1 12238 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12238 160) (d.w1 12238 160)
      (d.w2 12238 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12238 160) (d.f1 12238 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12238 160) (d.f1 12238 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12238 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12238 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12238 160) (d.f1 12238 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12238 160) (d.w1 12238 160) (d.w2 12238 160)
  have hwexpr0 : 0 ≤ d.w0 12238 160 + d.w1 12238 160 * √(π / 2) +
      2 * d.w2 12238 160 + energyR16 12238 *
      radiusPolynomialRoot16 (d.w0 12238 160) (d.w1 12238 160) (d.w2 12238 160) := by
    positivity
  constructor
  · change (12238 : ℝ) ^ 8 * (mA 12238 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12238 160) (d.f1 12238 160) d.f2 + locationR16 12238 *
        radiusPolynomialRoot16 (d.f0 12238 160) (d.f1 12238 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12238 : ℝ) ^ 8 * (mA 12238 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12238) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12238 : ℝ) ^ 16 *
      (d.w0 12238 160 + d.w1 12238 160 * √(π / 2) + 2 * d.w2 12238 160 +
        energyR16 12238 * radiusPolynomialRoot16 (d.w0 12238 160) (d.w1 12238 160)
          (d.w2 12238 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12238 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12238) *
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

end BstLean.Part262.Row12238

/-! A coarse bound on the actual paper statistics constant at dimension 12239. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12237 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12237 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12237 128 ≤ (12491 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12491 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12239) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12239 : ℕ))
    (by norm_num : (12239 : ℕ) ≤ 16384)
  have ht : paperTail256 12239 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12239 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12239 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12239 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12239 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12239 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12237 128 * √(2 / (12239 : ℝ)) *
      (√(12239 : ℝ) + paperT0 12239 + paperTail256 12239) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12239 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12239 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12239 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12237 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12237 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12239 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12239

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12239 (61 / 100) 160 (17 / (100 * 12239)) (26 / (10 * 12239)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12239 (61 / 100) 160 (17 / (100 * 12239)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12239 / 12239 * (61 / 100)) ^ 4 * inverseRadius8 (12239 - 1) /
            envelopeGap 12239 (61 / 100) 160 (17 / (100 * 12239)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12239

namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12239 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12239 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12239 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12239 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12239 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12239) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12239) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12239) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12239) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12239) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12239 * (160 : ℝ) ^ 2 + 26 / (10 * 12239) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12239) : ℝ)) (tA 12239 * 160 ^ 2 + 26 / (10 * 12239)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12239) : ℝ)) d.D d.V d.P (√(tA 12239) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12239) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12239) : ℝ)) (tA 12239 * 160 ^ 2 + 26 / (10 * 12239)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12239) : ℝ)) (√(26 / (10 * 12239) : ℝ)) d.D d.V d.P (√(tA 12239) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12239) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12239

namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12239 160 ∧
    0 ≤ (tableEnvelope C).f1 12239 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12239 160 ∧
    0 ≤ (tableEnvelope C).w1 12239 160 ∧ 0 ≤ (tableEnvelope C).w2 12239 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12239 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12239 160 ∧ 0 ≤ d.f1 12239 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12239 160 ∧ 0 ≤ d.w1 12239 160 ∧ 0 ≤ d.w2 12239 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12239 ≤ 2 * (228 / 100 : ℝ) / 12239 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12239 ≤ 2 * (370 / 100 : ℝ) / 12239 := by
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
    (completeRAData (tableEnvelope C) 12239 160).locationBound 12239 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12239 160).energyBound 12239 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12239 160) (d.f1 12239 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12239 160) (d.w1 12239 160)
      (d.w2 12239 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12239 160) (d.f1 12239 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12239 160) (d.f1 12239 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12239 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12239 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12239 160) (d.f1 12239 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12239 160) (d.w1 12239 160) (d.w2 12239 160)
  have hwexpr0 : 0 ≤ d.w0 12239 160 + d.w1 12239 160 * √(π / 2) +
      2 * d.w2 12239 160 + energyR16 12239 *
      radiusPolynomialRoot16 (d.w0 12239 160) (d.w1 12239 160) (d.w2 12239 160) := by
    positivity
  constructor
  · change (12239 : ℝ) ^ 8 * (mA 12239 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12239 160) (d.f1 12239 160) d.f2 + locationR16 12239 *
        radiusPolynomialRoot16 (d.f0 12239 160) (d.f1 12239 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12239 : ℝ) ^ 8 * (mA 12239 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12239) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12239 : ℝ) ^ 16 *
      (d.w0 12239 160 + d.w1 12239 160 * √(π / 2) + 2 * d.w2 12239 160 +
        energyR16 12239 * radiusPolynomialRoot16 (d.w0 12239 160) (d.w1 12239 160)
          (d.w2 12239 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12239 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12239) *
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

end BstLean.Part262.Row12239

/-! A coarse bound on the actual paper statistics constant at dimension 12240. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12238 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12238 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12238 128 ≤ (12492 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12492 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12240) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12240 : ℕ))
    (by norm_num : (12240 : ℕ) ≤ 16384)
  have ht : paperTail256 12240 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12240 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12240 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12240 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12240 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12240 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12238 128 * √(2 / (12240 : ℝ)) *
      (√(12240 : ℝ) + paperT0 12240 + paperTail256 12240) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12240 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12240 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12240 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12238 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12238 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12240 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12240

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12240 (61 / 100) 160 (17 / (100 * 12240)) (26 / (10 * 12240)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12240 (61 / 100) 160 (17 / (100 * 12240)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12240 / 12240 * (61 / 100)) ^ 4 * inverseRadius8 (12240 - 1) /
            envelopeGap 12240 (61 / 100) 160 (17 / (100 * 12240)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12240

namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12240 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12240 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12240 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12240 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12240 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12240) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12240) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12240) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12240) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12240) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12240 * (160 : ℝ) ^ 2 + 26 / (10 * 12240) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12240) : ℝ)) (tA 12240 * 160 ^ 2 + 26 / (10 * 12240)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12240) : ℝ)) d.D d.V d.P (√(tA 12240) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12240) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12240) : ℝ)) (tA 12240 * 160 ^ 2 + 26 / (10 * 12240)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12240) : ℝ)) (√(26 / (10 * 12240) : ℝ)) d.D d.V d.P (√(tA 12240) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12240) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12240

namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12240 160 ∧
    0 ≤ (tableEnvelope C).f1 12240 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12240 160 ∧
    0 ≤ (tableEnvelope C).w1 12240 160 ∧ 0 ≤ (tableEnvelope C).w2 12240 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12240 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12240 160 ∧ 0 ≤ d.f1 12240 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12240 160 ∧ 0 ≤ d.w1 12240 160 ∧ 0 ≤ d.w2 12240 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12240 ≤ 2 * (228 / 100 : ℝ) / 12240 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12240 ≤ 2 * (370 / 100 : ℝ) / 12240 := by
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
    (completeRAData (tableEnvelope C) 12240 160).locationBound 12240 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12240 160).energyBound 12240 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12240 160) (d.f1 12240 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12240 160) (d.w1 12240 160)
      (d.w2 12240 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12240 160) (d.f1 12240 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12240 160) (d.f1 12240 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12240 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12240 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12240 160) (d.f1 12240 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12240 160) (d.w1 12240 160) (d.w2 12240 160)
  have hwexpr0 : 0 ≤ d.w0 12240 160 + d.w1 12240 160 * √(π / 2) +
      2 * d.w2 12240 160 + energyR16 12240 *
      radiusPolynomialRoot16 (d.w0 12240 160) (d.w1 12240 160) (d.w2 12240 160) := by
    positivity
  constructor
  · change (12240 : ℝ) ^ 8 * (mA 12240 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12240 160) (d.f1 12240 160) d.f2 + locationR16 12240 *
        radiusPolynomialRoot16 (d.f0 12240 160) (d.f1 12240 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12240 : ℝ) ^ 8 * (mA 12240 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12240) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12240 : ℝ) ^ 16 *
      (d.w0 12240 160 + d.w1 12240 160 * √(π / 2) + 2 * d.w2 12240 160 +
        energyR16 12240 * radiusPolynomialRoot16 (d.w0 12240 160) (d.w1 12240 160)
          (d.w2 12240 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12240 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12240) *
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

end BstLean.Part262.Row12240

/-! A coarse bound on the actual paper statistics constant at dimension 12241. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12239 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12239 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12239 128 ≤ (12493 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12493 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12241) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12241 : ℕ))
    (by norm_num : (12241 : ℕ) ≤ 16384)
  have ht : paperTail256 12241 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12241 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12241 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12241 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12241 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12241 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12239 128 * √(2 / (12241 : ℝ)) *
      (√(12241 : ℝ) + paperT0 12241 + paperTail256 12241) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12241 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12241 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12241 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12239 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12239 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12241 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12241

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12241 (61 / 100) 160 (17 / (100 * 12241)) (26 / (10 * 12241)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12241 (61 / 100) 160 (17 / (100 * 12241)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12241 / 12241 * (61 / 100)) ^ 4 * inverseRadius8 (12241 - 1) /
            envelopeGap 12241 (61 / 100) 160 (17 / (100 * 12241)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12241

namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12241 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12241 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12241 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12241 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12241 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12241) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12241) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12241) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12241) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12241) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12241 * (160 : ℝ) ^ 2 + 26 / (10 * 12241) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12241) : ℝ)) (tA 12241 * 160 ^ 2 + 26 / (10 * 12241)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12241) : ℝ)) d.D d.V d.P (√(tA 12241) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12241) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12241) : ℝ)) (tA 12241 * 160 ^ 2 + 26 / (10 * 12241)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12241) : ℝ)) (√(26 / (10 * 12241) : ℝ)) d.D d.V d.P (√(tA 12241) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12241) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12241

namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12241 160 ∧
    0 ≤ (tableEnvelope C).f1 12241 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12241 160 ∧
    0 ≤ (tableEnvelope C).w1 12241 160 ∧ 0 ≤ (tableEnvelope C).w2 12241 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12241 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12241 160 ∧ 0 ≤ d.f1 12241 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12241 160 ∧ 0 ≤ d.w1 12241 160 ∧ 0 ≤ d.w2 12241 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12241 ≤ 2 * (228 / 100 : ℝ) / 12241 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12241 ≤ 2 * (370 / 100 : ℝ) / 12241 := by
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
    (completeRAData (tableEnvelope C) 12241 160).locationBound 12241 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12241 160).energyBound 12241 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12241 160) (d.f1 12241 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12241 160) (d.w1 12241 160)
      (d.w2 12241 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12241 160) (d.f1 12241 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12241 160) (d.f1 12241 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12241 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12241 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12241 160) (d.f1 12241 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12241 160) (d.w1 12241 160) (d.w2 12241 160)
  have hwexpr0 : 0 ≤ d.w0 12241 160 + d.w1 12241 160 * √(π / 2) +
      2 * d.w2 12241 160 + energyR16 12241 *
      radiusPolynomialRoot16 (d.w0 12241 160) (d.w1 12241 160) (d.w2 12241 160) := by
    positivity
  constructor
  · change (12241 : ℝ) ^ 8 * (mA 12241 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12241 160) (d.f1 12241 160) d.f2 + locationR16 12241 *
        radiusPolynomialRoot16 (d.f0 12241 160) (d.f1 12241 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12241 : ℝ) ^ 8 * (mA 12241 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12241) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12241 : ℝ) ^ 16 *
      (d.w0 12241 160 + d.w1 12241 160 * √(π / 2) + 2 * d.w2 12241 160 +
        energyR16 12241 * radiusPolynomialRoot16 (d.w0 12241 160) (d.w1 12241 160)
          (d.w2 12241 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12241 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12241) *
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

end BstLean.Part262.Row12241

/-! A coarse bound on the actual paper statistics constant at dimension 12242. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12240 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12240 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12240 128 ≤ (12494 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12494 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12242) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12242 : ℕ))
    (by norm_num : (12242 : ℕ) ≤ 16384)
  have ht : paperTail256 12242 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12242 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12242 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12242 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12242 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12242 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12240 128 * √(2 / (12242 : ℝ)) *
      (√(12242 : ℝ) + paperT0 12242 + paperTail256 12242) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12242 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12242 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12242 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12240 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12240 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12242 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12242

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12242 (61 / 100) 160 (17 / (100 * 12242)) (26 / (10 * 12242)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12242 (61 / 100) 160 (17 / (100 * 12242)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12242 / 12242 * (61 / 100)) ^ 4 * inverseRadius8 (12242 - 1) /
            envelopeGap 12242 (61 / 100) 160 (17 / (100 * 12242)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12242

namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12242 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12242 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12242 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12242 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12242 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12242) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12242) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12242) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12242) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12242) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12242 * (160 : ℝ) ^ 2 + 26 / (10 * 12242) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12242) : ℝ)) (tA 12242 * 160 ^ 2 + 26 / (10 * 12242)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12242) : ℝ)) d.D d.V d.P (√(tA 12242) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12242) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12242) : ℝ)) (tA 12242 * 160 ^ 2 + 26 / (10 * 12242)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12242) : ℝ)) (√(26 / (10 * 12242) : ℝ)) d.D d.V d.P (√(tA 12242) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12242) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12242

namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12242 160 ∧
    0 ≤ (tableEnvelope C).f1 12242 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12242 160 ∧
    0 ≤ (tableEnvelope C).w1 12242 160 ∧ 0 ≤ (tableEnvelope C).w2 12242 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12242 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12242 160 ∧ 0 ≤ d.f1 12242 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12242 160 ∧ 0 ≤ d.w1 12242 160 ∧ 0 ≤ d.w2 12242 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12242 ≤ 2 * (228 / 100 : ℝ) / 12242 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12242 ≤ 2 * (370 / 100 : ℝ) / 12242 := by
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
    (completeRAData (tableEnvelope C) 12242 160).locationBound 12242 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12242 160).energyBound 12242 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12242 160) (d.f1 12242 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12242 160) (d.w1 12242 160)
      (d.w2 12242 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12242 160) (d.f1 12242 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12242 160) (d.f1 12242 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12242 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12242 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12242 160) (d.f1 12242 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12242 160) (d.w1 12242 160) (d.w2 12242 160)
  have hwexpr0 : 0 ≤ d.w0 12242 160 + d.w1 12242 160 * √(π / 2) +
      2 * d.w2 12242 160 + energyR16 12242 *
      radiusPolynomialRoot16 (d.w0 12242 160) (d.w1 12242 160) (d.w2 12242 160) := by
    positivity
  constructor
  · change (12242 : ℝ) ^ 8 * (mA 12242 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12242 160) (d.f1 12242 160) d.f2 + locationR16 12242 *
        radiusPolynomialRoot16 (d.f0 12242 160) (d.f1 12242 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12242 : ℝ) ^ 8 * (mA 12242 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12242) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12242 : ℝ) ^ 16 *
      (d.w0 12242 160 + d.w1 12242 160 * √(π / 2) + 2 * d.w2 12242 160 +
        energyR16 12242 * radiusPolynomialRoot16 (d.w0 12242 160) (d.w1 12242 160)
          (d.w2 12242 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12242 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12242) *
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

end BstLean.Part262.Row12242

/-! A coarse bound on the actual paper statistics constant at dimension 12243. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12241 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12241 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12241 128 ≤ (12495 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12495 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12243) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12243 : ℕ))
    (by norm_num : (12243 : ℕ) ≤ 16384)
  have ht : paperTail256 12243 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12243 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12243 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12243 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12243 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12243 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12241 128 * √(2 / (12243 : ℝ)) *
      (√(12243 : ℝ) + paperT0 12243 + paperTail256 12243) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12243 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12243 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12243 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12241 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12241 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12243 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12243

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12243 (61 / 100) 160 (17 / (100 * 12243)) (26 / (10 * 12243)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12243 (61 / 100) 160 (17 / (100 * 12243)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12243 / 12243 * (61 / 100)) ^ 4 * inverseRadius8 (12243 - 1) /
            envelopeGap 12243 (61 / 100) 160 (17 / (100 * 12243)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12243

namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12243 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12243 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12243 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12243 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12243 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12243) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12243) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12243) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12243) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12243) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12243 * (160 : ℝ) ^ 2 + 26 / (10 * 12243) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12243) : ℝ)) (tA 12243 * 160 ^ 2 + 26 / (10 * 12243)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12243) : ℝ)) d.D d.V d.P (√(tA 12243) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12243) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12243) : ℝ)) (tA 12243 * 160 ^ 2 + 26 / (10 * 12243)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12243) : ℝ)) (√(26 / (10 * 12243) : ℝ)) d.D d.V d.P (√(tA 12243) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12243) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12243

namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12243 160 ∧
    0 ≤ (tableEnvelope C).f1 12243 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12243 160 ∧
    0 ≤ (tableEnvelope C).w1 12243 160 ∧ 0 ≤ (tableEnvelope C).w2 12243 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12243 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12243 160 ∧ 0 ≤ d.f1 12243 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12243 160 ∧ 0 ≤ d.w1 12243 160 ∧ 0 ≤ d.w2 12243 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12243 ≤ 2 * (228 / 100 : ℝ) / 12243 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12243 ≤ 2 * (370 / 100 : ℝ) / 12243 := by
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
    (completeRAData (tableEnvelope C) 12243 160).locationBound 12243 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12243 160).energyBound 12243 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12243 160) (d.f1 12243 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12243 160) (d.w1 12243 160)
      (d.w2 12243 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12243 160) (d.f1 12243 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12243 160) (d.f1 12243 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12243 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12243 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12243 160) (d.f1 12243 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12243 160) (d.w1 12243 160) (d.w2 12243 160)
  have hwexpr0 : 0 ≤ d.w0 12243 160 + d.w1 12243 160 * √(π / 2) +
      2 * d.w2 12243 160 + energyR16 12243 *
      radiusPolynomialRoot16 (d.w0 12243 160) (d.w1 12243 160) (d.w2 12243 160) := by
    positivity
  constructor
  · change (12243 : ℝ) ^ 8 * (mA 12243 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12243 160) (d.f1 12243 160) d.f2 + locationR16 12243 *
        radiusPolynomialRoot16 (d.f0 12243 160) (d.f1 12243 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12243 : ℝ) ^ 8 * (mA 12243 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12243) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12243 : ℝ) ^ 16 *
      (d.w0 12243 160 + d.w1 12243 160 * √(π / 2) + 2 * d.w2 12243 160 +
        energyR16 12243 * radiusPolynomialRoot16 (d.w0 12243 160) (d.w1 12243 160)
          (d.w2 12243 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12243 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12243) *
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

end BstLean.Part262.Row12243

/-! A coarse bound on the actual paper statistics constant at dimension 12244. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12242 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12242 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12242 128 ≤ (12496 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12496 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12244) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12244 : ℕ))
    (by norm_num : (12244 : ℕ) ≤ 16384)
  have ht : paperTail256 12244 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12244 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12244 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12244 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12244 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12244 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12242 128 * √(2 / (12244 : ℝ)) *
      (√(12244 : ℝ) + paperT0 12244 + paperTail256 12244) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12244 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12244 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12244 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12242 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12242 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12244 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12244

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12244 (61 / 100) 160 (17 / (100 * 12244)) (26 / (10 * 12244)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12244 (61 / 100) 160 (17 / (100 * 12244)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12244 / 12244 * (61 / 100)) ^ 4 * inverseRadius8 (12244 - 1) /
            envelopeGap 12244 (61 / 100) 160 (17 / (100 * 12244)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12244

namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12244 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12244 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12244 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12244 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12244 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12244) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12244) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12244) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12244) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12244) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12244 * (160 : ℝ) ^ 2 + 26 / (10 * 12244) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12244) : ℝ)) (tA 12244 * 160 ^ 2 + 26 / (10 * 12244)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12244) : ℝ)) d.D d.V d.P (√(tA 12244) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12244) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12244) : ℝ)) (tA 12244 * 160 ^ 2 + 26 / (10 * 12244)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12244) : ℝ)) (√(26 / (10 * 12244) : ℝ)) d.D d.V d.P (√(tA 12244) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12244) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12244

namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12244 160 ∧
    0 ≤ (tableEnvelope C).f1 12244 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12244 160 ∧
    0 ≤ (tableEnvelope C).w1 12244 160 ∧ 0 ≤ (tableEnvelope C).w2 12244 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12244 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12244 160 ∧ 0 ≤ d.f1 12244 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12244 160 ∧ 0 ≤ d.w1 12244 160 ∧ 0 ≤ d.w2 12244 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12244 ≤ 2 * (228 / 100 : ℝ) / 12244 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12244 ≤ 2 * (370 / 100 : ℝ) / 12244 := by
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
    (completeRAData (tableEnvelope C) 12244 160).locationBound 12244 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12244 160).energyBound 12244 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12244 160) (d.f1 12244 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12244 160) (d.w1 12244 160)
      (d.w2 12244 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12244 160) (d.f1 12244 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12244 160) (d.f1 12244 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12244 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12244 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12244 160) (d.f1 12244 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12244 160) (d.w1 12244 160) (d.w2 12244 160)
  have hwexpr0 : 0 ≤ d.w0 12244 160 + d.w1 12244 160 * √(π / 2) +
      2 * d.w2 12244 160 + energyR16 12244 *
      radiusPolynomialRoot16 (d.w0 12244 160) (d.w1 12244 160) (d.w2 12244 160) := by
    positivity
  constructor
  · change (12244 : ℝ) ^ 8 * (mA 12244 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12244 160) (d.f1 12244 160) d.f2 + locationR16 12244 *
        radiusPolynomialRoot16 (d.f0 12244 160) (d.f1 12244 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12244 : ℝ) ^ 8 * (mA 12244 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12244) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12244 : ℝ) ^ 16 *
      (d.w0 12244 160 + d.w1 12244 160 * √(π / 2) + 2 * d.w2 12244 160 +
        energyR16 12244 * radiusPolynomialRoot16 (d.w0 12244 160) (d.w1 12244 160)
          (d.w2 12244 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12244 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12244) *
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

end BstLean.Part262.Row12244

/-! A coarse bound on the actual paper statistics constant at dimension 12245. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12243 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12243 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12243 128 ≤ (12497 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12497 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12245) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12245 : ℕ))
    (by norm_num : (12245 : ℕ) ≤ 16384)
  have ht : paperTail256 12245 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12245 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12245 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12245 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12245 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12245 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12243 128 * √(2 / (12245 : ℝ)) *
      (√(12245 : ℝ) + paperT0 12245 + paperTail256 12245) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12245 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12245 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12245 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12243 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12243 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12245 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12245

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12245 (61 / 100) 160 (17 / (100 * 12245)) (26 / (10 * 12245)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12245 (61 / 100) 160 (17 / (100 * 12245)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12245 / 12245 * (61 / 100)) ^ 4 * inverseRadius8 (12245 - 1) /
            envelopeGap 12245 (61 / 100) 160 (17 / (100 * 12245)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12245

namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12245 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12245 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12245 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12245 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12245 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12245) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12245) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12245) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12245) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12245) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12245 * (160 : ℝ) ^ 2 + 26 / (10 * 12245) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12245) : ℝ)) (tA 12245 * 160 ^ 2 + 26 / (10 * 12245)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12245) : ℝ)) d.D d.V d.P (√(tA 12245) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12245) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12245) : ℝ)) (tA 12245 * 160 ^ 2 + 26 / (10 * 12245)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12245) : ℝ)) (√(26 / (10 * 12245) : ℝ)) d.D d.V d.P (√(tA 12245) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12245) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12245

namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12245 160 ∧
    0 ≤ (tableEnvelope C).f1 12245 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12245 160 ∧
    0 ≤ (tableEnvelope C).w1 12245 160 ∧ 0 ≤ (tableEnvelope C).w2 12245 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12245 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12245 160 ∧ 0 ≤ d.f1 12245 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12245 160 ∧ 0 ≤ d.w1 12245 160 ∧ 0 ≤ d.w2 12245 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12245 ≤ 2 * (228 / 100 : ℝ) / 12245 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12245 ≤ 2 * (370 / 100 : ℝ) / 12245 := by
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
    (completeRAData (tableEnvelope C) 12245 160).locationBound 12245 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12245 160).energyBound 12245 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12245 160) (d.f1 12245 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12245 160) (d.w1 12245 160)
      (d.w2 12245 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12245 160) (d.f1 12245 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12245 160) (d.f1 12245 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12245 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12245 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12245 160) (d.f1 12245 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12245 160) (d.w1 12245 160) (d.w2 12245 160)
  have hwexpr0 : 0 ≤ d.w0 12245 160 + d.w1 12245 160 * √(π / 2) +
      2 * d.w2 12245 160 + energyR16 12245 *
      radiusPolynomialRoot16 (d.w0 12245 160) (d.w1 12245 160) (d.w2 12245 160) := by
    positivity
  constructor
  · change (12245 : ℝ) ^ 8 * (mA 12245 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12245 160) (d.f1 12245 160) d.f2 + locationR16 12245 *
        radiusPolynomialRoot16 (d.f0 12245 160) (d.f1 12245 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12245 : ℝ) ^ 8 * (mA 12245 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12245) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12245 : ℝ) ^ 16 *
      (d.w0 12245 160 + d.w1 12245 160 * √(π / 2) + 2 * d.w2 12245 160 +
        energyR16 12245 * radiusPolynomialRoot16 (d.w0 12245 160) (d.w1 12245 160)
          (d.w2 12245 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12245 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12245) *
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

end BstLean.Part262.Row12245

/-! A coarse bound on the actual paper statistics constant at dimension 12246. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12244 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12244 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12244 128 ≤ (12498 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12498 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12246) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12246 : ℕ))
    (by norm_num : (12246 : ℕ) ≤ 16384)
  have ht : paperTail256 12246 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12246 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12246 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12246 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12246 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12246 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12244 128 * √(2 / (12246 : ℝ)) *
      (√(12246 : ℝ) + paperT0 12246 + paperTail256 12246) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12246 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12246 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12246 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12244 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12244 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12246 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12246

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12246 (61 / 100) 160 (17 / (100 * 12246)) (26 / (10 * 12246)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12246 (61 / 100) 160 (17 / (100 * 12246)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12246 / 12246 * (61 / 100)) ^ 4 * inverseRadius8 (12246 - 1) /
            envelopeGap 12246 (61 / 100) 160 (17 / (100 * 12246)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12246

namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12246 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12246 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12246 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12246 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12246 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12246) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12246) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12246) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12246) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12246) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12246 * (160 : ℝ) ^ 2 + 26 / (10 * 12246) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12246) : ℝ)) (tA 12246 * 160 ^ 2 + 26 / (10 * 12246)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12246) : ℝ)) d.D d.V d.P (√(tA 12246) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12246) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12246) : ℝ)) (tA 12246 * 160 ^ 2 + 26 / (10 * 12246)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12246) : ℝ)) (√(26 / (10 * 12246) : ℝ)) d.D d.V d.P (√(tA 12246) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12246) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12246

namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12246 160 ∧
    0 ≤ (tableEnvelope C).f1 12246 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12246 160 ∧
    0 ≤ (tableEnvelope C).w1 12246 160 ∧ 0 ≤ (tableEnvelope C).w2 12246 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12246 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12246 160 ∧ 0 ≤ d.f1 12246 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12246 160 ∧ 0 ≤ d.w1 12246 160 ∧ 0 ≤ d.w2 12246 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12246 ≤ 2 * (228 / 100 : ℝ) / 12246 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12246 ≤ 2 * (370 / 100 : ℝ) / 12246 := by
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
    (completeRAData (tableEnvelope C) 12246 160).locationBound 12246 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12246 160).energyBound 12246 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12246 160) (d.f1 12246 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12246 160) (d.w1 12246 160)
      (d.w2 12246 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12246 160) (d.f1 12246 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12246 160) (d.f1 12246 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12246 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12246 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12246 160) (d.f1 12246 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12246 160) (d.w1 12246 160) (d.w2 12246 160)
  have hwexpr0 : 0 ≤ d.w0 12246 160 + d.w1 12246 160 * √(π / 2) +
      2 * d.w2 12246 160 + energyR16 12246 *
      radiusPolynomialRoot16 (d.w0 12246 160) (d.w1 12246 160) (d.w2 12246 160) := by
    positivity
  constructor
  · change (12246 : ℝ) ^ 8 * (mA 12246 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12246 160) (d.f1 12246 160) d.f2 + locationR16 12246 *
        radiusPolynomialRoot16 (d.f0 12246 160) (d.f1 12246 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12246 : ℝ) ^ 8 * (mA 12246 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12246) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12246 : ℝ) ^ 16 *
      (d.w0 12246 160 + d.w1 12246 160 * √(π / 2) + 2 * d.w2 12246 160 +
        energyR16 12246 * radiusPolynomialRoot16 (d.w0 12246 160) (d.w1 12246 160)
          (d.w2 12246 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12246 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12246) *
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

end BstLean.Part262.Row12246

/-! A coarse bound on the actual paper statistics constant at dimension 12247. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12245 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12245 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12245 128 ≤ (12499 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12499 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12247) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12247 : ℕ))
    (by norm_num : (12247 : ℕ) ≤ 16384)
  have ht : paperTail256 12247 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12247 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12247 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12247 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12247 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12247 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12245 128 * √(2 / (12247 : ℝ)) *
      (√(12247 : ℝ) + paperT0 12247 + paperTail256 12247) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12247 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12247 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12247 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12245 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12245 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12247 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12247

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12247 (61 / 100) 160 (17 / (100 * 12247)) (26 / (10 * 12247)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12247 (61 / 100) 160 (17 / (100 * 12247)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12247 / 12247 * (61 / 100)) ^ 4 * inverseRadius8 (12247 - 1) /
            envelopeGap 12247 (61 / 100) 160 (17 / (100 * 12247)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12247

namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12247 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12247 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12247 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12247 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12247 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12247) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12247) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12247) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12247) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12247) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12247 * (160 : ℝ) ^ 2 + 26 / (10 * 12247) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12247) : ℝ)) (tA 12247 * 160 ^ 2 + 26 / (10 * 12247)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12247) : ℝ)) d.D d.V d.P (√(tA 12247) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12247) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12247) : ℝ)) (tA 12247 * 160 ^ 2 + 26 / (10 * 12247)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12247) : ℝ)) (√(26 / (10 * 12247) : ℝ)) d.D d.V d.P (√(tA 12247) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12247) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12247

namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12247 160 ∧
    0 ≤ (tableEnvelope C).f1 12247 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12247 160 ∧
    0 ≤ (tableEnvelope C).w1 12247 160 ∧ 0 ≤ (tableEnvelope C).w2 12247 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12247 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12247 160 ∧ 0 ≤ d.f1 12247 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12247 160 ∧ 0 ≤ d.w1 12247 160 ∧ 0 ≤ d.w2 12247 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12247 ≤ 2 * (228 / 100 : ℝ) / 12247 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12247 ≤ 2 * (370 / 100 : ℝ) / 12247 := by
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
    (completeRAData (tableEnvelope C) 12247 160).locationBound 12247 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12247 160).energyBound 12247 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12247 160) (d.f1 12247 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12247 160) (d.w1 12247 160)
      (d.w2 12247 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12247 160) (d.f1 12247 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12247 160) (d.f1 12247 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12247 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12247 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12247 160) (d.f1 12247 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12247 160) (d.w1 12247 160) (d.w2 12247 160)
  have hwexpr0 : 0 ≤ d.w0 12247 160 + d.w1 12247 160 * √(π / 2) +
      2 * d.w2 12247 160 + energyR16 12247 *
      radiusPolynomialRoot16 (d.w0 12247 160) (d.w1 12247 160) (d.w2 12247 160) := by
    positivity
  constructor
  · change (12247 : ℝ) ^ 8 * (mA 12247 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12247 160) (d.f1 12247 160) d.f2 + locationR16 12247 *
        radiusPolynomialRoot16 (d.f0 12247 160) (d.f1 12247 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12247 : ℝ) ^ 8 * (mA 12247 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12247) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12247 : ℝ) ^ 16 *
      (d.w0 12247 160 + d.w1 12247 160 * √(π / 2) + 2 * d.w2 12247 160 +
        energyR16 12247 * radiusPolynomialRoot16 (d.w0 12247 160) (d.w1 12247 160)
          (d.w2 12247 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12247 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12247) *
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

end BstLean.Part262.Row12247

/-! A coarse bound on the actual paper statistics constant at dimension 12248. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12246 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12246 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12246 128 ≤ (12500 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12500 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12248) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12248 : ℕ))
    (by norm_num : (12248 : ℕ) ≤ 16384)
  have ht : paperTail256 12248 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12248 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12248 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12248 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12248 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12248 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12246 128 * √(2 / (12248 : ℝ)) *
      (√(12248 : ℝ) + paperT0 12248 + paperTail256 12248) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12248 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12248 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12248 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12246 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12246 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12248 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12248

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12248 (61 / 100) 160 (17 / (100 * 12248)) (26 / (10 * 12248)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12248 (61 / 100) 160 (17 / (100 * 12248)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12248 / 12248 * (61 / 100)) ^ 4 * inverseRadius8 (12248 - 1) /
            envelopeGap 12248 (61 / 100) 160 (17 / (100 * 12248)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12248

namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12248 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12248 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12248 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12248 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12248 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12248) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12248) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12248) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12248) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12248) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12248 * (160 : ℝ) ^ 2 + 26 / (10 * 12248) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12248) : ℝ)) (tA 12248 * 160 ^ 2 + 26 / (10 * 12248)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12248) : ℝ)) d.D d.V d.P (√(tA 12248) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12248) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12248) : ℝ)) (tA 12248 * 160 ^ 2 + 26 / (10 * 12248)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12248) : ℝ)) (√(26 / (10 * 12248) : ℝ)) d.D d.V d.P (√(tA 12248) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12248) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12248

namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12248 160 ∧
    0 ≤ (tableEnvelope C).f1 12248 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12248 160 ∧
    0 ≤ (tableEnvelope C).w1 12248 160 ∧ 0 ≤ (tableEnvelope C).w2 12248 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12248 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12248 160 ∧ 0 ≤ d.f1 12248 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12248 160 ∧ 0 ≤ d.w1 12248 160 ∧ 0 ≤ d.w2 12248 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12248 ≤ 2 * (228 / 100 : ℝ) / 12248 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12248 ≤ 2 * (370 / 100 : ℝ) / 12248 := by
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
    (completeRAData (tableEnvelope C) 12248 160).locationBound 12248 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12248 160).energyBound 12248 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12248 160) (d.f1 12248 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12248 160) (d.w1 12248 160)
      (d.w2 12248 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12248 160) (d.f1 12248 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12248 160) (d.f1 12248 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12248 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12248 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12248 160) (d.f1 12248 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12248 160) (d.w1 12248 160) (d.w2 12248 160)
  have hwexpr0 : 0 ≤ d.w0 12248 160 + d.w1 12248 160 * √(π / 2) +
      2 * d.w2 12248 160 + energyR16 12248 *
      radiusPolynomialRoot16 (d.w0 12248 160) (d.w1 12248 160) (d.w2 12248 160) := by
    positivity
  constructor
  · change (12248 : ℝ) ^ 8 * (mA 12248 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12248 160) (d.f1 12248 160) d.f2 + locationR16 12248 *
        radiusPolynomialRoot16 (d.f0 12248 160) (d.f1 12248 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12248 : ℝ) ^ 8 * (mA 12248 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12248) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12248 : ℝ) ^ 16 *
      (d.w0 12248 160 + d.w1 12248 160 * √(π / 2) + 2 * d.w2 12248 160 +
        energyR16 12248 * radiusPolynomialRoot16 (d.w0 12248 160) (d.w1 12248 160)
          (d.w2 12248 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12248 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12248) *
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

end BstLean.Part262.Row12248

/-! A coarse bound on the actual paper statistics constant at dimension 12249. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12247 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12247 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12247 128 ≤ (12501 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12501 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 12249) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12249 : ℕ))
    (by norm_num : (12249 : ℕ) ≤ 16384)
  have ht : paperTail256 12249 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12249 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12249 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12249 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12249 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12249 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12247 128 * √(2 / (12249 : ℝ)) *
      (√(12249 : ℝ) + paperT0 12249 + paperTail256 12249) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12249 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 12249 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12249 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12247 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12247 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12249 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12249

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12249 (61 / 100) 160 (17 / (100 * 12249)) (26 / (10 * 12249)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12249 (61 / 100) 160 (17 / (100 * 12249)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ 535 / 10 ^ 14 := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ 175 / 10 ^ 17 := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ 7 / 10 ^ 15 := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12249 / 12249 * (61 / 100)) ^ 4 * inverseRadius8 (12249 - 1) /
            envelopeGap 12249 (61 / 100) 160 (17 / (100 * 12249)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12249

namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12249 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12249 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12249 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12249 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12249 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12249) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12249) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12249) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12249) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12249) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12249 * (160 : ℝ) ^ 2 + 26 / (10 * 12249) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12249) : ℝ)) (tA 12249 * 160 ^ 2 + 26 / (10 * 12249)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (370 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (370 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (370 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12249) : ℝ)) d.D d.V d.P (√(tA 12249) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (370 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12249) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12249) : ℝ)) (tA 12249 * 160 ^ 2 + 26 / (10 * 12249)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (370 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12249) : ℝ)) (√(26 / (10 * 12249) : ℝ)) d.D d.V d.P (√(tA 12249) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (370 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12249) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part262.Row12249

namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12249 160 ∧
    0 ≤ (tableEnvelope C).f1 12249 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12249 160 ∧
    0 ≤ (tableEnvelope C).w1 12249 160 ∧ 0 ≤ (tableEnvelope C).w2 12249 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12249 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12249 160 ∧ 0 ≤ d.f1 12249 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12249 160 ∧ 0 ≤ d.w1 12249 160 ∧ 0 ≤ d.w2 12249 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12249 ≤ 2 * (228 / 100 : ℝ) / 12249 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12249 ≤ 2 * (370 / 100 : ℝ) / 12249 := by
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
    (completeRAData (tableEnvelope C) 12249 160).locationBound 12249 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12249 160).energyBound 12249 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12249 160) (d.f1 12249 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12249 160) (d.w1 12249 160)
      (d.w2 12249 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12249 160) (d.f1 12249 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12249 160) (d.f1 12249 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12249 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12249 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12249 160) (d.f1 12249 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12249 160) (d.w1 12249 160) (d.w2 12249 160)
  have hwexpr0 : 0 ≤ d.w0 12249 160 + d.w1 12249 160 * √(π / 2) +
      2 * d.w2 12249 160 + energyR16 12249 *
      radiusPolynomialRoot16 (d.w0 12249 160) (d.w1 12249 160) (d.w2 12249 160) := by
    positivity
  constructor
  · change (12249 : ℝ) ^ 8 * (mA 12249 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12249 160) (d.f1 12249 160) d.f2 + locationR16 12249 *
        radiusPolynomialRoot16 (d.f0 12249 160) (d.f1 12249 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12249 : ℝ) ^ 8 * (mA 12249 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12249) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12249 : ℝ) ^ 16 *
      (d.w0 12249 160 + d.w1 12249 160 * √(π / 2) + 2 * d.w2 12249 160 +
        energyR16 12249 * radiusPolynomialRoot16 (d.w0 12249 160) (d.w1 12249 160)
          (d.w2 12249 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12249 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12249) *
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

end BstLean.Part262.Row12249
