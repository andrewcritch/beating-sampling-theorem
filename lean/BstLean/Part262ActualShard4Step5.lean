import BstLean.Part262ActualShard4Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12325. -/
namespace BstLean.Part262.Row12325
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12323 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12323 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12323 128 ≤ (12577 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12577 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12325) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12325 : ℕ))
    (by norm_num : (12325 : ℕ) ≤ 16384)
  have ht : paperTail256 12325 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12325 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12325 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12325 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12325 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12325 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12323 128 * √(2 / (12325 : ℝ)) *
      (√(12325 : ℝ) + paperT0 12325 + paperTail256 12325) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12325 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12325 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12325 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12323 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12323 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12325 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12325

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12325
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12325 (61 / 100) 160 (17 / (100 * 12325)) (26 / (10 * 12325)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12325 (61 / 100) 160 (17 / (100 * 12325)) := by
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
          (8 * tA 12325 / 12325 * (61 / 100)) ^ 4 * inverseRadius8 (12325 - 1) /
            envelopeGap 12325 (61 / 100) 160 (17 / (100 * 12325)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12325

namespace BstLean.Part262.Row12325
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12325 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12325 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12325 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12325 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12325 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12325) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12325) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12325) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12325) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12325) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12325 * (160 : ℝ) ^ 2 + 26 / (10 * 12325) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12325) : ℝ)) (tA 12325 * 160 ^ 2 + 26 / (10 * 12325)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12325) : ℝ)) d.D d.V d.P (√(tA 12325) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12325) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12325) : ℝ)) (tA 12325 * 160 ^ 2 + 26 / (10 * 12325)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12325) : ℝ)) (√(26 / (10 * 12325) : ℝ)) d.D d.V d.P (√(tA 12325) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12325) * 160) ≤ _
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

end BstLean.Part262.Row12325

namespace BstLean.Part262.Row12325
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12325 160 ∧
    0 ≤ (tableEnvelope C).f1 12325 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12325 160 ∧
    0 ≤ (tableEnvelope C).w1 12325 160 ∧ 0 ≤ (tableEnvelope C).w2 12325 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12325 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12325 160 ∧ 0 ≤ d.f1 12325 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12325 160 ∧ 0 ≤ d.w1 12325 160 ∧ 0 ≤ d.w2 12325 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12325 ≤ 2 * (228 / 100 : ℝ) / 12325 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12325 ≤ 2 * (370 / 100 : ℝ) / 12325 := by
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
    (completeRAData (tableEnvelope C) 12325 160).locationBound 12325 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12325 160).energyBound 12325 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12325 160) (d.f1 12325 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12325 160) (d.w1 12325 160)
      (d.w2 12325 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12325 160) (d.f1 12325 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12325 160) (d.f1 12325 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12325 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12325 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12325 160) (d.f1 12325 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12325 160) (d.w1 12325 160) (d.w2 12325 160)
  have hwexpr0 : 0 ≤ d.w0 12325 160 + d.w1 12325 160 * √(π / 2) +
      2 * d.w2 12325 160 + energyR16 12325 *
      radiusPolynomialRoot16 (d.w0 12325 160) (d.w1 12325 160) (d.w2 12325 160) := by
    positivity
  constructor
  · change (12325 : ℝ) ^ 8 * (mA 12325 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12325 160) (d.f1 12325 160) d.f2 + locationR16 12325 *
        radiusPolynomialRoot16 (d.f0 12325 160) (d.f1 12325 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12325 : ℝ) ^ 8 * (mA 12325 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12325) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12325 : ℝ) ^ 16 *
      (d.w0 12325 160 + d.w1 12325 160 * √(π / 2) + 2 * d.w2 12325 160 +
        energyR16 12325 * radiusPolynomialRoot16 (d.w0 12325 160) (d.w1 12325 160)
          (d.w2 12325 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12325 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12325) *
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

end BstLean.Part262.Row12325

/-! A coarse bound on the actual paper statistics constant at dimension 12326. -/
namespace BstLean.Part262.Row12326
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12324 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12324 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12324 128 ≤ (12578 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12578 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12326) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12326 : ℕ))
    (by norm_num : (12326 : ℕ) ≤ 16384)
  have ht : paperTail256 12326 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12326 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12326 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12326 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12326 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12326 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12324 128 * √(2 / (12326 : ℝ)) *
      (√(12326 : ℝ) + paperT0 12326 + paperTail256 12326) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12326 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12326 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12326 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12324 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12324 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12326 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12326

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12326
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12326 (61 / 100) 160 (17 / (100 * 12326)) (26 / (10 * 12326)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12326 (61 / 100) 160 (17 / (100 * 12326)) := by
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
          (8 * tA 12326 / 12326 * (61 / 100)) ^ 4 * inverseRadius8 (12326 - 1) /
            envelopeGap 12326 (61 / 100) 160 (17 / (100 * 12326)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12326

namespace BstLean.Part262.Row12326
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12326 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12326 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12326 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12326 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12326 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12326) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12326) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12326) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12326) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12326) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12326 * (160 : ℝ) ^ 2 + 26 / (10 * 12326) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12326) : ℝ)) (tA 12326 * 160 ^ 2 + 26 / (10 * 12326)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12326) : ℝ)) d.D d.V d.P (√(tA 12326) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12326) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12326) : ℝ)) (tA 12326 * 160 ^ 2 + 26 / (10 * 12326)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12326) : ℝ)) (√(26 / (10 * 12326) : ℝ)) d.D d.V d.P (√(tA 12326) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12326) * 160) ≤ _
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

end BstLean.Part262.Row12326

namespace BstLean.Part262.Row12326
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12326 160 ∧
    0 ≤ (tableEnvelope C).f1 12326 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12326 160 ∧
    0 ≤ (tableEnvelope C).w1 12326 160 ∧ 0 ≤ (tableEnvelope C).w2 12326 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12326 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12326 160 ∧ 0 ≤ d.f1 12326 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12326 160 ∧ 0 ≤ d.w1 12326 160 ∧ 0 ≤ d.w2 12326 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12326 ≤ 2 * (228 / 100 : ℝ) / 12326 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12326 ≤ 2 * (370 / 100 : ℝ) / 12326 := by
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
    (completeRAData (tableEnvelope C) 12326 160).locationBound 12326 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12326 160).energyBound 12326 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12326 160) (d.f1 12326 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12326 160) (d.w1 12326 160)
      (d.w2 12326 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12326 160) (d.f1 12326 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12326 160) (d.f1 12326 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12326 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12326 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12326 160) (d.f1 12326 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12326 160) (d.w1 12326 160) (d.w2 12326 160)
  have hwexpr0 : 0 ≤ d.w0 12326 160 + d.w1 12326 160 * √(π / 2) +
      2 * d.w2 12326 160 + energyR16 12326 *
      radiusPolynomialRoot16 (d.w0 12326 160) (d.w1 12326 160) (d.w2 12326 160) := by
    positivity
  constructor
  · change (12326 : ℝ) ^ 8 * (mA 12326 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12326 160) (d.f1 12326 160) d.f2 + locationR16 12326 *
        radiusPolynomialRoot16 (d.f0 12326 160) (d.f1 12326 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12326 : ℝ) ^ 8 * (mA 12326 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12326) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12326 : ℝ) ^ 16 *
      (d.w0 12326 160 + d.w1 12326 160 * √(π / 2) + 2 * d.w2 12326 160 +
        energyR16 12326 * radiusPolynomialRoot16 (d.w0 12326 160) (d.w1 12326 160)
          (d.w2 12326 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12326 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12326) *
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

end BstLean.Part262.Row12326

/-! A coarse bound on the actual paper statistics constant at dimension 12327. -/
namespace BstLean.Part262.Row12327
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12325 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12325 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12325 128 ≤ (12579 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12579 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12327) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12327 : ℕ))
    (by norm_num : (12327 : ℕ) ≤ 16384)
  have ht : paperTail256 12327 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12327 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12327 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12327 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12327 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12327 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12325 128 * √(2 / (12327 : ℝ)) *
      (√(12327 : ℝ) + paperT0 12327 + paperTail256 12327) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12327 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12327 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12327 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12325 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12325 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12327 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12327

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12327
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12327 (61 / 100) 160 (17 / (100 * 12327)) (26 / (10 * 12327)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12327 (61 / 100) 160 (17 / (100 * 12327)) := by
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
          (8 * tA 12327 / 12327 * (61 / 100)) ^ 4 * inverseRadius8 (12327 - 1) /
            envelopeGap 12327 (61 / 100) 160 (17 / (100 * 12327)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12327

namespace BstLean.Part262.Row12327
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12327 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12327 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12327 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12327 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12327 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12327) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12327) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12327) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12327) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12327) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12327 * (160 : ℝ) ^ 2 + 26 / (10 * 12327) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12327) : ℝ)) (tA 12327 * 160 ^ 2 + 26 / (10 * 12327)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12327) : ℝ)) d.D d.V d.P (√(tA 12327) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12327) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12327) : ℝ)) (tA 12327 * 160 ^ 2 + 26 / (10 * 12327)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12327) : ℝ)) (√(26 / (10 * 12327) : ℝ)) d.D d.V d.P (√(tA 12327) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12327) * 160) ≤ _
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

end BstLean.Part262.Row12327

namespace BstLean.Part262.Row12327
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12327 160 ∧
    0 ≤ (tableEnvelope C).f1 12327 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12327 160 ∧
    0 ≤ (tableEnvelope C).w1 12327 160 ∧ 0 ≤ (tableEnvelope C).w2 12327 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12327 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12327 160 ∧ 0 ≤ d.f1 12327 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12327 160 ∧ 0 ≤ d.w1 12327 160 ∧ 0 ≤ d.w2 12327 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12327 ≤ 2 * (228 / 100 : ℝ) / 12327 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12327 ≤ 2 * (370 / 100 : ℝ) / 12327 := by
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
    (completeRAData (tableEnvelope C) 12327 160).locationBound 12327 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12327 160).energyBound 12327 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12327 160) (d.f1 12327 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12327 160) (d.w1 12327 160)
      (d.w2 12327 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12327 160) (d.f1 12327 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12327 160) (d.f1 12327 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12327 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12327 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12327 160) (d.f1 12327 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12327 160) (d.w1 12327 160) (d.w2 12327 160)
  have hwexpr0 : 0 ≤ d.w0 12327 160 + d.w1 12327 160 * √(π / 2) +
      2 * d.w2 12327 160 + energyR16 12327 *
      radiusPolynomialRoot16 (d.w0 12327 160) (d.w1 12327 160) (d.w2 12327 160) := by
    positivity
  constructor
  · change (12327 : ℝ) ^ 8 * (mA 12327 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12327 160) (d.f1 12327 160) d.f2 + locationR16 12327 *
        radiusPolynomialRoot16 (d.f0 12327 160) (d.f1 12327 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12327 : ℝ) ^ 8 * (mA 12327 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12327) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12327 : ℝ) ^ 16 *
      (d.w0 12327 160 + d.w1 12327 160 * √(π / 2) + 2 * d.w2 12327 160 +
        energyR16 12327 * radiusPolynomialRoot16 (d.w0 12327 160) (d.w1 12327 160)
          (d.w2 12327 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12327 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12327) *
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

end BstLean.Part262.Row12327

/-! A coarse bound on the actual paper statistics constant at dimension 12328. -/
namespace BstLean.Part262.Row12328
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12326 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12326 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12326 128 ≤ (12580 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12580 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12328) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12328 : ℕ))
    (by norm_num : (12328 : ℕ) ≤ 16384)
  have ht : paperTail256 12328 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12328 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12328 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12328 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12328 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12328 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12326 128 * √(2 / (12328 : ℝ)) *
      (√(12328 : ℝ) + paperT0 12328 + paperTail256 12328) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12328 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12328 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12328 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12326 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12326 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12328 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12328

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12328
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12328 (61 / 100) 160 (17 / (100 * 12328)) (26 / (10 * 12328)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12328 (61 / 100) 160 (17 / (100 * 12328)) := by
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
          (8 * tA 12328 / 12328 * (61 / 100)) ^ 4 * inverseRadius8 (12328 - 1) /
            envelopeGap 12328 (61 / 100) 160 (17 / (100 * 12328)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12328

namespace BstLean.Part262.Row12328
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12328 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12328 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12328 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12328 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12328 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12328) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12328) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12328) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12328) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12328) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12328 * (160 : ℝ) ^ 2 + 26 / (10 * 12328) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12328) : ℝ)) (tA 12328 * 160 ^ 2 + 26 / (10 * 12328)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12328) : ℝ)) d.D d.V d.P (√(tA 12328) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12328) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12328) : ℝ)) (tA 12328 * 160 ^ 2 + 26 / (10 * 12328)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12328) : ℝ)) (√(26 / (10 * 12328) : ℝ)) d.D d.V d.P (√(tA 12328) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12328) * 160) ≤ _
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

end BstLean.Part262.Row12328

namespace BstLean.Part262.Row12328
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12328 160 ∧
    0 ≤ (tableEnvelope C).f1 12328 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12328 160 ∧
    0 ≤ (tableEnvelope C).w1 12328 160 ∧ 0 ≤ (tableEnvelope C).w2 12328 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12328 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12328 160 ∧ 0 ≤ d.f1 12328 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12328 160 ∧ 0 ≤ d.w1 12328 160 ∧ 0 ≤ d.w2 12328 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12328 ≤ 2 * (228 / 100 : ℝ) / 12328 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12328 ≤ 2 * (370 / 100 : ℝ) / 12328 := by
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
    (completeRAData (tableEnvelope C) 12328 160).locationBound 12328 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12328 160).energyBound 12328 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12328 160) (d.f1 12328 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12328 160) (d.w1 12328 160)
      (d.w2 12328 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12328 160) (d.f1 12328 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12328 160) (d.f1 12328 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12328 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12328 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12328 160) (d.f1 12328 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12328 160) (d.w1 12328 160) (d.w2 12328 160)
  have hwexpr0 : 0 ≤ d.w0 12328 160 + d.w1 12328 160 * √(π / 2) +
      2 * d.w2 12328 160 + energyR16 12328 *
      radiusPolynomialRoot16 (d.w0 12328 160) (d.w1 12328 160) (d.w2 12328 160) := by
    positivity
  constructor
  · change (12328 : ℝ) ^ 8 * (mA 12328 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12328 160) (d.f1 12328 160) d.f2 + locationR16 12328 *
        radiusPolynomialRoot16 (d.f0 12328 160) (d.f1 12328 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12328 : ℝ) ^ 8 * (mA 12328 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12328) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12328 : ℝ) ^ 16 *
      (d.w0 12328 160 + d.w1 12328 160 * √(π / 2) + 2 * d.w2 12328 160 +
        energyR16 12328 * radiusPolynomialRoot16 (d.w0 12328 160) (d.w1 12328 160)
          (d.w2 12328 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12328 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12328) *
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

end BstLean.Part262.Row12328

/-! A coarse bound on the actual paper statistics constant at dimension 12329. -/
namespace BstLean.Part262.Row12329
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12327 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12327 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12327 128 ≤ (12581 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12581 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12329) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12329 : ℕ))
    (by norm_num : (12329 : ℕ) ≤ 16384)
  have ht : paperTail256 12329 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12329 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12329 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12329 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12329 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12329 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12327 128 * √(2 / (12329 : ℝ)) *
      (√(12329 : ℝ) + paperT0 12329 + paperTail256 12329) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12329 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12329 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12329 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12327 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12327 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12329 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12329

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12329
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12329 (61 / 100) 160 (17 / (100 * 12329)) (26 / (10 * 12329)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12329 (61 / 100) 160 (17 / (100 * 12329)) := by
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
          (8 * tA 12329 / 12329 * (61 / 100)) ^ 4 * inverseRadius8 (12329 - 1) /
            envelopeGap 12329 (61 / 100) 160 (17 / (100 * 12329)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12329

namespace BstLean.Part262.Row12329
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12329 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12329 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12329 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12329 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12329 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12329) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12329) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12329) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12329) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12329) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12329 * (160 : ℝ) ^ 2 + 26 / (10 * 12329) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12329) : ℝ)) (tA 12329 * 160 ^ 2 + 26 / (10 * 12329)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12329) : ℝ)) d.D d.V d.P (√(tA 12329) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12329) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12329) : ℝ)) (tA 12329 * 160 ^ 2 + 26 / (10 * 12329)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12329) : ℝ)) (√(26 / (10 * 12329) : ℝ)) d.D d.V d.P (√(tA 12329) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12329) * 160) ≤ _
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

end BstLean.Part262.Row12329

namespace BstLean.Part262.Row12329
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12329 160 ∧
    0 ≤ (tableEnvelope C).f1 12329 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12329 160 ∧
    0 ≤ (tableEnvelope C).w1 12329 160 ∧ 0 ≤ (tableEnvelope C).w2 12329 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12329 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12329 160 ∧ 0 ≤ d.f1 12329 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12329 160 ∧ 0 ≤ d.w1 12329 160 ∧ 0 ≤ d.w2 12329 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12329 ≤ 2 * (228 / 100 : ℝ) / 12329 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12329 ≤ 2 * (370 / 100 : ℝ) / 12329 := by
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
    (completeRAData (tableEnvelope C) 12329 160).locationBound 12329 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12329 160).energyBound 12329 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12329 160) (d.f1 12329 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12329 160) (d.w1 12329 160)
      (d.w2 12329 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12329 160) (d.f1 12329 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12329 160) (d.f1 12329 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12329 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12329 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12329 160) (d.f1 12329 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12329 160) (d.w1 12329 160) (d.w2 12329 160)
  have hwexpr0 : 0 ≤ d.w0 12329 160 + d.w1 12329 160 * √(π / 2) +
      2 * d.w2 12329 160 + energyR16 12329 *
      radiusPolynomialRoot16 (d.w0 12329 160) (d.w1 12329 160) (d.w2 12329 160) := by
    positivity
  constructor
  · change (12329 : ℝ) ^ 8 * (mA 12329 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12329 160) (d.f1 12329 160) d.f2 + locationR16 12329 *
        radiusPolynomialRoot16 (d.f0 12329 160) (d.f1 12329 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12329 : ℝ) ^ 8 * (mA 12329 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12329) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12329 : ℝ) ^ 16 *
      (d.w0 12329 160 + d.w1 12329 160 * √(π / 2) + 2 * d.w2 12329 160 +
        energyR16 12329 * radiusPolynomialRoot16 (d.w0 12329 160) (d.w1 12329 160)
          (d.w2 12329 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12329 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12329) *
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

end BstLean.Part262.Row12329

/-! A coarse bound on the actual paper statistics constant at dimension 12330. -/
namespace BstLean.Part262.Row12330
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12328 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12328 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12328 128 ≤ (12582 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12582 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12330) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12330 : ℕ))
    (by norm_num : (12330 : ℕ) ≤ 16384)
  have ht : paperTail256 12330 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12330 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12330 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12330 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12330 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12330 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12328 128 * √(2 / (12330 : ℝ)) *
      (√(12330 : ℝ) + paperT0 12330 + paperTail256 12330) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12330 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12330 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12330 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12328 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12328 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12330 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12330

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12330
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12330 (61 / 100) 160 (17 / (100 * 12330)) (26 / (10 * 12330)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12330 (61 / 100) 160 (17 / (100 * 12330)) := by
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
          (8 * tA 12330 / 12330 * (61 / 100)) ^ 4 * inverseRadius8 (12330 - 1) /
            envelopeGap 12330 (61 / 100) 160 (17 / (100 * 12330)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12330

namespace BstLean.Part262.Row12330
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12330 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12330 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12330 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12330 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12330 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12330) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12330) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12330) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12330) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12330) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12330 * (160 : ℝ) ^ 2 + 26 / (10 * 12330) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12330) : ℝ)) (tA 12330 * 160 ^ 2 + 26 / (10 * 12330)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12330) : ℝ)) d.D d.V d.P (√(tA 12330) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12330) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12330) : ℝ)) (tA 12330 * 160 ^ 2 + 26 / (10 * 12330)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12330) : ℝ)) (√(26 / (10 * 12330) : ℝ)) d.D d.V d.P (√(tA 12330) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12330) * 160) ≤ _
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

end BstLean.Part262.Row12330

namespace BstLean.Part262.Row12330
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12330 160 ∧
    0 ≤ (tableEnvelope C).f1 12330 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12330 160 ∧
    0 ≤ (tableEnvelope C).w1 12330 160 ∧ 0 ≤ (tableEnvelope C).w2 12330 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12330 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12330 160 ∧ 0 ≤ d.f1 12330 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12330 160 ∧ 0 ≤ d.w1 12330 160 ∧ 0 ≤ d.w2 12330 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12330 ≤ 2 * (228 / 100 : ℝ) / 12330 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12330 ≤ 2 * (370 / 100 : ℝ) / 12330 := by
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
    (completeRAData (tableEnvelope C) 12330 160).locationBound 12330 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12330 160).energyBound 12330 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12330 160) (d.f1 12330 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12330 160) (d.w1 12330 160)
      (d.w2 12330 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12330 160) (d.f1 12330 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12330 160) (d.f1 12330 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12330 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12330 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12330 160) (d.f1 12330 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12330 160) (d.w1 12330 160) (d.w2 12330 160)
  have hwexpr0 : 0 ≤ d.w0 12330 160 + d.w1 12330 160 * √(π / 2) +
      2 * d.w2 12330 160 + energyR16 12330 *
      radiusPolynomialRoot16 (d.w0 12330 160) (d.w1 12330 160) (d.w2 12330 160) := by
    positivity
  constructor
  · change (12330 : ℝ) ^ 8 * (mA 12330 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12330 160) (d.f1 12330 160) d.f2 + locationR16 12330 *
        radiusPolynomialRoot16 (d.f0 12330 160) (d.f1 12330 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12330 : ℝ) ^ 8 * (mA 12330 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12330) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12330 : ℝ) ^ 16 *
      (d.w0 12330 160 + d.w1 12330 160 * √(π / 2) + 2 * d.w2 12330 160 +
        energyR16 12330 * radiusPolynomialRoot16 (d.w0 12330 160) (d.w1 12330 160)
          (d.w2 12330 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12330 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12330) *
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

end BstLean.Part262.Row12330

/-! A coarse bound on the actual paper statistics constant at dimension 12331. -/
namespace BstLean.Part262.Row12331
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12329 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12329 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12329 128 ≤ (12583 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12583 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12331) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12331 : ℕ))
    (by norm_num : (12331 : ℕ) ≤ 16384)
  have ht : paperTail256 12331 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12331 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12331 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12331 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12331 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12331 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12329 128 * √(2 / (12331 : ℝ)) *
      (√(12331 : ℝ) + paperT0 12331 + paperTail256 12331) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12331 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12331 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12331 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12329 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12329 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12331 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12331

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12331
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12331 (61 / 100) 160 (17 / (100 * 12331)) (26 / (10 * 12331)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12331 (61 / 100) 160 (17 / (100 * 12331)) := by
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
          (8 * tA 12331 / 12331 * (61 / 100)) ^ 4 * inverseRadius8 (12331 - 1) /
            envelopeGap 12331 (61 / 100) 160 (17 / (100 * 12331)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12331

namespace BstLean.Part262.Row12331
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12331 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12331 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12331 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12331 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12331 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12331) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12331) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12331) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12331) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12331) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12331 * (160 : ℝ) ^ 2 + 26 / (10 * 12331) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12331) : ℝ)) (tA 12331 * 160 ^ 2 + 26 / (10 * 12331)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12331) : ℝ)) d.D d.V d.P (√(tA 12331) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12331) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12331) : ℝ)) (tA 12331 * 160 ^ 2 + 26 / (10 * 12331)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12331) : ℝ)) (√(26 / (10 * 12331) : ℝ)) d.D d.V d.P (√(tA 12331) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12331) * 160) ≤ _
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

end BstLean.Part262.Row12331

namespace BstLean.Part262.Row12331
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12331 160 ∧
    0 ≤ (tableEnvelope C).f1 12331 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12331 160 ∧
    0 ≤ (tableEnvelope C).w1 12331 160 ∧ 0 ≤ (tableEnvelope C).w2 12331 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12331 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12331 160 ∧ 0 ≤ d.f1 12331 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12331 160 ∧ 0 ≤ d.w1 12331 160 ∧ 0 ≤ d.w2 12331 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12331 ≤ 2 * (228 / 100 : ℝ) / 12331 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12331 ≤ 2 * (370 / 100 : ℝ) / 12331 := by
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
    (completeRAData (tableEnvelope C) 12331 160).locationBound 12331 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12331 160).energyBound 12331 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12331 160) (d.f1 12331 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12331 160) (d.w1 12331 160)
      (d.w2 12331 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12331 160) (d.f1 12331 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12331 160) (d.f1 12331 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12331 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12331 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12331 160) (d.f1 12331 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12331 160) (d.w1 12331 160) (d.w2 12331 160)
  have hwexpr0 : 0 ≤ d.w0 12331 160 + d.w1 12331 160 * √(π / 2) +
      2 * d.w2 12331 160 + energyR16 12331 *
      radiusPolynomialRoot16 (d.w0 12331 160) (d.w1 12331 160) (d.w2 12331 160) := by
    positivity
  constructor
  · change (12331 : ℝ) ^ 8 * (mA 12331 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12331 160) (d.f1 12331 160) d.f2 + locationR16 12331 *
        radiusPolynomialRoot16 (d.f0 12331 160) (d.f1 12331 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12331 : ℝ) ^ 8 * (mA 12331 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12331) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12331 : ℝ) ^ 16 *
      (d.w0 12331 160 + d.w1 12331 160 * √(π / 2) + 2 * d.w2 12331 160 +
        energyR16 12331 * radiusPolynomialRoot16 (d.w0 12331 160) (d.w1 12331 160)
          (d.w2 12331 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12331 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12331) *
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

end BstLean.Part262.Row12331

/-! A coarse bound on the actual paper statistics constant at dimension 12332. -/
namespace BstLean.Part262.Row12332
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12330 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12330 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12330 128 ≤ (12584 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12584 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12332) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12332 : ℕ))
    (by norm_num : (12332 : ℕ) ≤ 16384)
  have ht : paperTail256 12332 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12332 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12332 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12332 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12332 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12332 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12330 128 * √(2 / (12332 : ℝ)) *
      (√(12332 : ℝ) + paperT0 12332 + paperTail256 12332) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12332 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12332 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12332 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12330 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12330 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12332 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12332

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12332
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12332 (61 / 100) 160 (17 / (100 * 12332)) (26 / (10 * 12332)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12332 (61 / 100) 160 (17 / (100 * 12332)) := by
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
          (8 * tA 12332 / 12332 * (61 / 100)) ^ 4 * inverseRadius8 (12332 - 1) /
            envelopeGap 12332 (61 / 100) 160 (17 / (100 * 12332)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12332

namespace BstLean.Part262.Row12332
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12332 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12332 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12332 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12332 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12332 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12332) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12332) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12332) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12332) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12332) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12332 * (160 : ℝ) ^ 2 + 26 / (10 * 12332) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12332) : ℝ)) (tA 12332 * 160 ^ 2 + 26 / (10 * 12332)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12332) : ℝ)) d.D d.V d.P (√(tA 12332) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12332) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12332) : ℝ)) (tA 12332 * 160 ^ 2 + 26 / (10 * 12332)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12332) : ℝ)) (√(26 / (10 * 12332) : ℝ)) d.D d.V d.P (√(tA 12332) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12332) * 160) ≤ _
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

end BstLean.Part262.Row12332

namespace BstLean.Part262.Row12332
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12332 160 ∧
    0 ≤ (tableEnvelope C).f1 12332 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12332 160 ∧
    0 ≤ (tableEnvelope C).w1 12332 160 ∧ 0 ≤ (tableEnvelope C).w2 12332 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12332 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12332 160 ∧ 0 ≤ d.f1 12332 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12332 160 ∧ 0 ≤ d.w1 12332 160 ∧ 0 ≤ d.w2 12332 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12332 ≤ 2 * (228 / 100 : ℝ) / 12332 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12332 ≤ 2 * (370 / 100 : ℝ) / 12332 := by
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
    (completeRAData (tableEnvelope C) 12332 160).locationBound 12332 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12332 160).energyBound 12332 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12332 160) (d.f1 12332 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12332 160) (d.w1 12332 160)
      (d.w2 12332 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12332 160) (d.f1 12332 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12332 160) (d.f1 12332 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12332 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12332 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12332 160) (d.f1 12332 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12332 160) (d.w1 12332 160) (d.w2 12332 160)
  have hwexpr0 : 0 ≤ d.w0 12332 160 + d.w1 12332 160 * √(π / 2) +
      2 * d.w2 12332 160 + energyR16 12332 *
      radiusPolynomialRoot16 (d.w0 12332 160) (d.w1 12332 160) (d.w2 12332 160) := by
    positivity
  constructor
  · change (12332 : ℝ) ^ 8 * (mA 12332 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12332 160) (d.f1 12332 160) d.f2 + locationR16 12332 *
        radiusPolynomialRoot16 (d.f0 12332 160) (d.f1 12332 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12332 : ℝ) ^ 8 * (mA 12332 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12332) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12332 : ℝ) ^ 16 *
      (d.w0 12332 160 + d.w1 12332 160 * √(π / 2) + 2 * d.w2 12332 160 +
        energyR16 12332 * radiusPolynomialRoot16 (d.w0 12332 160) (d.w1 12332 160)
          (d.w2 12332 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12332 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12332) *
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

end BstLean.Part262.Row12332

/-! A coarse bound on the actual paper statistics constant at dimension 12333. -/
namespace BstLean.Part262.Row12333
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12331 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12331 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12331 128 ≤ (12585 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12585 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12333) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12333 : ℕ))
    (by norm_num : (12333 : ℕ) ≤ 16384)
  have ht : paperTail256 12333 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12333 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12333 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12333 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12333 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12333 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12331 128 * √(2 / (12333 : ℝ)) *
      (√(12333 : ℝ) + paperT0 12333 + paperTail256 12333) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12333 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12333 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12333 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12331 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12331 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12333 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12333

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12333
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12333 (61 / 100) 160 (17 / (100 * 12333)) (26 / (10 * 12333)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12333 (61 / 100) 160 (17 / (100 * 12333)) := by
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
          (8 * tA 12333 / 12333 * (61 / 100)) ^ 4 * inverseRadius8 (12333 - 1) /
            envelopeGap 12333 (61 / 100) 160 (17 / (100 * 12333)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12333

namespace BstLean.Part262.Row12333
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12333 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12333 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12333 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12333 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12333 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12333) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12333) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12333) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12333) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12333) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12333 * (160 : ℝ) ^ 2 + 26 / (10 * 12333) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12333) : ℝ)) (tA 12333 * 160 ^ 2 + 26 / (10 * 12333)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12333) : ℝ)) d.D d.V d.P (√(tA 12333) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12333) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12333) : ℝ)) (tA 12333 * 160 ^ 2 + 26 / (10 * 12333)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12333) : ℝ)) (√(26 / (10 * 12333) : ℝ)) d.D d.V d.P (√(tA 12333) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12333) * 160) ≤ _
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

end BstLean.Part262.Row12333

namespace BstLean.Part262.Row12333
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12333 160 ∧
    0 ≤ (tableEnvelope C).f1 12333 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12333 160 ∧
    0 ≤ (tableEnvelope C).w1 12333 160 ∧ 0 ≤ (tableEnvelope C).w2 12333 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12333 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12333 160 ∧ 0 ≤ d.f1 12333 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12333 160 ∧ 0 ≤ d.w1 12333 160 ∧ 0 ≤ d.w2 12333 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12333 ≤ 2 * (228 / 100 : ℝ) / 12333 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12333 ≤ 2 * (370 / 100 : ℝ) / 12333 := by
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
    (completeRAData (tableEnvelope C) 12333 160).locationBound 12333 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12333 160).energyBound 12333 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12333 160) (d.f1 12333 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12333 160) (d.w1 12333 160)
      (d.w2 12333 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12333 160) (d.f1 12333 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12333 160) (d.f1 12333 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12333 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12333 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12333 160) (d.f1 12333 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12333 160) (d.w1 12333 160) (d.w2 12333 160)
  have hwexpr0 : 0 ≤ d.w0 12333 160 + d.w1 12333 160 * √(π / 2) +
      2 * d.w2 12333 160 + energyR16 12333 *
      radiusPolynomialRoot16 (d.w0 12333 160) (d.w1 12333 160) (d.w2 12333 160) := by
    positivity
  constructor
  · change (12333 : ℝ) ^ 8 * (mA 12333 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12333 160) (d.f1 12333 160) d.f2 + locationR16 12333 *
        radiusPolynomialRoot16 (d.f0 12333 160) (d.f1 12333 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12333 : ℝ) ^ 8 * (mA 12333 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12333) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12333 : ℝ) ^ 16 *
      (d.w0 12333 160 + d.w1 12333 160 * √(π / 2) + 2 * d.w2 12333 160 +
        energyR16 12333 * radiusPolynomialRoot16 (d.w0 12333 160) (d.w1 12333 160)
          (d.w2 12333 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12333 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12333) *
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

end BstLean.Part262.Row12333

/-! A coarse bound on the actual paper statistics constant at dimension 12334. -/
namespace BstLean.Part262.Row12334
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12332 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12332 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12332 128 ≤ (12586 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12586 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12334) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12334 : ℕ))
    (by norm_num : (12334 : ℕ) ≤ 16384)
  have ht : paperTail256 12334 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12334 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12334 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12334 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12334 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12334 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12332 128 * √(2 / (12334 : ℝ)) *
      (√(12334 : ℝ) + paperT0 12334 + paperTail256 12334) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12334 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12334 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12334 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12332 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12332 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12334 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12334

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12334
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12334 (61 / 100) 160 (17 / (100 * 12334)) (26 / (10 * 12334)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12334 (61 / 100) 160 (17 / (100 * 12334)) := by
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
          (8 * tA 12334 / 12334 * (61 / 100)) ^ 4 * inverseRadius8 (12334 - 1) /
            envelopeGap 12334 (61 / 100) 160 (17 / (100 * 12334)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12334

namespace BstLean.Part262.Row12334
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12334 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12334 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12334 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12334 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12334 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12334) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12334) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12334) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12334) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12334) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12334 * (160 : ℝ) ^ 2 + 26 / (10 * 12334) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12334) : ℝ)) (tA 12334 * 160 ^ 2 + 26 / (10 * 12334)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12334) : ℝ)) d.D d.V d.P (√(tA 12334) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12334) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12334) : ℝ)) (tA 12334 * 160 ^ 2 + 26 / (10 * 12334)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12334) : ℝ)) (√(26 / (10 * 12334) : ℝ)) d.D d.V d.P (√(tA 12334) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12334) * 160) ≤ _
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

end BstLean.Part262.Row12334

namespace BstLean.Part262.Row12334
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12334 160 ∧
    0 ≤ (tableEnvelope C).f1 12334 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12334 160 ∧
    0 ≤ (tableEnvelope C).w1 12334 160 ∧ 0 ≤ (tableEnvelope C).w2 12334 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12334 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12334 160 ∧ 0 ≤ d.f1 12334 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12334 160 ∧ 0 ≤ d.w1 12334 160 ∧ 0 ≤ d.w2 12334 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12334 ≤ 2 * (228 / 100 : ℝ) / 12334 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12334 ≤ 2 * (370 / 100 : ℝ) / 12334 := by
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
    (completeRAData (tableEnvelope C) 12334 160).locationBound 12334 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12334 160).energyBound 12334 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12334 160) (d.f1 12334 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12334 160) (d.w1 12334 160)
      (d.w2 12334 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12334 160) (d.f1 12334 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12334 160) (d.f1 12334 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12334 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12334 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12334 160) (d.f1 12334 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12334 160) (d.w1 12334 160) (d.w2 12334 160)
  have hwexpr0 : 0 ≤ d.w0 12334 160 + d.w1 12334 160 * √(π / 2) +
      2 * d.w2 12334 160 + energyR16 12334 *
      radiusPolynomialRoot16 (d.w0 12334 160) (d.w1 12334 160) (d.w2 12334 160) := by
    positivity
  constructor
  · change (12334 : ℝ) ^ 8 * (mA 12334 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12334 160) (d.f1 12334 160) d.f2 + locationR16 12334 *
        radiusPolynomialRoot16 (d.f0 12334 160) (d.f1 12334 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12334 : ℝ) ^ 8 * (mA 12334 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12334) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12334 : ℝ) ^ 16 *
      (d.w0 12334 160 + d.w1 12334 160 * √(π / 2) + 2 * d.w2 12334 160 +
        energyR16 12334 * radiusPolynomialRoot16 (d.w0 12334 160) (d.w1 12334 160)
          (d.w2 12334 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12334 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12334) *
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

end BstLean.Part262.Row12334

/-! A coarse bound on the actual paper statistics constant at dimension 12335. -/
namespace BstLean.Part262.Row12335
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12333 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12333 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12333 128 ≤ (12587 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12587 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12335) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12335 : ℕ))
    (by norm_num : (12335 : ℕ) ≤ 16384)
  have ht : paperTail256 12335 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12335 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12335 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12335 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12335 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12335 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12333 128 * √(2 / (12335 : ℝ)) *
      (√(12335 : ℝ) + paperT0 12335 + paperTail256 12335) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12335 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12335 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12335 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12333 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12333 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12335 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12335

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12335
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12335 (61 / 100) 160 (17 / (100 * 12335)) (26 / (10 * 12335)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12335 (61 / 100) 160 (17 / (100 * 12335)) := by
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
          (8 * tA 12335 / 12335 * (61 / 100)) ^ 4 * inverseRadius8 (12335 - 1) /
            envelopeGap 12335 (61 / 100) 160 (17 / (100 * 12335)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12335

namespace BstLean.Part262.Row12335
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12335 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12335 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12335 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12335 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12335 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12335) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12335) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12335) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12335) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12335) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12335 * (160 : ℝ) ^ 2 + 26 / (10 * 12335) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12335) : ℝ)) (tA 12335 * 160 ^ 2 + 26 / (10 * 12335)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12335) : ℝ)) d.D d.V d.P (√(tA 12335) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12335) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12335) : ℝ)) (tA 12335 * 160 ^ 2 + 26 / (10 * 12335)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12335) : ℝ)) (√(26 / (10 * 12335) : ℝ)) d.D d.V d.P (√(tA 12335) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12335) * 160) ≤ _
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

end BstLean.Part262.Row12335

namespace BstLean.Part262.Row12335
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12335 160 ∧
    0 ≤ (tableEnvelope C).f1 12335 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12335 160 ∧
    0 ≤ (tableEnvelope C).w1 12335 160 ∧ 0 ≤ (tableEnvelope C).w2 12335 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12335 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12335 160 ∧ 0 ≤ d.f1 12335 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12335 160 ∧ 0 ≤ d.w1 12335 160 ∧ 0 ≤ d.w2 12335 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12335 ≤ 2 * (228 / 100 : ℝ) / 12335 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12335 ≤ 2 * (370 / 100 : ℝ) / 12335 := by
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
    (completeRAData (tableEnvelope C) 12335 160).locationBound 12335 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12335 160).energyBound 12335 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12335 160) (d.f1 12335 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12335 160) (d.w1 12335 160)
      (d.w2 12335 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12335 160) (d.f1 12335 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12335 160) (d.f1 12335 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12335 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12335 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12335 160) (d.f1 12335 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12335 160) (d.w1 12335 160) (d.w2 12335 160)
  have hwexpr0 : 0 ≤ d.w0 12335 160 + d.w1 12335 160 * √(π / 2) +
      2 * d.w2 12335 160 + energyR16 12335 *
      radiusPolynomialRoot16 (d.w0 12335 160) (d.w1 12335 160) (d.w2 12335 160) := by
    positivity
  constructor
  · change (12335 : ℝ) ^ 8 * (mA 12335 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12335 160) (d.f1 12335 160) d.f2 + locationR16 12335 *
        radiusPolynomialRoot16 (d.f0 12335 160) (d.f1 12335 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12335 : ℝ) ^ 8 * (mA 12335 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12335) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12335 : ℝ) ^ 16 *
      (d.w0 12335 160 + d.w1 12335 160 * √(π / 2) + 2 * d.w2 12335 160 +
        energyR16 12335 * radiusPolynomialRoot16 (d.w0 12335 160) (d.w1 12335 160)
          (d.w2 12335 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12335 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12335) *
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

end BstLean.Part262.Row12335

/-! A coarse bound on the actual paper statistics constant at dimension 12336. -/
namespace BstLean.Part262.Row12336
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12334 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12334 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12334 128 ≤ (12588 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12588 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12336) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12336 : ℕ))
    (by norm_num : (12336 : ℕ) ≤ 16384)
  have ht : paperTail256 12336 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12336 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12336 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12336 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12336 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12336 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12334 128 * √(2 / (12336 : ℝ)) *
      (√(12336 : ℝ) + paperT0 12336 + paperTail256 12336) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12336 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12336 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12336 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12334 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12334 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12336 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12336

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12336
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12336 (61 / 100) 160 (17 / (100 * 12336)) (26 / (10 * 12336)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12336 (61 / 100) 160 (17 / (100 * 12336)) := by
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
          (8 * tA 12336 / 12336 * (61 / 100)) ^ 4 * inverseRadius8 (12336 - 1) /
            envelopeGap 12336 (61 / 100) 160 (17 / (100 * 12336)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12336

namespace BstLean.Part262.Row12336
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12336 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12336 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12336 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12336 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12336 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12336) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12336) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12336) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12336) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12336) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12336 * (160 : ℝ) ^ 2 + 26 / (10 * 12336) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12336) : ℝ)) (tA 12336 * 160 ^ 2 + 26 / (10 * 12336)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12336) : ℝ)) d.D d.V d.P (√(tA 12336) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12336) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12336) : ℝ)) (tA 12336 * 160 ^ 2 + 26 / (10 * 12336)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12336) : ℝ)) (√(26 / (10 * 12336) : ℝ)) d.D d.V d.P (√(tA 12336) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12336) * 160) ≤ _
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

end BstLean.Part262.Row12336

namespace BstLean.Part262.Row12336
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12336 160 ∧
    0 ≤ (tableEnvelope C).f1 12336 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12336 160 ∧
    0 ≤ (tableEnvelope C).w1 12336 160 ∧ 0 ≤ (tableEnvelope C).w2 12336 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12336 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12336 160 ∧ 0 ≤ d.f1 12336 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12336 160 ∧ 0 ≤ d.w1 12336 160 ∧ 0 ≤ d.w2 12336 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12336 ≤ 2 * (228 / 100 : ℝ) / 12336 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12336 ≤ 2 * (370 / 100 : ℝ) / 12336 := by
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
    (completeRAData (tableEnvelope C) 12336 160).locationBound 12336 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12336 160).energyBound 12336 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12336 160) (d.f1 12336 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12336 160) (d.w1 12336 160)
      (d.w2 12336 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12336 160) (d.f1 12336 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12336 160) (d.f1 12336 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12336 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12336 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12336 160) (d.f1 12336 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12336 160) (d.w1 12336 160) (d.w2 12336 160)
  have hwexpr0 : 0 ≤ d.w0 12336 160 + d.w1 12336 160 * √(π / 2) +
      2 * d.w2 12336 160 + energyR16 12336 *
      radiusPolynomialRoot16 (d.w0 12336 160) (d.w1 12336 160) (d.w2 12336 160) := by
    positivity
  constructor
  · change (12336 : ℝ) ^ 8 * (mA 12336 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12336 160) (d.f1 12336 160) d.f2 + locationR16 12336 *
        radiusPolynomialRoot16 (d.f0 12336 160) (d.f1 12336 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12336 : ℝ) ^ 8 * (mA 12336 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12336) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12336 : ℝ) ^ 16 *
      (d.w0 12336 160 + d.w1 12336 160 * √(π / 2) + 2 * d.w2 12336 160 +
        energyR16 12336 * radiusPolynomialRoot16 (d.w0 12336 160) (d.w1 12336 160)
          (d.w2 12336 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12336 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12336) *
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

end BstLean.Part262.Row12336

/-! A coarse bound on the actual paper statistics constant at dimension 12337. -/
namespace BstLean.Part262.Row12337
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12335 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12335 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12335 128 ≤ (12589 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12589 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12337) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12337 : ℕ))
    (by norm_num : (12337 : ℕ) ≤ 16384)
  have ht : paperTail256 12337 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12337 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12337 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12337 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12337 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12337 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12335 128 * √(2 / (12337 : ℝ)) *
      (√(12337 : ℝ) + paperT0 12337 + paperTail256 12337) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12337 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12337 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12337 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12335 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12335 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12337 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12337

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12337
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12337 (61 / 100) 160 (17 / (100 * 12337)) (26 / (10 * 12337)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12337 (61 / 100) 160 (17 / (100 * 12337)) := by
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
          (8 * tA 12337 / 12337 * (61 / 100)) ^ 4 * inverseRadius8 (12337 - 1) /
            envelopeGap 12337 (61 / 100) 160 (17 / (100 * 12337)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12337

namespace BstLean.Part262.Row12337
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12337 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12337 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12337 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12337 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12337 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12337) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12337) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12337) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12337) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12337) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12337 * (160 : ℝ) ^ 2 + 26 / (10 * 12337) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12337) : ℝ)) (tA 12337 * 160 ^ 2 + 26 / (10 * 12337)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12337) : ℝ)) d.D d.V d.P (√(tA 12337) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12337) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12337) : ℝ)) (tA 12337 * 160 ^ 2 + 26 / (10 * 12337)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12337) : ℝ)) (√(26 / (10 * 12337) : ℝ)) d.D d.V d.P (√(tA 12337) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12337) * 160) ≤ _
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

end BstLean.Part262.Row12337

namespace BstLean.Part262.Row12337
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12337 160 ∧
    0 ≤ (tableEnvelope C).f1 12337 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12337 160 ∧
    0 ≤ (tableEnvelope C).w1 12337 160 ∧ 0 ≤ (tableEnvelope C).w2 12337 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12337 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12337 160 ∧ 0 ≤ d.f1 12337 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12337 160 ∧ 0 ≤ d.w1 12337 160 ∧ 0 ≤ d.w2 12337 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12337 ≤ 2 * (228 / 100 : ℝ) / 12337 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12337 ≤ 2 * (370 / 100 : ℝ) / 12337 := by
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
    (completeRAData (tableEnvelope C) 12337 160).locationBound 12337 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12337 160).energyBound 12337 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12337 160) (d.f1 12337 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12337 160) (d.w1 12337 160)
      (d.w2 12337 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12337 160) (d.f1 12337 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12337 160) (d.f1 12337 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12337 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12337 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12337 160) (d.f1 12337 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12337 160) (d.w1 12337 160) (d.w2 12337 160)
  have hwexpr0 : 0 ≤ d.w0 12337 160 + d.w1 12337 160 * √(π / 2) +
      2 * d.w2 12337 160 + energyR16 12337 *
      radiusPolynomialRoot16 (d.w0 12337 160) (d.w1 12337 160) (d.w2 12337 160) := by
    positivity
  constructor
  · change (12337 : ℝ) ^ 8 * (mA 12337 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12337 160) (d.f1 12337 160) d.f2 + locationR16 12337 *
        radiusPolynomialRoot16 (d.f0 12337 160) (d.f1 12337 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12337 : ℝ) ^ 8 * (mA 12337 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12337) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12337 : ℝ) ^ 16 *
      (d.w0 12337 160 + d.w1 12337 160 * √(π / 2) + 2 * d.w2 12337 160 +
        energyR16 12337 * radiusPolynomialRoot16 (d.w0 12337 160) (d.w1 12337 160)
          (d.w2 12337 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12337 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12337) *
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

end BstLean.Part262.Row12337

/-! A coarse bound on the actual paper statistics constant at dimension 12338. -/
namespace BstLean.Part262.Row12338
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12336 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12336 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12336 128 ≤ (12590 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12590 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12338) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12338 : ℕ))
    (by norm_num : (12338 : ℕ) ≤ 16384)
  have ht : paperTail256 12338 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12338 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12338 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12338 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12338 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12338 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12336 128 * √(2 / (12338 : ℝ)) *
      (√(12338 : ℝ) + paperT0 12338 + paperTail256 12338) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12338 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12338 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12338 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12336 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12336 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12338 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12338

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12338
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12338 (61 / 100) 160 (17 / (100 * 12338)) (26 / (10 * 12338)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12338 (61 / 100) 160 (17 / (100 * 12338)) := by
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
          (8 * tA 12338 / 12338 * (61 / 100)) ^ 4 * inverseRadius8 (12338 - 1) /
            envelopeGap 12338 (61 / 100) 160 (17 / (100 * 12338)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12338

namespace BstLean.Part262.Row12338
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12338 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12338 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12338 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12338 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12338 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12338) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12338) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12338) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12338) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12338) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12338 * (160 : ℝ) ^ 2 + 26 / (10 * 12338) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12338) : ℝ)) (tA 12338 * 160 ^ 2 + 26 / (10 * 12338)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12338) : ℝ)) d.D d.V d.P (√(tA 12338) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12338) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12338) : ℝ)) (tA 12338 * 160 ^ 2 + 26 / (10 * 12338)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12338) : ℝ)) (√(26 / (10 * 12338) : ℝ)) d.D d.V d.P (√(tA 12338) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12338) * 160) ≤ _
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

end BstLean.Part262.Row12338

namespace BstLean.Part262.Row12338
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12338 160 ∧
    0 ≤ (tableEnvelope C).f1 12338 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12338 160 ∧
    0 ≤ (tableEnvelope C).w1 12338 160 ∧ 0 ≤ (tableEnvelope C).w2 12338 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12338 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12338 160 ∧ 0 ≤ d.f1 12338 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12338 160 ∧ 0 ≤ d.w1 12338 160 ∧ 0 ≤ d.w2 12338 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12338 ≤ 2 * (228 / 100 : ℝ) / 12338 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12338 ≤ 2 * (370 / 100 : ℝ) / 12338 := by
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
    (completeRAData (tableEnvelope C) 12338 160).locationBound 12338 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12338 160).energyBound 12338 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12338 160) (d.f1 12338 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12338 160) (d.w1 12338 160)
      (d.w2 12338 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12338 160) (d.f1 12338 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12338 160) (d.f1 12338 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12338 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12338 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12338 160) (d.f1 12338 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12338 160) (d.w1 12338 160) (d.w2 12338 160)
  have hwexpr0 : 0 ≤ d.w0 12338 160 + d.w1 12338 160 * √(π / 2) +
      2 * d.w2 12338 160 + energyR16 12338 *
      radiusPolynomialRoot16 (d.w0 12338 160) (d.w1 12338 160) (d.w2 12338 160) := by
    positivity
  constructor
  · change (12338 : ℝ) ^ 8 * (mA 12338 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12338 160) (d.f1 12338 160) d.f2 + locationR16 12338 *
        radiusPolynomialRoot16 (d.f0 12338 160) (d.f1 12338 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12338 : ℝ) ^ 8 * (mA 12338 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12338) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12338 : ℝ) ^ 16 *
      (d.w0 12338 160 + d.w1 12338 160 * √(π / 2) + 2 * d.w2 12338 160 +
        energyR16 12338 * radiusPolynomialRoot16 (d.w0 12338 160) (d.w1 12338 160)
          (d.w2 12338 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12338 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12338) *
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

end BstLean.Part262.Row12338

/-! A coarse bound on the actual paper statistics constant at dimension 12339. -/
namespace BstLean.Part262.Row12339
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12337 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12337 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12337 128 ≤ (12591 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12591 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12339) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12339 : ℕ))
    (by norm_num : (12339 : ℕ) ≤ 16384)
  have ht : paperTail256 12339 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12339 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12339 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12339 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12339 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12339 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12337 128 * √(2 / (12339 : ℝ)) *
      (√(12339 : ℝ) + paperT0 12339 + paperTail256 12339) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12339 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12339 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12339 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12337 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12337 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12339 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12339

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12339
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12339 (61 / 100) 160 (17 / (100 * 12339)) (26 / (10 * 12339)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12339 (61 / 100) 160 (17 / (100 * 12339)) := by
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
          (8 * tA 12339 / 12339 * (61 / 100)) ^ 4 * inverseRadius8 (12339 - 1) /
            envelopeGap 12339 (61 / 100) 160 (17 / (100 * 12339)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12339

namespace BstLean.Part262.Row12339
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12339 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12339 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12339 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12339 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12339 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12339) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12339) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12339) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12339) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12339) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12339 * (160 : ℝ) ^ 2 + 26 / (10 * 12339) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12339) : ℝ)) (tA 12339 * 160 ^ 2 + 26 / (10 * 12339)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12339) : ℝ)) d.D d.V d.P (√(tA 12339) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12339) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12339) : ℝ)) (tA 12339 * 160 ^ 2 + 26 / (10 * 12339)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12339) : ℝ)) (√(26 / (10 * 12339) : ℝ)) d.D d.V d.P (√(tA 12339) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12339) * 160) ≤ _
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

end BstLean.Part262.Row12339

namespace BstLean.Part262.Row12339
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12339 160 ∧
    0 ≤ (tableEnvelope C).f1 12339 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12339 160 ∧
    0 ≤ (tableEnvelope C).w1 12339 160 ∧ 0 ≤ (tableEnvelope C).w2 12339 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12339 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12339 160 ∧ 0 ≤ d.f1 12339 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12339 160 ∧ 0 ≤ d.w1 12339 160 ∧ 0 ≤ d.w2 12339 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12339 ≤ 2 * (228 / 100 : ℝ) / 12339 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12339 ≤ 2 * (370 / 100 : ℝ) / 12339 := by
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
    (completeRAData (tableEnvelope C) 12339 160).locationBound 12339 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12339 160).energyBound 12339 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12339 160) (d.f1 12339 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12339 160) (d.w1 12339 160)
      (d.w2 12339 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12339 160) (d.f1 12339 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12339 160) (d.f1 12339 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12339 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12339 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12339 160) (d.f1 12339 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12339 160) (d.w1 12339 160) (d.w2 12339 160)
  have hwexpr0 : 0 ≤ d.w0 12339 160 + d.w1 12339 160 * √(π / 2) +
      2 * d.w2 12339 160 + energyR16 12339 *
      radiusPolynomialRoot16 (d.w0 12339 160) (d.w1 12339 160) (d.w2 12339 160) := by
    positivity
  constructor
  · change (12339 : ℝ) ^ 8 * (mA 12339 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12339 160) (d.f1 12339 160) d.f2 + locationR16 12339 *
        radiusPolynomialRoot16 (d.f0 12339 160) (d.f1 12339 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12339 : ℝ) ^ 8 * (mA 12339 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12339) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12339 : ℝ) ^ 16 *
      (d.w0 12339 160 + d.w1 12339 160 * √(π / 2) + 2 * d.w2 12339 160 +
        energyR16 12339 * radiusPolynomialRoot16 (d.w0 12339 160) (d.w1 12339 160)
          (d.w2 12339 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12339 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12339) *
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

end BstLean.Part262.Row12339

/-! A coarse bound on the actual paper statistics constant at dimension 12340. -/
namespace BstLean.Part262.Row12340
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12338 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12338 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12338 128 ≤ (12592 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12592 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12340) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12340 : ℕ))
    (by norm_num : (12340 : ℕ) ≤ 16384)
  have ht : paperTail256 12340 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12340 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12340 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12340 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12340 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12340 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12338 128 * √(2 / (12340 : ℝ)) *
      (√(12340 : ℝ) + paperT0 12340 + paperTail256 12340) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12340 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12340 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12340 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12338 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12338 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12340 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12340

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12340
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12340 (61 / 100) 160 (17 / (100 * 12340)) (26 / (10 * 12340)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12340 (61 / 100) 160 (17 / (100 * 12340)) := by
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
          (8 * tA 12340 / 12340 * (61 / 100)) ^ 4 * inverseRadius8 (12340 - 1) /
            envelopeGap 12340 (61 / 100) 160 (17 / (100 * 12340)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12340

namespace BstLean.Part262.Row12340
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12340 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12340 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12340 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12340 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12340 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12340) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12340) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12340) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12340) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12340) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12340 * (160 : ℝ) ^ 2 + 26 / (10 * 12340) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12340) : ℝ)) (tA 12340 * 160 ^ 2 + 26 / (10 * 12340)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12340) : ℝ)) d.D d.V d.P (√(tA 12340) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12340) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12340) : ℝ)) (tA 12340 * 160 ^ 2 + 26 / (10 * 12340)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12340) : ℝ)) (√(26 / (10 * 12340) : ℝ)) d.D d.V d.P (√(tA 12340) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12340) * 160) ≤ _
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

end BstLean.Part262.Row12340

namespace BstLean.Part262.Row12340
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12340 160 ∧
    0 ≤ (tableEnvelope C).f1 12340 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12340 160 ∧
    0 ≤ (tableEnvelope C).w1 12340 160 ∧ 0 ≤ (tableEnvelope C).w2 12340 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12340 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12340 160 ∧ 0 ≤ d.f1 12340 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12340 160 ∧ 0 ≤ d.w1 12340 160 ∧ 0 ≤ d.w2 12340 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12340 ≤ 2 * (228 / 100 : ℝ) / 12340 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12340 ≤ 2 * (370 / 100 : ℝ) / 12340 := by
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
    (completeRAData (tableEnvelope C) 12340 160).locationBound 12340 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12340 160).energyBound 12340 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12340 160) (d.f1 12340 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12340 160) (d.w1 12340 160)
      (d.w2 12340 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12340 160) (d.f1 12340 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12340 160) (d.f1 12340 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12340 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12340 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12340 160) (d.f1 12340 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12340 160) (d.w1 12340 160) (d.w2 12340 160)
  have hwexpr0 : 0 ≤ d.w0 12340 160 + d.w1 12340 160 * √(π / 2) +
      2 * d.w2 12340 160 + energyR16 12340 *
      radiusPolynomialRoot16 (d.w0 12340 160) (d.w1 12340 160) (d.w2 12340 160) := by
    positivity
  constructor
  · change (12340 : ℝ) ^ 8 * (mA 12340 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12340 160) (d.f1 12340 160) d.f2 + locationR16 12340 *
        radiusPolynomialRoot16 (d.f0 12340 160) (d.f1 12340 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12340 : ℝ) ^ 8 * (mA 12340 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12340) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12340 : ℝ) ^ 16 *
      (d.w0 12340 160 + d.w1 12340 160 * √(π / 2) + 2 * d.w2 12340 160 +
        energyR16 12340 * radiusPolynomialRoot16 (d.w0 12340 160) (d.w1 12340 160)
          (d.w2 12340 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12340 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12340) *
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

end BstLean.Part262.Row12340

/-! A coarse bound on the actual paper statistics constant at dimension 12341. -/
namespace BstLean.Part262.Row12341
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12339 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12339 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12339 128 ≤ (12593 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12593 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12341) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12341 : ℕ))
    (by norm_num : (12341 : ℕ) ≤ 16384)
  have ht : paperTail256 12341 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12341 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12341 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12341 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12341 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12341 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12339 128 * √(2 / (12341 : ℝ)) *
      (√(12341 : ℝ) + paperT0 12341 + paperTail256 12341) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12341 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12341 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12341 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12339 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12339 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12341 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12341

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12341
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12341 (61 / 100) 160 (17 / (100 * 12341)) (26 / (10 * 12341)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12341 (61 / 100) 160 (17 / (100 * 12341)) := by
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
          (8 * tA 12341 / 12341 * (61 / 100)) ^ 4 * inverseRadius8 (12341 - 1) /
            envelopeGap 12341 (61 / 100) 160 (17 / (100 * 12341)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12341

namespace BstLean.Part262.Row12341
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12341 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12341 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12341 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12341 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12341 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12341) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12341) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12341) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12341) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12341) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12341 * (160 : ℝ) ^ 2 + 26 / (10 * 12341) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12341) : ℝ)) (tA 12341 * 160 ^ 2 + 26 / (10 * 12341)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12341) : ℝ)) d.D d.V d.P (√(tA 12341) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12341) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12341) : ℝ)) (tA 12341 * 160 ^ 2 + 26 / (10 * 12341)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12341) : ℝ)) (√(26 / (10 * 12341) : ℝ)) d.D d.V d.P (√(tA 12341) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12341) * 160) ≤ _
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

end BstLean.Part262.Row12341

namespace BstLean.Part262.Row12341
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12341 160 ∧
    0 ≤ (tableEnvelope C).f1 12341 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12341 160 ∧
    0 ≤ (tableEnvelope C).w1 12341 160 ∧ 0 ≤ (tableEnvelope C).w2 12341 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12341 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12341 160 ∧ 0 ≤ d.f1 12341 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12341 160 ∧ 0 ≤ d.w1 12341 160 ∧ 0 ≤ d.w2 12341 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12341 ≤ 2 * (228 / 100 : ℝ) / 12341 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12341 ≤ 2 * (370 / 100 : ℝ) / 12341 := by
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
    (completeRAData (tableEnvelope C) 12341 160).locationBound 12341 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12341 160).energyBound 12341 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12341 160) (d.f1 12341 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12341 160) (d.w1 12341 160)
      (d.w2 12341 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12341 160) (d.f1 12341 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12341 160) (d.f1 12341 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12341 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12341 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12341 160) (d.f1 12341 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12341 160) (d.w1 12341 160) (d.w2 12341 160)
  have hwexpr0 : 0 ≤ d.w0 12341 160 + d.w1 12341 160 * √(π / 2) +
      2 * d.w2 12341 160 + energyR16 12341 *
      radiusPolynomialRoot16 (d.w0 12341 160) (d.w1 12341 160) (d.w2 12341 160) := by
    positivity
  constructor
  · change (12341 : ℝ) ^ 8 * (mA 12341 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12341 160) (d.f1 12341 160) d.f2 + locationR16 12341 *
        radiusPolynomialRoot16 (d.f0 12341 160) (d.f1 12341 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12341 : ℝ) ^ 8 * (mA 12341 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12341) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12341 : ℝ) ^ 16 *
      (d.w0 12341 160 + d.w1 12341 160 * √(π / 2) + 2 * d.w2 12341 160 +
        energyR16 12341 * radiusPolynomialRoot16 (d.w0 12341 160) (d.w1 12341 160)
          (d.w2 12341 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12341 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12341) *
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

end BstLean.Part262.Row12341

/-! A coarse bound on the actual paper statistics constant at dimension 12342. -/
namespace BstLean.Part262.Row12342
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12340 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12340 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12340 128 ≤ (12594 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12594 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12342) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12342 : ℕ))
    (by norm_num : (12342 : ℕ) ≤ 16384)
  have ht : paperTail256 12342 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12342 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12342 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12342 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12342 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12342 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12340 128 * √(2 / (12342 : ℝ)) *
      (√(12342 : ℝ) + paperT0 12342 + paperTail256 12342) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12342 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12342 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12342 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12340 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12340 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12342 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12342

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12342
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12342 (61 / 100) 160 (17 / (100 * 12342)) (26 / (10 * 12342)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12342 (61 / 100) 160 (17 / (100 * 12342)) := by
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
          (8 * tA 12342 / 12342 * (61 / 100)) ^ 4 * inverseRadius8 (12342 - 1) /
            envelopeGap 12342 (61 / 100) 160 (17 / (100 * 12342)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12342

namespace BstLean.Part262.Row12342
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12342 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12342 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12342 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12342 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12342 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12342) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12342) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12342) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12342) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12342) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12342 * (160 : ℝ) ^ 2 + 26 / (10 * 12342) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12342) : ℝ)) (tA 12342 * 160 ^ 2 + 26 / (10 * 12342)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12342) : ℝ)) d.D d.V d.P (√(tA 12342) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12342) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12342) : ℝ)) (tA 12342 * 160 ^ 2 + 26 / (10 * 12342)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12342) : ℝ)) (√(26 / (10 * 12342) : ℝ)) d.D d.V d.P (√(tA 12342) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12342) * 160) ≤ _
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

end BstLean.Part262.Row12342

namespace BstLean.Part262.Row12342
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12342 160 ∧
    0 ≤ (tableEnvelope C).f1 12342 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12342 160 ∧
    0 ≤ (tableEnvelope C).w1 12342 160 ∧ 0 ≤ (tableEnvelope C).w2 12342 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12342 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12342 160 ∧ 0 ≤ d.f1 12342 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12342 160 ∧ 0 ≤ d.w1 12342 160 ∧ 0 ≤ d.w2 12342 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12342 ≤ 2 * (228 / 100 : ℝ) / 12342 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12342 ≤ 2 * (370 / 100 : ℝ) / 12342 := by
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
    (completeRAData (tableEnvelope C) 12342 160).locationBound 12342 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12342 160).energyBound 12342 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12342 160) (d.f1 12342 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12342 160) (d.w1 12342 160)
      (d.w2 12342 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12342 160) (d.f1 12342 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12342 160) (d.f1 12342 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12342 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12342 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12342 160) (d.f1 12342 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12342 160) (d.w1 12342 160) (d.w2 12342 160)
  have hwexpr0 : 0 ≤ d.w0 12342 160 + d.w1 12342 160 * √(π / 2) +
      2 * d.w2 12342 160 + energyR16 12342 *
      radiusPolynomialRoot16 (d.w0 12342 160) (d.w1 12342 160) (d.w2 12342 160) := by
    positivity
  constructor
  · change (12342 : ℝ) ^ 8 * (mA 12342 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12342 160) (d.f1 12342 160) d.f2 + locationR16 12342 *
        radiusPolynomialRoot16 (d.f0 12342 160) (d.f1 12342 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12342 : ℝ) ^ 8 * (mA 12342 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12342) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12342 : ℝ) ^ 16 *
      (d.w0 12342 160 + d.w1 12342 160 * √(π / 2) + 2 * d.w2 12342 160 +
        energyR16 12342 * radiusPolynomialRoot16 (d.w0 12342 160) (d.w1 12342 160)
          (d.w2 12342 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12342 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12342) *
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

end BstLean.Part262.Row12342

/-! A coarse bound on the actual paper statistics constant at dimension 12343. -/
namespace BstLean.Part262.Row12343
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12341 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12341 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12341 128 ≤ (12595 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12595 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12343) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12343 : ℕ))
    (by norm_num : (12343 : ℕ) ≤ 16384)
  have ht : paperTail256 12343 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12343 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12343 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12343 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12343 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12343 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12341 128 * √(2 / (12343 : ℝ)) *
      (√(12343 : ℝ) + paperT0 12343 + paperTail256 12343) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12343 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12343 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12343 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12341 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12341 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12343 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12343

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12343
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12343 (61 / 100) 160 (17 / (100 * 12343)) (26 / (10 * 12343)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12343 (61 / 100) 160 (17 / (100 * 12343)) := by
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
          (8 * tA 12343 / 12343 * (61 / 100)) ^ 4 * inverseRadius8 (12343 - 1) /
            envelopeGap 12343 (61 / 100) 160 (17 / (100 * 12343)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12343

namespace BstLean.Part262.Row12343
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12343 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12343 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12343 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12343 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12343 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12343) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12343) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12343) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12343) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12343) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12343 * (160 : ℝ) ^ 2 + 26 / (10 * 12343) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12343) : ℝ)) (tA 12343 * 160 ^ 2 + 26 / (10 * 12343)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12343) : ℝ)) d.D d.V d.P (√(tA 12343) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12343) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12343) : ℝ)) (tA 12343 * 160 ^ 2 + 26 / (10 * 12343)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12343) : ℝ)) (√(26 / (10 * 12343) : ℝ)) d.D d.V d.P (√(tA 12343) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12343) * 160) ≤ _
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

end BstLean.Part262.Row12343

namespace BstLean.Part262.Row12343
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12343 160 ∧
    0 ≤ (tableEnvelope C).f1 12343 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12343 160 ∧
    0 ≤ (tableEnvelope C).w1 12343 160 ∧ 0 ≤ (tableEnvelope C).w2 12343 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12343 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12343 160 ∧ 0 ≤ d.f1 12343 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12343 160 ∧ 0 ≤ d.w1 12343 160 ∧ 0 ≤ d.w2 12343 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12343 ≤ 2 * (228 / 100 : ℝ) / 12343 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12343 ≤ 2 * (370 / 100 : ℝ) / 12343 := by
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
    (completeRAData (tableEnvelope C) 12343 160).locationBound 12343 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12343 160).energyBound 12343 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12343 160) (d.f1 12343 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12343 160) (d.w1 12343 160)
      (d.w2 12343 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12343 160) (d.f1 12343 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12343 160) (d.f1 12343 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12343 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12343 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12343 160) (d.f1 12343 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12343 160) (d.w1 12343 160) (d.w2 12343 160)
  have hwexpr0 : 0 ≤ d.w0 12343 160 + d.w1 12343 160 * √(π / 2) +
      2 * d.w2 12343 160 + energyR16 12343 *
      radiusPolynomialRoot16 (d.w0 12343 160) (d.w1 12343 160) (d.w2 12343 160) := by
    positivity
  constructor
  · change (12343 : ℝ) ^ 8 * (mA 12343 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12343 160) (d.f1 12343 160) d.f2 + locationR16 12343 *
        radiusPolynomialRoot16 (d.f0 12343 160) (d.f1 12343 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12343 : ℝ) ^ 8 * (mA 12343 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12343) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12343 : ℝ) ^ 16 *
      (d.w0 12343 160 + d.w1 12343 160 * √(π / 2) + 2 * d.w2 12343 160 +
        energyR16 12343 * radiusPolynomialRoot16 (d.w0 12343 160) (d.w1 12343 160)
          (d.w2 12343 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12343 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12343) *
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

end BstLean.Part262.Row12343

/-! A coarse bound on the actual paper statistics constant at dimension 12344. -/
namespace BstLean.Part262.Row12344
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12342 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12342 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12342 128 ≤ (12596 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12596 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12344) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12344 : ℕ))
    (by norm_num : (12344 : ℕ) ≤ 16384)
  have ht : paperTail256 12344 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12344 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12344 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12344 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12344 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12344 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12342 128 * √(2 / (12344 : ℝ)) *
      (√(12344 : ℝ) + paperT0 12344 + paperTail256 12344) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12344 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12344 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12344 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12342 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12342 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12344 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12344

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12344
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12344 (61 / 100) 160 (17 / (100 * 12344)) (26 / (10 * 12344)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12344 (61 / 100) 160 (17 / (100 * 12344)) := by
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
          (8 * tA 12344 / 12344 * (61 / 100)) ^ 4 * inverseRadius8 (12344 - 1) /
            envelopeGap 12344 (61 / 100) 160 (17 / (100 * 12344)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12344

namespace BstLean.Part262.Row12344
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12344 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12344 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12344 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12344 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12344 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12344) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12344) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12344) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12344) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12344) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12344 * (160 : ℝ) ^ 2 + 26 / (10 * 12344) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12344) : ℝ)) (tA 12344 * 160 ^ 2 + 26 / (10 * 12344)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12344) : ℝ)) d.D d.V d.P (√(tA 12344) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12344) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12344) : ℝ)) (tA 12344 * 160 ^ 2 + 26 / (10 * 12344)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12344) : ℝ)) (√(26 / (10 * 12344) : ℝ)) d.D d.V d.P (√(tA 12344) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12344) * 160) ≤ _
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

end BstLean.Part262.Row12344

namespace BstLean.Part262.Row12344
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12344 160 ∧
    0 ≤ (tableEnvelope C).f1 12344 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12344 160 ∧
    0 ≤ (tableEnvelope C).w1 12344 160 ∧ 0 ≤ (tableEnvelope C).w2 12344 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12344 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12344 160 ∧ 0 ≤ d.f1 12344 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12344 160 ∧ 0 ≤ d.w1 12344 160 ∧ 0 ≤ d.w2 12344 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12344 ≤ 2 * (228 / 100 : ℝ) / 12344 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12344 ≤ 2 * (370 / 100 : ℝ) / 12344 := by
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
    (completeRAData (tableEnvelope C) 12344 160).locationBound 12344 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12344 160).energyBound 12344 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12344 160) (d.f1 12344 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12344 160) (d.w1 12344 160)
      (d.w2 12344 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12344 160) (d.f1 12344 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12344 160) (d.f1 12344 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12344 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12344 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12344 160) (d.f1 12344 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12344 160) (d.w1 12344 160) (d.w2 12344 160)
  have hwexpr0 : 0 ≤ d.w0 12344 160 + d.w1 12344 160 * √(π / 2) +
      2 * d.w2 12344 160 + energyR16 12344 *
      radiusPolynomialRoot16 (d.w0 12344 160) (d.w1 12344 160) (d.w2 12344 160) := by
    positivity
  constructor
  · change (12344 : ℝ) ^ 8 * (mA 12344 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12344 160) (d.f1 12344 160) d.f2 + locationR16 12344 *
        radiusPolynomialRoot16 (d.f0 12344 160) (d.f1 12344 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12344 : ℝ) ^ 8 * (mA 12344 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12344) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12344 : ℝ) ^ 16 *
      (d.w0 12344 160 + d.w1 12344 160 * √(π / 2) + 2 * d.w2 12344 160 +
        energyR16 12344 * radiusPolynomialRoot16 (d.w0 12344 160) (d.w1 12344 160)
          (d.w2 12344 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12344 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12344) *
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

end BstLean.Part262.Row12344

/-! A coarse bound on the actual paper statistics constant at dimension 12345. -/
namespace BstLean.Part262.Row12345
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12343 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12343 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12343 128 ≤ (12597 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12597 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12345) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12345 : ℕ))
    (by norm_num : (12345 : ℕ) ≤ 16384)
  have ht : paperTail256 12345 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12345 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12345 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12345 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12345 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12345 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12343 128 * √(2 / (12345 : ℝ)) *
      (√(12345 : ℝ) + paperT0 12345 + paperTail256 12345) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12345 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12345 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12345 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12343 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12343 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12345 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12345

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12345
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12345 (61 / 100) 160 (17 / (100 * 12345)) (26 / (10 * 12345)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12345 (61 / 100) 160 (17 / (100 * 12345)) := by
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
          (8 * tA 12345 / 12345 * (61 / 100)) ^ 4 * inverseRadius8 (12345 - 1) /
            envelopeGap 12345 (61 / 100) 160 (17 / (100 * 12345)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12345

namespace BstLean.Part262.Row12345
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12345 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12345 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12345 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12345 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12345 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12345) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12345) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12345) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12345) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12345) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12345 * (160 : ℝ) ^ 2 + 26 / (10 * 12345) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12345) : ℝ)) (tA 12345 * 160 ^ 2 + 26 / (10 * 12345)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12345) : ℝ)) d.D d.V d.P (√(tA 12345) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12345) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12345) : ℝ)) (tA 12345 * 160 ^ 2 + 26 / (10 * 12345)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12345) : ℝ)) (√(26 / (10 * 12345) : ℝ)) d.D d.V d.P (√(tA 12345) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12345) * 160) ≤ _
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

end BstLean.Part262.Row12345

namespace BstLean.Part262.Row12345
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12345 160 ∧
    0 ≤ (tableEnvelope C).f1 12345 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12345 160 ∧
    0 ≤ (tableEnvelope C).w1 12345 160 ∧ 0 ≤ (tableEnvelope C).w2 12345 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12345 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12345 160 ∧ 0 ≤ d.f1 12345 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12345 160 ∧ 0 ≤ d.w1 12345 160 ∧ 0 ≤ d.w2 12345 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12345 ≤ 2 * (228 / 100 : ℝ) / 12345 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12345 ≤ 2 * (370 / 100 : ℝ) / 12345 := by
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
    (completeRAData (tableEnvelope C) 12345 160).locationBound 12345 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12345 160).energyBound 12345 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12345 160) (d.f1 12345 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12345 160) (d.w1 12345 160)
      (d.w2 12345 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12345 160) (d.f1 12345 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12345 160) (d.f1 12345 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12345 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12345 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12345 160) (d.f1 12345 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12345 160) (d.w1 12345 160) (d.w2 12345 160)
  have hwexpr0 : 0 ≤ d.w0 12345 160 + d.w1 12345 160 * √(π / 2) +
      2 * d.w2 12345 160 + energyR16 12345 *
      radiusPolynomialRoot16 (d.w0 12345 160) (d.w1 12345 160) (d.w2 12345 160) := by
    positivity
  constructor
  · change (12345 : ℝ) ^ 8 * (mA 12345 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12345 160) (d.f1 12345 160) d.f2 + locationR16 12345 *
        radiusPolynomialRoot16 (d.f0 12345 160) (d.f1 12345 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12345 : ℝ) ^ 8 * (mA 12345 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12345) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12345 : ℝ) ^ 16 *
      (d.w0 12345 160 + d.w1 12345 160 * √(π / 2) + 2 * d.w2 12345 160 +
        energyR16 12345 * radiusPolynomialRoot16 (d.w0 12345 160) (d.w1 12345 160)
          (d.w2 12345 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12345 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12345) *
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

end BstLean.Part262.Row12345

/-! A coarse bound on the actual paper statistics constant at dimension 12346. -/
namespace BstLean.Part262.Row12346
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12344 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12344 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12344 128 ≤ (12598 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12598 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12346) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12346 : ℕ))
    (by norm_num : (12346 : ℕ) ≤ 16384)
  have ht : paperTail256 12346 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12346 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12346 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12346 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12346 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12346 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12344 128 * √(2 / (12346 : ℝ)) *
      (√(12346 : ℝ) + paperT0 12346 + paperTail256 12346) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12346 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12346 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12346 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12344 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12344 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12346 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12346

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12346
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12346 (61 / 100) 160 (17 / (100 * 12346)) (26 / (10 * 12346)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12346 (61 / 100) 160 (17 / (100 * 12346)) := by
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
          (8 * tA 12346 / 12346 * (61 / 100)) ^ 4 * inverseRadius8 (12346 - 1) /
            envelopeGap 12346 (61 / 100) 160 (17 / (100 * 12346)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12346

namespace BstLean.Part262.Row12346
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12346 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12346 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12346 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12346 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12346 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12346) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12346) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12346) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12346) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12346) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12346 * (160 : ℝ) ^ 2 + 26 / (10 * 12346) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12346) : ℝ)) (tA 12346 * 160 ^ 2 + 26 / (10 * 12346)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12346) : ℝ)) d.D d.V d.P (√(tA 12346) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12346) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12346) : ℝ)) (tA 12346 * 160 ^ 2 + 26 / (10 * 12346)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12346) : ℝ)) (√(26 / (10 * 12346) : ℝ)) d.D d.V d.P (√(tA 12346) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12346) * 160) ≤ _
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

end BstLean.Part262.Row12346

namespace BstLean.Part262.Row12346
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12346 160 ∧
    0 ≤ (tableEnvelope C).f1 12346 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12346 160 ∧
    0 ≤ (tableEnvelope C).w1 12346 160 ∧ 0 ≤ (tableEnvelope C).w2 12346 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12346 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12346 160 ∧ 0 ≤ d.f1 12346 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12346 160 ∧ 0 ≤ d.w1 12346 160 ∧ 0 ≤ d.w2 12346 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12346 ≤ 2 * (228 / 100 : ℝ) / 12346 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12346 ≤ 2 * (370 / 100 : ℝ) / 12346 := by
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
    (completeRAData (tableEnvelope C) 12346 160).locationBound 12346 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12346 160).energyBound 12346 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12346 160) (d.f1 12346 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12346 160) (d.w1 12346 160)
      (d.w2 12346 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12346 160) (d.f1 12346 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12346 160) (d.f1 12346 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12346 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12346 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12346 160) (d.f1 12346 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12346 160) (d.w1 12346 160) (d.w2 12346 160)
  have hwexpr0 : 0 ≤ d.w0 12346 160 + d.w1 12346 160 * √(π / 2) +
      2 * d.w2 12346 160 + energyR16 12346 *
      radiusPolynomialRoot16 (d.w0 12346 160) (d.w1 12346 160) (d.w2 12346 160) := by
    positivity
  constructor
  · change (12346 : ℝ) ^ 8 * (mA 12346 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12346 160) (d.f1 12346 160) d.f2 + locationR16 12346 *
        radiusPolynomialRoot16 (d.f0 12346 160) (d.f1 12346 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12346 : ℝ) ^ 8 * (mA 12346 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12346) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12346 : ℝ) ^ 16 *
      (d.w0 12346 160 + d.w1 12346 160 * √(π / 2) + 2 * d.w2 12346 160 +
        energyR16 12346 * radiusPolynomialRoot16 (d.w0 12346 160) (d.w1 12346 160)
          (d.w2 12346 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12346 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12346) *
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

end BstLean.Part262.Row12346

/-! A coarse bound on the actual paper statistics constant at dimension 12347. -/
namespace BstLean.Part262.Row12347
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12345 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12345 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12345 128 ≤ (12599 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12599 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12347) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12347 : ℕ))
    (by norm_num : (12347 : ℕ) ≤ 16384)
  have ht : paperTail256 12347 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12347 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12347 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12347 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12347 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12347 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12345 128 * √(2 / (12347 : ℝ)) *
      (√(12347 : ℝ) + paperT0 12347 + paperTail256 12347) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12347 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12347 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12347 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12345 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12345 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12347 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12347

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12347
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12347 (61 / 100) 160 (17 / (100 * 12347)) (26 / (10 * 12347)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12347 (61 / 100) 160 (17 / (100 * 12347)) := by
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
          (8 * tA 12347 / 12347 * (61 / 100)) ^ 4 * inverseRadius8 (12347 - 1) /
            envelopeGap 12347 (61 / 100) 160 (17 / (100 * 12347)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12347

namespace BstLean.Part262.Row12347
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12347 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12347 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12347 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12347 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12347 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12347) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12347) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12347) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12347) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12347) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12347 * (160 : ℝ) ^ 2 + 26 / (10 * 12347) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12347) : ℝ)) (tA 12347 * 160 ^ 2 + 26 / (10 * 12347)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12347) : ℝ)) d.D d.V d.P (√(tA 12347) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12347) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12347) : ℝ)) (tA 12347 * 160 ^ 2 + 26 / (10 * 12347)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12347) : ℝ)) (√(26 / (10 * 12347) : ℝ)) d.D d.V d.P (√(tA 12347) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12347) * 160) ≤ _
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

end BstLean.Part262.Row12347

namespace BstLean.Part262.Row12347
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12347 160 ∧
    0 ≤ (tableEnvelope C).f1 12347 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12347 160 ∧
    0 ≤ (tableEnvelope C).w1 12347 160 ∧ 0 ≤ (tableEnvelope C).w2 12347 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12347 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12347 160 ∧ 0 ≤ d.f1 12347 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12347 160 ∧ 0 ≤ d.w1 12347 160 ∧ 0 ≤ d.w2 12347 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12347 ≤ 2 * (228 / 100 : ℝ) / 12347 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12347 ≤ 2 * (370 / 100 : ℝ) / 12347 := by
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
    (completeRAData (tableEnvelope C) 12347 160).locationBound 12347 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12347 160).energyBound 12347 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12347 160) (d.f1 12347 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12347 160) (d.w1 12347 160)
      (d.w2 12347 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12347 160) (d.f1 12347 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12347 160) (d.f1 12347 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12347 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12347 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12347 160) (d.f1 12347 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12347 160) (d.w1 12347 160) (d.w2 12347 160)
  have hwexpr0 : 0 ≤ d.w0 12347 160 + d.w1 12347 160 * √(π / 2) +
      2 * d.w2 12347 160 + energyR16 12347 *
      radiusPolynomialRoot16 (d.w0 12347 160) (d.w1 12347 160) (d.w2 12347 160) := by
    positivity
  constructor
  · change (12347 : ℝ) ^ 8 * (mA 12347 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12347 160) (d.f1 12347 160) d.f2 + locationR16 12347 *
        radiusPolynomialRoot16 (d.f0 12347 160) (d.f1 12347 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12347 : ℝ) ^ 8 * (mA 12347 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12347) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12347 : ℝ) ^ 16 *
      (d.w0 12347 160 + d.w1 12347 160 * √(π / 2) + 2 * d.w2 12347 160 +
        energyR16 12347 * radiusPolynomialRoot16 (d.w0 12347 160) (d.w1 12347 160)
          (d.w2 12347 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12347 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12347) *
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

end BstLean.Part262.Row12347

/-! A coarse bound on the actual paper statistics constant at dimension 12348. -/
namespace BstLean.Part262.Row12348
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12346 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12346 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12346 128 ≤ (12600 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12600 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12348) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12348 : ℕ))
    (by norm_num : (12348 : ℕ) ≤ 16384)
  have ht : paperTail256 12348 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12348 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12348 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12348 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12348 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12348 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12346 128 * √(2 / (12348 : ℝ)) *
      (√(12348 : ℝ) + paperT0 12348 + paperTail256 12348) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12348 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12348 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12348 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12346 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12346 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12348 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12348

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12348
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12348 (61 / 100) 160 (17 / (100 * 12348)) (26 / (10 * 12348)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12348 (61 / 100) 160 (17 / (100 * 12348)) := by
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
          (8 * tA 12348 / 12348 * (61 / 100)) ^ 4 * inverseRadius8 (12348 - 1) /
            envelopeGap 12348 (61 / 100) 160 (17 / (100 * 12348)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12348

namespace BstLean.Part262.Row12348
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12348 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12348 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12348 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12348 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12348 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12348) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12348) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12348) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12348) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12348) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12348 * (160 : ℝ) ^ 2 + 26 / (10 * 12348) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12348) : ℝ)) (tA 12348 * 160 ^ 2 + 26 / (10 * 12348)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12348) : ℝ)) d.D d.V d.P (√(tA 12348) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12348) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12348) : ℝ)) (tA 12348 * 160 ^ 2 + 26 / (10 * 12348)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12348) : ℝ)) (√(26 / (10 * 12348) : ℝ)) d.D d.V d.P (√(tA 12348) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12348) * 160) ≤ _
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

end BstLean.Part262.Row12348

namespace BstLean.Part262.Row12348
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12348 160 ∧
    0 ≤ (tableEnvelope C).f1 12348 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12348 160 ∧
    0 ≤ (tableEnvelope C).w1 12348 160 ∧ 0 ≤ (tableEnvelope C).w2 12348 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12348 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12348 160 ∧ 0 ≤ d.f1 12348 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12348 160 ∧ 0 ≤ d.w1 12348 160 ∧ 0 ≤ d.w2 12348 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12348 ≤ 2 * (228 / 100 : ℝ) / 12348 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12348 ≤ 2 * (370 / 100 : ℝ) / 12348 := by
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
    (completeRAData (tableEnvelope C) 12348 160).locationBound 12348 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12348 160).energyBound 12348 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12348 160) (d.f1 12348 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12348 160) (d.w1 12348 160)
      (d.w2 12348 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12348 160) (d.f1 12348 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12348 160) (d.f1 12348 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12348 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12348 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12348 160) (d.f1 12348 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12348 160) (d.w1 12348 160) (d.w2 12348 160)
  have hwexpr0 : 0 ≤ d.w0 12348 160 + d.w1 12348 160 * √(π / 2) +
      2 * d.w2 12348 160 + energyR16 12348 *
      radiusPolynomialRoot16 (d.w0 12348 160) (d.w1 12348 160) (d.w2 12348 160) := by
    positivity
  constructor
  · change (12348 : ℝ) ^ 8 * (mA 12348 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12348 160) (d.f1 12348 160) d.f2 + locationR16 12348 *
        radiusPolynomialRoot16 (d.f0 12348 160) (d.f1 12348 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12348 : ℝ) ^ 8 * (mA 12348 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12348) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12348 : ℝ) ^ 16 *
      (d.w0 12348 160 + d.w1 12348 160 * √(π / 2) + 2 * d.w2 12348 160 +
        energyR16 12348 * radiusPolynomialRoot16 (d.w0 12348 160) (d.w1 12348 160)
          (d.w2 12348 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12348 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12348) *
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

end BstLean.Part262.Row12348
