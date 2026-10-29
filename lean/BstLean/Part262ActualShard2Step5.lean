import BstLean.Part262ActualShard2Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12275. -/
namespace BstLean.Part262.Row12275
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12273 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12273 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12273 128 ≤ (12527 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12527 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12275) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12275 : ℕ))
    (by norm_num : (12275 : ℕ) ≤ 16384)
  have ht : paperTail256 12275 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12275 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12275 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12275 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12275 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12275 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12273 128 * √(2 / (12275 : ℝ)) *
      (√(12275 : ℝ) + paperT0 12275 + paperTail256 12275) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12275 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12275 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12275 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12273 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12273 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12275 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12275

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12275
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12275 (61 / 100) 160 (17 / (100 * 12275)) (26 / (10 * 12275)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12275 (61 / 100) 160 (17 / (100 * 12275)) := by
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
          (8 * tA 12275 / 12275 * (61 / 100)) ^ 4 * inverseRadius8 (12275 - 1) /
            envelopeGap 12275 (61 / 100) 160 (17 / (100 * 12275)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12275

namespace BstLean.Part262.Row12275
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12275 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12275 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12275 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12275 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12275 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12275) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12275) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12275) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12275) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12275) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12275 * (160 : ℝ) ^ 2 + 26 / (10 * 12275) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12275) : ℝ)) (tA 12275 * 160 ^ 2 + 26 / (10 * 12275)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12275) : ℝ)) d.D d.V d.P (√(tA 12275) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12275) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12275) : ℝ)) (tA 12275 * 160 ^ 2 + 26 / (10 * 12275)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12275) : ℝ)) (√(26 / (10 * 12275) : ℝ)) d.D d.V d.P (√(tA 12275) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12275) * 160) ≤ _
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

end BstLean.Part262.Row12275

namespace BstLean.Part262.Row12275
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12275 160 ∧
    0 ≤ (tableEnvelope C).f1 12275 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12275 160 ∧
    0 ≤ (tableEnvelope C).w1 12275 160 ∧ 0 ≤ (tableEnvelope C).w2 12275 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12275 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12275 160 ∧ 0 ≤ d.f1 12275 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12275 160 ∧ 0 ≤ d.w1 12275 160 ∧ 0 ≤ d.w2 12275 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12275 ≤ 2 * (228 / 100 : ℝ) / 12275 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12275 ≤ 2 * (370 / 100 : ℝ) / 12275 := by
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
    (completeRAData (tableEnvelope C) 12275 160).locationBound 12275 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12275 160).energyBound 12275 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12275 160) (d.f1 12275 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12275 160) (d.w1 12275 160)
      (d.w2 12275 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12275 160) (d.f1 12275 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12275 160) (d.f1 12275 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12275 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12275 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12275 160) (d.f1 12275 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12275 160) (d.w1 12275 160) (d.w2 12275 160)
  have hwexpr0 : 0 ≤ d.w0 12275 160 + d.w1 12275 160 * √(π / 2) +
      2 * d.w2 12275 160 + energyR16 12275 *
      radiusPolynomialRoot16 (d.w0 12275 160) (d.w1 12275 160) (d.w2 12275 160) := by
    positivity
  constructor
  · change (12275 : ℝ) ^ 8 * (mA 12275 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12275 160) (d.f1 12275 160) d.f2 + locationR16 12275 *
        radiusPolynomialRoot16 (d.f0 12275 160) (d.f1 12275 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12275 : ℝ) ^ 8 * (mA 12275 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12275) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12275 : ℝ) ^ 16 *
      (d.w0 12275 160 + d.w1 12275 160 * √(π / 2) + 2 * d.w2 12275 160 +
        energyR16 12275 * radiusPolynomialRoot16 (d.w0 12275 160) (d.w1 12275 160)
          (d.w2 12275 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12275 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12275) *
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

end BstLean.Part262.Row12275

/-! A coarse bound on the actual paper statistics constant at dimension 12276. -/
namespace BstLean.Part262.Row12276
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12274 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12274 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12274 128 ≤ (12528 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12528 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12276) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12276 : ℕ))
    (by norm_num : (12276 : ℕ) ≤ 16384)
  have ht : paperTail256 12276 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12276 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12276 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12276 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12276 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12276 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12274 128 * √(2 / (12276 : ℝ)) *
      (√(12276 : ℝ) + paperT0 12276 + paperTail256 12276) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12276 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12276 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12276 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12274 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12274 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12276 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12276

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12276
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12276 (61 / 100) 160 (17 / (100 * 12276)) (26 / (10 * 12276)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12276 (61 / 100) 160 (17 / (100 * 12276)) := by
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
          (8 * tA 12276 / 12276 * (61 / 100)) ^ 4 * inverseRadius8 (12276 - 1) /
            envelopeGap 12276 (61 / 100) 160 (17 / (100 * 12276)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12276

namespace BstLean.Part262.Row12276
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12276 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12276 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12276 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12276 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12276 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12276) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12276) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12276) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12276) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12276) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12276 * (160 : ℝ) ^ 2 + 26 / (10 * 12276) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12276) : ℝ)) (tA 12276 * 160 ^ 2 + 26 / (10 * 12276)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12276) : ℝ)) d.D d.V d.P (√(tA 12276) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12276) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12276) : ℝ)) (tA 12276 * 160 ^ 2 + 26 / (10 * 12276)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12276) : ℝ)) (√(26 / (10 * 12276) : ℝ)) d.D d.V d.P (√(tA 12276) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12276) * 160) ≤ _
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

end BstLean.Part262.Row12276

namespace BstLean.Part262.Row12276
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12276 160 ∧
    0 ≤ (tableEnvelope C).f1 12276 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12276 160 ∧
    0 ≤ (tableEnvelope C).w1 12276 160 ∧ 0 ≤ (tableEnvelope C).w2 12276 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12276 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12276 160 ∧ 0 ≤ d.f1 12276 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12276 160 ∧ 0 ≤ d.w1 12276 160 ∧ 0 ≤ d.w2 12276 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12276 ≤ 2 * (228 / 100 : ℝ) / 12276 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12276 ≤ 2 * (370 / 100 : ℝ) / 12276 := by
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
    (completeRAData (tableEnvelope C) 12276 160).locationBound 12276 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12276 160).energyBound 12276 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12276 160) (d.f1 12276 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12276 160) (d.w1 12276 160)
      (d.w2 12276 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12276 160) (d.f1 12276 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12276 160) (d.f1 12276 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12276 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12276 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12276 160) (d.f1 12276 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12276 160) (d.w1 12276 160) (d.w2 12276 160)
  have hwexpr0 : 0 ≤ d.w0 12276 160 + d.w1 12276 160 * √(π / 2) +
      2 * d.w2 12276 160 + energyR16 12276 *
      radiusPolynomialRoot16 (d.w0 12276 160) (d.w1 12276 160) (d.w2 12276 160) := by
    positivity
  constructor
  · change (12276 : ℝ) ^ 8 * (mA 12276 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12276 160) (d.f1 12276 160) d.f2 + locationR16 12276 *
        radiusPolynomialRoot16 (d.f0 12276 160) (d.f1 12276 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12276 : ℝ) ^ 8 * (mA 12276 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12276) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12276 : ℝ) ^ 16 *
      (d.w0 12276 160 + d.w1 12276 160 * √(π / 2) + 2 * d.w2 12276 160 +
        energyR16 12276 * radiusPolynomialRoot16 (d.w0 12276 160) (d.w1 12276 160)
          (d.w2 12276 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12276 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12276) *
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

end BstLean.Part262.Row12276

/-! A coarse bound on the actual paper statistics constant at dimension 12277. -/
namespace BstLean.Part262.Row12277
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12275 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12275 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12275 128 ≤ (12529 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12529 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12277) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12277 : ℕ))
    (by norm_num : (12277 : ℕ) ≤ 16384)
  have ht : paperTail256 12277 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12277 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12277 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12277 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12277 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12277 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12275 128 * √(2 / (12277 : ℝ)) *
      (√(12277 : ℝ) + paperT0 12277 + paperTail256 12277) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12277 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12277 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12277 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12275 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12275 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12277 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12277

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12277
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12277 (61 / 100) 160 (17 / (100 * 12277)) (26 / (10 * 12277)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12277 (61 / 100) 160 (17 / (100 * 12277)) := by
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
          (8 * tA 12277 / 12277 * (61 / 100)) ^ 4 * inverseRadius8 (12277 - 1) /
            envelopeGap 12277 (61 / 100) 160 (17 / (100 * 12277)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12277

namespace BstLean.Part262.Row12277
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12277 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12277 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12277 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12277 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12277 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12277) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12277) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12277) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12277) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12277) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12277 * (160 : ℝ) ^ 2 + 26 / (10 * 12277) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12277) : ℝ)) (tA 12277 * 160 ^ 2 + 26 / (10 * 12277)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12277) : ℝ)) d.D d.V d.P (√(tA 12277) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12277) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12277) : ℝ)) (tA 12277 * 160 ^ 2 + 26 / (10 * 12277)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12277) : ℝ)) (√(26 / (10 * 12277) : ℝ)) d.D d.V d.P (√(tA 12277) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12277) * 160) ≤ _
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

end BstLean.Part262.Row12277

namespace BstLean.Part262.Row12277
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12277 160 ∧
    0 ≤ (tableEnvelope C).f1 12277 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12277 160 ∧
    0 ≤ (tableEnvelope C).w1 12277 160 ∧ 0 ≤ (tableEnvelope C).w2 12277 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12277 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12277 160 ∧ 0 ≤ d.f1 12277 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12277 160 ∧ 0 ≤ d.w1 12277 160 ∧ 0 ≤ d.w2 12277 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12277 ≤ 2 * (228 / 100 : ℝ) / 12277 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12277 ≤ 2 * (370 / 100 : ℝ) / 12277 := by
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
    (completeRAData (tableEnvelope C) 12277 160).locationBound 12277 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12277 160).energyBound 12277 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12277 160) (d.f1 12277 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12277 160) (d.w1 12277 160)
      (d.w2 12277 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12277 160) (d.f1 12277 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12277 160) (d.f1 12277 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12277 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12277 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12277 160) (d.f1 12277 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12277 160) (d.w1 12277 160) (d.w2 12277 160)
  have hwexpr0 : 0 ≤ d.w0 12277 160 + d.w1 12277 160 * √(π / 2) +
      2 * d.w2 12277 160 + energyR16 12277 *
      radiusPolynomialRoot16 (d.w0 12277 160) (d.w1 12277 160) (d.w2 12277 160) := by
    positivity
  constructor
  · change (12277 : ℝ) ^ 8 * (mA 12277 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12277 160) (d.f1 12277 160) d.f2 + locationR16 12277 *
        radiusPolynomialRoot16 (d.f0 12277 160) (d.f1 12277 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12277 : ℝ) ^ 8 * (mA 12277 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12277) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12277 : ℝ) ^ 16 *
      (d.w0 12277 160 + d.w1 12277 160 * √(π / 2) + 2 * d.w2 12277 160 +
        energyR16 12277 * radiusPolynomialRoot16 (d.w0 12277 160) (d.w1 12277 160)
          (d.w2 12277 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12277 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12277) *
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

end BstLean.Part262.Row12277

/-! A coarse bound on the actual paper statistics constant at dimension 12278. -/
namespace BstLean.Part262.Row12278
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12276 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12276 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12276 128 ≤ (12530 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12530 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12278) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12278 : ℕ))
    (by norm_num : (12278 : ℕ) ≤ 16384)
  have ht : paperTail256 12278 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12278 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12278 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12278 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12278 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12278 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12276 128 * √(2 / (12278 : ℝ)) *
      (√(12278 : ℝ) + paperT0 12278 + paperTail256 12278) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12278 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12278 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12278 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12276 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12276 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12278 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12278

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12278
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12278 (61 / 100) 160 (17 / (100 * 12278)) (26 / (10 * 12278)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12278 (61 / 100) 160 (17 / (100 * 12278)) := by
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
          (8 * tA 12278 / 12278 * (61 / 100)) ^ 4 * inverseRadius8 (12278 - 1) /
            envelopeGap 12278 (61 / 100) 160 (17 / (100 * 12278)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12278

namespace BstLean.Part262.Row12278
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12278 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12278 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12278 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12278 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12278 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12278) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12278) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12278) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12278) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12278) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12278 * (160 : ℝ) ^ 2 + 26 / (10 * 12278) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12278) : ℝ)) (tA 12278 * 160 ^ 2 + 26 / (10 * 12278)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12278) : ℝ)) d.D d.V d.P (√(tA 12278) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12278) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12278) : ℝ)) (tA 12278 * 160 ^ 2 + 26 / (10 * 12278)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12278) : ℝ)) (√(26 / (10 * 12278) : ℝ)) d.D d.V d.P (√(tA 12278) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12278) * 160) ≤ _
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

end BstLean.Part262.Row12278

namespace BstLean.Part262.Row12278
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12278 160 ∧
    0 ≤ (tableEnvelope C).f1 12278 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12278 160 ∧
    0 ≤ (tableEnvelope C).w1 12278 160 ∧ 0 ≤ (tableEnvelope C).w2 12278 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12278 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12278 160 ∧ 0 ≤ d.f1 12278 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12278 160 ∧ 0 ≤ d.w1 12278 160 ∧ 0 ≤ d.w2 12278 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12278 ≤ 2 * (228 / 100 : ℝ) / 12278 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12278 ≤ 2 * (370 / 100 : ℝ) / 12278 := by
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
    (completeRAData (tableEnvelope C) 12278 160).locationBound 12278 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12278 160).energyBound 12278 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12278 160) (d.f1 12278 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12278 160) (d.w1 12278 160)
      (d.w2 12278 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12278 160) (d.f1 12278 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12278 160) (d.f1 12278 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12278 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12278 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12278 160) (d.f1 12278 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12278 160) (d.w1 12278 160) (d.w2 12278 160)
  have hwexpr0 : 0 ≤ d.w0 12278 160 + d.w1 12278 160 * √(π / 2) +
      2 * d.w2 12278 160 + energyR16 12278 *
      radiusPolynomialRoot16 (d.w0 12278 160) (d.w1 12278 160) (d.w2 12278 160) := by
    positivity
  constructor
  · change (12278 : ℝ) ^ 8 * (mA 12278 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12278 160) (d.f1 12278 160) d.f2 + locationR16 12278 *
        radiusPolynomialRoot16 (d.f0 12278 160) (d.f1 12278 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12278 : ℝ) ^ 8 * (mA 12278 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12278) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12278 : ℝ) ^ 16 *
      (d.w0 12278 160 + d.w1 12278 160 * √(π / 2) + 2 * d.w2 12278 160 +
        energyR16 12278 * radiusPolynomialRoot16 (d.w0 12278 160) (d.w1 12278 160)
          (d.w2 12278 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12278 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12278) *
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

end BstLean.Part262.Row12278

/-! A coarse bound on the actual paper statistics constant at dimension 12279. -/
namespace BstLean.Part262.Row12279
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12277 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12277 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12277 128 ≤ (12531 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12531 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12279) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12279 : ℕ))
    (by norm_num : (12279 : ℕ) ≤ 16384)
  have ht : paperTail256 12279 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12279 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12279 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12279 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12279 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12279 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12277 128 * √(2 / (12279 : ℝ)) *
      (√(12279 : ℝ) + paperT0 12279 + paperTail256 12279) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12279 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12279 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12279 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12277 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12277 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12279 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12279

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12279
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12279 (61 / 100) 160 (17 / (100 * 12279)) (26 / (10 * 12279)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12279 (61 / 100) 160 (17 / (100 * 12279)) := by
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
          (8 * tA 12279 / 12279 * (61 / 100)) ^ 4 * inverseRadius8 (12279 - 1) /
            envelopeGap 12279 (61 / 100) 160 (17 / (100 * 12279)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12279

namespace BstLean.Part262.Row12279
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12279 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12279 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12279 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12279 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12279 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12279) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12279) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12279) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12279) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12279) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12279 * (160 : ℝ) ^ 2 + 26 / (10 * 12279) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12279) : ℝ)) (tA 12279 * 160 ^ 2 + 26 / (10 * 12279)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12279) : ℝ)) d.D d.V d.P (√(tA 12279) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12279) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12279) : ℝ)) (tA 12279 * 160 ^ 2 + 26 / (10 * 12279)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12279) : ℝ)) (√(26 / (10 * 12279) : ℝ)) d.D d.V d.P (√(tA 12279) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12279) * 160) ≤ _
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

end BstLean.Part262.Row12279

namespace BstLean.Part262.Row12279
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12279 160 ∧
    0 ≤ (tableEnvelope C).f1 12279 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12279 160 ∧
    0 ≤ (tableEnvelope C).w1 12279 160 ∧ 0 ≤ (tableEnvelope C).w2 12279 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12279 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12279 160 ∧ 0 ≤ d.f1 12279 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12279 160 ∧ 0 ≤ d.w1 12279 160 ∧ 0 ≤ d.w2 12279 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12279 ≤ 2 * (228 / 100 : ℝ) / 12279 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12279 ≤ 2 * (370 / 100 : ℝ) / 12279 := by
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
    (completeRAData (tableEnvelope C) 12279 160).locationBound 12279 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12279 160).energyBound 12279 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12279 160) (d.f1 12279 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12279 160) (d.w1 12279 160)
      (d.w2 12279 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12279 160) (d.f1 12279 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12279 160) (d.f1 12279 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12279 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12279 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12279 160) (d.f1 12279 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12279 160) (d.w1 12279 160) (d.w2 12279 160)
  have hwexpr0 : 0 ≤ d.w0 12279 160 + d.w1 12279 160 * √(π / 2) +
      2 * d.w2 12279 160 + energyR16 12279 *
      radiusPolynomialRoot16 (d.w0 12279 160) (d.w1 12279 160) (d.w2 12279 160) := by
    positivity
  constructor
  · change (12279 : ℝ) ^ 8 * (mA 12279 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12279 160) (d.f1 12279 160) d.f2 + locationR16 12279 *
        radiusPolynomialRoot16 (d.f0 12279 160) (d.f1 12279 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12279 : ℝ) ^ 8 * (mA 12279 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12279) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12279 : ℝ) ^ 16 *
      (d.w0 12279 160 + d.w1 12279 160 * √(π / 2) + 2 * d.w2 12279 160 +
        energyR16 12279 * radiusPolynomialRoot16 (d.w0 12279 160) (d.w1 12279 160)
          (d.w2 12279 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12279 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12279) *
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

end BstLean.Part262.Row12279

/-! A coarse bound on the actual paper statistics constant at dimension 12280. -/
namespace BstLean.Part262.Row12280
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12278 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12278 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12278 128 ≤ (12532 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12532 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12280) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12280 : ℕ))
    (by norm_num : (12280 : ℕ) ≤ 16384)
  have ht : paperTail256 12280 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12280 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12280 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12280 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12280 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12280 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12278 128 * √(2 / (12280 : ℝ)) *
      (√(12280 : ℝ) + paperT0 12280 + paperTail256 12280) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12280 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12280 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12280 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12278 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12278 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12280 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12280

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12280
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12280 (61 / 100) 160 (17 / (100 * 12280)) (26 / (10 * 12280)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12280 (61 / 100) 160 (17 / (100 * 12280)) := by
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
          (8 * tA 12280 / 12280 * (61 / 100)) ^ 4 * inverseRadius8 (12280 - 1) /
            envelopeGap 12280 (61 / 100) 160 (17 / (100 * 12280)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12280

namespace BstLean.Part262.Row12280
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12280 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12280 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12280 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12280 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12280 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12280) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12280) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12280) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12280) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12280) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12280 * (160 : ℝ) ^ 2 + 26 / (10 * 12280) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12280) : ℝ)) (tA 12280 * 160 ^ 2 + 26 / (10 * 12280)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12280) : ℝ)) d.D d.V d.P (√(tA 12280) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12280) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12280) : ℝ)) (tA 12280 * 160 ^ 2 + 26 / (10 * 12280)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12280) : ℝ)) (√(26 / (10 * 12280) : ℝ)) d.D d.V d.P (√(tA 12280) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12280) * 160) ≤ _
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

end BstLean.Part262.Row12280

namespace BstLean.Part262.Row12280
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12280 160 ∧
    0 ≤ (tableEnvelope C).f1 12280 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12280 160 ∧
    0 ≤ (tableEnvelope C).w1 12280 160 ∧ 0 ≤ (tableEnvelope C).w2 12280 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12280 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12280 160 ∧ 0 ≤ d.f1 12280 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12280 160 ∧ 0 ≤ d.w1 12280 160 ∧ 0 ≤ d.w2 12280 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12280 ≤ 2 * (228 / 100 : ℝ) / 12280 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12280 ≤ 2 * (370 / 100 : ℝ) / 12280 := by
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
    (completeRAData (tableEnvelope C) 12280 160).locationBound 12280 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12280 160).energyBound 12280 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12280 160) (d.f1 12280 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12280 160) (d.w1 12280 160)
      (d.w2 12280 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12280 160) (d.f1 12280 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12280 160) (d.f1 12280 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12280 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12280 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12280 160) (d.f1 12280 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12280 160) (d.w1 12280 160) (d.w2 12280 160)
  have hwexpr0 : 0 ≤ d.w0 12280 160 + d.w1 12280 160 * √(π / 2) +
      2 * d.w2 12280 160 + energyR16 12280 *
      radiusPolynomialRoot16 (d.w0 12280 160) (d.w1 12280 160) (d.w2 12280 160) := by
    positivity
  constructor
  · change (12280 : ℝ) ^ 8 * (mA 12280 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12280 160) (d.f1 12280 160) d.f2 + locationR16 12280 *
        radiusPolynomialRoot16 (d.f0 12280 160) (d.f1 12280 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12280 : ℝ) ^ 8 * (mA 12280 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12280) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12280 : ℝ) ^ 16 *
      (d.w0 12280 160 + d.w1 12280 160 * √(π / 2) + 2 * d.w2 12280 160 +
        energyR16 12280 * radiusPolynomialRoot16 (d.w0 12280 160) (d.w1 12280 160)
          (d.w2 12280 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12280 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12280) *
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

end BstLean.Part262.Row12280

/-! A coarse bound on the actual paper statistics constant at dimension 12281. -/
namespace BstLean.Part262.Row12281
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12279 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12279 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12279 128 ≤ (12533 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12533 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12281) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12281 : ℕ))
    (by norm_num : (12281 : ℕ) ≤ 16384)
  have ht : paperTail256 12281 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12281 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12281 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12281 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12281 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12281 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12279 128 * √(2 / (12281 : ℝ)) *
      (√(12281 : ℝ) + paperT0 12281 + paperTail256 12281) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12281 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12281 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12281 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12279 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12279 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12281 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12281

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12281
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12281 (61 / 100) 160 (17 / (100 * 12281)) (26 / (10 * 12281)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12281 (61 / 100) 160 (17 / (100 * 12281)) := by
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
          (8 * tA 12281 / 12281 * (61 / 100)) ^ 4 * inverseRadius8 (12281 - 1) /
            envelopeGap 12281 (61 / 100) 160 (17 / (100 * 12281)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12281

namespace BstLean.Part262.Row12281
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12281 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12281 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12281 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12281 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12281 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12281) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12281) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12281) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12281) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12281) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12281 * (160 : ℝ) ^ 2 + 26 / (10 * 12281) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12281) : ℝ)) (tA 12281 * 160 ^ 2 + 26 / (10 * 12281)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12281) : ℝ)) d.D d.V d.P (√(tA 12281) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12281) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12281) : ℝ)) (tA 12281 * 160 ^ 2 + 26 / (10 * 12281)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12281) : ℝ)) (√(26 / (10 * 12281) : ℝ)) d.D d.V d.P (√(tA 12281) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12281) * 160) ≤ _
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

end BstLean.Part262.Row12281

namespace BstLean.Part262.Row12281
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12281 160 ∧
    0 ≤ (tableEnvelope C).f1 12281 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12281 160 ∧
    0 ≤ (tableEnvelope C).w1 12281 160 ∧ 0 ≤ (tableEnvelope C).w2 12281 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12281 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12281 160 ∧ 0 ≤ d.f1 12281 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12281 160 ∧ 0 ≤ d.w1 12281 160 ∧ 0 ≤ d.w2 12281 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12281 ≤ 2 * (228 / 100 : ℝ) / 12281 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12281 ≤ 2 * (370 / 100 : ℝ) / 12281 := by
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
    (completeRAData (tableEnvelope C) 12281 160).locationBound 12281 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12281 160).energyBound 12281 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12281 160) (d.f1 12281 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12281 160) (d.w1 12281 160)
      (d.w2 12281 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12281 160) (d.f1 12281 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12281 160) (d.f1 12281 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12281 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12281 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12281 160) (d.f1 12281 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12281 160) (d.w1 12281 160) (d.w2 12281 160)
  have hwexpr0 : 0 ≤ d.w0 12281 160 + d.w1 12281 160 * √(π / 2) +
      2 * d.w2 12281 160 + energyR16 12281 *
      radiusPolynomialRoot16 (d.w0 12281 160) (d.w1 12281 160) (d.w2 12281 160) := by
    positivity
  constructor
  · change (12281 : ℝ) ^ 8 * (mA 12281 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12281 160) (d.f1 12281 160) d.f2 + locationR16 12281 *
        radiusPolynomialRoot16 (d.f0 12281 160) (d.f1 12281 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12281 : ℝ) ^ 8 * (mA 12281 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12281) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12281 : ℝ) ^ 16 *
      (d.w0 12281 160 + d.w1 12281 160 * √(π / 2) + 2 * d.w2 12281 160 +
        energyR16 12281 * radiusPolynomialRoot16 (d.w0 12281 160) (d.w1 12281 160)
          (d.w2 12281 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12281 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12281) *
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

end BstLean.Part262.Row12281

/-! A coarse bound on the actual paper statistics constant at dimension 12282. -/
namespace BstLean.Part262.Row12282
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12280 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12280 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12280 128 ≤ (12534 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12534 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12282) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12282 : ℕ))
    (by norm_num : (12282 : ℕ) ≤ 16384)
  have ht : paperTail256 12282 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12282 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12282 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12282 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12282 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12282 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12280 128 * √(2 / (12282 : ℝ)) *
      (√(12282 : ℝ) + paperT0 12282 + paperTail256 12282) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12282 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12282 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12282 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12280 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12280 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12282 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12282

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12282
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12282 (61 / 100) 160 (17 / (100 * 12282)) (26 / (10 * 12282)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12282 (61 / 100) 160 (17 / (100 * 12282)) := by
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
          (8 * tA 12282 / 12282 * (61 / 100)) ^ 4 * inverseRadius8 (12282 - 1) /
            envelopeGap 12282 (61 / 100) 160 (17 / (100 * 12282)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12282

namespace BstLean.Part262.Row12282
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12282 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12282 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12282 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12282 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12282 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12282) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12282) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12282) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12282) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12282) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12282 * (160 : ℝ) ^ 2 + 26 / (10 * 12282) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12282) : ℝ)) (tA 12282 * 160 ^ 2 + 26 / (10 * 12282)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12282) : ℝ)) d.D d.V d.P (√(tA 12282) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12282) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12282) : ℝ)) (tA 12282 * 160 ^ 2 + 26 / (10 * 12282)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12282) : ℝ)) (√(26 / (10 * 12282) : ℝ)) d.D d.V d.P (√(tA 12282) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12282) * 160) ≤ _
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

end BstLean.Part262.Row12282

namespace BstLean.Part262.Row12282
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12282 160 ∧
    0 ≤ (tableEnvelope C).f1 12282 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12282 160 ∧
    0 ≤ (tableEnvelope C).w1 12282 160 ∧ 0 ≤ (tableEnvelope C).w2 12282 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12282 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12282 160 ∧ 0 ≤ d.f1 12282 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12282 160 ∧ 0 ≤ d.w1 12282 160 ∧ 0 ≤ d.w2 12282 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12282 ≤ 2 * (228 / 100 : ℝ) / 12282 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12282 ≤ 2 * (370 / 100 : ℝ) / 12282 := by
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
    (completeRAData (tableEnvelope C) 12282 160).locationBound 12282 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12282 160).energyBound 12282 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12282 160) (d.f1 12282 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12282 160) (d.w1 12282 160)
      (d.w2 12282 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12282 160) (d.f1 12282 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12282 160) (d.f1 12282 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12282 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12282 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12282 160) (d.f1 12282 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12282 160) (d.w1 12282 160) (d.w2 12282 160)
  have hwexpr0 : 0 ≤ d.w0 12282 160 + d.w1 12282 160 * √(π / 2) +
      2 * d.w2 12282 160 + energyR16 12282 *
      radiusPolynomialRoot16 (d.w0 12282 160) (d.w1 12282 160) (d.w2 12282 160) := by
    positivity
  constructor
  · change (12282 : ℝ) ^ 8 * (mA 12282 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12282 160) (d.f1 12282 160) d.f2 + locationR16 12282 *
        radiusPolynomialRoot16 (d.f0 12282 160) (d.f1 12282 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12282 : ℝ) ^ 8 * (mA 12282 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12282) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12282 : ℝ) ^ 16 *
      (d.w0 12282 160 + d.w1 12282 160 * √(π / 2) + 2 * d.w2 12282 160 +
        energyR16 12282 * radiusPolynomialRoot16 (d.w0 12282 160) (d.w1 12282 160)
          (d.w2 12282 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12282 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12282) *
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

end BstLean.Part262.Row12282

/-! A coarse bound on the actual paper statistics constant at dimension 12283. -/
namespace BstLean.Part262.Row12283
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12281 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12281 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12281 128 ≤ (12535 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12535 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12283) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12283 : ℕ))
    (by norm_num : (12283 : ℕ) ≤ 16384)
  have ht : paperTail256 12283 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12283 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12283 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12283 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12283 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12283 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12281 128 * √(2 / (12283 : ℝ)) *
      (√(12283 : ℝ) + paperT0 12283 + paperTail256 12283) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12283 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12283 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12283 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12281 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12281 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12283 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12283

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12283
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12283 (61 / 100) 160 (17 / (100 * 12283)) (26 / (10 * 12283)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12283 (61 / 100) 160 (17 / (100 * 12283)) := by
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
          (8 * tA 12283 / 12283 * (61 / 100)) ^ 4 * inverseRadius8 (12283 - 1) /
            envelopeGap 12283 (61 / 100) 160 (17 / (100 * 12283)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12283

namespace BstLean.Part262.Row12283
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12283 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12283 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12283 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12283 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12283 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12283) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12283) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12283) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12283) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12283) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12283 * (160 : ℝ) ^ 2 + 26 / (10 * 12283) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12283) : ℝ)) (tA 12283 * 160 ^ 2 + 26 / (10 * 12283)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12283) : ℝ)) d.D d.V d.P (√(tA 12283) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12283) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12283) : ℝ)) (tA 12283 * 160 ^ 2 + 26 / (10 * 12283)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12283) : ℝ)) (√(26 / (10 * 12283) : ℝ)) d.D d.V d.P (√(tA 12283) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12283) * 160) ≤ _
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

end BstLean.Part262.Row12283

namespace BstLean.Part262.Row12283
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12283 160 ∧
    0 ≤ (tableEnvelope C).f1 12283 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12283 160 ∧
    0 ≤ (tableEnvelope C).w1 12283 160 ∧ 0 ≤ (tableEnvelope C).w2 12283 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12283 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12283 160 ∧ 0 ≤ d.f1 12283 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12283 160 ∧ 0 ≤ d.w1 12283 160 ∧ 0 ≤ d.w2 12283 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12283 ≤ 2 * (228 / 100 : ℝ) / 12283 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12283 ≤ 2 * (370 / 100 : ℝ) / 12283 := by
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
    (completeRAData (tableEnvelope C) 12283 160).locationBound 12283 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12283 160).energyBound 12283 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12283 160) (d.f1 12283 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12283 160) (d.w1 12283 160)
      (d.w2 12283 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12283 160) (d.f1 12283 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12283 160) (d.f1 12283 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12283 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12283 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12283 160) (d.f1 12283 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12283 160) (d.w1 12283 160) (d.w2 12283 160)
  have hwexpr0 : 0 ≤ d.w0 12283 160 + d.w1 12283 160 * √(π / 2) +
      2 * d.w2 12283 160 + energyR16 12283 *
      radiusPolynomialRoot16 (d.w0 12283 160) (d.w1 12283 160) (d.w2 12283 160) := by
    positivity
  constructor
  · change (12283 : ℝ) ^ 8 * (mA 12283 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12283 160) (d.f1 12283 160) d.f2 + locationR16 12283 *
        radiusPolynomialRoot16 (d.f0 12283 160) (d.f1 12283 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12283 : ℝ) ^ 8 * (mA 12283 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12283) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12283 : ℝ) ^ 16 *
      (d.w0 12283 160 + d.w1 12283 160 * √(π / 2) + 2 * d.w2 12283 160 +
        energyR16 12283 * radiusPolynomialRoot16 (d.w0 12283 160) (d.w1 12283 160)
          (d.w2 12283 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12283 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12283) *
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

end BstLean.Part262.Row12283

/-! A coarse bound on the actual paper statistics constant at dimension 12284. -/
namespace BstLean.Part262.Row12284
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12282 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12282 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12282 128 ≤ (12536 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12536 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12284) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12284 : ℕ))
    (by norm_num : (12284 : ℕ) ≤ 16384)
  have ht : paperTail256 12284 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12284 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12284 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12284 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12284 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12284 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12282 128 * √(2 / (12284 : ℝ)) *
      (√(12284 : ℝ) + paperT0 12284 + paperTail256 12284) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12284 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12284 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12284 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12282 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12282 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12284 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12284

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12284
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12284 (61 / 100) 160 (17 / (100 * 12284)) (26 / (10 * 12284)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12284 (61 / 100) 160 (17 / (100 * 12284)) := by
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
          (8 * tA 12284 / 12284 * (61 / 100)) ^ 4 * inverseRadius8 (12284 - 1) /
            envelopeGap 12284 (61 / 100) 160 (17 / (100 * 12284)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12284

namespace BstLean.Part262.Row12284
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12284 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12284 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12284 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12284 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12284 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12284) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12284) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12284) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12284) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12284) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12284 * (160 : ℝ) ^ 2 + 26 / (10 * 12284) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12284) : ℝ)) (tA 12284 * 160 ^ 2 + 26 / (10 * 12284)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12284) : ℝ)) d.D d.V d.P (√(tA 12284) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12284) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12284) : ℝ)) (tA 12284 * 160 ^ 2 + 26 / (10 * 12284)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12284) : ℝ)) (√(26 / (10 * 12284) : ℝ)) d.D d.V d.P (√(tA 12284) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12284) * 160) ≤ _
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

end BstLean.Part262.Row12284

namespace BstLean.Part262.Row12284
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12284 160 ∧
    0 ≤ (tableEnvelope C).f1 12284 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12284 160 ∧
    0 ≤ (tableEnvelope C).w1 12284 160 ∧ 0 ≤ (tableEnvelope C).w2 12284 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12284 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12284 160 ∧ 0 ≤ d.f1 12284 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12284 160 ∧ 0 ≤ d.w1 12284 160 ∧ 0 ≤ d.w2 12284 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12284 ≤ 2 * (228 / 100 : ℝ) / 12284 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12284 ≤ 2 * (370 / 100 : ℝ) / 12284 := by
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
    (completeRAData (tableEnvelope C) 12284 160).locationBound 12284 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12284 160).energyBound 12284 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12284 160) (d.f1 12284 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12284 160) (d.w1 12284 160)
      (d.w2 12284 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12284 160) (d.f1 12284 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12284 160) (d.f1 12284 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12284 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12284 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12284 160) (d.f1 12284 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12284 160) (d.w1 12284 160) (d.w2 12284 160)
  have hwexpr0 : 0 ≤ d.w0 12284 160 + d.w1 12284 160 * √(π / 2) +
      2 * d.w2 12284 160 + energyR16 12284 *
      radiusPolynomialRoot16 (d.w0 12284 160) (d.w1 12284 160) (d.w2 12284 160) := by
    positivity
  constructor
  · change (12284 : ℝ) ^ 8 * (mA 12284 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12284 160) (d.f1 12284 160) d.f2 + locationR16 12284 *
        radiusPolynomialRoot16 (d.f0 12284 160) (d.f1 12284 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12284 : ℝ) ^ 8 * (mA 12284 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12284) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12284 : ℝ) ^ 16 *
      (d.w0 12284 160 + d.w1 12284 160 * √(π / 2) + 2 * d.w2 12284 160 +
        energyR16 12284 * radiusPolynomialRoot16 (d.w0 12284 160) (d.w1 12284 160)
          (d.w2 12284 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12284 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12284) *
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

end BstLean.Part262.Row12284

/-! A coarse bound on the actual paper statistics constant at dimension 12285. -/
namespace BstLean.Part262.Row12285
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12283 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12283 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12283 128 ≤ (12537 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12537 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12285) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12285 : ℕ))
    (by norm_num : (12285 : ℕ) ≤ 16384)
  have ht : paperTail256 12285 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12285 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12285 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12285 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12285 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12285 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12283 128 * √(2 / (12285 : ℝ)) *
      (√(12285 : ℝ) + paperT0 12285 + paperTail256 12285) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12285 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12285 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12285 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12283 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12283 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12285 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12285

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12285
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12285 (61 / 100) 160 (17 / (100 * 12285)) (26 / (10 * 12285)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12285 (61 / 100) 160 (17 / (100 * 12285)) := by
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
          (8 * tA 12285 / 12285 * (61 / 100)) ^ 4 * inverseRadius8 (12285 - 1) /
            envelopeGap 12285 (61 / 100) 160 (17 / (100 * 12285)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12285

namespace BstLean.Part262.Row12285
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12285 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12285 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12285 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12285 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12285 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12285) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12285) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12285) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12285) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12285) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12285 * (160 : ℝ) ^ 2 + 26 / (10 * 12285) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12285) : ℝ)) (tA 12285 * 160 ^ 2 + 26 / (10 * 12285)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12285) : ℝ)) d.D d.V d.P (√(tA 12285) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12285) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12285) : ℝ)) (tA 12285 * 160 ^ 2 + 26 / (10 * 12285)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12285) : ℝ)) (√(26 / (10 * 12285) : ℝ)) d.D d.V d.P (√(tA 12285) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12285) * 160) ≤ _
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

end BstLean.Part262.Row12285

namespace BstLean.Part262.Row12285
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12285 160 ∧
    0 ≤ (tableEnvelope C).f1 12285 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12285 160 ∧
    0 ≤ (tableEnvelope C).w1 12285 160 ∧ 0 ≤ (tableEnvelope C).w2 12285 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12285 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12285 160 ∧ 0 ≤ d.f1 12285 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12285 160 ∧ 0 ≤ d.w1 12285 160 ∧ 0 ≤ d.w2 12285 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12285 ≤ 2 * (228 / 100 : ℝ) / 12285 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12285 ≤ 2 * (370 / 100 : ℝ) / 12285 := by
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
    (completeRAData (tableEnvelope C) 12285 160).locationBound 12285 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12285 160).energyBound 12285 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12285 160) (d.f1 12285 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12285 160) (d.w1 12285 160)
      (d.w2 12285 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12285 160) (d.f1 12285 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12285 160) (d.f1 12285 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12285 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12285 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12285 160) (d.f1 12285 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12285 160) (d.w1 12285 160) (d.w2 12285 160)
  have hwexpr0 : 0 ≤ d.w0 12285 160 + d.w1 12285 160 * √(π / 2) +
      2 * d.w2 12285 160 + energyR16 12285 *
      radiusPolynomialRoot16 (d.w0 12285 160) (d.w1 12285 160) (d.w2 12285 160) := by
    positivity
  constructor
  · change (12285 : ℝ) ^ 8 * (mA 12285 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12285 160) (d.f1 12285 160) d.f2 + locationR16 12285 *
        radiusPolynomialRoot16 (d.f0 12285 160) (d.f1 12285 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12285 : ℝ) ^ 8 * (mA 12285 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12285) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12285 : ℝ) ^ 16 *
      (d.w0 12285 160 + d.w1 12285 160 * √(π / 2) + 2 * d.w2 12285 160 +
        energyR16 12285 * radiusPolynomialRoot16 (d.w0 12285 160) (d.w1 12285 160)
          (d.w2 12285 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12285 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12285) *
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

end BstLean.Part262.Row12285

/-! A coarse bound on the actual paper statistics constant at dimension 12286. -/
namespace BstLean.Part262.Row12286
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12284 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12284 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12284 128 ≤ (12538 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12538 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12286) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12286 : ℕ))
    (by norm_num : (12286 : ℕ) ≤ 16384)
  have ht : paperTail256 12286 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12286 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12286 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12286 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12286 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12286 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12284 128 * √(2 / (12286 : ℝ)) *
      (√(12286 : ℝ) + paperT0 12286 + paperTail256 12286) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12286 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12286 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12286 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12284 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12284 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12286 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12286

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12286
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12286 (61 / 100) 160 (17 / (100 * 12286)) (26 / (10 * 12286)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12286 (61 / 100) 160 (17 / (100 * 12286)) := by
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
          (8 * tA 12286 / 12286 * (61 / 100)) ^ 4 * inverseRadius8 (12286 - 1) /
            envelopeGap 12286 (61 / 100) 160 (17 / (100 * 12286)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12286

namespace BstLean.Part262.Row12286
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12286 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12286 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12286 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12286 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12286 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12286) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12286) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12286) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12286) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12286) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12286 * (160 : ℝ) ^ 2 + 26 / (10 * 12286) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12286) : ℝ)) (tA 12286 * 160 ^ 2 + 26 / (10 * 12286)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12286) : ℝ)) d.D d.V d.P (√(tA 12286) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12286) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12286) : ℝ)) (tA 12286 * 160 ^ 2 + 26 / (10 * 12286)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12286) : ℝ)) (√(26 / (10 * 12286) : ℝ)) d.D d.V d.P (√(tA 12286) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12286) * 160) ≤ _
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

end BstLean.Part262.Row12286

namespace BstLean.Part262.Row12286
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12286 160 ∧
    0 ≤ (tableEnvelope C).f1 12286 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12286 160 ∧
    0 ≤ (tableEnvelope C).w1 12286 160 ∧ 0 ≤ (tableEnvelope C).w2 12286 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12286 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12286 160 ∧ 0 ≤ d.f1 12286 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12286 160 ∧ 0 ≤ d.w1 12286 160 ∧ 0 ≤ d.w2 12286 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12286 ≤ 2 * (228 / 100 : ℝ) / 12286 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12286 ≤ 2 * (370 / 100 : ℝ) / 12286 := by
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
    (completeRAData (tableEnvelope C) 12286 160).locationBound 12286 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12286 160).energyBound 12286 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12286 160) (d.f1 12286 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12286 160) (d.w1 12286 160)
      (d.w2 12286 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12286 160) (d.f1 12286 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12286 160) (d.f1 12286 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12286 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12286 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12286 160) (d.f1 12286 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12286 160) (d.w1 12286 160) (d.w2 12286 160)
  have hwexpr0 : 0 ≤ d.w0 12286 160 + d.w1 12286 160 * √(π / 2) +
      2 * d.w2 12286 160 + energyR16 12286 *
      radiusPolynomialRoot16 (d.w0 12286 160) (d.w1 12286 160) (d.w2 12286 160) := by
    positivity
  constructor
  · change (12286 : ℝ) ^ 8 * (mA 12286 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12286 160) (d.f1 12286 160) d.f2 + locationR16 12286 *
        radiusPolynomialRoot16 (d.f0 12286 160) (d.f1 12286 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12286 : ℝ) ^ 8 * (mA 12286 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12286) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12286 : ℝ) ^ 16 *
      (d.w0 12286 160 + d.w1 12286 160 * √(π / 2) + 2 * d.w2 12286 160 +
        energyR16 12286 * radiusPolynomialRoot16 (d.w0 12286 160) (d.w1 12286 160)
          (d.w2 12286 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12286 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12286) *
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

end BstLean.Part262.Row12286

/-! A coarse bound on the actual paper statistics constant at dimension 12287. -/
namespace BstLean.Part262.Row12287
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12285 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12285 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12285 128 ≤ (12539 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12539 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12287) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12287 : ℕ))
    (by norm_num : (12287 : ℕ) ≤ 16384)
  have ht : paperTail256 12287 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12287 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12287 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12287 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12287 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12287 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12285 128 * √(2 / (12287 : ℝ)) *
      (√(12287 : ℝ) + paperT0 12287 + paperTail256 12287) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12287 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12287 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12287 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12285 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12285 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12287 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12287

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12287
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12287 (61 / 100) 160 (17 / (100 * 12287)) (26 / (10 * 12287)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12287 (61 / 100) 160 (17 / (100 * 12287)) := by
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
          (8 * tA 12287 / 12287 * (61 / 100)) ^ 4 * inverseRadius8 (12287 - 1) /
            envelopeGap 12287 (61 / 100) 160 (17 / (100 * 12287)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12287

namespace BstLean.Part262.Row12287
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12287 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12287 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12287 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12287 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12287 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12287) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12287) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12287) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12287) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12287) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12287 * (160 : ℝ) ^ 2 + 26 / (10 * 12287) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12287) : ℝ)) (tA 12287 * 160 ^ 2 + 26 / (10 * 12287)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12287) : ℝ)) d.D d.V d.P (√(tA 12287) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12287) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12287) : ℝ)) (tA 12287 * 160 ^ 2 + 26 / (10 * 12287)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12287) : ℝ)) (√(26 / (10 * 12287) : ℝ)) d.D d.V d.P (√(tA 12287) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12287) * 160) ≤ _
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

end BstLean.Part262.Row12287

namespace BstLean.Part262.Row12287
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12287 160 ∧
    0 ≤ (tableEnvelope C).f1 12287 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12287 160 ∧
    0 ≤ (tableEnvelope C).w1 12287 160 ∧ 0 ≤ (tableEnvelope C).w2 12287 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12287 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12287 160 ∧ 0 ≤ d.f1 12287 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12287 160 ∧ 0 ≤ d.w1 12287 160 ∧ 0 ≤ d.w2 12287 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12287 ≤ 2 * (228 / 100 : ℝ) / 12287 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12287 ≤ 2 * (370 / 100 : ℝ) / 12287 := by
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
    (completeRAData (tableEnvelope C) 12287 160).locationBound 12287 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12287 160).energyBound 12287 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12287 160) (d.f1 12287 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12287 160) (d.w1 12287 160)
      (d.w2 12287 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12287 160) (d.f1 12287 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12287 160) (d.f1 12287 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12287 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12287 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12287 160) (d.f1 12287 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12287 160) (d.w1 12287 160) (d.w2 12287 160)
  have hwexpr0 : 0 ≤ d.w0 12287 160 + d.w1 12287 160 * √(π / 2) +
      2 * d.w2 12287 160 + energyR16 12287 *
      radiusPolynomialRoot16 (d.w0 12287 160) (d.w1 12287 160) (d.w2 12287 160) := by
    positivity
  constructor
  · change (12287 : ℝ) ^ 8 * (mA 12287 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12287 160) (d.f1 12287 160) d.f2 + locationR16 12287 *
        radiusPolynomialRoot16 (d.f0 12287 160) (d.f1 12287 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12287 : ℝ) ^ 8 * (mA 12287 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12287) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12287 : ℝ) ^ 16 *
      (d.w0 12287 160 + d.w1 12287 160 * √(π / 2) + 2 * d.w2 12287 160 +
        energyR16 12287 * radiusPolynomialRoot16 (d.w0 12287 160) (d.w1 12287 160)
          (d.w2 12287 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12287 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12287) *
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

end BstLean.Part262.Row12287

/-! A coarse bound on the actual paper statistics constant at dimension 12288. -/
namespace BstLean.Part262.Row12288
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12286 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12286 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12286 128 ≤ (12540 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12540 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12288) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12288 : ℕ))
    (by norm_num : (12288 : ℕ) ≤ 16384)
  have ht : paperTail256 12288 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12288 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12288 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12288 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12288 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12288 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12286 128 * √(2 / (12288 : ℝ)) *
      (√(12288 : ℝ) + paperT0 12288 + paperTail256 12288) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12288 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12288 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12288 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12286 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12286 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12288 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12288

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12288
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12288 (61 / 100) 160 (17 / (100 * 12288)) (26 / (10 * 12288)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12288 (61 / 100) 160 (17 / (100 * 12288)) := by
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
          (8 * tA 12288 / 12288 * (61 / 100)) ^ 4 * inverseRadius8 (12288 - 1) /
            envelopeGap 12288 (61 / 100) 160 (17 / (100 * 12288)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12288

namespace BstLean.Part262.Row12288
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12288 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12288 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12288 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12288 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12288 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12288) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12288) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12288) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12288) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12288) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12288 * (160 : ℝ) ^ 2 + 26 / (10 * 12288) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12288) : ℝ)) (tA 12288 * 160 ^ 2 + 26 / (10 * 12288)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12288) : ℝ)) d.D d.V d.P (√(tA 12288) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12288) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12288) : ℝ)) (tA 12288 * 160 ^ 2 + 26 / (10 * 12288)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12288) : ℝ)) (√(26 / (10 * 12288) : ℝ)) d.D d.V d.P (√(tA 12288) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12288) * 160) ≤ _
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

end BstLean.Part262.Row12288

namespace BstLean.Part262.Row12288
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12288 160 ∧
    0 ≤ (tableEnvelope C).f1 12288 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12288 160 ∧
    0 ≤ (tableEnvelope C).w1 12288 160 ∧ 0 ≤ (tableEnvelope C).w2 12288 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12288 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12288 160 ∧ 0 ≤ d.f1 12288 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12288 160 ∧ 0 ≤ d.w1 12288 160 ∧ 0 ≤ d.w2 12288 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12288 ≤ 2 * (228 / 100 : ℝ) / 12288 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12288 ≤ 2 * (370 / 100 : ℝ) / 12288 := by
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
    (completeRAData (tableEnvelope C) 12288 160).locationBound 12288 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12288 160).energyBound 12288 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12288 160) (d.f1 12288 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12288 160) (d.w1 12288 160)
      (d.w2 12288 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12288 160) (d.f1 12288 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12288 160) (d.f1 12288 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12288 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12288 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12288 160) (d.f1 12288 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12288 160) (d.w1 12288 160) (d.w2 12288 160)
  have hwexpr0 : 0 ≤ d.w0 12288 160 + d.w1 12288 160 * √(π / 2) +
      2 * d.w2 12288 160 + energyR16 12288 *
      radiusPolynomialRoot16 (d.w0 12288 160) (d.w1 12288 160) (d.w2 12288 160) := by
    positivity
  constructor
  · change (12288 : ℝ) ^ 8 * (mA 12288 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12288 160) (d.f1 12288 160) d.f2 + locationR16 12288 *
        radiusPolynomialRoot16 (d.f0 12288 160) (d.f1 12288 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12288 : ℝ) ^ 8 * (mA 12288 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12288) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12288 : ℝ) ^ 16 *
      (d.w0 12288 160 + d.w1 12288 160 * √(π / 2) + 2 * d.w2 12288 160 +
        energyR16 12288 * radiusPolynomialRoot16 (d.w0 12288 160) (d.w1 12288 160)
          (d.w2 12288 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12288 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12288) *
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

end BstLean.Part262.Row12288

/-! A coarse bound on the actual paper statistics constant at dimension 12289. -/
namespace BstLean.Part262.Row12289
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12287 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12287 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12287 128 ≤ (12541 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12541 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12289) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12289 : ℕ))
    (by norm_num : (12289 : ℕ) ≤ 16384)
  have ht : paperTail256 12289 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12289 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12289 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12289 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12289 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12289 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12287 128 * √(2 / (12289 : ℝ)) *
      (√(12289 : ℝ) + paperT0 12289 + paperTail256 12289) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12289 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12289 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12289 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12287 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12287 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12289 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12289

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12289
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12289 (61 / 100) 160 (17 / (100 * 12289)) (26 / (10 * 12289)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12289 (61 / 100) 160 (17 / (100 * 12289)) := by
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
          (8 * tA 12289 / 12289 * (61 / 100)) ^ 4 * inverseRadius8 (12289 - 1) /
            envelopeGap 12289 (61 / 100) 160 (17 / (100 * 12289)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12289

namespace BstLean.Part262.Row12289
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12289 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12289 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12289 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12289 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12289 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12289) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12289) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12289) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12289) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12289) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12289 * (160 : ℝ) ^ 2 + 26 / (10 * 12289) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12289) : ℝ)) (tA 12289 * 160 ^ 2 + 26 / (10 * 12289)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12289) : ℝ)) d.D d.V d.P (√(tA 12289) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12289) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12289) : ℝ)) (tA 12289 * 160 ^ 2 + 26 / (10 * 12289)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12289) : ℝ)) (√(26 / (10 * 12289) : ℝ)) d.D d.V d.P (√(tA 12289) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12289) * 160) ≤ _
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

end BstLean.Part262.Row12289

namespace BstLean.Part262.Row12289
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12289 160 ∧
    0 ≤ (tableEnvelope C).f1 12289 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12289 160 ∧
    0 ≤ (tableEnvelope C).w1 12289 160 ∧ 0 ≤ (tableEnvelope C).w2 12289 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12289 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12289 160 ∧ 0 ≤ d.f1 12289 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12289 160 ∧ 0 ≤ d.w1 12289 160 ∧ 0 ≤ d.w2 12289 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12289 ≤ 2 * (228 / 100 : ℝ) / 12289 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12289 ≤ 2 * (370 / 100 : ℝ) / 12289 := by
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
    (completeRAData (tableEnvelope C) 12289 160).locationBound 12289 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12289 160).energyBound 12289 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12289 160) (d.f1 12289 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12289 160) (d.w1 12289 160)
      (d.w2 12289 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12289 160) (d.f1 12289 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12289 160) (d.f1 12289 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12289 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12289 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12289 160) (d.f1 12289 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12289 160) (d.w1 12289 160) (d.w2 12289 160)
  have hwexpr0 : 0 ≤ d.w0 12289 160 + d.w1 12289 160 * √(π / 2) +
      2 * d.w2 12289 160 + energyR16 12289 *
      radiusPolynomialRoot16 (d.w0 12289 160) (d.w1 12289 160) (d.w2 12289 160) := by
    positivity
  constructor
  · change (12289 : ℝ) ^ 8 * (mA 12289 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12289 160) (d.f1 12289 160) d.f2 + locationR16 12289 *
        radiusPolynomialRoot16 (d.f0 12289 160) (d.f1 12289 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12289 : ℝ) ^ 8 * (mA 12289 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12289) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12289 : ℝ) ^ 16 *
      (d.w0 12289 160 + d.w1 12289 160 * √(π / 2) + 2 * d.w2 12289 160 +
        energyR16 12289 * radiusPolynomialRoot16 (d.w0 12289 160) (d.w1 12289 160)
          (d.w2 12289 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12289 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12289) *
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

end BstLean.Part262.Row12289

/-! A coarse bound on the actual paper statistics constant at dimension 12290. -/
namespace BstLean.Part262.Row12290
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12288 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12288 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12288 128 ≤ (12542 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12542 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12290) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12290 : ℕ))
    (by norm_num : (12290 : ℕ) ≤ 16384)
  have ht : paperTail256 12290 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12290 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12290 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12290 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12290 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12290 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12288 128 * √(2 / (12290 : ℝ)) *
      (√(12290 : ℝ) + paperT0 12290 + paperTail256 12290) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12290 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12290 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12290 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12288 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12288 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12290 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12290

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12290
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12290 (61 / 100) 160 (17 / (100 * 12290)) (26 / (10 * 12290)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12290 (61 / 100) 160 (17 / (100 * 12290)) := by
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
          (8 * tA 12290 / 12290 * (61 / 100)) ^ 4 * inverseRadius8 (12290 - 1) /
            envelopeGap 12290 (61 / 100) 160 (17 / (100 * 12290)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12290

namespace BstLean.Part262.Row12290
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12290 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12290 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12290 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12290 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12290 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12290) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12290) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12290) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12290) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12290) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12290 * (160 : ℝ) ^ 2 + 26 / (10 * 12290) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12290) : ℝ)) (tA 12290 * 160 ^ 2 + 26 / (10 * 12290)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12290) : ℝ)) d.D d.V d.P (√(tA 12290) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12290) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12290) : ℝ)) (tA 12290 * 160 ^ 2 + 26 / (10 * 12290)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12290) : ℝ)) (√(26 / (10 * 12290) : ℝ)) d.D d.V d.P (√(tA 12290) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12290) * 160) ≤ _
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

end BstLean.Part262.Row12290

namespace BstLean.Part262.Row12290
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12290 160 ∧
    0 ≤ (tableEnvelope C).f1 12290 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12290 160 ∧
    0 ≤ (tableEnvelope C).w1 12290 160 ∧ 0 ≤ (tableEnvelope C).w2 12290 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12290 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12290 160 ∧ 0 ≤ d.f1 12290 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12290 160 ∧ 0 ≤ d.w1 12290 160 ∧ 0 ≤ d.w2 12290 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12290 ≤ 2 * (228 / 100 : ℝ) / 12290 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12290 ≤ 2 * (370 / 100 : ℝ) / 12290 := by
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
    (completeRAData (tableEnvelope C) 12290 160).locationBound 12290 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12290 160).energyBound 12290 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12290 160) (d.f1 12290 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12290 160) (d.w1 12290 160)
      (d.w2 12290 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12290 160) (d.f1 12290 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12290 160) (d.f1 12290 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12290 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12290 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12290 160) (d.f1 12290 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12290 160) (d.w1 12290 160) (d.w2 12290 160)
  have hwexpr0 : 0 ≤ d.w0 12290 160 + d.w1 12290 160 * √(π / 2) +
      2 * d.w2 12290 160 + energyR16 12290 *
      radiusPolynomialRoot16 (d.w0 12290 160) (d.w1 12290 160) (d.w2 12290 160) := by
    positivity
  constructor
  · change (12290 : ℝ) ^ 8 * (mA 12290 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12290 160) (d.f1 12290 160) d.f2 + locationR16 12290 *
        radiusPolynomialRoot16 (d.f0 12290 160) (d.f1 12290 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12290 : ℝ) ^ 8 * (mA 12290 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12290) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12290 : ℝ) ^ 16 *
      (d.w0 12290 160 + d.w1 12290 160 * √(π / 2) + 2 * d.w2 12290 160 +
        energyR16 12290 * radiusPolynomialRoot16 (d.w0 12290 160) (d.w1 12290 160)
          (d.w2 12290 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12290 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12290) *
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

end BstLean.Part262.Row12290

/-! A coarse bound on the actual paper statistics constant at dimension 12291. -/
namespace BstLean.Part262.Row12291
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12289 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12289 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12289 128 ≤ (12543 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12543 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12291) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12291 : ℕ))
    (by norm_num : (12291 : ℕ) ≤ 16384)
  have ht : paperTail256 12291 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12291 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12291 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12291 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12291 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12291 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12289 128 * √(2 / (12291 : ℝ)) *
      (√(12291 : ℝ) + paperT0 12291 + paperTail256 12291) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12291 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12291 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12291 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12289 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12289 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12291 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12291

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12291
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12291 (61 / 100) 160 (17 / (100 * 12291)) (26 / (10 * 12291)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12291 (61 / 100) 160 (17 / (100 * 12291)) := by
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
          (8 * tA 12291 / 12291 * (61 / 100)) ^ 4 * inverseRadius8 (12291 - 1) /
            envelopeGap 12291 (61 / 100) 160 (17 / (100 * 12291)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12291

namespace BstLean.Part262.Row12291
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12291 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12291 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12291 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12291 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12291 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12291) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12291) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12291) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12291) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12291) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12291 * (160 : ℝ) ^ 2 + 26 / (10 * 12291) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12291) : ℝ)) (tA 12291 * 160 ^ 2 + 26 / (10 * 12291)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12291) : ℝ)) d.D d.V d.P (√(tA 12291) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12291) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12291) : ℝ)) (tA 12291 * 160 ^ 2 + 26 / (10 * 12291)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12291) : ℝ)) (√(26 / (10 * 12291) : ℝ)) d.D d.V d.P (√(tA 12291) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12291) * 160) ≤ _
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

end BstLean.Part262.Row12291

namespace BstLean.Part262.Row12291
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12291 160 ∧
    0 ≤ (tableEnvelope C).f1 12291 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12291 160 ∧
    0 ≤ (tableEnvelope C).w1 12291 160 ∧ 0 ≤ (tableEnvelope C).w2 12291 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12291 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12291 160 ∧ 0 ≤ d.f1 12291 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12291 160 ∧ 0 ≤ d.w1 12291 160 ∧ 0 ≤ d.w2 12291 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12291 ≤ 2 * (228 / 100 : ℝ) / 12291 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12291 ≤ 2 * (370 / 100 : ℝ) / 12291 := by
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
    (completeRAData (tableEnvelope C) 12291 160).locationBound 12291 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12291 160).energyBound 12291 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12291 160) (d.f1 12291 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12291 160) (d.w1 12291 160)
      (d.w2 12291 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12291 160) (d.f1 12291 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12291 160) (d.f1 12291 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12291 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12291 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12291 160) (d.f1 12291 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12291 160) (d.w1 12291 160) (d.w2 12291 160)
  have hwexpr0 : 0 ≤ d.w0 12291 160 + d.w1 12291 160 * √(π / 2) +
      2 * d.w2 12291 160 + energyR16 12291 *
      radiusPolynomialRoot16 (d.w0 12291 160) (d.w1 12291 160) (d.w2 12291 160) := by
    positivity
  constructor
  · change (12291 : ℝ) ^ 8 * (mA 12291 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12291 160) (d.f1 12291 160) d.f2 + locationR16 12291 *
        radiusPolynomialRoot16 (d.f0 12291 160) (d.f1 12291 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12291 : ℝ) ^ 8 * (mA 12291 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12291) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12291 : ℝ) ^ 16 *
      (d.w0 12291 160 + d.w1 12291 160 * √(π / 2) + 2 * d.w2 12291 160 +
        energyR16 12291 * radiusPolynomialRoot16 (d.w0 12291 160) (d.w1 12291 160)
          (d.w2 12291 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12291 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12291) *
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

end BstLean.Part262.Row12291

/-! A coarse bound on the actual paper statistics constant at dimension 12292. -/
namespace BstLean.Part262.Row12292
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12290 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12290 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12290 128 ≤ (12544 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12544 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12292) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12292 : ℕ))
    (by norm_num : (12292 : ℕ) ≤ 16384)
  have ht : paperTail256 12292 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12292 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12292 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12292 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12292 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12292 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12290 128 * √(2 / (12292 : ℝ)) *
      (√(12292 : ℝ) + paperT0 12292 + paperTail256 12292) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12292 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12292 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12292 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12290 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12290 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12292 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12292

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12292
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12292 (61 / 100) 160 (17 / (100 * 12292)) (26 / (10 * 12292)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12292 (61 / 100) 160 (17 / (100 * 12292)) := by
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
          (8 * tA 12292 / 12292 * (61 / 100)) ^ 4 * inverseRadius8 (12292 - 1) /
            envelopeGap 12292 (61 / 100) 160 (17 / (100 * 12292)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12292

namespace BstLean.Part262.Row12292
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12292 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12292 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12292 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12292 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12292 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12292) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12292) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12292) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12292) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12292) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12292 * (160 : ℝ) ^ 2 + 26 / (10 * 12292) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12292) : ℝ)) (tA 12292 * 160 ^ 2 + 26 / (10 * 12292)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12292) : ℝ)) d.D d.V d.P (√(tA 12292) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12292) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12292) : ℝ)) (tA 12292 * 160 ^ 2 + 26 / (10 * 12292)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12292) : ℝ)) (√(26 / (10 * 12292) : ℝ)) d.D d.V d.P (√(tA 12292) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12292) * 160) ≤ _
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

end BstLean.Part262.Row12292

namespace BstLean.Part262.Row12292
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12292 160 ∧
    0 ≤ (tableEnvelope C).f1 12292 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12292 160 ∧
    0 ≤ (tableEnvelope C).w1 12292 160 ∧ 0 ≤ (tableEnvelope C).w2 12292 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12292 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12292 160 ∧ 0 ≤ d.f1 12292 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12292 160 ∧ 0 ≤ d.w1 12292 160 ∧ 0 ≤ d.w2 12292 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12292 ≤ 2 * (228 / 100 : ℝ) / 12292 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12292 ≤ 2 * (370 / 100 : ℝ) / 12292 := by
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
    (completeRAData (tableEnvelope C) 12292 160).locationBound 12292 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12292 160).energyBound 12292 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12292 160) (d.f1 12292 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12292 160) (d.w1 12292 160)
      (d.w2 12292 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12292 160) (d.f1 12292 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12292 160) (d.f1 12292 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12292 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12292 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12292 160) (d.f1 12292 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12292 160) (d.w1 12292 160) (d.w2 12292 160)
  have hwexpr0 : 0 ≤ d.w0 12292 160 + d.w1 12292 160 * √(π / 2) +
      2 * d.w2 12292 160 + energyR16 12292 *
      radiusPolynomialRoot16 (d.w0 12292 160) (d.w1 12292 160) (d.w2 12292 160) := by
    positivity
  constructor
  · change (12292 : ℝ) ^ 8 * (mA 12292 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12292 160) (d.f1 12292 160) d.f2 + locationR16 12292 *
        radiusPolynomialRoot16 (d.f0 12292 160) (d.f1 12292 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12292 : ℝ) ^ 8 * (mA 12292 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12292) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12292 : ℝ) ^ 16 *
      (d.w0 12292 160 + d.w1 12292 160 * √(π / 2) + 2 * d.w2 12292 160 +
        energyR16 12292 * radiusPolynomialRoot16 (d.w0 12292 160) (d.w1 12292 160)
          (d.w2 12292 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12292 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12292) *
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

end BstLean.Part262.Row12292

/-! A coarse bound on the actual paper statistics constant at dimension 12293. -/
namespace BstLean.Part262.Row12293
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12291 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12291 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12291 128 ≤ (12545 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12545 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12293) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12293 : ℕ))
    (by norm_num : (12293 : ℕ) ≤ 16384)
  have ht : paperTail256 12293 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12293 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12293 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12293 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12293 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12293 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12291 128 * √(2 / (12293 : ℝ)) *
      (√(12293 : ℝ) + paperT0 12293 + paperTail256 12293) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12293 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12293 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12293 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12291 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12291 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12293 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12293

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12293
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12293 (61 / 100) 160 (17 / (100 * 12293)) (26 / (10 * 12293)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12293 (61 / 100) 160 (17 / (100 * 12293)) := by
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
          (8 * tA 12293 / 12293 * (61 / 100)) ^ 4 * inverseRadius8 (12293 - 1) /
            envelopeGap 12293 (61 / 100) 160 (17 / (100 * 12293)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12293

namespace BstLean.Part262.Row12293
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12293 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12293 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12293 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12293 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12293 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12293) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12293) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12293) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12293) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12293) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12293 * (160 : ℝ) ^ 2 + 26 / (10 * 12293) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12293) : ℝ)) (tA 12293 * 160 ^ 2 + 26 / (10 * 12293)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12293) : ℝ)) d.D d.V d.P (√(tA 12293) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12293) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12293) : ℝ)) (tA 12293 * 160 ^ 2 + 26 / (10 * 12293)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12293) : ℝ)) (√(26 / (10 * 12293) : ℝ)) d.D d.V d.P (√(tA 12293) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12293) * 160) ≤ _
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

end BstLean.Part262.Row12293

namespace BstLean.Part262.Row12293
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12293 160 ∧
    0 ≤ (tableEnvelope C).f1 12293 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12293 160 ∧
    0 ≤ (tableEnvelope C).w1 12293 160 ∧ 0 ≤ (tableEnvelope C).w2 12293 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12293 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12293 160 ∧ 0 ≤ d.f1 12293 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12293 160 ∧ 0 ≤ d.w1 12293 160 ∧ 0 ≤ d.w2 12293 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12293 ≤ 2 * (228 / 100 : ℝ) / 12293 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12293 ≤ 2 * (370 / 100 : ℝ) / 12293 := by
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
    (completeRAData (tableEnvelope C) 12293 160).locationBound 12293 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12293 160).energyBound 12293 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12293 160) (d.f1 12293 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12293 160) (d.w1 12293 160)
      (d.w2 12293 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12293 160) (d.f1 12293 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12293 160) (d.f1 12293 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12293 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12293 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12293 160) (d.f1 12293 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12293 160) (d.w1 12293 160) (d.w2 12293 160)
  have hwexpr0 : 0 ≤ d.w0 12293 160 + d.w1 12293 160 * √(π / 2) +
      2 * d.w2 12293 160 + energyR16 12293 *
      radiusPolynomialRoot16 (d.w0 12293 160) (d.w1 12293 160) (d.w2 12293 160) := by
    positivity
  constructor
  · change (12293 : ℝ) ^ 8 * (mA 12293 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12293 160) (d.f1 12293 160) d.f2 + locationR16 12293 *
        radiusPolynomialRoot16 (d.f0 12293 160) (d.f1 12293 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12293 : ℝ) ^ 8 * (mA 12293 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12293) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12293 : ℝ) ^ 16 *
      (d.w0 12293 160 + d.w1 12293 160 * √(π / 2) + 2 * d.w2 12293 160 +
        energyR16 12293 * radiusPolynomialRoot16 (d.w0 12293 160) (d.w1 12293 160)
          (d.w2 12293 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12293 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12293) *
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

end BstLean.Part262.Row12293

/-! A coarse bound on the actual paper statistics constant at dimension 12294. -/
namespace BstLean.Part262.Row12294
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12292 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12292 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12292 128 ≤ (12546 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12546 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12294) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12294 : ℕ))
    (by norm_num : (12294 : ℕ) ≤ 16384)
  have ht : paperTail256 12294 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12294 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12294 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12294 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12294 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12294 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12292 128 * √(2 / (12294 : ℝ)) *
      (√(12294 : ℝ) + paperT0 12294 + paperTail256 12294) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12294 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12294 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12294 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12292 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12292 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12294 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12294

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12294
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12294 (61 / 100) 160 (17 / (100 * 12294)) (26 / (10 * 12294)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12294 (61 / 100) 160 (17 / (100 * 12294)) := by
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
          (8 * tA 12294 / 12294 * (61 / 100)) ^ 4 * inverseRadius8 (12294 - 1) /
            envelopeGap 12294 (61 / 100) 160 (17 / (100 * 12294)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12294

namespace BstLean.Part262.Row12294
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12294 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12294 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12294 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12294 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12294 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12294) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12294) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12294) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12294) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12294) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12294 * (160 : ℝ) ^ 2 + 26 / (10 * 12294) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12294) : ℝ)) (tA 12294 * 160 ^ 2 + 26 / (10 * 12294)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12294) : ℝ)) d.D d.V d.P (√(tA 12294) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12294) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12294) : ℝ)) (tA 12294 * 160 ^ 2 + 26 / (10 * 12294)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12294) : ℝ)) (√(26 / (10 * 12294) : ℝ)) d.D d.V d.P (√(tA 12294) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12294) * 160) ≤ _
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

end BstLean.Part262.Row12294

namespace BstLean.Part262.Row12294
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12294 160 ∧
    0 ≤ (tableEnvelope C).f1 12294 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12294 160 ∧
    0 ≤ (tableEnvelope C).w1 12294 160 ∧ 0 ≤ (tableEnvelope C).w2 12294 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12294 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12294 160 ∧ 0 ≤ d.f1 12294 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12294 160 ∧ 0 ≤ d.w1 12294 160 ∧ 0 ≤ d.w2 12294 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12294 ≤ 2 * (228 / 100 : ℝ) / 12294 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12294 ≤ 2 * (370 / 100 : ℝ) / 12294 := by
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
    (completeRAData (tableEnvelope C) 12294 160).locationBound 12294 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12294 160).energyBound 12294 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12294 160) (d.f1 12294 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12294 160) (d.w1 12294 160)
      (d.w2 12294 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12294 160) (d.f1 12294 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12294 160) (d.f1 12294 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12294 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12294 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12294 160) (d.f1 12294 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12294 160) (d.w1 12294 160) (d.w2 12294 160)
  have hwexpr0 : 0 ≤ d.w0 12294 160 + d.w1 12294 160 * √(π / 2) +
      2 * d.w2 12294 160 + energyR16 12294 *
      radiusPolynomialRoot16 (d.w0 12294 160) (d.w1 12294 160) (d.w2 12294 160) := by
    positivity
  constructor
  · change (12294 : ℝ) ^ 8 * (mA 12294 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12294 160) (d.f1 12294 160) d.f2 + locationR16 12294 *
        radiusPolynomialRoot16 (d.f0 12294 160) (d.f1 12294 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12294 : ℝ) ^ 8 * (mA 12294 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12294) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12294 : ℝ) ^ 16 *
      (d.w0 12294 160 + d.w1 12294 160 * √(π / 2) + 2 * d.w2 12294 160 +
        energyR16 12294 * radiusPolynomialRoot16 (d.w0 12294 160) (d.w1 12294 160)
          (d.w2 12294 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12294 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12294) *
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

end BstLean.Part262.Row12294

/-! A coarse bound on the actual paper statistics constant at dimension 12295. -/
namespace BstLean.Part262.Row12295
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12293 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12293 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12293 128 ≤ (12547 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12547 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12295) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12295 : ℕ))
    (by norm_num : (12295 : ℕ) ≤ 16384)
  have ht : paperTail256 12295 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12295 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12295 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12295 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12295 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12295 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12293 128 * √(2 / (12295 : ℝ)) *
      (√(12295 : ℝ) + paperT0 12295 + paperTail256 12295) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12295 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12295 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12295 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12293 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12293 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12295 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12295

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12295
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12295 (61 / 100) 160 (17 / (100 * 12295)) (26 / (10 * 12295)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12295 (61 / 100) 160 (17 / (100 * 12295)) := by
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
          (8 * tA 12295 / 12295 * (61 / 100)) ^ 4 * inverseRadius8 (12295 - 1) /
            envelopeGap 12295 (61 / 100) 160 (17 / (100 * 12295)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12295

namespace BstLean.Part262.Row12295
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12295 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12295 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12295 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12295 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12295 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12295) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12295) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12295) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12295) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12295) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12295 * (160 : ℝ) ^ 2 + 26 / (10 * 12295) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12295) : ℝ)) (tA 12295 * 160 ^ 2 + 26 / (10 * 12295)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12295) : ℝ)) d.D d.V d.P (√(tA 12295) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12295) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12295) : ℝ)) (tA 12295 * 160 ^ 2 + 26 / (10 * 12295)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12295) : ℝ)) (√(26 / (10 * 12295) : ℝ)) d.D d.V d.P (√(tA 12295) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12295) * 160) ≤ _
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

end BstLean.Part262.Row12295

namespace BstLean.Part262.Row12295
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12295 160 ∧
    0 ≤ (tableEnvelope C).f1 12295 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12295 160 ∧
    0 ≤ (tableEnvelope C).w1 12295 160 ∧ 0 ≤ (tableEnvelope C).w2 12295 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12295 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12295 160 ∧ 0 ≤ d.f1 12295 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12295 160 ∧ 0 ≤ d.w1 12295 160 ∧ 0 ≤ d.w2 12295 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12295 ≤ 2 * (228 / 100 : ℝ) / 12295 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12295 ≤ 2 * (370 / 100 : ℝ) / 12295 := by
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
    (completeRAData (tableEnvelope C) 12295 160).locationBound 12295 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12295 160).energyBound 12295 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12295 160) (d.f1 12295 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12295 160) (d.w1 12295 160)
      (d.w2 12295 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12295 160) (d.f1 12295 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12295 160) (d.f1 12295 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12295 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12295 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12295 160) (d.f1 12295 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12295 160) (d.w1 12295 160) (d.w2 12295 160)
  have hwexpr0 : 0 ≤ d.w0 12295 160 + d.w1 12295 160 * √(π / 2) +
      2 * d.w2 12295 160 + energyR16 12295 *
      radiusPolynomialRoot16 (d.w0 12295 160) (d.w1 12295 160) (d.w2 12295 160) := by
    positivity
  constructor
  · change (12295 : ℝ) ^ 8 * (mA 12295 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12295 160) (d.f1 12295 160) d.f2 + locationR16 12295 *
        radiusPolynomialRoot16 (d.f0 12295 160) (d.f1 12295 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12295 : ℝ) ^ 8 * (mA 12295 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12295) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12295 : ℝ) ^ 16 *
      (d.w0 12295 160 + d.w1 12295 160 * √(π / 2) + 2 * d.w2 12295 160 +
        energyR16 12295 * radiusPolynomialRoot16 (d.w0 12295 160) (d.w1 12295 160)
          (d.w2 12295 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12295 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12295) *
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

end BstLean.Part262.Row12295

/-! A coarse bound on the actual paper statistics constant at dimension 12296. -/
namespace BstLean.Part262.Row12296
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12294 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12294 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12294 128 ≤ (12548 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12548 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12296) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12296 : ℕ))
    (by norm_num : (12296 : ℕ) ≤ 16384)
  have ht : paperTail256 12296 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12296 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12296 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12296 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12296 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12296 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12294 128 * √(2 / (12296 : ℝ)) *
      (√(12296 : ℝ) + paperT0 12296 + paperTail256 12296) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12296 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12296 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12296 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12294 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12294 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12296 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12296

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12296
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12296 (61 / 100) 160 (17 / (100 * 12296)) (26 / (10 * 12296)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12296 (61 / 100) 160 (17 / (100 * 12296)) := by
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
          (8 * tA 12296 / 12296 * (61 / 100)) ^ 4 * inverseRadius8 (12296 - 1) /
            envelopeGap 12296 (61 / 100) 160 (17 / (100 * 12296)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12296

namespace BstLean.Part262.Row12296
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12296 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12296 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12296 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12296 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12296 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12296) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12296) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12296) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12296) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12296) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12296 * (160 : ℝ) ^ 2 + 26 / (10 * 12296) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12296) : ℝ)) (tA 12296 * 160 ^ 2 + 26 / (10 * 12296)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12296) : ℝ)) d.D d.V d.P (√(tA 12296) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12296) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12296) : ℝ)) (tA 12296 * 160 ^ 2 + 26 / (10 * 12296)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12296) : ℝ)) (√(26 / (10 * 12296) : ℝ)) d.D d.V d.P (√(tA 12296) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12296) * 160) ≤ _
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

end BstLean.Part262.Row12296

namespace BstLean.Part262.Row12296
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12296 160 ∧
    0 ≤ (tableEnvelope C).f1 12296 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12296 160 ∧
    0 ≤ (tableEnvelope C).w1 12296 160 ∧ 0 ≤ (tableEnvelope C).w2 12296 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12296 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12296 160 ∧ 0 ≤ d.f1 12296 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12296 160 ∧ 0 ≤ d.w1 12296 160 ∧ 0 ≤ d.w2 12296 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12296 ≤ 2 * (228 / 100 : ℝ) / 12296 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12296 ≤ 2 * (370 / 100 : ℝ) / 12296 := by
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
    (completeRAData (tableEnvelope C) 12296 160).locationBound 12296 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12296 160).energyBound 12296 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12296 160) (d.f1 12296 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12296 160) (d.w1 12296 160)
      (d.w2 12296 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12296 160) (d.f1 12296 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12296 160) (d.f1 12296 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12296 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12296 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12296 160) (d.f1 12296 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12296 160) (d.w1 12296 160) (d.w2 12296 160)
  have hwexpr0 : 0 ≤ d.w0 12296 160 + d.w1 12296 160 * √(π / 2) +
      2 * d.w2 12296 160 + energyR16 12296 *
      radiusPolynomialRoot16 (d.w0 12296 160) (d.w1 12296 160) (d.w2 12296 160) := by
    positivity
  constructor
  · change (12296 : ℝ) ^ 8 * (mA 12296 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12296 160) (d.f1 12296 160) d.f2 + locationR16 12296 *
        radiusPolynomialRoot16 (d.f0 12296 160) (d.f1 12296 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12296 : ℝ) ^ 8 * (mA 12296 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12296) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12296 : ℝ) ^ 16 *
      (d.w0 12296 160 + d.w1 12296 160 * √(π / 2) + 2 * d.w2 12296 160 +
        energyR16 12296 * radiusPolynomialRoot16 (d.w0 12296 160) (d.w1 12296 160)
          (d.w2 12296 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12296 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12296) *
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

end BstLean.Part262.Row12296

/-! A coarse bound on the actual paper statistics constant at dimension 12297. -/
namespace BstLean.Part262.Row12297
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12295 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12295 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12295 128 ≤ (12549 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12549 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12297) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12297 : ℕ))
    (by norm_num : (12297 : ℕ) ≤ 16384)
  have ht : paperTail256 12297 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12297 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12297 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12297 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12297 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12297 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12295 128 * √(2 / (12297 : ℝ)) *
      (√(12297 : ℝ) + paperT0 12297 + paperTail256 12297) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12297 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12297 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12297 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12295 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12295 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12297 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12297

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12297
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12297 (61 / 100) 160 (17 / (100 * 12297)) (26 / (10 * 12297)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12297 (61 / 100) 160 (17 / (100 * 12297)) := by
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
          (8 * tA 12297 / 12297 * (61 / 100)) ^ 4 * inverseRadius8 (12297 - 1) /
            envelopeGap 12297 (61 / 100) 160 (17 / (100 * 12297)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12297

namespace BstLean.Part262.Row12297
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12297 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12297 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12297 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12297 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12297 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12297) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12297) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12297) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12297) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12297) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12297 * (160 : ℝ) ^ 2 + 26 / (10 * 12297) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12297) : ℝ)) (tA 12297 * 160 ^ 2 + 26 / (10 * 12297)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12297) : ℝ)) d.D d.V d.P (√(tA 12297) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12297) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12297) : ℝ)) (tA 12297 * 160 ^ 2 + 26 / (10 * 12297)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12297) : ℝ)) (√(26 / (10 * 12297) : ℝ)) d.D d.V d.P (√(tA 12297) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12297) * 160) ≤ _
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

end BstLean.Part262.Row12297

namespace BstLean.Part262.Row12297
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12297 160 ∧
    0 ≤ (tableEnvelope C).f1 12297 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12297 160 ∧
    0 ≤ (tableEnvelope C).w1 12297 160 ∧ 0 ≤ (tableEnvelope C).w2 12297 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12297 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12297 160 ∧ 0 ≤ d.f1 12297 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12297 160 ∧ 0 ≤ d.w1 12297 160 ∧ 0 ≤ d.w2 12297 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12297 ≤ 2 * (228 / 100 : ℝ) / 12297 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12297 ≤ 2 * (370 / 100 : ℝ) / 12297 := by
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
    (completeRAData (tableEnvelope C) 12297 160).locationBound 12297 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12297 160).energyBound 12297 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12297 160) (d.f1 12297 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12297 160) (d.w1 12297 160)
      (d.w2 12297 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12297 160) (d.f1 12297 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12297 160) (d.f1 12297 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12297 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12297 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12297 160) (d.f1 12297 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12297 160) (d.w1 12297 160) (d.w2 12297 160)
  have hwexpr0 : 0 ≤ d.w0 12297 160 + d.w1 12297 160 * √(π / 2) +
      2 * d.w2 12297 160 + energyR16 12297 *
      radiusPolynomialRoot16 (d.w0 12297 160) (d.w1 12297 160) (d.w2 12297 160) := by
    positivity
  constructor
  · change (12297 : ℝ) ^ 8 * (mA 12297 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12297 160) (d.f1 12297 160) d.f2 + locationR16 12297 *
        radiusPolynomialRoot16 (d.f0 12297 160) (d.f1 12297 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12297 : ℝ) ^ 8 * (mA 12297 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12297) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12297 : ℝ) ^ 16 *
      (d.w0 12297 160 + d.w1 12297 160 * √(π / 2) + 2 * d.w2 12297 160 +
        energyR16 12297 * radiusPolynomialRoot16 (d.w0 12297 160) (d.w1 12297 160)
          (d.w2 12297 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12297 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12297) *
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

end BstLean.Part262.Row12297

/-! A coarse bound on the actual paper statistics constant at dimension 12298. -/
namespace BstLean.Part262.Row12298
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12296 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12296 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12296 128 ≤ (12550 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12550 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12298) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12298 : ℕ))
    (by norm_num : (12298 : ℕ) ≤ 16384)
  have ht : paperTail256 12298 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12298 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12298 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12298 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12298 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12298 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12296 128 * √(2 / (12298 : ℝ)) *
      (√(12298 : ℝ) + paperT0 12298 + paperTail256 12298) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12298 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12298 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12298 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12296 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12296 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12298 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12298

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12298
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12298 (61 / 100) 160 (17 / (100 * 12298)) (26 / (10 * 12298)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12298 (61 / 100) 160 (17 / (100 * 12298)) := by
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
          (8 * tA 12298 / 12298 * (61 / 100)) ^ 4 * inverseRadius8 (12298 - 1) /
            envelopeGap 12298 (61 / 100) 160 (17 / (100 * 12298)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12298

namespace BstLean.Part262.Row12298
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12298 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12298 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12298 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12298 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12298 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12298) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12298) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12298) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12298) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12298) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12298 * (160 : ℝ) ^ 2 + 26 / (10 * 12298) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12298) : ℝ)) (tA 12298 * 160 ^ 2 + 26 / (10 * 12298)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12298) : ℝ)) d.D d.V d.P (√(tA 12298) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12298) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12298) : ℝ)) (tA 12298 * 160 ^ 2 + 26 / (10 * 12298)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12298) : ℝ)) (√(26 / (10 * 12298) : ℝ)) d.D d.V d.P (√(tA 12298) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12298) * 160) ≤ _
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

end BstLean.Part262.Row12298

namespace BstLean.Part262.Row12298
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12298 160 ∧
    0 ≤ (tableEnvelope C).f1 12298 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12298 160 ∧
    0 ≤ (tableEnvelope C).w1 12298 160 ∧ 0 ≤ (tableEnvelope C).w2 12298 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12298 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12298 160 ∧ 0 ≤ d.f1 12298 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12298 160 ∧ 0 ≤ d.w1 12298 160 ∧ 0 ≤ d.w2 12298 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12298 ≤ 2 * (228 / 100 : ℝ) / 12298 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12298 ≤ 2 * (370 / 100 : ℝ) / 12298 := by
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
    (completeRAData (tableEnvelope C) 12298 160).locationBound 12298 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12298 160).energyBound 12298 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12298 160) (d.f1 12298 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12298 160) (d.w1 12298 160)
      (d.w2 12298 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12298 160) (d.f1 12298 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12298 160) (d.f1 12298 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12298 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12298 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12298 160) (d.f1 12298 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12298 160) (d.w1 12298 160) (d.w2 12298 160)
  have hwexpr0 : 0 ≤ d.w0 12298 160 + d.w1 12298 160 * √(π / 2) +
      2 * d.w2 12298 160 + energyR16 12298 *
      radiusPolynomialRoot16 (d.w0 12298 160) (d.w1 12298 160) (d.w2 12298 160) := by
    positivity
  constructor
  · change (12298 : ℝ) ^ 8 * (mA 12298 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12298 160) (d.f1 12298 160) d.f2 + locationR16 12298 *
        radiusPolynomialRoot16 (d.f0 12298 160) (d.f1 12298 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12298 : ℝ) ^ 8 * (mA 12298 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12298) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12298 : ℝ) ^ 16 *
      (d.w0 12298 160 + d.w1 12298 160 * √(π / 2) + 2 * d.w2 12298 160 +
        energyR16 12298 * radiusPolynomialRoot16 (d.w0 12298 160) (d.w1 12298 160)
          (d.w2 12298 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12298 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12298) *
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

end BstLean.Part262.Row12298

/-! A coarse bound on the actual paper statistics constant at dimension 12299. -/
namespace BstLean.Part262.Row12299
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12297 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12297 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12297 128 ≤ (12551 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12551 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12299) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12299 : ℕ))
    (by norm_num : (12299 : ℕ) ≤ 16384)
  have ht : paperTail256 12299 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12299 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12299 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12299 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12299 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12299 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12297 128 * √(2 / (12299 : ℝ)) *
      (√(12299 : ℝ) + paperT0 12299 + paperTail256 12299) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12299 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12299 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12299 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12297 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12297 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12299 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12299

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12299
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12299 (61 / 100) 160 (17 / (100 * 12299)) (26 / (10 * 12299)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12299 (61 / 100) 160 (17 / (100 * 12299)) := by
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
          (8 * tA 12299 / 12299 * (61 / 100)) ^ 4 * inverseRadius8 (12299 - 1) /
            envelopeGap 12299 (61 / 100) 160 (17 / (100 * 12299)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12299

namespace BstLean.Part262.Row12299
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12299 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12299 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12299 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12299 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12299 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12299) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12299) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12299) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12299) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12299) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12299 * (160 : ℝ) ^ 2 + 26 / (10 * 12299) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12299) : ℝ)) (tA 12299 * 160 ^ 2 + 26 / (10 * 12299)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12299) : ℝ)) d.D d.V d.P (√(tA 12299) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12299) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12299) : ℝ)) (tA 12299 * 160 ^ 2 + 26 / (10 * 12299)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12299) : ℝ)) (√(26 / (10 * 12299) : ℝ)) d.D d.V d.P (√(tA 12299) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12299) * 160) ≤ _
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

end BstLean.Part262.Row12299

namespace BstLean.Part262.Row12299
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12299 160 ∧
    0 ≤ (tableEnvelope C).f1 12299 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12299 160 ∧
    0 ≤ (tableEnvelope C).w1 12299 160 ∧ 0 ≤ (tableEnvelope C).w2 12299 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12299 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12299 160 ∧ 0 ≤ d.f1 12299 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12299 160 ∧ 0 ≤ d.w1 12299 160 ∧ 0 ≤ d.w2 12299 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12299 ≤ 2 * (228 / 100 : ℝ) / 12299 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12299 ≤ 2 * (370 / 100 : ℝ) / 12299 := by
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
    (completeRAData (tableEnvelope C) 12299 160).locationBound 12299 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12299 160).energyBound 12299 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12299 160) (d.f1 12299 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12299 160) (d.w1 12299 160)
      (d.w2 12299 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12299 160) (d.f1 12299 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12299 160) (d.f1 12299 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12299 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12299 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12299 160) (d.f1 12299 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12299 160) (d.w1 12299 160) (d.w2 12299 160)
  have hwexpr0 : 0 ≤ d.w0 12299 160 + d.w1 12299 160 * √(π / 2) +
      2 * d.w2 12299 160 + energyR16 12299 *
      radiusPolynomialRoot16 (d.w0 12299 160) (d.w1 12299 160) (d.w2 12299 160) := by
    positivity
  constructor
  · change (12299 : ℝ) ^ 8 * (mA 12299 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12299 160) (d.f1 12299 160) d.f2 + locationR16 12299 *
        radiusPolynomialRoot16 (d.f0 12299 160) (d.f1 12299 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12299 : ℝ) ^ 8 * (mA 12299 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12299) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12299 : ℝ) ^ 16 *
      (d.w0 12299 160 + d.w1 12299 160 * √(π / 2) + 2 * d.w2 12299 160 +
        energyR16 12299 * radiusPolynomialRoot16 (d.w0 12299 160) (d.w1 12299 160)
          (d.w2 12299 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12299 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12299) *
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

end BstLean.Part262.Row12299
