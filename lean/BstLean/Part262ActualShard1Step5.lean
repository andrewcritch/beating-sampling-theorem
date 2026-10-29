import BstLean.Part262ActualShard1Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12250. -/
namespace BstLean.Part262.Row12250
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12248 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12248 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12248 128 ≤ (12502 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12502 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12250) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12250 : ℕ))
    (by norm_num : (12250 : ℕ) ≤ 16384)
  have ht : paperTail256 12250 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12250 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12250 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12250 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12250 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12250 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12248 128 * √(2 / (12250 : ℝ)) *
      (√(12250 : ℝ) + paperT0 12250 + paperTail256 12250) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12250 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12250 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12250 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12248 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12248 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12250 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12250

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12250
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12250 (61 / 100) 160 (17 / (100 * 12250)) (26 / (10 * 12250)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12250 (61 / 100) 160 (17 / (100 * 12250)) := by
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
          (8 * tA 12250 / 12250 * (61 / 100)) ^ 4 * inverseRadius8 (12250 - 1) /
            envelopeGap 12250 (61 / 100) 160 (17 / (100 * 12250)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12250

namespace BstLean.Part262.Row12250
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12250 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12250 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12250 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12250 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12250 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12250) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12250) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12250) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12250) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12250) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12250 * (160 : ℝ) ^ 2 + 26 / (10 * 12250) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12250) : ℝ)) (tA 12250 * 160 ^ 2 + 26 / (10 * 12250)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12250) : ℝ)) d.D d.V d.P (√(tA 12250) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12250) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12250) : ℝ)) (tA 12250 * 160 ^ 2 + 26 / (10 * 12250)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12250) : ℝ)) (√(26 / (10 * 12250) : ℝ)) d.D d.V d.P (√(tA 12250) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12250) * 160) ≤ _
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

end BstLean.Part262.Row12250

namespace BstLean.Part262.Row12250
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12250 160 ∧
    0 ≤ (tableEnvelope C).f1 12250 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12250 160 ∧
    0 ≤ (tableEnvelope C).w1 12250 160 ∧ 0 ≤ (tableEnvelope C).w2 12250 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12250 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12250 160 ∧ 0 ≤ d.f1 12250 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12250 160 ∧ 0 ≤ d.w1 12250 160 ∧ 0 ≤ d.w2 12250 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12250 ≤ 2 * (228 / 100 : ℝ) / 12250 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12250 ≤ 2 * (370 / 100 : ℝ) / 12250 := by
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
    (completeRAData (tableEnvelope C) 12250 160).locationBound 12250 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12250 160).energyBound 12250 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12250 160) (d.f1 12250 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12250 160) (d.w1 12250 160)
      (d.w2 12250 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12250 160) (d.f1 12250 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12250 160) (d.f1 12250 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12250 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12250 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12250 160) (d.f1 12250 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12250 160) (d.w1 12250 160) (d.w2 12250 160)
  have hwexpr0 : 0 ≤ d.w0 12250 160 + d.w1 12250 160 * √(π / 2) +
      2 * d.w2 12250 160 + energyR16 12250 *
      radiusPolynomialRoot16 (d.w0 12250 160) (d.w1 12250 160) (d.w2 12250 160) := by
    positivity
  constructor
  · change (12250 : ℝ) ^ 8 * (mA 12250 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12250 160) (d.f1 12250 160) d.f2 + locationR16 12250 *
        radiusPolynomialRoot16 (d.f0 12250 160) (d.f1 12250 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12250 : ℝ) ^ 8 * (mA 12250 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12250) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12250 : ℝ) ^ 16 *
      (d.w0 12250 160 + d.w1 12250 160 * √(π / 2) + 2 * d.w2 12250 160 +
        energyR16 12250 * radiusPolynomialRoot16 (d.w0 12250 160) (d.w1 12250 160)
          (d.w2 12250 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12250 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12250) *
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

end BstLean.Part262.Row12250

/-! A coarse bound on the actual paper statistics constant at dimension 12251. -/
namespace BstLean.Part262.Row12251
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12249 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12249 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12249 128 ≤ (12503 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12503 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12251) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12251 : ℕ))
    (by norm_num : (12251 : ℕ) ≤ 16384)
  have ht : paperTail256 12251 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12251 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12251 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12251 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12251 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12251 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12249 128 * √(2 / (12251 : ℝ)) *
      (√(12251 : ℝ) + paperT0 12251 + paperTail256 12251) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12251 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12251 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12251 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12249 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12249 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12251 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12251

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12251
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12251 (61 / 100) 160 (17 / (100 * 12251)) (26 / (10 * 12251)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12251 (61 / 100) 160 (17 / (100 * 12251)) := by
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
          (8 * tA 12251 / 12251 * (61 / 100)) ^ 4 * inverseRadius8 (12251 - 1) /
            envelopeGap 12251 (61 / 100) 160 (17 / (100 * 12251)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12251

namespace BstLean.Part262.Row12251
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12251 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12251 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12251 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12251 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12251 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12251) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12251) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12251) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12251) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12251) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12251 * (160 : ℝ) ^ 2 + 26 / (10 * 12251) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12251) : ℝ)) (tA 12251 * 160 ^ 2 + 26 / (10 * 12251)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12251) : ℝ)) d.D d.V d.P (√(tA 12251) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12251) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12251) : ℝ)) (tA 12251 * 160 ^ 2 + 26 / (10 * 12251)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12251) : ℝ)) (√(26 / (10 * 12251) : ℝ)) d.D d.V d.P (√(tA 12251) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12251) * 160) ≤ _
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

end BstLean.Part262.Row12251

namespace BstLean.Part262.Row12251
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12251 160 ∧
    0 ≤ (tableEnvelope C).f1 12251 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12251 160 ∧
    0 ≤ (tableEnvelope C).w1 12251 160 ∧ 0 ≤ (tableEnvelope C).w2 12251 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12251 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12251 160 ∧ 0 ≤ d.f1 12251 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12251 160 ∧ 0 ≤ d.w1 12251 160 ∧ 0 ≤ d.w2 12251 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12251 ≤ 2 * (228 / 100 : ℝ) / 12251 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12251 ≤ 2 * (370 / 100 : ℝ) / 12251 := by
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
    (completeRAData (tableEnvelope C) 12251 160).locationBound 12251 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12251 160).energyBound 12251 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12251 160) (d.f1 12251 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12251 160) (d.w1 12251 160)
      (d.w2 12251 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12251 160) (d.f1 12251 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12251 160) (d.f1 12251 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12251 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12251 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12251 160) (d.f1 12251 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12251 160) (d.w1 12251 160) (d.w2 12251 160)
  have hwexpr0 : 0 ≤ d.w0 12251 160 + d.w1 12251 160 * √(π / 2) +
      2 * d.w2 12251 160 + energyR16 12251 *
      radiusPolynomialRoot16 (d.w0 12251 160) (d.w1 12251 160) (d.w2 12251 160) := by
    positivity
  constructor
  · change (12251 : ℝ) ^ 8 * (mA 12251 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12251 160) (d.f1 12251 160) d.f2 + locationR16 12251 *
        radiusPolynomialRoot16 (d.f0 12251 160) (d.f1 12251 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12251 : ℝ) ^ 8 * (mA 12251 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12251) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12251 : ℝ) ^ 16 *
      (d.w0 12251 160 + d.w1 12251 160 * √(π / 2) + 2 * d.w2 12251 160 +
        energyR16 12251 * radiusPolynomialRoot16 (d.w0 12251 160) (d.w1 12251 160)
          (d.w2 12251 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12251 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12251) *
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

end BstLean.Part262.Row12251

/-! A coarse bound on the actual paper statistics constant at dimension 12252. -/
namespace BstLean.Part262.Row12252
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12250 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12250 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12250 128 ≤ (12504 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12504 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12252) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12252 : ℕ))
    (by norm_num : (12252 : ℕ) ≤ 16384)
  have ht : paperTail256 12252 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12252 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12252 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12252 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12252 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12252 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12250 128 * √(2 / (12252 : ℝ)) *
      (√(12252 : ℝ) + paperT0 12252 + paperTail256 12252) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12252 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12252 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12252 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12250 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12250 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12252 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12252

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12252
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12252 (61 / 100) 160 (17 / (100 * 12252)) (26 / (10 * 12252)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12252 (61 / 100) 160 (17 / (100 * 12252)) := by
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
          (8 * tA 12252 / 12252 * (61 / 100)) ^ 4 * inverseRadius8 (12252 - 1) /
            envelopeGap 12252 (61 / 100) 160 (17 / (100 * 12252)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12252

namespace BstLean.Part262.Row12252
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12252 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12252 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12252 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12252 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12252 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12252) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12252) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12252) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12252) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12252) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12252 * (160 : ℝ) ^ 2 + 26 / (10 * 12252) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12252) : ℝ)) (tA 12252 * 160 ^ 2 + 26 / (10 * 12252)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12252) : ℝ)) d.D d.V d.P (√(tA 12252) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12252) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12252) : ℝ)) (tA 12252 * 160 ^ 2 + 26 / (10 * 12252)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12252) : ℝ)) (√(26 / (10 * 12252) : ℝ)) d.D d.V d.P (√(tA 12252) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12252) * 160) ≤ _
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

end BstLean.Part262.Row12252

namespace BstLean.Part262.Row12252
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12252 160 ∧
    0 ≤ (tableEnvelope C).f1 12252 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12252 160 ∧
    0 ≤ (tableEnvelope C).w1 12252 160 ∧ 0 ≤ (tableEnvelope C).w2 12252 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12252 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12252 160 ∧ 0 ≤ d.f1 12252 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12252 160 ∧ 0 ≤ d.w1 12252 160 ∧ 0 ≤ d.w2 12252 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12252 ≤ 2 * (228 / 100 : ℝ) / 12252 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12252 ≤ 2 * (370 / 100 : ℝ) / 12252 := by
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
    (completeRAData (tableEnvelope C) 12252 160).locationBound 12252 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12252 160).energyBound 12252 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12252 160) (d.f1 12252 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12252 160) (d.w1 12252 160)
      (d.w2 12252 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12252 160) (d.f1 12252 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12252 160) (d.f1 12252 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12252 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12252 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12252 160) (d.f1 12252 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12252 160) (d.w1 12252 160) (d.w2 12252 160)
  have hwexpr0 : 0 ≤ d.w0 12252 160 + d.w1 12252 160 * √(π / 2) +
      2 * d.w2 12252 160 + energyR16 12252 *
      radiusPolynomialRoot16 (d.w0 12252 160) (d.w1 12252 160) (d.w2 12252 160) := by
    positivity
  constructor
  · change (12252 : ℝ) ^ 8 * (mA 12252 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12252 160) (d.f1 12252 160) d.f2 + locationR16 12252 *
        radiusPolynomialRoot16 (d.f0 12252 160) (d.f1 12252 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12252 : ℝ) ^ 8 * (mA 12252 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12252) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12252 : ℝ) ^ 16 *
      (d.w0 12252 160 + d.w1 12252 160 * √(π / 2) + 2 * d.w2 12252 160 +
        energyR16 12252 * radiusPolynomialRoot16 (d.w0 12252 160) (d.w1 12252 160)
          (d.w2 12252 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12252 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12252) *
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

end BstLean.Part262.Row12252

/-! A coarse bound on the actual paper statistics constant at dimension 12253. -/
namespace BstLean.Part262.Row12253
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12251 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12251 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12251 128 ≤ (12505 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12505 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12253) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12253 : ℕ))
    (by norm_num : (12253 : ℕ) ≤ 16384)
  have ht : paperTail256 12253 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12253 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12253 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12253 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12253 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12253 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12251 128 * √(2 / (12253 : ℝ)) *
      (√(12253 : ℝ) + paperT0 12253 + paperTail256 12253) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12253 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12253 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12253 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12251 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12251 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12253 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12253

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12253
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12253 (61 / 100) 160 (17 / (100 * 12253)) (26 / (10 * 12253)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12253 (61 / 100) 160 (17 / (100 * 12253)) := by
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
          (8 * tA 12253 / 12253 * (61 / 100)) ^ 4 * inverseRadius8 (12253 - 1) /
            envelopeGap 12253 (61 / 100) 160 (17 / (100 * 12253)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12253

namespace BstLean.Part262.Row12253
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12253 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12253 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12253 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12253 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12253 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12253) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12253) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12253) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12253) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12253) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12253 * (160 : ℝ) ^ 2 + 26 / (10 * 12253) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12253) : ℝ)) (tA 12253 * 160 ^ 2 + 26 / (10 * 12253)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12253) : ℝ)) d.D d.V d.P (√(tA 12253) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12253) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12253) : ℝ)) (tA 12253 * 160 ^ 2 + 26 / (10 * 12253)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12253) : ℝ)) (√(26 / (10 * 12253) : ℝ)) d.D d.V d.P (√(tA 12253) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12253) * 160) ≤ _
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

end BstLean.Part262.Row12253

namespace BstLean.Part262.Row12253
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12253 160 ∧
    0 ≤ (tableEnvelope C).f1 12253 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12253 160 ∧
    0 ≤ (tableEnvelope C).w1 12253 160 ∧ 0 ≤ (tableEnvelope C).w2 12253 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12253 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12253 160 ∧ 0 ≤ d.f1 12253 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12253 160 ∧ 0 ≤ d.w1 12253 160 ∧ 0 ≤ d.w2 12253 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12253 ≤ 2 * (228 / 100 : ℝ) / 12253 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12253 ≤ 2 * (370 / 100 : ℝ) / 12253 := by
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
    (completeRAData (tableEnvelope C) 12253 160).locationBound 12253 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12253 160).energyBound 12253 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12253 160) (d.f1 12253 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12253 160) (d.w1 12253 160)
      (d.w2 12253 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12253 160) (d.f1 12253 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12253 160) (d.f1 12253 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12253 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12253 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12253 160) (d.f1 12253 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12253 160) (d.w1 12253 160) (d.w2 12253 160)
  have hwexpr0 : 0 ≤ d.w0 12253 160 + d.w1 12253 160 * √(π / 2) +
      2 * d.w2 12253 160 + energyR16 12253 *
      radiusPolynomialRoot16 (d.w0 12253 160) (d.w1 12253 160) (d.w2 12253 160) := by
    positivity
  constructor
  · change (12253 : ℝ) ^ 8 * (mA 12253 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12253 160) (d.f1 12253 160) d.f2 + locationR16 12253 *
        radiusPolynomialRoot16 (d.f0 12253 160) (d.f1 12253 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12253 : ℝ) ^ 8 * (mA 12253 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12253) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12253 : ℝ) ^ 16 *
      (d.w0 12253 160 + d.w1 12253 160 * √(π / 2) + 2 * d.w2 12253 160 +
        energyR16 12253 * radiusPolynomialRoot16 (d.w0 12253 160) (d.w1 12253 160)
          (d.w2 12253 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12253 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12253) *
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

end BstLean.Part262.Row12253

/-! A coarse bound on the actual paper statistics constant at dimension 12254. -/
namespace BstLean.Part262.Row12254
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12252 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12252 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12252 128 ≤ (12506 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12506 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12254) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12254 : ℕ))
    (by norm_num : (12254 : ℕ) ≤ 16384)
  have ht : paperTail256 12254 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12254 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12254 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12254 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12254 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12254 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12252 128 * √(2 / (12254 : ℝ)) *
      (√(12254 : ℝ) + paperT0 12254 + paperTail256 12254) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12254 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12254 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12254 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12252 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12252 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12254 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12254

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12254
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12254 (61 / 100) 160 (17 / (100 * 12254)) (26 / (10 * 12254)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12254 (61 / 100) 160 (17 / (100 * 12254)) := by
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
          (8 * tA 12254 / 12254 * (61 / 100)) ^ 4 * inverseRadius8 (12254 - 1) /
            envelopeGap 12254 (61 / 100) 160 (17 / (100 * 12254)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12254

namespace BstLean.Part262.Row12254
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12254 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12254 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12254 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12254 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12254 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12254) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12254) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12254) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12254) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12254) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12254 * (160 : ℝ) ^ 2 + 26 / (10 * 12254) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12254) : ℝ)) (tA 12254 * 160 ^ 2 + 26 / (10 * 12254)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12254) : ℝ)) d.D d.V d.P (√(tA 12254) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12254) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12254) : ℝ)) (tA 12254 * 160 ^ 2 + 26 / (10 * 12254)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12254) : ℝ)) (√(26 / (10 * 12254) : ℝ)) d.D d.V d.P (√(tA 12254) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12254) * 160) ≤ _
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

end BstLean.Part262.Row12254

namespace BstLean.Part262.Row12254
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12254 160 ∧
    0 ≤ (tableEnvelope C).f1 12254 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12254 160 ∧
    0 ≤ (tableEnvelope C).w1 12254 160 ∧ 0 ≤ (tableEnvelope C).w2 12254 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12254 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12254 160 ∧ 0 ≤ d.f1 12254 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12254 160 ∧ 0 ≤ d.w1 12254 160 ∧ 0 ≤ d.w2 12254 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12254 ≤ 2 * (228 / 100 : ℝ) / 12254 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12254 ≤ 2 * (370 / 100 : ℝ) / 12254 := by
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
    (completeRAData (tableEnvelope C) 12254 160).locationBound 12254 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12254 160).energyBound 12254 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12254 160) (d.f1 12254 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12254 160) (d.w1 12254 160)
      (d.w2 12254 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12254 160) (d.f1 12254 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12254 160) (d.f1 12254 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12254 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12254 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12254 160) (d.f1 12254 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12254 160) (d.w1 12254 160) (d.w2 12254 160)
  have hwexpr0 : 0 ≤ d.w0 12254 160 + d.w1 12254 160 * √(π / 2) +
      2 * d.w2 12254 160 + energyR16 12254 *
      radiusPolynomialRoot16 (d.w0 12254 160) (d.w1 12254 160) (d.w2 12254 160) := by
    positivity
  constructor
  · change (12254 : ℝ) ^ 8 * (mA 12254 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12254 160) (d.f1 12254 160) d.f2 + locationR16 12254 *
        radiusPolynomialRoot16 (d.f0 12254 160) (d.f1 12254 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12254 : ℝ) ^ 8 * (mA 12254 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12254) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12254 : ℝ) ^ 16 *
      (d.w0 12254 160 + d.w1 12254 160 * √(π / 2) + 2 * d.w2 12254 160 +
        energyR16 12254 * radiusPolynomialRoot16 (d.w0 12254 160) (d.w1 12254 160)
          (d.w2 12254 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12254 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12254) *
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

end BstLean.Part262.Row12254

/-! A coarse bound on the actual paper statistics constant at dimension 12255. -/
namespace BstLean.Part262.Row12255
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12253 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12253 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12253 128 ≤ (12507 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12507 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12255) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12255 : ℕ))
    (by norm_num : (12255 : ℕ) ≤ 16384)
  have ht : paperTail256 12255 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12255 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12255 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12255 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12255 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12255 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12253 128 * √(2 / (12255 : ℝ)) *
      (√(12255 : ℝ) + paperT0 12255 + paperTail256 12255) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12255 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12255 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12255 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12253 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12253 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12255 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12255

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12255
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12255 (61 / 100) 160 (17 / (100 * 12255)) (26 / (10 * 12255)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12255 (61 / 100) 160 (17 / (100 * 12255)) := by
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
          (8 * tA 12255 / 12255 * (61 / 100)) ^ 4 * inverseRadius8 (12255 - 1) /
            envelopeGap 12255 (61 / 100) 160 (17 / (100 * 12255)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12255

namespace BstLean.Part262.Row12255
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12255 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12255 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12255 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12255 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12255 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12255) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12255) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12255) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12255) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12255) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12255 * (160 : ℝ) ^ 2 + 26 / (10 * 12255) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12255) : ℝ)) (tA 12255 * 160 ^ 2 + 26 / (10 * 12255)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12255) : ℝ)) d.D d.V d.P (√(tA 12255) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12255) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12255) : ℝ)) (tA 12255 * 160 ^ 2 + 26 / (10 * 12255)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12255) : ℝ)) (√(26 / (10 * 12255) : ℝ)) d.D d.V d.P (√(tA 12255) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12255) * 160) ≤ _
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

end BstLean.Part262.Row12255

namespace BstLean.Part262.Row12255
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12255 160 ∧
    0 ≤ (tableEnvelope C).f1 12255 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12255 160 ∧
    0 ≤ (tableEnvelope C).w1 12255 160 ∧ 0 ≤ (tableEnvelope C).w2 12255 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12255 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12255 160 ∧ 0 ≤ d.f1 12255 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12255 160 ∧ 0 ≤ d.w1 12255 160 ∧ 0 ≤ d.w2 12255 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12255 ≤ 2 * (228 / 100 : ℝ) / 12255 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12255 ≤ 2 * (370 / 100 : ℝ) / 12255 := by
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
    (completeRAData (tableEnvelope C) 12255 160).locationBound 12255 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12255 160).energyBound 12255 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12255 160) (d.f1 12255 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12255 160) (d.w1 12255 160)
      (d.w2 12255 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12255 160) (d.f1 12255 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12255 160) (d.f1 12255 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12255 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12255 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12255 160) (d.f1 12255 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12255 160) (d.w1 12255 160) (d.w2 12255 160)
  have hwexpr0 : 0 ≤ d.w0 12255 160 + d.w1 12255 160 * √(π / 2) +
      2 * d.w2 12255 160 + energyR16 12255 *
      radiusPolynomialRoot16 (d.w0 12255 160) (d.w1 12255 160) (d.w2 12255 160) := by
    positivity
  constructor
  · change (12255 : ℝ) ^ 8 * (mA 12255 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12255 160) (d.f1 12255 160) d.f2 + locationR16 12255 *
        radiusPolynomialRoot16 (d.f0 12255 160) (d.f1 12255 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12255 : ℝ) ^ 8 * (mA 12255 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12255) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12255 : ℝ) ^ 16 *
      (d.w0 12255 160 + d.w1 12255 160 * √(π / 2) + 2 * d.w2 12255 160 +
        energyR16 12255 * radiusPolynomialRoot16 (d.w0 12255 160) (d.w1 12255 160)
          (d.w2 12255 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12255 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12255) *
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

end BstLean.Part262.Row12255

/-! A coarse bound on the actual paper statistics constant at dimension 12256. -/
namespace BstLean.Part262.Row12256
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12254 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12254 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12254 128 ≤ (12508 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12508 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12256) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12256 : ℕ))
    (by norm_num : (12256 : ℕ) ≤ 16384)
  have ht : paperTail256 12256 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12256 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12256 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12256 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12256 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12256 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12254 128 * √(2 / (12256 : ℝ)) *
      (√(12256 : ℝ) + paperT0 12256 + paperTail256 12256) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12256 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12256 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12256 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12254 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12254 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12256 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12256

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12256
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12256 (61 / 100) 160 (17 / (100 * 12256)) (26 / (10 * 12256)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12256 (61 / 100) 160 (17 / (100 * 12256)) := by
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
          (8 * tA 12256 / 12256 * (61 / 100)) ^ 4 * inverseRadius8 (12256 - 1) /
            envelopeGap 12256 (61 / 100) 160 (17 / (100 * 12256)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12256

namespace BstLean.Part262.Row12256
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12256 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12256 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12256 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12256 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12256 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12256) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12256) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12256) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12256) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12256) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12256 * (160 : ℝ) ^ 2 + 26 / (10 * 12256) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12256) : ℝ)) (tA 12256 * 160 ^ 2 + 26 / (10 * 12256)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12256) : ℝ)) d.D d.V d.P (√(tA 12256) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12256) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12256) : ℝ)) (tA 12256 * 160 ^ 2 + 26 / (10 * 12256)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12256) : ℝ)) (√(26 / (10 * 12256) : ℝ)) d.D d.V d.P (√(tA 12256) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12256) * 160) ≤ _
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

end BstLean.Part262.Row12256

namespace BstLean.Part262.Row12256
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12256 160 ∧
    0 ≤ (tableEnvelope C).f1 12256 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12256 160 ∧
    0 ≤ (tableEnvelope C).w1 12256 160 ∧ 0 ≤ (tableEnvelope C).w2 12256 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12256 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12256 160 ∧ 0 ≤ d.f1 12256 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12256 160 ∧ 0 ≤ d.w1 12256 160 ∧ 0 ≤ d.w2 12256 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12256 ≤ 2 * (228 / 100 : ℝ) / 12256 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12256 ≤ 2 * (370 / 100 : ℝ) / 12256 := by
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
    (completeRAData (tableEnvelope C) 12256 160).locationBound 12256 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12256 160).energyBound 12256 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12256 160) (d.f1 12256 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12256 160) (d.w1 12256 160)
      (d.w2 12256 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12256 160) (d.f1 12256 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12256 160) (d.f1 12256 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12256 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12256 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12256 160) (d.f1 12256 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12256 160) (d.w1 12256 160) (d.w2 12256 160)
  have hwexpr0 : 0 ≤ d.w0 12256 160 + d.w1 12256 160 * √(π / 2) +
      2 * d.w2 12256 160 + energyR16 12256 *
      radiusPolynomialRoot16 (d.w0 12256 160) (d.w1 12256 160) (d.w2 12256 160) := by
    positivity
  constructor
  · change (12256 : ℝ) ^ 8 * (mA 12256 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12256 160) (d.f1 12256 160) d.f2 + locationR16 12256 *
        radiusPolynomialRoot16 (d.f0 12256 160) (d.f1 12256 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12256 : ℝ) ^ 8 * (mA 12256 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12256) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12256 : ℝ) ^ 16 *
      (d.w0 12256 160 + d.w1 12256 160 * √(π / 2) + 2 * d.w2 12256 160 +
        energyR16 12256 * radiusPolynomialRoot16 (d.w0 12256 160) (d.w1 12256 160)
          (d.w2 12256 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12256 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12256) *
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

end BstLean.Part262.Row12256

/-! A coarse bound on the actual paper statistics constant at dimension 12257. -/
namespace BstLean.Part262.Row12257
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12255 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12255 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12255 128 ≤ (12509 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12509 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12257) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12257 : ℕ))
    (by norm_num : (12257 : ℕ) ≤ 16384)
  have ht : paperTail256 12257 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12257 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12257 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12257 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12257 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12257 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12255 128 * √(2 / (12257 : ℝ)) *
      (√(12257 : ℝ) + paperT0 12257 + paperTail256 12257) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12257 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12257 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12257 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12255 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12255 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12257 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12257

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12257
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12257 (61 / 100) 160 (17 / (100 * 12257)) (26 / (10 * 12257)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12257 (61 / 100) 160 (17 / (100 * 12257)) := by
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
          (8 * tA 12257 / 12257 * (61 / 100)) ^ 4 * inverseRadius8 (12257 - 1) /
            envelopeGap 12257 (61 / 100) 160 (17 / (100 * 12257)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12257

namespace BstLean.Part262.Row12257
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12257 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12257 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12257 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12257 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12257 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12257) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12257) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12257) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12257) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12257) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12257 * (160 : ℝ) ^ 2 + 26 / (10 * 12257) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12257) : ℝ)) (tA 12257 * 160 ^ 2 + 26 / (10 * 12257)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12257) : ℝ)) d.D d.V d.P (√(tA 12257) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12257) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12257) : ℝ)) (tA 12257 * 160 ^ 2 + 26 / (10 * 12257)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12257) : ℝ)) (√(26 / (10 * 12257) : ℝ)) d.D d.V d.P (√(tA 12257) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12257) * 160) ≤ _
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

end BstLean.Part262.Row12257

namespace BstLean.Part262.Row12257
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12257 160 ∧
    0 ≤ (tableEnvelope C).f1 12257 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12257 160 ∧
    0 ≤ (tableEnvelope C).w1 12257 160 ∧ 0 ≤ (tableEnvelope C).w2 12257 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12257 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12257 160 ∧ 0 ≤ d.f1 12257 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12257 160 ∧ 0 ≤ d.w1 12257 160 ∧ 0 ≤ d.w2 12257 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12257 ≤ 2 * (228 / 100 : ℝ) / 12257 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12257 ≤ 2 * (370 / 100 : ℝ) / 12257 := by
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
    (completeRAData (tableEnvelope C) 12257 160).locationBound 12257 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12257 160).energyBound 12257 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12257 160) (d.f1 12257 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12257 160) (d.w1 12257 160)
      (d.w2 12257 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12257 160) (d.f1 12257 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12257 160) (d.f1 12257 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12257 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12257 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12257 160) (d.f1 12257 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12257 160) (d.w1 12257 160) (d.w2 12257 160)
  have hwexpr0 : 0 ≤ d.w0 12257 160 + d.w1 12257 160 * √(π / 2) +
      2 * d.w2 12257 160 + energyR16 12257 *
      radiusPolynomialRoot16 (d.w0 12257 160) (d.w1 12257 160) (d.w2 12257 160) := by
    positivity
  constructor
  · change (12257 : ℝ) ^ 8 * (mA 12257 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12257 160) (d.f1 12257 160) d.f2 + locationR16 12257 *
        radiusPolynomialRoot16 (d.f0 12257 160) (d.f1 12257 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12257 : ℝ) ^ 8 * (mA 12257 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12257) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12257 : ℝ) ^ 16 *
      (d.w0 12257 160 + d.w1 12257 160 * √(π / 2) + 2 * d.w2 12257 160 +
        energyR16 12257 * radiusPolynomialRoot16 (d.w0 12257 160) (d.w1 12257 160)
          (d.w2 12257 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12257 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12257) *
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

end BstLean.Part262.Row12257

/-! A coarse bound on the actual paper statistics constant at dimension 12258. -/
namespace BstLean.Part262.Row12258
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12256 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12256 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12256 128 ≤ (12510 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12510 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12258) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12258 : ℕ))
    (by norm_num : (12258 : ℕ) ≤ 16384)
  have ht : paperTail256 12258 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12258 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12258 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12258 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12258 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12258 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12256 128 * √(2 / (12258 : ℝ)) *
      (√(12258 : ℝ) + paperT0 12258 + paperTail256 12258) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12258 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12258 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12258 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12256 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12256 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12258 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12258

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12258
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12258 (61 / 100) 160 (17 / (100 * 12258)) (26 / (10 * 12258)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12258 (61 / 100) 160 (17 / (100 * 12258)) := by
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
          (8 * tA 12258 / 12258 * (61 / 100)) ^ 4 * inverseRadius8 (12258 - 1) /
            envelopeGap 12258 (61 / 100) 160 (17 / (100 * 12258)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12258

namespace BstLean.Part262.Row12258
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12258 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12258 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12258 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12258 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12258 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12258) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12258) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12258) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12258) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12258) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12258 * (160 : ℝ) ^ 2 + 26 / (10 * 12258) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12258) : ℝ)) (tA 12258 * 160 ^ 2 + 26 / (10 * 12258)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12258) : ℝ)) d.D d.V d.P (√(tA 12258) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12258) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12258) : ℝ)) (tA 12258 * 160 ^ 2 + 26 / (10 * 12258)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12258) : ℝ)) (√(26 / (10 * 12258) : ℝ)) d.D d.V d.P (√(tA 12258) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12258) * 160) ≤ _
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

end BstLean.Part262.Row12258

namespace BstLean.Part262.Row12258
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12258 160 ∧
    0 ≤ (tableEnvelope C).f1 12258 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12258 160 ∧
    0 ≤ (tableEnvelope C).w1 12258 160 ∧ 0 ≤ (tableEnvelope C).w2 12258 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12258 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12258 160 ∧ 0 ≤ d.f1 12258 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12258 160 ∧ 0 ≤ d.w1 12258 160 ∧ 0 ≤ d.w2 12258 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12258 ≤ 2 * (228 / 100 : ℝ) / 12258 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12258 ≤ 2 * (370 / 100 : ℝ) / 12258 := by
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
    (completeRAData (tableEnvelope C) 12258 160).locationBound 12258 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12258 160).energyBound 12258 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12258 160) (d.f1 12258 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12258 160) (d.w1 12258 160)
      (d.w2 12258 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12258 160) (d.f1 12258 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12258 160) (d.f1 12258 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12258 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12258 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12258 160) (d.f1 12258 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12258 160) (d.w1 12258 160) (d.w2 12258 160)
  have hwexpr0 : 0 ≤ d.w0 12258 160 + d.w1 12258 160 * √(π / 2) +
      2 * d.w2 12258 160 + energyR16 12258 *
      radiusPolynomialRoot16 (d.w0 12258 160) (d.w1 12258 160) (d.w2 12258 160) := by
    positivity
  constructor
  · change (12258 : ℝ) ^ 8 * (mA 12258 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12258 160) (d.f1 12258 160) d.f2 + locationR16 12258 *
        radiusPolynomialRoot16 (d.f0 12258 160) (d.f1 12258 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12258 : ℝ) ^ 8 * (mA 12258 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12258) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12258 : ℝ) ^ 16 *
      (d.w0 12258 160 + d.w1 12258 160 * √(π / 2) + 2 * d.w2 12258 160 +
        energyR16 12258 * radiusPolynomialRoot16 (d.w0 12258 160) (d.w1 12258 160)
          (d.w2 12258 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12258 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12258) *
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

end BstLean.Part262.Row12258

/-! A coarse bound on the actual paper statistics constant at dimension 12259. -/
namespace BstLean.Part262.Row12259
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12257 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12257 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12257 128 ≤ (12511 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12511 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12259) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12259 : ℕ))
    (by norm_num : (12259 : ℕ) ≤ 16384)
  have ht : paperTail256 12259 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12259 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12259 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12259 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12259 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12259 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12257 128 * √(2 / (12259 : ℝ)) *
      (√(12259 : ℝ) + paperT0 12259 + paperTail256 12259) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12259 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12259 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12259 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12257 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12257 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12259 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12259

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12259
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12259 (61 / 100) 160 (17 / (100 * 12259)) (26 / (10 * 12259)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12259 (61 / 100) 160 (17 / (100 * 12259)) := by
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
          (8 * tA 12259 / 12259 * (61 / 100)) ^ 4 * inverseRadius8 (12259 - 1) /
            envelopeGap 12259 (61 / 100) 160 (17 / (100 * 12259)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12259

namespace BstLean.Part262.Row12259
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12259 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12259 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12259 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12259 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12259 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12259) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12259) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12259) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12259) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12259) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12259 * (160 : ℝ) ^ 2 + 26 / (10 * 12259) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12259) : ℝ)) (tA 12259 * 160 ^ 2 + 26 / (10 * 12259)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12259) : ℝ)) d.D d.V d.P (√(tA 12259) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12259) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12259) : ℝ)) (tA 12259 * 160 ^ 2 + 26 / (10 * 12259)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12259) : ℝ)) (√(26 / (10 * 12259) : ℝ)) d.D d.V d.P (√(tA 12259) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12259) * 160) ≤ _
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

end BstLean.Part262.Row12259

namespace BstLean.Part262.Row12259
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12259 160 ∧
    0 ≤ (tableEnvelope C).f1 12259 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12259 160 ∧
    0 ≤ (tableEnvelope C).w1 12259 160 ∧ 0 ≤ (tableEnvelope C).w2 12259 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12259 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12259 160 ∧ 0 ≤ d.f1 12259 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12259 160 ∧ 0 ≤ d.w1 12259 160 ∧ 0 ≤ d.w2 12259 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12259 ≤ 2 * (228 / 100 : ℝ) / 12259 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12259 ≤ 2 * (370 / 100 : ℝ) / 12259 := by
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
    (completeRAData (tableEnvelope C) 12259 160).locationBound 12259 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12259 160).energyBound 12259 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12259 160) (d.f1 12259 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12259 160) (d.w1 12259 160)
      (d.w2 12259 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12259 160) (d.f1 12259 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12259 160) (d.f1 12259 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12259 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12259 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12259 160) (d.f1 12259 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12259 160) (d.w1 12259 160) (d.w2 12259 160)
  have hwexpr0 : 0 ≤ d.w0 12259 160 + d.w1 12259 160 * √(π / 2) +
      2 * d.w2 12259 160 + energyR16 12259 *
      radiusPolynomialRoot16 (d.w0 12259 160) (d.w1 12259 160) (d.w2 12259 160) := by
    positivity
  constructor
  · change (12259 : ℝ) ^ 8 * (mA 12259 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12259 160) (d.f1 12259 160) d.f2 + locationR16 12259 *
        radiusPolynomialRoot16 (d.f0 12259 160) (d.f1 12259 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12259 : ℝ) ^ 8 * (mA 12259 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12259) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12259 : ℝ) ^ 16 *
      (d.w0 12259 160 + d.w1 12259 160 * √(π / 2) + 2 * d.w2 12259 160 +
        energyR16 12259 * radiusPolynomialRoot16 (d.w0 12259 160) (d.w1 12259 160)
          (d.w2 12259 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12259 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12259) *
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

end BstLean.Part262.Row12259

/-! A coarse bound on the actual paper statistics constant at dimension 12260. -/
namespace BstLean.Part262.Row12260
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12258 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12258 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12258 128 ≤ (12512 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12512 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12260) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12260 : ℕ))
    (by norm_num : (12260 : ℕ) ≤ 16384)
  have ht : paperTail256 12260 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12260 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12260 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12260 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12260 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12260 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12258 128 * √(2 / (12260 : ℝ)) *
      (√(12260 : ℝ) + paperT0 12260 + paperTail256 12260) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12260 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12260 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12260 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12258 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12258 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12260 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12260

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12260
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12260 (61 / 100) 160 (17 / (100 * 12260)) (26 / (10 * 12260)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12260 (61 / 100) 160 (17 / (100 * 12260)) := by
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
          (8 * tA 12260 / 12260 * (61 / 100)) ^ 4 * inverseRadius8 (12260 - 1) /
            envelopeGap 12260 (61 / 100) 160 (17 / (100 * 12260)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12260

namespace BstLean.Part262.Row12260
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12260 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12260 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12260 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12260 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12260 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12260) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12260) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12260) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12260) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12260) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12260 * (160 : ℝ) ^ 2 + 26 / (10 * 12260) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12260) : ℝ)) (tA 12260 * 160 ^ 2 + 26 / (10 * 12260)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12260) : ℝ)) d.D d.V d.P (√(tA 12260) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12260) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12260) : ℝ)) (tA 12260 * 160 ^ 2 + 26 / (10 * 12260)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12260) : ℝ)) (√(26 / (10 * 12260) : ℝ)) d.D d.V d.P (√(tA 12260) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12260) * 160) ≤ _
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

end BstLean.Part262.Row12260

namespace BstLean.Part262.Row12260
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12260 160 ∧
    0 ≤ (tableEnvelope C).f1 12260 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12260 160 ∧
    0 ≤ (tableEnvelope C).w1 12260 160 ∧ 0 ≤ (tableEnvelope C).w2 12260 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12260 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12260 160 ∧ 0 ≤ d.f1 12260 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12260 160 ∧ 0 ≤ d.w1 12260 160 ∧ 0 ≤ d.w2 12260 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12260 ≤ 2 * (228 / 100 : ℝ) / 12260 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12260 ≤ 2 * (370 / 100 : ℝ) / 12260 := by
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
    (completeRAData (tableEnvelope C) 12260 160).locationBound 12260 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12260 160).energyBound 12260 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12260 160) (d.f1 12260 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12260 160) (d.w1 12260 160)
      (d.w2 12260 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12260 160) (d.f1 12260 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12260 160) (d.f1 12260 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12260 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12260 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12260 160) (d.f1 12260 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12260 160) (d.w1 12260 160) (d.w2 12260 160)
  have hwexpr0 : 0 ≤ d.w0 12260 160 + d.w1 12260 160 * √(π / 2) +
      2 * d.w2 12260 160 + energyR16 12260 *
      radiusPolynomialRoot16 (d.w0 12260 160) (d.w1 12260 160) (d.w2 12260 160) := by
    positivity
  constructor
  · change (12260 : ℝ) ^ 8 * (mA 12260 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12260 160) (d.f1 12260 160) d.f2 + locationR16 12260 *
        radiusPolynomialRoot16 (d.f0 12260 160) (d.f1 12260 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12260 : ℝ) ^ 8 * (mA 12260 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12260) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12260 : ℝ) ^ 16 *
      (d.w0 12260 160 + d.w1 12260 160 * √(π / 2) + 2 * d.w2 12260 160 +
        energyR16 12260 * radiusPolynomialRoot16 (d.w0 12260 160) (d.w1 12260 160)
          (d.w2 12260 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12260 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12260) *
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

end BstLean.Part262.Row12260

/-! A coarse bound on the actual paper statistics constant at dimension 12261. -/
namespace BstLean.Part262.Row12261
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12259 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12259 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12259 128 ≤ (12513 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12513 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12261) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12261 : ℕ))
    (by norm_num : (12261 : ℕ) ≤ 16384)
  have ht : paperTail256 12261 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12261 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12261 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12261 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12261 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12261 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12259 128 * √(2 / (12261 : ℝ)) *
      (√(12261 : ℝ) + paperT0 12261 + paperTail256 12261) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12261 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12261 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12261 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12259 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12259 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12261 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12261

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12261
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12261 (61 / 100) 160 (17 / (100 * 12261)) (26 / (10 * 12261)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12261 (61 / 100) 160 (17 / (100 * 12261)) := by
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
          (8 * tA 12261 / 12261 * (61 / 100)) ^ 4 * inverseRadius8 (12261 - 1) /
            envelopeGap 12261 (61 / 100) 160 (17 / (100 * 12261)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12261

namespace BstLean.Part262.Row12261
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12261 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12261 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12261 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12261 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12261 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12261) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12261) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12261) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12261) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12261) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12261 * (160 : ℝ) ^ 2 + 26 / (10 * 12261) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12261) : ℝ)) (tA 12261 * 160 ^ 2 + 26 / (10 * 12261)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12261) : ℝ)) d.D d.V d.P (√(tA 12261) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12261) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12261) : ℝ)) (tA 12261 * 160 ^ 2 + 26 / (10 * 12261)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12261) : ℝ)) (√(26 / (10 * 12261) : ℝ)) d.D d.V d.P (√(tA 12261) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12261) * 160) ≤ _
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

end BstLean.Part262.Row12261

namespace BstLean.Part262.Row12261
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12261 160 ∧
    0 ≤ (tableEnvelope C).f1 12261 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12261 160 ∧
    0 ≤ (tableEnvelope C).w1 12261 160 ∧ 0 ≤ (tableEnvelope C).w2 12261 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12261 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12261 160 ∧ 0 ≤ d.f1 12261 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12261 160 ∧ 0 ≤ d.w1 12261 160 ∧ 0 ≤ d.w2 12261 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12261 ≤ 2 * (228 / 100 : ℝ) / 12261 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12261 ≤ 2 * (370 / 100 : ℝ) / 12261 := by
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
    (completeRAData (tableEnvelope C) 12261 160).locationBound 12261 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12261 160).energyBound 12261 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12261 160) (d.f1 12261 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12261 160) (d.w1 12261 160)
      (d.w2 12261 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12261 160) (d.f1 12261 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12261 160) (d.f1 12261 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12261 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12261 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12261 160) (d.f1 12261 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12261 160) (d.w1 12261 160) (d.w2 12261 160)
  have hwexpr0 : 0 ≤ d.w0 12261 160 + d.w1 12261 160 * √(π / 2) +
      2 * d.w2 12261 160 + energyR16 12261 *
      radiusPolynomialRoot16 (d.w0 12261 160) (d.w1 12261 160) (d.w2 12261 160) := by
    positivity
  constructor
  · change (12261 : ℝ) ^ 8 * (mA 12261 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12261 160) (d.f1 12261 160) d.f2 + locationR16 12261 *
        radiusPolynomialRoot16 (d.f0 12261 160) (d.f1 12261 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12261 : ℝ) ^ 8 * (mA 12261 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12261) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12261 : ℝ) ^ 16 *
      (d.w0 12261 160 + d.w1 12261 160 * √(π / 2) + 2 * d.w2 12261 160 +
        energyR16 12261 * radiusPolynomialRoot16 (d.w0 12261 160) (d.w1 12261 160)
          (d.w2 12261 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12261 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12261) *
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

end BstLean.Part262.Row12261

/-! A coarse bound on the actual paper statistics constant at dimension 12262. -/
namespace BstLean.Part262.Row12262
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12260 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12260 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12260 128 ≤ (12514 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12514 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12262) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12262 : ℕ))
    (by norm_num : (12262 : ℕ) ≤ 16384)
  have ht : paperTail256 12262 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12262 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12262 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12262 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12262 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12262 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12260 128 * √(2 / (12262 : ℝ)) *
      (√(12262 : ℝ) + paperT0 12262 + paperTail256 12262) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12262 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12262 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12262 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12260 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12260 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12262 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12262

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12262
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12262 (61 / 100) 160 (17 / (100 * 12262)) (26 / (10 * 12262)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12262 (61 / 100) 160 (17 / (100 * 12262)) := by
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
          (8 * tA 12262 / 12262 * (61 / 100)) ^ 4 * inverseRadius8 (12262 - 1) /
            envelopeGap 12262 (61 / 100) 160 (17 / (100 * 12262)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12262

namespace BstLean.Part262.Row12262
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12262 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12262 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12262 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12262 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12262 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12262) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12262) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12262) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12262) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12262) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12262 * (160 : ℝ) ^ 2 + 26 / (10 * 12262) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12262) : ℝ)) (tA 12262 * 160 ^ 2 + 26 / (10 * 12262)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12262) : ℝ)) d.D d.V d.P (√(tA 12262) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12262) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12262) : ℝ)) (tA 12262 * 160 ^ 2 + 26 / (10 * 12262)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12262) : ℝ)) (√(26 / (10 * 12262) : ℝ)) d.D d.V d.P (√(tA 12262) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12262) * 160) ≤ _
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

end BstLean.Part262.Row12262

namespace BstLean.Part262.Row12262
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12262 160 ∧
    0 ≤ (tableEnvelope C).f1 12262 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12262 160 ∧
    0 ≤ (tableEnvelope C).w1 12262 160 ∧ 0 ≤ (tableEnvelope C).w2 12262 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12262 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12262 160 ∧ 0 ≤ d.f1 12262 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12262 160 ∧ 0 ≤ d.w1 12262 160 ∧ 0 ≤ d.w2 12262 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12262 ≤ 2 * (228 / 100 : ℝ) / 12262 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12262 ≤ 2 * (370 / 100 : ℝ) / 12262 := by
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
    (completeRAData (tableEnvelope C) 12262 160).locationBound 12262 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12262 160).energyBound 12262 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12262 160) (d.f1 12262 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12262 160) (d.w1 12262 160)
      (d.w2 12262 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12262 160) (d.f1 12262 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12262 160) (d.f1 12262 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12262 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12262 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12262 160) (d.f1 12262 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12262 160) (d.w1 12262 160) (d.w2 12262 160)
  have hwexpr0 : 0 ≤ d.w0 12262 160 + d.w1 12262 160 * √(π / 2) +
      2 * d.w2 12262 160 + energyR16 12262 *
      radiusPolynomialRoot16 (d.w0 12262 160) (d.w1 12262 160) (d.w2 12262 160) := by
    positivity
  constructor
  · change (12262 : ℝ) ^ 8 * (mA 12262 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12262 160) (d.f1 12262 160) d.f2 + locationR16 12262 *
        radiusPolynomialRoot16 (d.f0 12262 160) (d.f1 12262 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12262 : ℝ) ^ 8 * (mA 12262 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12262) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12262 : ℝ) ^ 16 *
      (d.w0 12262 160 + d.w1 12262 160 * √(π / 2) + 2 * d.w2 12262 160 +
        energyR16 12262 * radiusPolynomialRoot16 (d.w0 12262 160) (d.w1 12262 160)
          (d.w2 12262 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12262 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12262) *
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

end BstLean.Part262.Row12262

/-! A coarse bound on the actual paper statistics constant at dimension 12263. -/
namespace BstLean.Part262.Row12263
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12261 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12261 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12261 128 ≤ (12515 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12515 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12263) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12263 : ℕ))
    (by norm_num : (12263 : ℕ) ≤ 16384)
  have ht : paperTail256 12263 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12263 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12263 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12263 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12263 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12263 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12261 128 * √(2 / (12263 : ℝ)) *
      (√(12263 : ℝ) + paperT0 12263 + paperTail256 12263) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12263 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12263 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12263 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12261 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12261 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12263 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12263

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12263
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12263 (61 / 100) 160 (17 / (100 * 12263)) (26 / (10 * 12263)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12263 (61 / 100) 160 (17 / (100 * 12263)) := by
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
          (8 * tA 12263 / 12263 * (61 / 100)) ^ 4 * inverseRadius8 (12263 - 1) /
            envelopeGap 12263 (61 / 100) 160 (17 / (100 * 12263)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12263

namespace BstLean.Part262.Row12263
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12263 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12263 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12263 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12263 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12263 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12263) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12263) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12263) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12263) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12263) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12263 * (160 : ℝ) ^ 2 + 26 / (10 * 12263) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12263) : ℝ)) (tA 12263 * 160 ^ 2 + 26 / (10 * 12263)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12263) : ℝ)) d.D d.V d.P (√(tA 12263) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12263) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12263) : ℝ)) (tA 12263 * 160 ^ 2 + 26 / (10 * 12263)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12263) : ℝ)) (√(26 / (10 * 12263) : ℝ)) d.D d.V d.P (√(tA 12263) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12263) * 160) ≤ _
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

end BstLean.Part262.Row12263

namespace BstLean.Part262.Row12263
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12263 160 ∧
    0 ≤ (tableEnvelope C).f1 12263 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12263 160 ∧
    0 ≤ (tableEnvelope C).w1 12263 160 ∧ 0 ≤ (tableEnvelope C).w2 12263 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12263 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12263 160 ∧ 0 ≤ d.f1 12263 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12263 160 ∧ 0 ≤ d.w1 12263 160 ∧ 0 ≤ d.w2 12263 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12263 ≤ 2 * (228 / 100 : ℝ) / 12263 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12263 ≤ 2 * (370 / 100 : ℝ) / 12263 := by
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
    (completeRAData (tableEnvelope C) 12263 160).locationBound 12263 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12263 160).energyBound 12263 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12263 160) (d.f1 12263 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12263 160) (d.w1 12263 160)
      (d.w2 12263 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12263 160) (d.f1 12263 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12263 160) (d.f1 12263 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12263 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12263 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12263 160) (d.f1 12263 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12263 160) (d.w1 12263 160) (d.w2 12263 160)
  have hwexpr0 : 0 ≤ d.w0 12263 160 + d.w1 12263 160 * √(π / 2) +
      2 * d.w2 12263 160 + energyR16 12263 *
      radiusPolynomialRoot16 (d.w0 12263 160) (d.w1 12263 160) (d.w2 12263 160) := by
    positivity
  constructor
  · change (12263 : ℝ) ^ 8 * (mA 12263 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12263 160) (d.f1 12263 160) d.f2 + locationR16 12263 *
        radiusPolynomialRoot16 (d.f0 12263 160) (d.f1 12263 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12263 : ℝ) ^ 8 * (mA 12263 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12263) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12263 : ℝ) ^ 16 *
      (d.w0 12263 160 + d.w1 12263 160 * √(π / 2) + 2 * d.w2 12263 160 +
        energyR16 12263 * radiusPolynomialRoot16 (d.w0 12263 160) (d.w1 12263 160)
          (d.w2 12263 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12263 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12263) *
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

end BstLean.Part262.Row12263

/-! A coarse bound on the actual paper statistics constant at dimension 12264. -/
namespace BstLean.Part262.Row12264
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12262 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12262 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12262 128 ≤ (12516 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12516 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12264) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12264 : ℕ))
    (by norm_num : (12264 : ℕ) ≤ 16384)
  have ht : paperTail256 12264 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12264 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12264 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12264 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12264 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12264 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12262 128 * √(2 / (12264 : ℝ)) *
      (√(12264 : ℝ) + paperT0 12264 + paperTail256 12264) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12264 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12264 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12264 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12262 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12262 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12264 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12264

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12264
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12264 (61 / 100) 160 (17 / (100 * 12264)) (26 / (10 * 12264)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12264 (61 / 100) 160 (17 / (100 * 12264)) := by
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
          (8 * tA 12264 / 12264 * (61 / 100)) ^ 4 * inverseRadius8 (12264 - 1) /
            envelopeGap 12264 (61 / 100) 160 (17 / (100 * 12264)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12264

namespace BstLean.Part262.Row12264
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12264 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12264 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12264 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12264 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12264 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12264) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12264) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12264) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12264) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12264) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12264 * (160 : ℝ) ^ 2 + 26 / (10 * 12264) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12264) : ℝ)) (tA 12264 * 160 ^ 2 + 26 / (10 * 12264)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12264) : ℝ)) d.D d.V d.P (√(tA 12264) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12264) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12264) : ℝ)) (tA 12264 * 160 ^ 2 + 26 / (10 * 12264)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12264) : ℝ)) (√(26 / (10 * 12264) : ℝ)) d.D d.V d.P (√(tA 12264) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12264) * 160) ≤ _
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

end BstLean.Part262.Row12264

namespace BstLean.Part262.Row12264
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12264 160 ∧
    0 ≤ (tableEnvelope C).f1 12264 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12264 160 ∧
    0 ≤ (tableEnvelope C).w1 12264 160 ∧ 0 ≤ (tableEnvelope C).w2 12264 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12264 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12264 160 ∧ 0 ≤ d.f1 12264 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12264 160 ∧ 0 ≤ d.w1 12264 160 ∧ 0 ≤ d.w2 12264 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12264 ≤ 2 * (228 / 100 : ℝ) / 12264 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12264 ≤ 2 * (370 / 100 : ℝ) / 12264 := by
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
    (completeRAData (tableEnvelope C) 12264 160).locationBound 12264 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12264 160).energyBound 12264 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12264 160) (d.f1 12264 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12264 160) (d.w1 12264 160)
      (d.w2 12264 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12264 160) (d.f1 12264 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12264 160) (d.f1 12264 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12264 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12264 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12264 160) (d.f1 12264 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12264 160) (d.w1 12264 160) (d.w2 12264 160)
  have hwexpr0 : 0 ≤ d.w0 12264 160 + d.w1 12264 160 * √(π / 2) +
      2 * d.w2 12264 160 + energyR16 12264 *
      radiusPolynomialRoot16 (d.w0 12264 160) (d.w1 12264 160) (d.w2 12264 160) := by
    positivity
  constructor
  · change (12264 : ℝ) ^ 8 * (mA 12264 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12264 160) (d.f1 12264 160) d.f2 + locationR16 12264 *
        radiusPolynomialRoot16 (d.f0 12264 160) (d.f1 12264 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12264 : ℝ) ^ 8 * (mA 12264 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12264) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12264 : ℝ) ^ 16 *
      (d.w0 12264 160 + d.w1 12264 160 * √(π / 2) + 2 * d.w2 12264 160 +
        energyR16 12264 * radiusPolynomialRoot16 (d.w0 12264 160) (d.w1 12264 160)
          (d.w2 12264 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12264 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12264) *
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

end BstLean.Part262.Row12264

/-! A coarse bound on the actual paper statistics constant at dimension 12265. -/
namespace BstLean.Part262.Row12265
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12263 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12263 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12263 128 ≤ (12517 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12517 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12265) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12265 : ℕ))
    (by norm_num : (12265 : ℕ) ≤ 16384)
  have ht : paperTail256 12265 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12265 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12265 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12265 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12265 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12265 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12263 128 * √(2 / (12265 : ℝ)) *
      (√(12265 : ℝ) + paperT0 12265 + paperTail256 12265) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12265 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12265 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12265 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12263 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12263 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12265 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12265

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12265
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12265 (61 / 100) 160 (17 / (100 * 12265)) (26 / (10 * 12265)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12265 (61 / 100) 160 (17 / (100 * 12265)) := by
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
          (8 * tA 12265 / 12265 * (61 / 100)) ^ 4 * inverseRadius8 (12265 - 1) /
            envelopeGap 12265 (61 / 100) 160 (17 / (100 * 12265)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12265

namespace BstLean.Part262.Row12265
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12265 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12265 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12265 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12265 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12265 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12265) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12265) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12265) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12265) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12265) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12265 * (160 : ℝ) ^ 2 + 26 / (10 * 12265) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12265) : ℝ)) (tA 12265 * 160 ^ 2 + 26 / (10 * 12265)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12265) : ℝ)) d.D d.V d.P (√(tA 12265) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12265) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12265) : ℝ)) (tA 12265 * 160 ^ 2 + 26 / (10 * 12265)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12265) : ℝ)) (√(26 / (10 * 12265) : ℝ)) d.D d.V d.P (√(tA 12265) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12265) * 160) ≤ _
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

end BstLean.Part262.Row12265

namespace BstLean.Part262.Row12265
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12265 160 ∧
    0 ≤ (tableEnvelope C).f1 12265 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12265 160 ∧
    0 ≤ (tableEnvelope C).w1 12265 160 ∧ 0 ≤ (tableEnvelope C).w2 12265 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12265 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12265 160 ∧ 0 ≤ d.f1 12265 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12265 160 ∧ 0 ≤ d.w1 12265 160 ∧ 0 ≤ d.w2 12265 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12265 ≤ 2 * (228 / 100 : ℝ) / 12265 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12265 ≤ 2 * (370 / 100 : ℝ) / 12265 := by
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
    (completeRAData (tableEnvelope C) 12265 160).locationBound 12265 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12265 160).energyBound 12265 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12265 160) (d.f1 12265 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12265 160) (d.w1 12265 160)
      (d.w2 12265 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12265 160) (d.f1 12265 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12265 160) (d.f1 12265 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12265 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12265 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12265 160) (d.f1 12265 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12265 160) (d.w1 12265 160) (d.w2 12265 160)
  have hwexpr0 : 0 ≤ d.w0 12265 160 + d.w1 12265 160 * √(π / 2) +
      2 * d.w2 12265 160 + energyR16 12265 *
      radiusPolynomialRoot16 (d.w0 12265 160) (d.w1 12265 160) (d.w2 12265 160) := by
    positivity
  constructor
  · change (12265 : ℝ) ^ 8 * (mA 12265 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12265 160) (d.f1 12265 160) d.f2 + locationR16 12265 *
        radiusPolynomialRoot16 (d.f0 12265 160) (d.f1 12265 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12265 : ℝ) ^ 8 * (mA 12265 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12265) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12265 : ℝ) ^ 16 *
      (d.w0 12265 160 + d.w1 12265 160 * √(π / 2) + 2 * d.w2 12265 160 +
        energyR16 12265 * radiusPolynomialRoot16 (d.w0 12265 160) (d.w1 12265 160)
          (d.w2 12265 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12265 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12265) *
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

end BstLean.Part262.Row12265

/-! A coarse bound on the actual paper statistics constant at dimension 12266. -/
namespace BstLean.Part262.Row12266
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12264 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12264 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12264 128 ≤ (12518 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12518 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12266) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12266 : ℕ))
    (by norm_num : (12266 : ℕ) ≤ 16384)
  have ht : paperTail256 12266 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12266 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12266 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12266 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12266 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12266 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12264 128 * √(2 / (12266 : ℝ)) *
      (√(12266 : ℝ) + paperT0 12266 + paperTail256 12266) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12266 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12266 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12266 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12264 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12264 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12266 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12266

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12266
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12266 (61 / 100) 160 (17 / (100 * 12266)) (26 / (10 * 12266)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12266 (61 / 100) 160 (17 / (100 * 12266)) := by
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
          (8 * tA 12266 / 12266 * (61 / 100)) ^ 4 * inverseRadius8 (12266 - 1) /
            envelopeGap 12266 (61 / 100) 160 (17 / (100 * 12266)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12266

namespace BstLean.Part262.Row12266
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12266 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12266 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12266 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12266 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12266 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12266) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12266) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12266) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12266) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12266) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12266 * (160 : ℝ) ^ 2 + 26 / (10 * 12266) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12266) : ℝ)) (tA 12266 * 160 ^ 2 + 26 / (10 * 12266)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12266) : ℝ)) d.D d.V d.P (√(tA 12266) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12266) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12266) : ℝ)) (tA 12266 * 160 ^ 2 + 26 / (10 * 12266)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12266) : ℝ)) (√(26 / (10 * 12266) : ℝ)) d.D d.V d.P (√(tA 12266) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12266) * 160) ≤ _
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

end BstLean.Part262.Row12266

namespace BstLean.Part262.Row12266
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12266 160 ∧
    0 ≤ (tableEnvelope C).f1 12266 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12266 160 ∧
    0 ≤ (tableEnvelope C).w1 12266 160 ∧ 0 ≤ (tableEnvelope C).w2 12266 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12266 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12266 160 ∧ 0 ≤ d.f1 12266 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12266 160 ∧ 0 ≤ d.w1 12266 160 ∧ 0 ≤ d.w2 12266 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12266 ≤ 2 * (228 / 100 : ℝ) / 12266 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12266 ≤ 2 * (370 / 100 : ℝ) / 12266 := by
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
    (completeRAData (tableEnvelope C) 12266 160).locationBound 12266 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12266 160).energyBound 12266 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12266 160) (d.f1 12266 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12266 160) (d.w1 12266 160)
      (d.w2 12266 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12266 160) (d.f1 12266 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12266 160) (d.f1 12266 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12266 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12266 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12266 160) (d.f1 12266 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12266 160) (d.w1 12266 160) (d.w2 12266 160)
  have hwexpr0 : 0 ≤ d.w0 12266 160 + d.w1 12266 160 * √(π / 2) +
      2 * d.w2 12266 160 + energyR16 12266 *
      radiusPolynomialRoot16 (d.w0 12266 160) (d.w1 12266 160) (d.w2 12266 160) := by
    positivity
  constructor
  · change (12266 : ℝ) ^ 8 * (mA 12266 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12266 160) (d.f1 12266 160) d.f2 + locationR16 12266 *
        radiusPolynomialRoot16 (d.f0 12266 160) (d.f1 12266 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12266 : ℝ) ^ 8 * (mA 12266 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12266) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12266 : ℝ) ^ 16 *
      (d.w0 12266 160 + d.w1 12266 160 * √(π / 2) + 2 * d.w2 12266 160 +
        energyR16 12266 * radiusPolynomialRoot16 (d.w0 12266 160) (d.w1 12266 160)
          (d.w2 12266 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12266 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12266) *
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

end BstLean.Part262.Row12266

/-! A coarse bound on the actual paper statistics constant at dimension 12267. -/
namespace BstLean.Part262.Row12267
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12265 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12265 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12265 128 ≤ (12519 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12519 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12267) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12267 : ℕ))
    (by norm_num : (12267 : ℕ) ≤ 16384)
  have ht : paperTail256 12267 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12267 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12267 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12267 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12267 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12267 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12265 128 * √(2 / (12267 : ℝ)) *
      (√(12267 : ℝ) + paperT0 12267 + paperTail256 12267) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12267 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12267 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12267 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12265 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12265 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12267 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12267

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12267
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12267 (61 / 100) 160 (17 / (100 * 12267)) (26 / (10 * 12267)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12267 (61 / 100) 160 (17 / (100 * 12267)) := by
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
          (8 * tA 12267 / 12267 * (61 / 100)) ^ 4 * inverseRadius8 (12267 - 1) /
            envelopeGap 12267 (61 / 100) 160 (17 / (100 * 12267)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12267

namespace BstLean.Part262.Row12267
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12267 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12267 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12267 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12267 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12267 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12267) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12267) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12267) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12267) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12267) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12267 * (160 : ℝ) ^ 2 + 26 / (10 * 12267) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12267) : ℝ)) (tA 12267 * 160 ^ 2 + 26 / (10 * 12267)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12267) : ℝ)) d.D d.V d.P (√(tA 12267) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12267) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12267) : ℝ)) (tA 12267 * 160 ^ 2 + 26 / (10 * 12267)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12267) : ℝ)) (√(26 / (10 * 12267) : ℝ)) d.D d.V d.P (√(tA 12267) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12267) * 160) ≤ _
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

end BstLean.Part262.Row12267

namespace BstLean.Part262.Row12267
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12267 160 ∧
    0 ≤ (tableEnvelope C).f1 12267 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12267 160 ∧
    0 ≤ (tableEnvelope C).w1 12267 160 ∧ 0 ≤ (tableEnvelope C).w2 12267 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12267 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12267 160 ∧ 0 ≤ d.f1 12267 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12267 160 ∧ 0 ≤ d.w1 12267 160 ∧ 0 ≤ d.w2 12267 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12267 ≤ 2 * (228 / 100 : ℝ) / 12267 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12267 ≤ 2 * (370 / 100 : ℝ) / 12267 := by
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
    (completeRAData (tableEnvelope C) 12267 160).locationBound 12267 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12267 160).energyBound 12267 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12267 160) (d.f1 12267 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12267 160) (d.w1 12267 160)
      (d.w2 12267 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12267 160) (d.f1 12267 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12267 160) (d.f1 12267 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12267 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12267 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12267 160) (d.f1 12267 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12267 160) (d.w1 12267 160) (d.w2 12267 160)
  have hwexpr0 : 0 ≤ d.w0 12267 160 + d.w1 12267 160 * √(π / 2) +
      2 * d.w2 12267 160 + energyR16 12267 *
      radiusPolynomialRoot16 (d.w0 12267 160) (d.w1 12267 160) (d.w2 12267 160) := by
    positivity
  constructor
  · change (12267 : ℝ) ^ 8 * (mA 12267 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12267 160) (d.f1 12267 160) d.f2 + locationR16 12267 *
        radiusPolynomialRoot16 (d.f0 12267 160) (d.f1 12267 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12267 : ℝ) ^ 8 * (mA 12267 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12267) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12267 : ℝ) ^ 16 *
      (d.w0 12267 160 + d.w1 12267 160 * √(π / 2) + 2 * d.w2 12267 160 +
        energyR16 12267 * radiusPolynomialRoot16 (d.w0 12267 160) (d.w1 12267 160)
          (d.w2 12267 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12267 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12267) *
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

end BstLean.Part262.Row12267

/-! A coarse bound on the actual paper statistics constant at dimension 12268. -/
namespace BstLean.Part262.Row12268
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12266 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12266 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12266 128 ≤ (12520 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12520 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12268) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12268 : ℕ))
    (by norm_num : (12268 : ℕ) ≤ 16384)
  have ht : paperTail256 12268 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12268 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12268 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12268 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12268 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12268 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12266 128 * √(2 / (12268 : ℝ)) *
      (√(12268 : ℝ) + paperT0 12268 + paperTail256 12268) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12268 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12268 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12268 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12266 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12266 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12268 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12268

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12268
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12268 (61 / 100) 160 (17 / (100 * 12268)) (26 / (10 * 12268)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12268 (61 / 100) 160 (17 / (100 * 12268)) := by
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
          (8 * tA 12268 / 12268 * (61 / 100)) ^ 4 * inverseRadius8 (12268 - 1) /
            envelopeGap 12268 (61 / 100) 160 (17 / (100 * 12268)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12268

namespace BstLean.Part262.Row12268
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12268 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12268 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12268 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12268 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12268 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12268) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12268) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12268) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12268) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12268) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12268 * (160 : ℝ) ^ 2 + 26 / (10 * 12268) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12268) : ℝ)) (tA 12268 * 160 ^ 2 + 26 / (10 * 12268)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12268) : ℝ)) d.D d.V d.P (√(tA 12268) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12268) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12268) : ℝ)) (tA 12268 * 160 ^ 2 + 26 / (10 * 12268)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12268) : ℝ)) (√(26 / (10 * 12268) : ℝ)) d.D d.V d.P (√(tA 12268) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12268) * 160) ≤ _
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

end BstLean.Part262.Row12268

namespace BstLean.Part262.Row12268
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12268 160 ∧
    0 ≤ (tableEnvelope C).f1 12268 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12268 160 ∧
    0 ≤ (tableEnvelope C).w1 12268 160 ∧ 0 ≤ (tableEnvelope C).w2 12268 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12268 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12268 160 ∧ 0 ≤ d.f1 12268 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12268 160 ∧ 0 ≤ d.w1 12268 160 ∧ 0 ≤ d.w2 12268 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12268 ≤ 2 * (228 / 100 : ℝ) / 12268 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12268 ≤ 2 * (370 / 100 : ℝ) / 12268 := by
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
    (completeRAData (tableEnvelope C) 12268 160).locationBound 12268 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12268 160).energyBound 12268 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12268 160) (d.f1 12268 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12268 160) (d.w1 12268 160)
      (d.w2 12268 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12268 160) (d.f1 12268 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12268 160) (d.f1 12268 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12268 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12268 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12268 160) (d.f1 12268 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12268 160) (d.w1 12268 160) (d.w2 12268 160)
  have hwexpr0 : 0 ≤ d.w0 12268 160 + d.w1 12268 160 * √(π / 2) +
      2 * d.w2 12268 160 + energyR16 12268 *
      radiusPolynomialRoot16 (d.w0 12268 160) (d.w1 12268 160) (d.w2 12268 160) := by
    positivity
  constructor
  · change (12268 : ℝ) ^ 8 * (mA 12268 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12268 160) (d.f1 12268 160) d.f2 + locationR16 12268 *
        radiusPolynomialRoot16 (d.f0 12268 160) (d.f1 12268 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12268 : ℝ) ^ 8 * (mA 12268 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12268) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12268 : ℝ) ^ 16 *
      (d.w0 12268 160 + d.w1 12268 160 * √(π / 2) + 2 * d.w2 12268 160 +
        energyR16 12268 * radiusPolynomialRoot16 (d.w0 12268 160) (d.w1 12268 160)
          (d.w2 12268 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12268 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12268) *
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

end BstLean.Part262.Row12268

/-! A coarse bound on the actual paper statistics constant at dimension 12269. -/
namespace BstLean.Part262.Row12269
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12267 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12267 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12267 128 ≤ (12521 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12521 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12269) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12269 : ℕ))
    (by norm_num : (12269 : ℕ) ≤ 16384)
  have ht : paperTail256 12269 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12269 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12269 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12269 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12269 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12269 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12267 128 * √(2 / (12269 : ℝ)) *
      (√(12269 : ℝ) + paperT0 12269 + paperTail256 12269) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12269 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12269 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12269 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12267 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12267 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12269 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12269

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12269
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12269 (61 / 100) 160 (17 / (100 * 12269)) (26 / (10 * 12269)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12269 (61 / 100) 160 (17 / (100 * 12269)) := by
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
          (8 * tA 12269 / 12269 * (61 / 100)) ^ 4 * inverseRadius8 (12269 - 1) /
            envelopeGap 12269 (61 / 100) 160 (17 / (100 * 12269)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12269

namespace BstLean.Part262.Row12269
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12269 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12269 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12269 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12269 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12269 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12269) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12269) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12269) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12269) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12269) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12269 * (160 : ℝ) ^ 2 + 26 / (10 * 12269) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12269) : ℝ)) (tA 12269 * 160 ^ 2 + 26 / (10 * 12269)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12269) : ℝ)) d.D d.V d.P (√(tA 12269) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12269) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12269) : ℝ)) (tA 12269 * 160 ^ 2 + 26 / (10 * 12269)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12269) : ℝ)) (√(26 / (10 * 12269) : ℝ)) d.D d.V d.P (√(tA 12269) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12269) * 160) ≤ _
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

end BstLean.Part262.Row12269

namespace BstLean.Part262.Row12269
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12269 160 ∧
    0 ≤ (tableEnvelope C).f1 12269 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12269 160 ∧
    0 ≤ (tableEnvelope C).w1 12269 160 ∧ 0 ≤ (tableEnvelope C).w2 12269 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12269 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12269 160 ∧ 0 ≤ d.f1 12269 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12269 160 ∧ 0 ≤ d.w1 12269 160 ∧ 0 ≤ d.w2 12269 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12269 ≤ 2 * (228 / 100 : ℝ) / 12269 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12269 ≤ 2 * (370 / 100 : ℝ) / 12269 := by
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
    (completeRAData (tableEnvelope C) 12269 160).locationBound 12269 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12269 160).energyBound 12269 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12269 160) (d.f1 12269 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12269 160) (d.w1 12269 160)
      (d.w2 12269 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12269 160) (d.f1 12269 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12269 160) (d.f1 12269 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12269 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12269 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12269 160) (d.f1 12269 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12269 160) (d.w1 12269 160) (d.w2 12269 160)
  have hwexpr0 : 0 ≤ d.w0 12269 160 + d.w1 12269 160 * √(π / 2) +
      2 * d.w2 12269 160 + energyR16 12269 *
      radiusPolynomialRoot16 (d.w0 12269 160) (d.w1 12269 160) (d.w2 12269 160) := by
    positivity
  constructor
  · change (12269 : ℝ) ^ 8 * (mA 12269 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12269 160) (d.f1 12269 160) d.f2 + locationR16 12269 *
        radiusPolynomialRoot16 (d.f0 12269 160) (d.f1 12269 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12269 : ℝ) ^ 8 * (mA 12269 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12269) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12269 : ℝ) ^ 16 *
      (d.w0 12269 160 + d.w1 12269 160 * √(π / 2) + 2 * d.w2 12269 160 +
        energyR16 12269 * radiusPolynomialRoot16 (d.w0 12269 160) (d.w1 12269 160)
          (d.w2 12269 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12269 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12269) *
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

end BstLean.Part262.Row12269

/-! A coarse bound on the actual paper statistics constant at dimension 12270. -/
namespace BstLean.Part262.Row12270
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12268 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12268 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12268 128 ≤ (12522 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12522 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12270) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12270 : ℕ))
    (by norm_num : (12270 : ℕ) ≤ 16384)
  have ht : paperTail256 12270 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12270 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12270 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12270 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12270 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12270 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12268 128 * √(2 / (12270 : ℝ)) *
      (√(12270 : ℝ) + paperT0 12270 + paperTail256 12270) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12270 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12270 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12270 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12268 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12268 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12270 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12270

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12270
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12270 (61 / 100) 160 (17 / (100 * 12270)) (26 / (10 * 12270)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12270 (61 / 100) 160 (17 / (100 * 12270)) := by
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
          (8 * tA 12270 / 12270 * (61 / 100)) ^ 4 * inverseRadius8 (12270 - 1) /
            envelopeGap 12270 (61 / 100) 160 (17 / (100 * 12270)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12270

namespace BstLean.Part262.Row12270
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12270 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12270 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12270 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12270 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12270 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12270) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12270) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12270) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12270) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12270) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12270 * (160 : ℝ) ^ 2 + 26 / (10 * 12270) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12270) : ℝ)) (tA 12270 * 160 ^ 2 + 26 / (10 * 12270)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12270) : ℝ)) d.D d.V d.P (√(tA 12270) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12270) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12270) : ℝ)) (tA 12270 * 160 ^ 2 + 26 / (10 * 12270)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12270) : ℝ)) (√(26 / (10 * 12270) : ℝ)) d.D d.V d.P (√(tA 12270) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12270) * 160) ≤ _
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

end BstLean.Part262.Row12270

namespace BstLean.Part262.Row12270
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12270 160 ∧
    0 ≤ (tableEnvelope C).f1 12270 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12270 160 ∧
    0 ≤ (tableEnvelope C).w1 12270 160 ∧ 0 ≤ (tableEnvelope C).w2 12270 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12270 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12270 160 ∧ 0 ≤ d.f1 12270 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12270 160 ∧ 0 ≤ d.w1 12270 160 ∧ 0 ≤ d.w2 12270 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12270 ≤ 2 * (228 / 100 : ℝ) / 12270 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12270 ≤ 2 * (370 / 100 : ℝ) / 12270 := by
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
    (completeRAData (tableEnvelope C) 12270 160).locationBound 12270 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12270 160).energyBound 12270 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12270 160) (d.f1 12270 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12270 160) (d.w1 12270 160)
      (d.w2 12270 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12270 160) (d.f1 12270 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12270 160) (d.f1 12270 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12270 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12270 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12270 160) (d.f1 12270 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12270 160) (d.w1 12270 160) (d.w2 12270 160)
  have hwexpr0 : 0 ≤ d.w0 12270 160 + d.w1 12270 160 * √(π / 2) +
      2 * d.w2 12270 160 + energyR16 12270 *
      radiusPolynomialRoot16 (d.w0 12270 160) (d.w1 12270 160) (d.w2 12270 160) := by
    positivity
  constructor
  · change (12270 : ℝ) ^ 8 * (mA 12270 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12270 160) (d.f1 12270 160) d.f2 + locationR16 12270 *
        radiusPolynomialRoot16 (d.f0 12270 160) (d.f1 12270 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12270 : ℝ) ^ 8 * (mA 12270 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12270) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12270 : ℝ) ^ 16 *
      (d.w0 12270 160 + d.w1 12270 160 * √(π / 2) + 2 * d.w2 12270 160 +
        energyR16 12270 * radiusPolynomialRoot16 (d.w0 12270 160) (d.w1 12270 160)
          (d.w2 12270 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12270 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12270) *
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

end BstLean.Part262.Row12270

/-! A coarse bound on the actual paper statistics constant at dimension 12271. -/
namespace BstLean.Part262.Row12271
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12269 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12269 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12269 128 ≤ (12523 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12523 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12271) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12271 : ℕ))
    (by norm_num : (12271 : ℕ) ≤ 16384)
  have ht : paperTail256 12271 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12271 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12271 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12271 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12271 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12271 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12269 128 * √(2 / (12271 : ℝ)) *
      (√(12271 : ℝ) + paperT0 12271 + paperTail256 12271) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12271 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12271 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12271 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12269 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12269 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12271 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12271

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12271
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12271 (61 / 100) 160 (17 / (100 * 12271)) (26 / (10 * 12271)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12271 (61 / 100) 160 (17 / (100 * 12271)) := by
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
          (8 * tA 12271 / 12271 * (61 / 100)) ^ 4 * inverseRadius8 (12271 - 1) /
            envelopeGap 12271 (61 / 100) 160 (17 / (100 * 12271)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12271

namespace BstLean.Part262.Row12271
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12271 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12271 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12271 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12271 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12271 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12271) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12271) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12271) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12271) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12271) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12271 * (160 : ℝ) ^ 2 + 26 / (10 * 12271) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12271) : ℝ)) (tA 12271 * 160 ^ 2 + 26 / (10 * 12271)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12271) : ℝ)) d.D d.V d.P (√(tA 12271) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12271) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12271) : ℝ)) (tA 12271 * 160 ^ 2 + 26 / (10 * 12271)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12271) : ℝ)) (√(26 / (10 * 12271) : ℝ)) d.D d.V d.P (√(tA 12271) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12271) * 160) ≤ _
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

end BstLean.Part262.Row12271

namespace BstLean.Part262.Row12271
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12271 160 ∧
    0 ≤ (tableEnvelope C).f1 12271 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12271 160 ∧
    0 ≤ (tableEnvelope C).w1 12271 160 ∧ 0 ≤ (tableEnvelope C).w2 12271 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12271 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12271 160 ∧ 0 ≤ d.f1 12271 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12271 160 ∧ 0 ≤ d.w1 12271 160 ∧ 0 ≤ d.w2 12271 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12271 ≤ 2 * (228 / 100 : ℝ) / 12271 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12271 ≤ 2 * (370 / 100 : ℝ) / 12271 := by
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
    (completeRAData (tableEnvelope C) 12271 160).locationBound 12271 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12271 160).energyBound 12271 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12271 160) (d.f1 12271 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12271 160) (d.w1 12271 160)
      (d.w2 12271 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12271 160) (d.f1 12271 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12271 160) (d.f1 12271 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12271 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12271 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12271 160) (d.f1 12271 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12271 160) (d.w1 12271 160) (d.w2 12271 160)
  have hwexpr0 : 0 ≤ d.w0 12271 160 + d.w1 12271 160 * √(π / 2) +
      2 * d.w2 12271 160 + energyR16 12271 *
      radiusPolynomialRoot16 (d.w0 12271 160) (d.w1 12271 160) (d.w2 12271 160) := by
    positivity
  constructor
  · change (12271 : ℝ) ^ 8 * (mA 12271 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12271 160) (d.f1 12271 160) d.f2 + locationR16 12271 *
        radiusPolynomialRoot16 (d.f0 12271 160) (d.f1 12271 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12271 : ℝ) ^ 8 * (mA 12271 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12271) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12271 : ℝ) ^ 16 *
      (d.w0 12271 160 + d.w1 12271 160 * √(π / 2) + 2 * d.w2 12271 160 +
        energyR16 12271 * radiusPolynomialRoot16 (d.w0 12271 160) (d.w1 12271 160)
          (d.w2 12271 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12271 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12271) *
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

end BstLean.Part262.Row12271

/-! A coarse bound on the actual paper statistics constant at dimension 12272. -/
namespace BstLean.Part262.Row12272
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12270 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12270 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12270 128 ≤ (12524 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12524 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12272) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12272 : ℕ))
    (by norm_num : (12272 : ℕ) ≤ 16384)
  have ht : paperTail256 12272 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12272 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12272 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12272 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12272 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12272 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12270 128 * √(2 / (12272 : ℝ)) *
      (√(12272 : ℝ) + paperT0 12272 + paperTail256 12272) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12272 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12272 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12272 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12270 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12270 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12272 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12272

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12272
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12272 (61 / 100) 160 (17 / (100 * 12272)) (26 / (10 * 12272)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12272 (61 / 100) 160 (17 / (100 * 12272)) := by
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
          (8 * tA 12272 / 12272 * (61 / 100)) ^ 4 * inverseRadius8 (12272 - 1) /
            envelopeGap 12272 (61 / 100) 160 (17 / (100 * 12272)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12272

namespace BstLean.Part262.Row12272
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12272 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12272 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12272 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12272 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12272 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12272) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12272) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12272) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12272) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12272) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12272 * (160 : ℝ) ^ 2 + 26 / (10 * 12272) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12272) : ℝ)) (tA 12272 * 160 ^ 2 + 26 / (10 * 12272)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12272) : ℝ)) d.D d.V d.P (√(tA 12272) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12272) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12272) : ℝ)) (tA 12272 * 160 ^ 2 + 26 / (10 * 12272)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12272) : ℝ)) (√(26 / (10 * 12272) : ℝ)) d.D d.V d.P (√(tA 12272) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12272) * 160) ≤ _
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

end BstLean.Part262.Row12272

namespace BstLean.Part262.Row12272
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12272 160 ∧
    0 ≤ (tableEnvelope C).f1 12272 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12272 160 ∧
    0 ≤ (tableEnvelope C).w1 12272 160 ∧ 0 ≤ (tableEnvelope C).w2 12272 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12272 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12272 160 ∧ 0 ≤ d.f1 12272 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12272 160 ∧ 0 ≤ d.w1 12272 160 ∧ 0 ≤ d.w2 12272 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12272 ≤ 2 * (228 / 100 : ℝ) / 12272 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12272 ≤ 2 * (370 / 100 : ℝ) / 12272 := by
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
    (completeRAData (tableEnvelope C) 12272 160).locationBound 12272 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12272 160).energyBound 12272 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12272 160) (d.f1 12272 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12272 160) (d.w1 12272 160)
      (d.w2 12272 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12272 160) (d.f1 12272 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12272 160) (d.f1 12272 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12272 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12272 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12272 160) (d.f1 12272 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12272 160) (d.w1 12272 160) (d.w2 12272 160)
  have hwexpr0 : 0 ≤ d.w0 12272 160 + d.w1 12272 160 * √(π / 2) +
      2 * d.w2 12272 160 + energyR16 12272 *
      radiusPolynomialRoot16 (d.w0 12272 160) (d.w1 12272 160) (d.w2 12272 160) := by
    positivity
  constructor
  · change (12272 : ℝ) ^ 8 * (mA 12272 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12272 160) (d.f1 12272 160) d.f2 + locationR16 12272 *
        radiusPolynomialRoot16 (d.f0 12272 160) (d.f1 12272 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12272 : ℝ) ^ 8 * (mA 12272 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12272) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12272 : ℝ) ^ 16 *
      (d.w0 12272 160 + d.w1 12272 160 * √(π / 2) + 2 * d.w2 12272 160 +
        energyR16 12272 * radiusPolynomialRoot16 (d.w0 12272 160) (d.w1 12272 160)
          (d.w2 12272 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12272 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12272) *
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

end BstLean.Part262.Row12272

/-! A coarse bound on the actual paper statistics constant at dimension 12273. -/
namespace BstLean.Part262.Row12273
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12271 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12271 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12271 128 ≤ (12525 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12525 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12273) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12273 : ℕ))
    (by norm_num : (12273 : ℕ) ≤ 16384)
  have ht : paperTail256 12273 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12273 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12273 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12273 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12273 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12273 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12271 128 * √(2 / (12273 : ℝ)) *
      (√(12273 : ℝ) + paperT0 12273 + paperTail256 12273) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12273 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12273 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12273 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12271 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12271 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12273 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12273

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12273
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12273 (61 / 100) 160 (17 / (100 * 12273)) (26 / (10 * 12273)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12273 (61 / 100) 160 (17 / (100 * 12273)) := by
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
          (8 * tA 12273 / 12273 * (61 / 100)) ^ 4 * inverseRadius8 (12273 - 1) /
            envelopeGap 12273 (61 / 100) 160 (17 / (100 * 12273)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12273

namespace BstLean.Part262.Row12273
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12273 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12273 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12273 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12273 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12273 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12273) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12273) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12273) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12273) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12273) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12273 * (160 : ℝ) ^ 2 + 26 / (10 * 12273) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12273) : ℝ)) (tA 12273 * 160 ^ 2 + 26 / (10 * 12273)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12273) : ℝ)) d.D d.V d.P (√(tA 12273) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12273) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12273) : ℝ)) (tA 12273 * 160 ^ 2 + 26 / (10 * 12273)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12273) : ℝ)) (√(26 / (10 * 12273) : ℝ)) d.D d.V d.P (√(tA 12273) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12273) * 160) ≤ _
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

end BstLean.Part262.Row12273

namespace BstLean.Part262.Row12273
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12273 160 ∧
    0 ≤ (tableEnvelope C).f1 12273 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12273 160 ∧
    0 ≤ (tableEnvelope C).w1 12273 160 ∧ 0 ≤ (tableEnvelope C).w2 12273 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12273 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12273 160 ∧ 0 ≤ d.f1 12273 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12273 160 ∧ 0 ≤ d.w1 12273 160 ∧ 0 ≤ d.w2 12273 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12273 ≤ 2 * (228 / 100 : ℝ) / 12273 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12273 ≤ 2 * (370 / 100 : ℝ) / 12273 := by
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
    (completeRAData (tableEnvelope C) 12273 160).locationBound 12273 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12273 160).energyBound 12273 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12273 160) (d.f1 12273 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12273 160) (d.w1 12273 160)
      (d.w2 12273 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12273 160) (d.f1 12273 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12273 160) (d.f1 12273 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12273 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12273 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12273 160) (d.f1 12273 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12273 160) (d.w1 12273 160) (d.w2 12273 160)
  have hwexpr0 : 0 ≤ d.w0 12273 160 + d.w1 12273 160 * √(π / 2) +
      2 * d.w2 12273 160 + energyR16 12273 *
      radiusPolynomialRoot16 (d.w0 12273 160) (d.w1 12273 160) (d.w2 12273 160) := by
    positivity
  constructor
  · change (12273 : ℝ) ^ 8 * (mA 12273 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12273 160) (d.f1 12273 160) d.f2 + locationR16 12273 *
        radiusPolynomialRoot16 (d.f0 12273 160) (d.f1 12273 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12273 : ℝ) ^ 8 * (mA 12273 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12273) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12273 : ℝ) ^ 16 *
      (d.w0 12273 160 + d.w1 12273 160 * √(π / 2) + 2 * d.w2 12273 160 +
        energyR16 12273 * radiusPolynomialRoot16 (d.w0 12273 160) (d.w1 12273 160)
          (d.w2 12273 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12273 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12273) *
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

end BstLean.Part262.Row12273

/-! A coarse bound on the actual paper statistics constant at dimension 12274. -/
namespace BstLean.Part262.Row12274
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12272 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12272 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12272 128 ≤ (12526 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12526 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12274) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12274 : ℕ))
    (by norm_num : (12274 : ℕ) ≤ 16384)
  have ht : paperTail256 12274 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12274 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12274 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12274 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12274 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12274 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12272 128 * √(2 / (12274 : ℝ)) *
      (√(12274 : ℝ) + paperT0 12274 + paperTail256 12274) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12274 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12274 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12274 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12272 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12272 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12274 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part262.Row12274

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part262.Row12274
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12274 (61 / 100) 160 (17 / (100 * 12274)) (26 / (10 * 12274)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12274 (61 / 100) 160 (17 / (100 * 12274)) := by
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
          (8 * tA 12274 / 12274 * (61 / 100)) ^ 4 * inverseRadius8 (12274 - 1) /
            envelopeGap 12274 (61 / 100) 160 (17 / (100 * 12274)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part262.Row12274

namespace BstLean.Part262.Row12274
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12274 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12274 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12274 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12274 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12274 160 ≤ 54 / 10 ^ 13

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
  have hsm : (370 / 100000 : ℝ) ≤ √(17 / (100 * 12274) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12274) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12274) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12274) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12274) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12274 * (160 : ℝ) ^ 2 + 26 / (10 * 12274) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12274) : ℝ)) (tA 12274 * 160 ^ 2 + 26 / (10 * 12274)) d.H d.V d.P ≤ _
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
    change AF1 (√(17 / (100 * 12274) : ℝ)) d.D d.V d.P (√(tA 12274) * 160) ≤ _
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
    change AF2 (√(17 / (100 * 12274) : ℝ)) d.D ≤ _
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
    change AW0 (√(17 / (100 * 12274) : ℝ)) (tA 12274 * 160 ^ 2 + 26 / (10 * 12274)) d.H d.V d.P ≤ _
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
    change AW1 (√(17 / (100 * 12274) : ℝ)) (√(26 / (10 * 12274) : ℝ)) d.D d.V d.P (√(tA 12274) * 160) ≤ _
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
    change AW2 d.D d.P (√(tA 12274) * 160) ≤ _
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

end BstLean.Part262.Row12274

namespace BstLean.Part262.Row12274
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12274 160 ∧
    0 ≤ (tableEnvelope C).f1 12274 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12274 160 ∧
    0 ≤ (tableEnvelope C).w1 12274 160 ∧ 0 ≤ (tableEnvelope C).w2 12274 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12274 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12274 160 ∧ 0 ≤ d.f1 12274 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12274 160 ∧ 0 ≤ d.w1 12274 160 ∧ 0 ≤ d.w2 12274 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12274 ≤ 2 * (228 / 100 : ℝ) / 12274 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12274 ≤ 2 * (370 / 100 : ℝ) / 12274 := by
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
    (completeRAData (tableEnvelope C) 12274 160).locationBound 12274 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12274 160).energyBound 12274 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12274 160) (d.f1 12274 160) d.f2 ≤
      32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12274 160) (d.w1 12274 160)
      (d.w2 12274 160) ≤
      32 * ((210 / 10 ^ 13 : ℝ) + 150 / 10 ^ 13 + 54 / 10 ^ 13) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12274 160) (d.f1 12274 160) d.f2 ≤
      (520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
      2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
      6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12274 160) (d.f1 12274 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12274 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12274 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12274 160) (d.f1 12274 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12274 160) (d.w1 12274 160) (d.w2 12274 160)
  have hwexpr0 : 0 ≤ d.w0 12274 160 + d.w1 12274 160 * √(π / 2) +
      2 * d.w2 12274 160 + energyR16 12274 *
      radiusPolynomialRoot16 (d.w0 12274 160) (d.w1 12274 160) (d.w2 12274 160) := by
    positivity
  constructor
  · change (12274 : ℝ) ^ 8 * (mA 12274 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12274 160) (d.f1 12274 160) d.f2 + locationR16 12274 *
        radiusPolynomialRoot16 (d.f0 12274 160) (d.f1 12274 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12274 : ℝ) ^ 8 * (mA 12274 : ℝ) ^ 8 *
        (((520 / 10 ^ 11 : ℝ) ^ 2 + 2 * (520 / 10 ^ 11) * (180 / 10 ^ 11) * (126 / 100) +
          2 * ((180 / 10 ^ 11) ^ 2 + 2 * (520 / 10 ^ 11) * (42 / 10 ^ 11)) +
          6 * (180 / 10 ^ 11) * (42 / 10 ^ 11) * (126 / 100) + 8 * (42 / 10 ^ 11) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12274) *
          (32 * ((520 / 10 ^ 11 : ℝ) + 180 / 10 ^ 11 + 42 / 10 ^ 11)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12274 : ℝ) ^ 16 *
      (d.w0 12274 160 + d.w1 12274 160 * √(π / 2) + 2 * d.w2 12274 160 +
        energyR16 12274 * radiusPolynomialRoot16 (d.w0 12274 160) (d.w1 12274 160)
          (d.w2 12274 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12274 : ℝ) ^ 16 *
        ((210 / 10 ^ 13 : ℝ) + (150 / 10 ^ 13) * (126 / 100) + 2 * (54 / 10 ^ 13) +
          (2 * (370 / 100 : ℝ) / 12274) *
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

end BstLean.Part262.Row12274
