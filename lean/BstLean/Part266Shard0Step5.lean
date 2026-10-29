import BstLean.Part266Shard0Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12351. -/
namespace BstLean.Part266.Row12351
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12349 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12349 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12349 128 ≤ (12603 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12603 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12351) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12351 : ℕ))
    (by norm_num : (12351 : ℕ) ≤ 16384)
  have ht : paperTail256 12351 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12351 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12351 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12351 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12351 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12351 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12349 128 * √(2 / (12351 : ℝ)) *
      (√(12351 : ℝ) + paperT0 12351 + paperTail256 12351) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12351 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12351 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12351 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12349 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12349 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12351 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12351

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12351
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12351 (61 / 100) 160 (17 / (100 * 12351)) (26 / (10 * 12351)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12351 (61 / 100) 160 (17 / (100 * 12351)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (518100229 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1677921583 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (800036877 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12351 / 12351 * (61 / 100)) ^ 4 * inverseRadius8 (12351 - 1) /
            envelopeGap 12351 (61 / 100) 160 (17 / (100 * 12351)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12351

namespace BstLean.Part266.Row12351
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12351 160 ≤ (2456674643 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12351 160 ≤ (1639176521 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393976643 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12351 160 ≤ (1993042121 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12351 160 ≤ (8862571 / 625000000000000000)
  w2 : (tableEnvelope C).w2 12351 160 ≤ (518106429 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (518100229 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (518100229 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1677921583 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (800036877 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741999 / 200000000) : ℝ) ≤ √(17 / (100 * 12351) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12351) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (569045379 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20481220563 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12351) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12351) ≤ (114501949 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12351) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12351 * (160 : ℝ) ^ 2 + 26 / (10 * 12351) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12351) : ℝ)) (tA 12351 * 160 ^ 2 + 26 / (10 * 12351)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741999 / 200000000))) * ((518100229 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741999 / 200000000)) ^ 3) * ((1677921583 / 1000000000000000000000000))) + ((800036877 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741999 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12351) : ℝ)) d.D d.V d.P (√(tA 12351) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741999 / 200000000)) ^ 2 * (((569045379 / 250000000000000)) * ((20481220563 / 500000000000000000)))) + ((800036877 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12351) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741999 / 200000000)) * ((518100229 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12351) : ℝ)) (tA 12351 * 160 ^ 2 + 26 / (10 * 12351)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((518100229 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741999 / 200000000)) ^ 2) * ((1677921583 / 1000000000000000000000000)) + ((800036877 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12351) : ℝ)) (√(26 / (10 * 12351) : ℝ)) d.D d.V d.P (√(tA 12351) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741999 / 200000000)) * (((569045379 / 250000000000000)) * ((20481220563 / 500000000000000000))) + ((800036877 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12351) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ ((518100229 / 100000000000000000000) : ℝ) + ((800036877 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12351

namespace BstLean.Part266.Row12351
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12351 160 ∧
    0 ≤ (tableEnvelope C).f1 12351 160 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12351 160 ∧
    0 ≤ (tableEnvelope C).w1 12351 160 ∧ 0 ≤ (tableEnvelope C).w2 12351 160 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12351 * (160 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12351 160 ∧ 0 ≤ d.f1 12351 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12351 160 ∧ 0 ≤ d.w1 12351 160 ∧ 0 ≤ d.w2 12351 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12351 ≤ 2 * (228 / 100 : ℝ) / 12351 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12351 ≤ 2 * (370 / 100 : ℝ) / 12351 := by
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
    (completeRAData (tableEnvelope C) 12351 160).locationBound 12351 160 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12351 160).energyBound 12351 160 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12351 160) (d.f1 12351 160) d.f2 ≤
      32 * (((2456674643 / 500000000000000000) : ℝ) + (1639176521 / 1000000000000000000) + (393976643 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12351 160) (d.w1 12351 160)
      (d.w2 12351 160) ≤
      32 * (((1993042121 / 100000000000000000000) : ℝ) + (8862571 / 625000000000000000) + (518106429 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12351 160) (d.f1 12351 160) d.f2 ≤
      ((2456674643 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2456674643 / 500000000000000000)) * ((1639176521 / 1000000000000000000)) * (126 / 100) +
      2 * (((1639176521 / 1000000000000000000)) ^ 2 + 2 * ((2456674643 / 500000000000000000)) * ((393976643 / 1000000000000000000))) +
      6 * ((1639176521 / 1000000000000000000)) * ((393976643 / 1000000000000000000)) * (126 / 100) + 8 * ((393976643 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12351 160) (d.f1 12351 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12351 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12351 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12351 160) (d.f1 12351 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12351 160) (d.w1 12351 160) (d.w2 12351 160)
  have hwexpr0 : 0 ≤ d.w0 12351 160 + d.w1 12351 160 * √(π / 2) +
      2 * d.w2 12351 160 + energyR16 12351 *
      radiusPolynomialRoot16 (d.w0 12351 160) (d.w1 12351 160) (d.w2 12351 160) := by
    positivity
  constructor
  · change (12351 : ℝ) ^ 8 * (mA 12351 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12351 160) (d.f1 12351 160) d.f2 + locationR16 12351 *
        radiusPolynomialRoot16 (d.f0 12351 160) (d.f1 12351 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12351 : ℝ) ^ 8 * (mA 12351 : ℝ) ^ 8 *
        ((((2456674643 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2456674643 / 500000000000000000)) * ((1639176521 / 1000000000000000000)) * (126 / 100) +
          2 * (((1639176521 / 1000000000000000000)) ^ 2 + 2 * ((2456674643 / 500000000000000000)) * ((393976643 / 1000000000000000000))) +
          6 * ((1639176521 / 1000000000000000000)) * ((393976643 / 1000000000000000000)) * (126 / 100) + 8 * ((393976643 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12351) *
          (32 * (((2456674643 / 500000000000000000) : ℝ) + (1639176521 / 1000000000000000000) + (393976643 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12351 : ℝ) ^ 16 *
      (d.w0 12351 160 + d.w1 12351 160 * √(π / 2) + 2 * d.w2 12351 160 +
        energyR16 12351 * radiusPolynomialRoot16 (d.w0 12351 160) (d.w1 12351 160)
          (d.w2 12351 160)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12351 : ℝ) ^ 16 *
        (((1993042121 / 100000000000000000000) : ℝ) + ((8862571 / 625000000000000000)) * (126 / 100) + 2 * ((518106429 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12351) *
          (32 * (((1993042121 / 100000000000000000000) : ℝ) + (8862571 / 625000000000000000) + (518106429 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12351

/-! A coarse bound on the actual paper statistics constant at dimension 12352. -/
namespace BstLean.Part266.Row12352
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12350 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12350 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12350 128 ≤ (12604 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12604 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12352) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12352 : ℕ))
    (by norm_num : (12352 : ℕ) ≤ 16384)
  have ht : paperTail256 12352 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12352 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12352 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12352 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12352 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12352 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12350 128 * √(2 / (12352 : ℝ)) *
      (√(12352 : ℝ) + paperT0 12352 + paperTail256 12352) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12352 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12352 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12352 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12350 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12350 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12352 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12352

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12352
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12352 (61 / 100) 161 (17 / (100 * 12352)) (26 / (10 * 12352)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12352 (61 / 100) 161 (17 / (100 * 12352)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (258987199 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (838689129 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6399216459 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12352 / 12352 * (61 / 100)) ^ 4 * inverseRadius8 (12352 - 1) /
            envelopeGap 12352 (61 / 100) 161 (17 / (100 * 12352)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12352

namespace BstLean.Part266.Row12352
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12352 161 ≤ (153511067 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12352 161 ≤ (409711149 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (98474221 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12352 161 ≤ (249069741 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12352 161 ≤ (1417666899 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12352 161 ≤ (517980597 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (258987199 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (258987199 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (838689129 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6399216459 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741969 / 200000000) : ℝ) ≤ √(17 / (100 * 12352) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12352) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2275905091 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (204779043 / 5000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12352) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12352) ≤ (114492679 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12352) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12352 * (161 : ℝ) ^ 2 + 26 / (10 * 12352) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12352) : ℝ)) (tA 12352 * 161 ^ 2 + 26 / (10 * 12352)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741969 / 200000000))) * ((258987199 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741969 / 200000000)) ^ 3) * ((838689129 / 500000000000000000000000))) + ((6399216459 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741969 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12352) : ℝ)) d.D d.V d.P (√(tA 12352) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741969 / 200000000)) ^ 2 * (((2275905091 / 1000000000000000)) * ((204779043 / 5000000000000000)))) + ((6399216459 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12352) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741969 / 200000000)) * ((258987199 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12352) : ℝ)) (tA 12352 * 161 ^ 2 + 26 / (10 * 12352)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((258987199 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741969 / 200000000)) ^ 2) * ((838689129 / 500000000000000000000000)) + ((6399216459 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12352) : ℝ)) (√(26 / (10 * 12352) : ℝ)) d.D d.V d.P (√(tA 12352) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741969 / 200000000)) * (((2275905091 / 1000000000000000)) * ((204779043 / 5000000000000000))) + ((6399216459 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12352) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((258987199 / 50000000000000000000) : ℝ) + ((6399216459 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12352

namespace BstLean.Part266.Row12352
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12352 161 ∧
    0 ≤ (tableEnvelope C).f1 12352 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12352 161 ∧
    0 ≤ (tableEnvelope C).w1 12352 161 ∧ 0 ≤ (tableEnvelope C).w2 12352 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12352 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12352 161 ∧ 0 ≤ d.f1 12352 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12352 161 ∧ 0 ≤ d.w1 12352 161 ∧ 0 ≤ d.w2 12352 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12352 ≤ 2 * (228 / 100 : ℝ) / 12352 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12352 ≤ 2 * (370 / 100 : ℝ) / 12352 := by
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
    (completeRAData (tableEnvelope C) 12352 161).locationBound 12352 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12352 161).energyBound 12352 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12352 161) (d.f1 12352 161) d.f2 ≤
      32 * (((153511067 / 31250000000000000) : ℝ) + (409711149 / 250000000000000000) + (98474221 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12352 161) (d.w1 12352 161)
      (d.w2 12352 161) ≤
      32 * (((249069741 / 12500000000000000000) : ℝ) + (1417666899 / 100000000000000000000) + (517980597 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12352 161) (d.f1 12352 161) d.f2 ≤
      ((153511067 / 31250000000000000) : ℝ) ^ 2 + 2 * ((153511067 / 31250000000000000)) * ((409711149 / 250000000000000000)) * (126 / 100) +
      2 * (((409711149 / 250000000000000000)) ^ 2 + 2 * ((153511067 / 31250000000000000)) * ((98474221 / 250000000000000000))) +
      6 * ((409711149 / 250000000000000000)) * ((98474221 / 250000000000000000)) * (126 / 100) + 8 * ((98474221 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12352 161) (d.f1 12352 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12352 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12352 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12352 161) (d.f1 12352 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12352 161) (d.w1 12352 161) (d.w2 12352 161)
  have hwexpr0 : 0 ≤ d.w0 12352 161 + d.w1 12352 161 * √(π / 2) +
      2 * d.w2 12352 161 + energyR16 12352 *
      radiusPolynomialRoot16 (d.w0 12352 161) (d.w1 12352 161) (d.w2 12352 161) := by
    positivity
  constructor
  · change (12352 : ℝ) ^ 8 * (mA 12352 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12352 161) (d.f1 12352 161) d.f2 + locationR16 12352 *
        radiusPolynomialRoot16 (d.f0 12352 161) (d.f1 12352 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12352 : ℝ) ^ 8 * (mA 12352 : ℝ) ^ 8 *
        ((((153511067 / 31250000000000000) : ℝ) ^ 2 + 2 * ((153511067 / 31250000000000000)) * ((409711149 / 250000000000000000)) * (126 / 100) +
          2 * (((409711149 / 250000000000000000)) ^ 2 + 2 * ((153511067 / 31250000000000000)) * ((98474221 / 250000000000000000))) +
          6 * ((409711149 / 250000000000000000)) * ((98474221 / 250000000000000000)) * (126 / 100) + 8 * ((98474221 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12352) *
          (32 * (((153511067 / 31250000000000000) : ℝ) + (409711149 / 250000000000000000) + (98474221 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12352 : ℝ) ^ 16 *
      (d.w0 12352 161 + d.w1 12352 161 * √(π / 2) + 2 * d.w2 12352 161 +
        energyR16 12352 * radiusPolynomialRoot16 (d.w0 12352 161) (d.w1 12352 161)
          (d.w2 12352 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12352 : ℝ) ^ 16 *
        (((249069741 / 12500000000000000000) : ℝ) + ((1417666899 / 100000000000000000000)) * (126 / 100) + 2 * ((517980597 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12352) *
          (32 * (((249069741 / 12500000000000000000) : ℝ) + (1417666899 / 100000000000000000000) + (517980597 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12352

/-! A coarse bound on the actual paper statistics constant at dimension 12353. -/
namespace BstLean.Part266.Row12353
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12351 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12351 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12351 128 ≤ (12605 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12605 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12353) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12353 : ℕ))
    (by norm_num : (12353 : ℕ) ≤ 16384)
  have ht : paperTail256 12353 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12353 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12353 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12353 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12353 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12353 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12351 128 * √(2 / (12353 : ℝ)) *
      (√(12353 : ℝ) + paperT0 12353 + paperTail256 12353) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12353 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12353 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12353 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12351 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12351 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12353 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12353

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12353
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12353 (61 / 100) 161 (17 / (100 * 12353)) (26 / (10 * 12353)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12353 (61 / 100) 161 (17 / (100 * 12353)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (16182769 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (838417577 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (639503179 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12353 / 12353 * (61 / 100)) ^ 4 * inverseRadius8 (12353 - 1) /
            envelopeGap 12353 (61 / 100) 161 (17 / (100 * 12353)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12353

namespace BstLean.Part266.Row12353
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12353 161 ≤ (4911359357 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12353 161 ≤ (81925639 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393817149 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12353 161 ≤ (996036953 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12353 161 ≤ (1417322557 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12353 161 ≤ (517854803 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (16182769 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (16182769 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (838417577 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (639503179 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741939 / 200000000) : ℝ) ≤ √(17 / (100 * 12353) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12353) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1137814361 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40949177697 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12353) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12353) ≤ (11448341 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12353) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12353 * (161 : ℝ) ^ 2 + 26 / (10 * 12353) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12353) : ℝ)) (tA 12353 * 161 ^ 2 + 26 / (10 * 12353)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741939 / 200000000))) * ((16182769 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741939 / 200000000)) ^ 3) * ((838417577 / 500000000000000000000000))) + ((639503179 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741939 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12353) : ℝ)) d.D d.V d.P (√(tA 12353) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741939 / 200000000)) ^ 2 * (((1137814361 / 500000000000000)) * ((40949177697 / 1000000000000000000)))) + ((639503179 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12353) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741939 / 200000000)) * ((16182769 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12353) : ℝ)) (tA 12353 * 161 ^ 2 + 26 / (10 * 12353)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((16182769 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741939 / 200000000)) ^ 2) * ((838417577 / 500000000000000000000000)) + ((639503179 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12353) : ℝ)) (√(26 / (10 * 12353) : ℝ)) d.D d.V d.P (√(tA 12353) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741939 / 200000000)) * (((1137814361 / 500000000000000)) * ((40949177697 / 1000000000000000000))) + ((639503179 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12353) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((16182769 / 3125000000000000000) : ℝ) + ((639503179 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12353

namespace BstLean.Part266.Row12353
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12353 161 ∧
    0 ≤ (tableEnvelope C).f1 12353 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12353 161 ∧
    0 ≤ (tableEnvelope C).w1 12353 161 ∧ 0 ≤ (tableEnvelope C).w2 12353 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12353 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12353 161 ∧ 0 ≤ d.f1 12353 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12353 161 ∧ 0 ≤ d.w1 12353 161 ∧ 0 ≤ d.w2 12353 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12353 ≤ 2 * (228 / 100 : ℝ) / 12353 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12353 ≤ 2 * (370 / 100 : ℝ) / 12353 := by
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
    (completeRAData (tableEnvelope C) 12353 161).locationBound 12353 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12353 161).energyBound 12353 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12353 161) (d.f1 12353 161) d.f2 ≤
      32 * (((4911359357 / 1000000000000000000) : ℝ) + (81925639 / 50000000000000000) + (393817149 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12353 161) (d.w1 12353 161)
      (d.w2 12353 161) ≤
      32 * (((996036953 / 50000000000000000000) : ℝ) + (1417322557 / 100000000000000000000) + (517854803 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12353 161) (d.f1 12353 161) d.f2 ≤
      ((4911359357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4911359357 / 1000000000000000000)) * ((81925639 / 50000000000000000)) * (126 / 100) +
      2 * (((81925639 / 50000000000000000)) ^ 2 + 2 * ((4911359357 / 1000000000000000000)) * ((393817149 / 1000000000000000000))) +
      6 * ((81925639 / 50000000000000000)) * ((393817149 / 1000000000000000000)) * (126 / 100) + 8 * ((393817149 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12353 161) (d.f1 12353 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12353 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12353 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12353 161) (d.f1 12353 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12353 161) (d.w1 12353 161) (d.w2 12353 161)
  have hwexpr0 : 0 ≤ d.w0 12353 161 + d.w1 12353 161 * √(π / 2) +
      2 * d.w2 12353 161 + energyR16 12353 *
      radiusPolynomialRoot16 (d.w0 12353 161) (d.w1 12353 161) (d.w2 12353 161) := by
    positivity
  constructor
  · change (12353 : ℝ) ^ 8 * (mA 12353 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12353 161) (d.f1 12353 161) d.f2 + locationR16 12353 *
        radiusPolynomialRoot16 (d.f0 12353 161) (d.f1 12353 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12353 : ℝ) ^ 8 * (mA 12353 : ℝ) ^ 8 *
        ((((4911359357 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4911359357 / 1000000000000000000)) * ((81925639 / 50000000000000000)) * (126 / 100) +
          2 * (((81925639 / 50000000000000000)) ^ 2 + 2 * ((4911359357 / 1000000000000000000)) * ((393817149 / 1000000000000000000))) +
          6 * ((81925639 / 50000000000000000)) * ((393817149 / 1000000000000000000)) * (126 / 100) + 8 * ((393817149 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12353) *
          (32 * (((4911359357 / 1000000000000000000) : ℝ) + (81925639 / 50000000000000000) + (393817149 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12353 : ℝ) ^ 16 *
      (d.w0 12353 161 + d.w1 12353 161 * √(π / 2) + 2 * d.w2 12353 161 +
        energyR16 12353 * radiusPolynomialRoot16 (d.w0 12353 161) (d.w1 12353 161)
          (d.w2 12353 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12353 : ℝ) ^ 16 *
        (((996036953 / 50000000000000000000) : ℝ) + ((1417322557 / 100000000000000000000)) * (126 / 100) + 2 * ((517854803 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12353) *
          (32 * (((996036953 / 50000000000000000000) : ℝ) + (1417322557 / 100000000000000000000) + (517854803 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12353

/-! A coarse bound on the actual paper statistics constant at dimension 12354. -/
namespace BstLean.Part266.Row12354
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12352 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12352 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12352 128 ≤ (12606 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12606 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12354) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12354 : ℕ))
    (by norm_num : (12354 : ℕ) ≤ 16384)
  have ht : paperTail256 12354 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12354 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12354 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12354 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12354 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12354 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12352 128 * √(2 / (12354 : ℝ)) *
      (√(12354 : ℝ) + paperT0 12354 + paperTail256 12354) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12354 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12354 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12354 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12352 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12352 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12354 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12354

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12354
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12354 (61 / 100) 161 (17 / (100 * 12354)) (26 / (10 * 12354)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12354 (61 / 100) 161 (17 / (100 * 12354)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (517722859 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1676292269 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3195425101 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12354 / 12354 * (61 / 100)) ^ 4 * inverseRadius8 (12354 - 1) /
            envelopeGap 12354 (61 / 100) 161 (17 / (100 * 12354)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12354

namespace BstLean.Part266.Row12354
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12354 161 ≤ (122759123 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12354 161 ≤ (409545269 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393737439 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12354 161 ≤ (248948757 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12354 161 ≤ (1416978333 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12354 161 ≤ (10354581 / 2000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (517722859 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (517722859 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1676292269 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3195425101 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741909 / 200000000) : ℝ) ≤ √(17 / (100 * 12354) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12354) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2275352411 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8188509679 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12354) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12354) ≤ (114474143 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12354) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12354 * (161 : ℝ) ^ 2 + 26 / (10 * 12354) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12354) : ℝ)) (tA 12354 * 161 ^ 2 + 26 / (10 * 12354)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741909 / 200000000))) * ((517722859 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741909 / 200000000)) ^ 3) * ((1676292269 / 1000000000000000000000000))) + ((3195425101 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741909 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12354) : ℝ)) d.D d.V d.P (√(tA 12354) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741909 / 200000000)) ^ 2 * (((2275352411 / 1000000000000000)) * ((8188509679 / 200000000000000000)))) + ((3195425101 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12354) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741909 / 200000000)) * ((517722859 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12354) : ℝ)) (tA 12354 * 161 ^ 2 + 26 / (10 * 12354)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((517722859 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741909 / 200000000)) ^ 2) * ((1676292269 / 1000000000000000000000000)) + ((3195425101 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12354) : ℝ)) (√(26 / (10 * 12354) : ℝ)) d.D d.V d.P (√(tA 12354) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741909 / 200000000)) * (((2275352411 / 1000000000000000)) * ((8188509679 / 200000000000000000))) + ((3195425101 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12354) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((517722859 / 100000000000000000000) : ℝ) + ((3195425101 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12354

namespace BstLean.Part266.Row12354
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12354 161 ∧
    0 ≤ (tableEnvelope C).f1 12354 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12354 161 ∧
    0 ≤ (tableEnvelope C).w1 12354 161 ∧ 0 ≤ (tableEnvelope C).w2 12354 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12354 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12354 161 ∧ 0 ≤ d.f1 12354 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12354 161 ∧ 0 ≤ d.w1 12354 161 ∧ 0 ≤ d.w2 12354 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12354 ≤ 2 * (228 / 100 : ℝ) / 12354 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12354 ≤ 2 * (370 / 100 : ℝ) / 12354 := by
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
    (completeRAData (tableEnvelope C) 12354 161).locationBound 12354 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12354 161).energyBound 12354 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12354 161) (d.f1 12354 161) d.f2 ≤
      32 * (((122759123 / 25000000000000000) : ℝ) + (409545269 / 250000000000000000) + (393737439 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12354 161) (d.w1 12354 161)
      (d.w2 12354 161) ≤
      32 * (((248948757 / 12500000000000000000) : ℝ) + (1416978333 / 100000000000000000000) + (10354581 / 2000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12354 161) (d.f1 12354 161) d.f2 ≤
      ((122759123 / 25000000000000000) : ℝ) ^ 2 + 2 * ((122759123 / 25000000000000000)) * ((409545269 / 250000000000000000)) * (126 / 100) +
      2 * (((409545269 / 250000000000000000)) ^ 2 + 2 * ((122759123 / 25000000000000000)) * ((393737439 / 1000000000000000000))) +
      6 * ((409545269 / 250000000000000000)) * ((393737439 / 1000000000000000000)) * (126 / 100) + 8 * ((393737439 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12354 161) (d.f1 12354 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12354 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12354 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12354 161) (d.f1 12354 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12354 161) (d.w1 12354 161) (d.w2 12354 161)
  have hwexpr0 : 0 ≤ d.w0 12354 161 + d.w1 12354 161 * √(π / 2) +
      2 * d.w2 12354 161 + energyR16 12354 *
      radiusPolynomialRoot16 (d.w0 12354 161) (d.w1 12354 161) (d.w2 12354 161) := by
    positivity
  constructor
  · change (12354 : ℝ) ^ 8 * (mA 12354 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12354 161) (d.f1 12354 161) d.f2 + locationR16 12354 *
        radiusPolynomialRoot16 (d.f0 12354 161) (d.f1 12354 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12354 : ℝ) ^ 8 * (mA 12354 : ℝ) ^ 8 *
        ((((122759123 / 25000000000000000) : ℝ) ^ 2 + 2 * ((122759123 / 25000000000000000)) * ((409545269 / 250000000000000000)) * (126 / 100) +
          2 * (((409545269 / 250000000000000000)) ^ 2 + 2 * ((122759123 / 25000000000000000)) * ((393737439 / 1000000000000000000))) +
          6 * ((409545269 / 250000000000000000)) * ((393737439 / 1000000000000000000)) * (126 / 100) + 8 * ((393737439 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12354) *
          (32 * (((122759123 / 25000000000000000) : ℝ) + (409545269 / 250000000000000000) + (393737439 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12354 : ℝ) ^ 16 *
      (d.w0 12354 161 + d.w1 12354 161 * √(π / 2) + 2 * d.w2 12354 161 +
        energyR16 12354 * radiusPolynomialRoot16 (d.w0 12354 161) (d.w1 12354 161)
          (d.w2 12354 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12354 : ℝ) ^ 16 *
        (((248948757 / 12500000000000000000) : ℝ) + ((1416978333 / 100000000000000000000)) * (126 / 100) + 2 * ((10354581 / 2000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12354) *
          (32 * (((248948757 / 12500000000000000000) : ℝ) + (1416978333 / 100000000000000000000) + (10354581 / 2000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12354

/-! A coarse bound on the actual paper statistics constant at dimension 12355. -/
namespace BstLean.Part266.Row12355
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12353 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12353 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12353 128 ≤ (12607 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12607 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12355) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12355 : ℕ))
    (by norm_num : (12355 : ℕ) ≤ 16384)
  have ht : paperTail256 12355 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12355 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12355 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12355 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12355 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12355 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12353 128 * √(2 / (12355 : ℝ)) *
      (√(12355 : ℝ) + paperT0 12355 + paperTail256 12355) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12355 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12355 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12355 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12353 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12353 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12355 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12355

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12355
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12355 (61 / 100) 161 (17 / (100 * 12355)) (26 / (10 * 12355)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12355 (61 / 100) 161 (17 / (100 * 12355)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (517597151 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (418937401 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6386671693 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12355 / 12355 * (61 / 100)) ^ 4 * inverseRadius8 (12355 - 1) /
            envelopeGap 12355 (61 / 100) 161 (17 / (100 * 12355)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12355

namespace BstLean.Part266.Row12355
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12355 161 ≤ (981874167 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12355 161 ≤ (818924741 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (196828877 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12355 161 ≤ (1991106377 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12355 161 ≤ (354158557 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12355 161 ≤ (258801669 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (517597151 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (517597151 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (418937401 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6386671693 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741879 / 200000000) : ℝ) ≤ √(17 / (100 * 12355) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12355) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (455015231 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20467960353 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12355) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12355) ≤ (57232439 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12355) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12355 * (161 : ℝ) ^ 2 + 26 / (10 * 12355) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12355) : ℝ)) (tA 12355 * 161 ^ 2 + 26 / (10 * 12355)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741879 / 200000000))) * ((517597151 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741879 / 200000000)) ^ 3) * ((418937401 / 250000000000000000000000))) + ((6386671693 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741879 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12355) : ℝ)) d.D d.V d.P (√(tA 12355) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741879 / 200000000)) ^ 2 * (((455015231 / 200000000000000)) * ((20467960353 / 500000000000000000)))) + ((6386671693 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12355) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741879 / 200000000)) * ((517597151 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12355) : ℝ)) (tA 12355 * 161 ^ 2 + 26 / (10 * 12355)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((517597151 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741879 / 200000000)) ^ 2) * ((418937401 / 250000000000000000000000)) + ((6386671693 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12355) : ℝ)) (√(26 / (10 * 12355) : ℝ)) d.D d.V d.P (√(tA 12355) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741879 / 200000000)) * (((455015231 / 200000000000000)) * ((20467960353 / 500000000000000000))) + ((6386671693 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12355) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((517597151 / 100000000000000000000) : ℝ) + ((6386671693 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12355

namespace BstLean.Part266.Row12355
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12355 161 ∧
    0 ≤ (tableEnvelope C).f1 12355 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12355 161 ∧
    0 ≤ (tableEnvelope C).w1 12355 161 ∧ 0 ≤ (tableEnvelope C).w2 12355 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12355 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12355 161 ∧ 0 ≤ d.f1 12355 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12355 161 ∧ 0 ≤ d.w1 12355 161 ∧ 0 ≤ d.w2 12355 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12355 ≤ 2 * (228 / 100 : ℝ) / 12355 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12355 ≤ 2 * (370 / 100 : ℝ) / 12355 := by
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
    (completeRAData (tableEnvelope C) 12355 161).locationBound 12355 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12355 161).energyBound 12355 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12355 161) (d.f1 12355 161) d.f2 ≤
      32 * (((981874167 / 200000000000000000) : ℝ) + (818924741 / 500000000000000000) + (196828877 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12355 161) (d.w1 12355 161)
      (d.w2 12355 161) ≤
      32 * (((1991106377 / 100000000000000000000) : ℝ) + (354158557 / 25000000000000000000) + (258801669 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12355 161) (d.f1 12355 161) d.f2 ≤
      ((981874167 / 200000000000000000) : ℝ) ^ 2 + 2 * ((981874167 / 200000000000000000)) * ((818924741 / 500000000000000000)) * (126 / 100) +
      2 * (((818924741 / 500000000000000000)) ^ 2 + 2 * ((981874167 / 200000000000000000)) * ((196828877 / 500000000000000000))) +
      6 * ((818924741 / 500000000000000000)) * ((196828877 / 500000000000000000)) * (126 / 100) + 8 * ((196828877 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12355 161) (d.f1 12355 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12355 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12355 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12355 161) (d.f1 12355 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12355 161) (d.w1 12355 161) (d.w2 12355 161)
  have hwexpr0 : 0 ≤ d.w0 12355 161 + d.w1 12355 161 * √(π / 2) +
      2 * d.w2 12355 161 + energyR16 12355 *
      radiusPolynomialRoot16 (d.w0 12355 161) (d.w1 12355 161) (d.w2 12355 161) := by
    positivity
  constructor
  · change (12355 : ℝ) ^ 8 * (mA 12355 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12355 161) (d.f1 12355 161) d.f2 + locationR16 12355 *
        radiusPolynomialRoot16 (d.f0 12355 161) (d.f1 12355 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12355 : ℝ) ^ 8 * (mA 12355 : ℝ) ^ 8 *
        ((((981874167 / 200000000000000000) : ℝ) ^ 2 + 2 * ((981874167 / 200000000000000000)) * ((818924741 / 500000000000000000)) * (126 / 100) +
          2 * (((818924741 / 500000000000000000)) ^ 2 + 2 * ((981874167 / 200000000000000000)) * ((196828877 / 500000000000000000))) +
          6 * ((818924741 / 500000000000000000)) * ((196828877 / 500000000000000000)) * (126 / 100) + 8 * ((196828877 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12355) *
          (32 * (((981874167 / 200000000000000000) : ℝ) + (818924741 / 500000000000000000) + (196828877 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12355 : ℝ) ^ 16 *
      (d.w0 12355 161 + d.w1 12355 161 * √(π / 2) + 2 * d.w2 12355 161 +
        energyR16 12355 * radiusPolynomialRoot16 (d.w0 12355 161) (d.w1 12355 161)
          (d.w2 12355 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12355 : ℝ) ^ 16 *
        (((1991106377 / 100000000000000000000) : ℝ) + ((354158557 / 25000000000000000000)) * (126 / 100) + 2 * ((258801669 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12355) *
          (32 * (((1991106377 / 100000000000000000000) : ℝ) + (354158557 / 25000000000000000000) + (258801669 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12355

/-! A coarse bound on the actual paper statistics constant at dimension 12356. -/
namespace BstLean.Part266.Row12356
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12354 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12354 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12354 128 ≤ (12608 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12608 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12356) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12356 : ℕ))
    (by norm_num : (12356 : ℕ) ≤ 16384)
  have ht : paperTail256 12356 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12356 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12356 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12356 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12356 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12356 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12354 128 * √(2 / (12356 : ℝ)) *
      (√(12356 : ℝ) + paperT0 12356 + paperTail256 12356) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12356 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12356 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12356 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12354 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12354 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12356 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12356

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12356
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12356 (61 / 100) 161 (17 / (100 * 12356)) (26 / (10 * 12356)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12356 (61 / 100) 161 (17 / (100 * 12356)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (517471483 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1675207159 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6382496261 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12356 / 12356 * (61 / 100)) ^ 4 * inverseRadius8 (12356 - 1) /
            envelopeGap 12356 (61 / 100) 161 (17 / (100 * 12356)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12356

namespace BstLean.Part266.Row12356
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12356 161 ≤ (4908380921 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12356 161 ≤ (10234493 / 6250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393578199 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12356 161 ≤ (124413979 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12356 161 ≤ (1416290623 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12356 161 ≤ (258738833 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (517471483 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (517471483 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1675207159 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6382496261 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((927311 / 250000000) : ℝ) ≤ √(17 / (100 * 12356) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12356) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1137399977 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5116161829 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12356) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12356) ≤ (57227807 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12356) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12356 * (161 : ℝ) ^ 2 + 26 / (10 * 12356) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12356) : ℝ)) (tA 12356 * 161 ^ 2 + 26 / (10 * 12356)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((927311 / 250000000))) * ((517471483 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((927311 / 250000000)) ^ 3) * ((1675207159 / 1000000000000000000000000))) + ((6382496261 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((927311 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12356) : ℝ)) d.D d.V d.P (√(tA 12356) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((927311 / 250000000)) ^ 2 * (((1137399977 / 500000000000000)) * ((5116161829 / 125000000000000000)))) + ((6382496261 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12356) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((927311 / 250000000)) * ((517471483 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12356) : ℝ)) (tA 12356 * 161 ^ 2 + 26 / (10 * 12356)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((517471483 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((927311 / 250000000)) ^ 2) * ((1675207159 / 1000000000000000000000000)) + ((6382496261 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12356) : ℝ)) (√(26 / (10 * 12356) : ℝ)) d.D d.V d.P (√(tA 12356) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((927311 / 250000000)) * (((1137399977 / 500000000000000)) * ((5116161829 / 125000000000000000))) + ((6382496261 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12356) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((517471483 / 100000000000000000000) : ℝ) + ((6382496261 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12356

namespace BstLean.Part266.Row12356
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12356 161 ∧
    0 ≤ (tableEnvelope C).f1 12356 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12356 161 ∧
    0 ≤ (tableEnvelope C).w1 12356 161 ∧ 0 ≤ (tableEnvelope C).w2 12356 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12356 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12356 161 ∧ 0 ≤ d.f1 12356 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12356 161 ∧ 0 ≤ d.w1 12356 161 ∧ 0 ≤ d.w2 12356 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12356 ≤ 2 * (228 / 100 : ℝ) / 12356 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12356 ≤ 2 * (370 / 100 : ℝ) / 12356 := by
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
    (completeRAData (tableEnvelope C) 12356 161).locationBound 12356 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12356 161).energyBound 12356 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12356 161) (d.f1 12356 161) d.f2 ≤
      32 * (((4908380921 / 1000000000000000000) : ℝ) + (10234493 / 6250000000000000) + (393578199 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12356 161) (d.w1 12356 161)
      (d.w2 12356 161) ≤
      32 * (((124413979 / 6250000000000000000) : ℝ) + (1416290623 / 100000000000000000000) + (258738833 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12356 161) (d.f1 12356 161) d.f2 ≤
      ((4908380921 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4908380921 / 1000000000000000000)) * ((10234493 / 6250000000000000)) * (126 / 100) +
      2 * (((10234493 / 6250000000000000)) ^ 2 + 2 * ((4908380921 / 1000000000000000000)) * ((393578199 / 1000000000000000000))) +
      6 * ((10234493 / 6250000000000000)) * ((393578199 / 1000000000000000000)) * (126 / 100) + 8 * ((393578199 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12356 161) (d.f1 12356 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12356 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12356 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12356 161) (d.f1 12356 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12356 161) (d.w1 12356 161) (d.w2 12356 161)
  have hwexpr0 : 0 ≤ d.w0 12356 161 + d.w1 12356 161 * √(π / 2) +
      2 * d.w2 12356 161 + energyR16 12356 *
      radiusPolynomialRoot16 (d.w0 12356 161) (d.w1 12356 161) (d.w2 12356 161) := by
    positivity
  constructor
  · change (12356 : ℝ) ^ 8 * (mA 12356 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12356 161) (d.f1 12356 161) d.f2 + locationR16 12356 *
        radiusPolynomialRoot16 (d.f0 12356 161) (d.f1 12356 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12356 : ℝ) ^ 8 * (mA 12356 : ℝ) ^ 8 *
        ((((4908380921 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4908380921 / 1000000000000000000)) * ((10234493 / 6250000000000000)) * (126 / 100) +
          2 * (((10234493 / 6250000000000000)) ^ 2 + 2 * ((4908380921 / 1000000000000000000)) * ((393578199 / 1000000000000000000))) +
          6 * ((10234493 / 6250000000000000)) * ((393578199 / 1000000000000000000)) * (126 / 100) + 8 * ((393578199 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12356) *
          (32 * (((4908380921 / 1000000000000000000) : ℝ) + (10234493 / 6250000000000000) + (393578199 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12356 : ℝ) ^ 16 *
      (d.w0 12356 161 + d.w1 12356 161 * √(π / 2) + 2 * d.w2 12356 161 +
        energyR16 12356 * radiusPolynomialRoot16 (d.w0 12356 161) (d.w1 12356 161)
          (d.w2 12356 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12356 : ℝ) ^ 16 *
        (((124413979 / 6250000000000000000) : ℝ) + ((1416290623 / 100000000000000000000)) * (126 / 100) + 2 * ((258738833 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12356) *
          (32 * (((124413979 / 6250000000000000000) : ℝ) + (1416290623 / 100000000000000000000) + (258738833 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12356

/-! A coarse bound on the actual paper statistics constant at dimension 12357. -/
namespace BstLean.Part266.Row12357
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12355 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12355 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12355 128 ≤ (12609 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12609 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12357) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12357 : ℕ))
    (by norm_num : (12357 : ℕ) ≤ 16384)
  have ht : paperTail256 12357 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12357 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12357 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12357 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12357 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12357 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12355 128 * √(2 / (12357 : ℝ)) *
      (√(12357 : ℝ) + paperT0 12357 + paperTail256 12357) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12357 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12357 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12357 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12355 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12355 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12357 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12357

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12357
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12357 (61 / 100) 161 (17 / (100 * 12357)) (26 / (10 * 12357)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12357 (61 / 100) 161 (17 / (100 * 12357)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (8083529 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1674664933 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3189161951 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12357 / 12357 * (61 / 100)) ^ 4 * inverseRadius8 (12357 - 1) /
            envelopeGap 12357 (61 / 100) 161 (17 / (100 * 12357)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12357

namespace BstLean.Part266.Row12357
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12357 161 ≤ (2453693769 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12357 161 ≤ (327437501 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393498563 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12357 161 ≤ (995070163 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12357 161 ≤ (707973377 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12357 161 ≤ (103470407 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (8083529 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (8083529 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1674664933 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3189161951 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1854547 / 500000000) : ℝ) ≤ √(17 / (100 * 12357) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12357) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (227452381 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (511533377 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12357) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12357) ≤ (7152897 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12357) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12357 * (161 : ℝ) ^ 2 + 26 / (10 * 12357) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12357) : ℝ)) (tA 12357 * 161 ^ 2 + 26 / (10 * 12357)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1854547 / 500000000))) * ((8083529 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1854547 / 500000000)) ^ 3) * ((1674664933 / 1000000000000000000000000))) + ((3189161951 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1854547 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12357) : ℝ)) d.D d.V d.P (√(tA 12357) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1854547 / 500000000)) ^ 2 * (((227452381 / 100000000000000)) * ((511533377 / 12500000000000000)))) + ((3189161951 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12357) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1854547 / 500000000)) * ((8083529 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12357) : ℝ)) (tA 12357 * 161 ^ 2 + 26 / (10 * 12357)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((8083529 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((1854547 / 500000000)) ^ 2) * ((1674664933 / 1000000000000000000000000)) + ((3189161951 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12357) : ℝ)) (√(26 / (10 * 12357) : ℝ)) d.D d.V d.P (√(tA 12357) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1854547 / 500000000)) * (((227452381 / 100000000000000)) * ((511533377 / 12500000000000000))) + ((3189161951 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12357) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((8083529 / 1562500000000000000) : ℝ) + ((3189161951 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12357

namespace BstLean.Part266.Row12357
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12357 161 ∧
    0 ≤ (tableEnvelope C).f1 12357 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12357 161 ∧
    0 ≤ (tableEnvelope C).w1 12357 161 ∧ 0 ≤ (tableEnvelope C).w2 12357 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12357 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12357 161 ∧ 0 ≤ d.f1 12357 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12357 161 ∧ 0 ≤ d.w1 12357 161 ∧ 0 ≤ d.w2 12357 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12357 ≤ 2 * (228 / 100 : ℝ) / 12357 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12357 ≤ 2 * (370 / 100 : ℝ) / 12357 := by
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
    (completeRAData (tableEnvelope C) 12357 161).locationBound 12357 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12357 161).energyBound 12357 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12357 161) (d.f1 12357 161) d.f2 ≤
      32 * (((2453693769 / 500000000000000000) : ℝ) + (327437501 / 200000000000000000) + (393498563 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12357 161) (d.w1 12357 161)
      (d.w2 12357 161) ≤
      32 * (((995070163 / 50000000000000000000) : ℝ) + (707973377 / 50000000000000000000) + (103470407 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12357 161) (d.f1 12357 161) d.f2 ≤
      ((2453693769 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2453693769 / 500000000000000000)) * ((327437501 / 200000000000000000)) * (126 / 100) +
      2 * (((327437501 / 200000000000000000)) ^ 2 + 2 * ((2453693769 / 500000000000000000)) * ((393498563 / 1000000000000000000))) +
      6 * ((327437501 / 200000000000000000)) * ((393498563 / 1000000000000000000)) * (126 / 100) + 8 * ((393498563 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12357 161) (d.f1 12357 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12357 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12357 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12357 161) (d.f1 12357 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12357 161) (d.w1 12357 161) (d.w2 12357 161)
  have hwexpr0 : 0 ≤ d.w0 12357 161 + d.w1 12357 161 * √(π / 2) +
      2 * d.w2 12357 161 + energyR16 12357 *
      radiusPolynomialRoot16 (d.w0 12357 161) (d.w1 12357 161) (d.w2 12357 161) := by
    positivity
  constructor
  · change (12357 : ℝ) ^ 8 * (mA 12357 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12357 161) (d.f1 12357 161) d.f2 + locationR16 12357 *
        radiusPolynomialRoot16 (d.f0 12357 161) (d.f1 12357 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12357 : ℝ) ^ 8 * (mA 12357 : ℝ) ^ 8 *
        ((((2453693769 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2453693769 / 500000000000000000)) * ((327437501 / 200000000000000000)) * (126 / 100) +
          2 * (((327437501 / 200000000000000000)) ^ 2 + 2 * ((2453693769 / 500000000000000000)) * ((393498563 / 1000000000000000000))) +
          6 * ((327437501 / 200000000000000000)) * ((393498563 / 1000000000000000000)) * (126 / 100) + 8 * ((393498563 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12357) *
          (32 * (((2453693769 / 500000000000000000) : ℝ) + (327437501 / 200000000000000000) + (393498563 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12357 : ℝ) ^ 16 *
      (d.w0 12357 161 + d.w1 12357 161 * √(π / 2) + 2 * d.w2 12357 161 +
        energyR16 12357 * radiusPolynomialRoot16 (d.w0 12357 161) (d.w1 12357 161)
          (d.w2 12357 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12357 : ℝ) ^ 16 *
        (((995070163 / 50000000000000000000) : ℝ) + ((707973377 / 50000000000000000000)) * (126 / 100) + 2 * ((103470407 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12357) *
          (32 * (((995070163 / 50000000000000000000) : ℝ) + (707973377 / 50000000000000000000) + (103470407 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12357

/-! A coarse bound on the actual paper statistics constant at dimension 12358. -/
namespace BstLean.Part266.Row12358
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12356 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12356 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12356 128 ≤ (12610 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12610 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12358) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12358 : ℕ))
    (by norm_num : (12358 : ℕ) ≤ 16384)
  have ht : paperTail256 12358 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12358 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12358 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12358 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12358 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12358 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12356 128 * √(2 / (12358 : ℝ)) *
      (√(12358 : ℝ) + paperT0 12358 + paperTail256 12358) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12358 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12358 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12358 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12356 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12356 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12358 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12358

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12358
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12358 (61 / 100) 161 (17 / (100 * 12358)) (26 / (10 * 12358)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12358 (61 / 100) 161 (17 / (100 * 12358)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (51722027 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (837061463 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (796769327 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12358 / 12358 * (61 / 100)) ^ 4 * inverseRadius8 (12358 - 1) /
            envelopeGap 12358 (61 / 100) 161 (17 / (100 * 12358)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12358

namespace BstLean.Part266.Row12358
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12358 161 ≤ (613299313 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12358 161 ≤ (1636856241 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393418951 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12358 161 ≤ (49741429 / 2500000000000000000)
  w1 : (tableEnvelope C).w1 12358 161 ≤ (353900751 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12358 161 ≤ (103445289 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (51722027 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (51722027 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (837061463 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (796769327 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((231809 / 62500000) : ℝ) ≤ √(17 / (100 * 12358) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12358) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1137123861 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10229011823 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12358) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12358) ≤ (114437091 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12358) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12358 * (161 : ℝ) ^ 2 + 26 / (10 * 12358) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12358) : ℝ)) (tA 12358 * 161 ^ 2 + 26 / (10 * 12358)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((231809 / 62500000))) * ((51722027 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((231809 / 62500000)) ^ 3) * ((837061463 / 500000000000000000000000))) + ((796769327 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((231809 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12358) : ℝ)) d.D d.V d.P (√(tA 12358) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((231809 / 62500000)) ^ 2 * (((1137123861 / 500000000000000)) * ((10229011823 / 250000000000000000)))) + ((796769327 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12358) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((231809 / 62500000)) * ((51722027 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12358) : ℝ)) (tA 12358 * 161 ^ 2 + 26 / (10 * 12358)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((51722027 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((231809 / 62500000)) ^ 2) * ((837061463 / 500000000000000000000000)) + ((796769327 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12358) : ℝ)) (√(26 / (10 * 12358) : ℝ)) d.D d.V d.P (√(tA 12358) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((231809 / 62500000)) * (((1137123861 / 500000000000000)) * ((10229011823 / 250000000000000000))) + ((796769327 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12358) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((51722027 / 10000000000000000000) : ℝ) + ((796769327 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12358

namespace BstLean.Part266.Row12358
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12358 161 ∧
    0 ≤ (tableEnvelope C).f1 12358 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12358 161 ∧
    0 ≤ (tableEnvelope C).w1 12358 161 ∧ 0 ≤ (tableEnvelope C).w2 12358 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12358 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12358 161 ∧ 0 ≤ d.f1 12358 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12358 161 ∧ 0 ≤ d.w1 12358 161 ∧ 0 ≤ d.w2 12358 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12358 ≤ 2 * (228 / 100 : ℝ) / 12358 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12358 ≤ 2 * (370 / 100 : ℝ) / 12358 := by
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
    (completeRAData (tableEnvelope C) 12358 161).locationBound 12358 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12358 161).energyBound 12358 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12358 161) (d.f1 12358 161) d.f2 ≤
      32 * (((613299313 / 125000000000000000) : ℝ) + (1636856241 / 1000000000000000000) + (393418951 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12358 161) (d.w1 12358 161)
      (d.w2 12358 161) ≤
      32 * (((49741429 / 2500000000000000000) : ℝ) + (353900751 / 25000000000000000000) + (103445289 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12358 161) (d.f1 12358 161) d.f2 ≤
      ((613299313 / 125000000000000000) : ℝ) ^ 2 + 2 * ((613299313 / 125000000000000000)) * ((1636856241 / 1000000000000000000)) * (126 / 100) +
      2 * (((1636856241 / 1000000000000000000)) ^ 2 + 2 * ((613299313 / 125000000000000000)) * ((393418951 / 1000000000000000000))) +
      6 * ((1636856241 / 1000000000000000000)) * ((393418951 / 1000000000000000000)) * (126 / 100) + 8 * ((393418951 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12358 161) (d.f1 12358 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12358 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12358 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12358 161) (d.f1 12358 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12358 161) (d.w1 12358 161) (d.w2 12358 161)
  have hwexpr0 : 0 ≤ d.w0 12358 161 + d.w1 12358 161 * √(π / 2) +
      2 * d.w2 12358 161 + energyR16 12358 *
      radiusPolynomialRoot16 (d.w0 12358 161) (d.w1 12358 161) (d.w2 12358 161) := by
    positivity
  constructor
  · change (12358 : ℝ) ^ 8 * (mA 12358 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12358 161) (d.f1 12358 161) d.f2 + locationR16 12358 *
        radiusPolynomialRoot16 (d.f0 12358 161) (d.f1 12358 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12358 : ℝ) ^ 8 * (mA 12358 : ℝ) ^ 8 *
        ((((613299313 / 125000000000000000) : ℝ) ^ 2 + 2 * ((613299313 / 125000000000000000)) * ((1636856241 / 1000000000000000000)) * (126 / 100) +
          2 * (((1636856241 / 1000000000000000000)) ^ 2 + 2 * ((613299313 / 125000000000000000)) * ((393418951 / 1000000000000000000))) +
          6 * ((1636856241 / 1000000000000000000)) * ((393418951 / 1000000000000000000)) * (126 / 100) + 8 * ((393418951 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12358) *
          (32 * (((613299313 / 125000000000000000) : ℝ) + (1636856241 / 1000000000000000000) + (393418951 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12358 : ℝ) ^ 16 *
      (d.w0 12358 161 + d.w1 12358 161 * √(π / 2) + 2 * d.w2 12358 161 +
        energyR16 12358 * radiusPolynomialRoot16 (d.w0 12358 161) (d.w1 12358 161)
          (d.w2 12358 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12358 : ℝ) ^ 16 *
        (((49741429 / 2500000000000000000) : ℝ) + ((353900751 / 25000000000000000000)) * (126 / 100) + 2 * ((103445289 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12358) *
          (32 * (((49741429 / 2500000000000000000) : ℝ) + (353900751 / 25000000000000000000) + (103445289 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12358

/-! A coarse bound on the actual paper statistics constant at dimension 12359. -/
namespace BstLean.Part266.Row12359
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12357 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12357 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12357 128 ≤ (12611 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12611 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12359) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12359 : ℕ))
    (by norm_num : (12359 : ℕ) ≤ 16384)
  have ht : paperTail256 12359 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12359 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12359 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12359 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12359 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12359 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12357 128 * √(2 / (12359 : ℝ)) *
      (√(12359 : ℝ) + paperT0 12359 + paperTail256 12359) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12359 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12359 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12359 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12357 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12357 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12359 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12359

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12359
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12359 (61 / 100) 161 (17 / (100 * 12359)) (26 / (10 * 12359)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12359 (61 / 100) 161 (17 / (100 * 12359)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (129273681 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1673581139 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3184994199 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12359 / 12359 * (61 / 100)) ^ 4 * inverseRadius8 (12359 - 1) /
            envelopeGap 12359 (61 / 100) 161 (17 / (100 * 12359)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12359

namespace BstLean.Part266.Row12359
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12359 161 ≤ (4905401823 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12359 161 ≤ (818262543 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393339363 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12359 161 ≤ (497293541 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12359 161 ≤ (1415259371 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12359 161 ≤ (103420179 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (129273681 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (129273681 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1673581139 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3184994199 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1854397 / 500000000) : ℝ) ≤ √(17 / (100 * 12359) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12359) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2273971689 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40909426041 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12359) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12359) ≤ (114427831 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12359) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12359 * (161 : ℝ) ^ 2 + 26 / (10 * 12359) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12359) : ℝ)) (tA 12359 * 161 ^ 2 + 26 / (10 * 12359)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1854397 / 500000000))) * ((129273681 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1854397 / 500000000)) ^ 3) * ((1673581139 / 1000000000000000000000000))) + ((3184994199 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1854397 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12359) : ℝ)) d.D d.V d.P (√(tA 12359) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1854397 / 500000000)) ^ 2 * (((2273971689 / 1000000000000000)) * ((40909426041 / 1000000000000000000)))) + ((3184994199 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12359) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1854397 / 500000000)) * ((129273681 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12359) : ℝ)) (tA 12359 * 161 ^ 2 + 26 / (10 * 12359)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((129273681 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1854397 / 500000000)) ^ 2) * ((1673581139 / 1000000000000000000000000)) + ((3184994199 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12359) : ℝ)) (√(26 / (10 * 12359) : ℝ)) d.D d.V d.P (√(tA 12359) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1854397 / 500000000)) * (((2273971689 / 1000000000000000)) * ((40909426041 / 1000000000000000000))) + ((3184994199 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12359) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((129273681 / 25000000000000000000) : ℝ) + ((3184994199 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12359

namespace BstLean.Part266.Row12359
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12359 161 ∧
    0 ≤ (tableEnvelope C).f1 12359 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12359 161 ∧
    0 ≤ (tableEnvelope C).w1 12359 161 ∧ 0 ≤ (tableEnvelope C).w2 12359 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12359 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12359 161 ∧ 0 ≤ d.f1 12359 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12359 161 ∧ 0 ≤ d.w1 12359 161 ∧ 0 ≤ d.w2 12359 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12359 ≤ 2 * (228 / 100 : ℝ) / 12359 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12359 ≤ 2 * (370 / 100 : ℝ) / 12359 := by
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
    (completeRAData (tableEnvelope C) 12359 161).locationBound 12359 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12359 161).energyBound 12359 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12359 161) (d.f1 12359 161) d.f2 ≤
      32 * (((4905401823 / 1000000000000000000) : ℝ) + (818262543 / 500000000000000000) + (393339363 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12359 161) (d.w1 12359 161)
      (d.w2 12359 161) ≤
      32 * (((497293541 / 25000000000000000000) : ℝ) + (1415259371 / 100000000000000000000) + (103420179 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12359 161) (d.f1 12359 161) d.f2 ≤
      ((4905401823 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4905401823 / 1000000000000000000)) * ((818262543 / 500000000000000000)) * (126 / 100) +
      2 * (((818262543 / 500000000000000000)) ^ 2 + 2 * ((4905401823 / 1000000000000000000)) * ((393339363 / 1000000000000000000))) +
      6 * ((818262543 / 500000000000000000)) * ((393339363 / 1000000000000000000)) * (126 / 100) + 8 * ((393339363 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12359 161) (d.f1 12359 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12359 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12359 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12359 161) (d.f1 12359 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12359 161) (d.w1 12359 161) (d.w2 12359 161)
  have hwexpr0 : 0 ≤ d.w0 12359 161 + d.w1 12359 161 * √(π / 2) +
      2 * d.w2 12359 161 + energyR16 12359 *
      radiusPolynomialRoot16 (d.w0 12359 161) (d.w1 12359 161) (d.w2 12359 161) := by
    positivity
  constructor
  · change (12359 : ℝ) ^ 8 * (mA 12359 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12359 161) (d.f1 12359 161) d.f2 + locationR16 12359 *
        radiusPolynomialRoot16 (d.f0 12359 161) (d.f1 12359 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12359 : ℝ) ^ 8 * (mA 12359 : ℝ) ^ 8 *
        ((((4905401823 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4905401823 / 1000000000000000000)) * ((818262543 / 500000000000000000)) * (126 / 100) +
          2 * (((818262543 / 500000000000000000)) ^ 2 + 2 * ((4905401823 / 1000000000000000000)) * ((393339363 / 1000000000000000000))) +
          6 * ((818262543 / 500000000000000000)) * ((393339363 / 1000000000000000000)) * (126 / 100) + 8 * ((393339363 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12359) *
          (32 * (((4905401823 / 1000000000000000000) : ℝ) + (818262543 / 500000000000000000) + (393339363 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12359 : ℝ) ^ 16 *
      (d.w0 12359 161 + d.w1 12359 161 * √(π / 2) + 2 * d.w2 12359 161 +
        energyR16 12359 * radiusPolynomialRoot16 (d.w0 12359 161) (d.w1 12359 161)
          (d.w2 12359 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12359 : ℝ) ^ 16 *
        (((497293541 / 25000000000000000000) : ℝ) + ((1415259371 / 100000000000000000000)) * (126 / 100) + 2 * ((103420179 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12359) *
          (32 * (((497293541 / 25000000000000000000) : ℝ) + (1415259371 / 100000000000000000000) + (103420179 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12359

/-! A coarse bound on the actual paper statistics constant at dimension 12360. -/
namespace BstLean.Part266.Row12360
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12358 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12358 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12358 128 ≤ (12612 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12612 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12360) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12360 : ℕ))
    (by norm_num : (12360 : ℕ) ≤ 16384)
  have ht : paperTail256 12360 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12360 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12360 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12360 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12360 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12360 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12358 128 * √(2 / (12360 : ℝ)) *
      (√(12360 : ℝ) + paperT0 12360 + paperTail256 12360) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12360 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12360 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12360 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12358 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12358 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12360 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12360

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12360
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12360 (61 / 100) 161 (17 / (100 * 12360)) (26 / (10 * 12360)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12360 (61 / 100) 161 (17 / (100 * 12360)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (516969219 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (167303957 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6365825247 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12360 / 12360 * (61 / 100)) ^ 4 * inverseRadius8 (12360 - 1) /
            envelopeGap 12360 (61 / 100) 161 (17 / (100 * 12360)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12360

namespace BstLean.Part266.Row12360
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12360 161 ≤ (4904409489 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12360 161 ≤ (40904851 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1966299 / 5000000000000000)
  w0 : (tableEnvelope C).w0 12360 161 ≤ (1988691339 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12360 161 ≤ (1414915857 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12360 161 ≤ (258487693 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (516969219 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (516969219 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (167303957 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6365825247 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((927161 / 250000000) : ℝ) ≤ √(17 / (100 * 12360) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12360) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (71052991 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40902806383 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12360) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12360) ≤ (57209287 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12360) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12360 * (161 : ℝ) ^ 2 + 26 / (10 * 12360) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12360) : ℝ)) (tA 12360 * 161 ^ 2 + 26 / (10 * 12360)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((927161 / 250000000))) * ((516969219 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((927161 / 250000000)) ^ 3) * ((167303957 / 100000000000000000000000))) + ((6365825247 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((927161 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12360) : ℝ)) d.D d.V d.P (√(tA 12360) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((927161 / 250000000)) ^ 2 * (((71052991 / 31250000000000)) * ((40902806383 / 1000000000000000000)))) + ((6365825247 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12360) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((927161 / 250000000)) * ((516969219 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12360) : ℝ)) (tA 12360 * 161 ^ 2 + 26 / (10 * 12360)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((516969219 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((927161 / 250000000)) ^ 2) * ((167303957 / 100000000000000000000000)) + ((6365825247 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12360) : ℝ)) (√(26 / (10 * 12360) : ℝ)) d.D d.V d.P (√(tA 12360) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((927161 / 250000000)) * (((71052991 / 31250000000000)) * ((40902806383 / 1000000000000000000))) + ((6365825247 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12360) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((516969219 / 100000000000000000000) : ℝ) + ((6365825247 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12360

namespace BstLean.Part266.Row12360
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12360 161 ∧
    0 ≤ (tableEnvelope C).f1 12360 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12360 161 ∧
    0 ≤ (tableEnvelope C).w1 12360 161 ∧ 0 ≤ (tableEnvelope C).w2 12360 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12360 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12360 161 ∧ 0 ≤ d.f1 12360 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12360 161 ∧ 0 ≤ d.w1 12360 161 ∧ 0 ≤ d.w2 12360 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12360 ≤ 2 * (228 / 100 : ℝ) / 12360 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12360 ≤ 2 * (370 / 100 : ℝ) / 12360 := by
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
    (completeRAData (tableEnvelope C) 12360 161).locationBound 12360 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12360 161).energyBound 12360 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12360 161) (d.f1 12360 161) d.f2 ≤
      32 * (((4904409489 / 1000000000000000000) : ℝ) + (40904851 / 25000000000000000) + (1966299 / 5000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12360 161) (d.w1 12360 161)
      (d.w2 12360 161) ≤
      32 * (((1988691339 / 100000000000000000000) : ℝ) + (1414915857 / 100000000000000000000) + (258487693 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12360 161) (d.f1 12360 161) d.f2 ≤
      ((4904409489 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4904409489 / 1000000000000000000)) * ((40904851 / 25000000000000000)) * (126 / 100) +
      2 * (((40904851 / 25000000000000000)) ^ 2 + 2 * ((4904409489 / 1000000000000000000)) * ((1966299 / 5000000000000000))) +
      6 * ((40904851 / 25000000000000000)) * ((1966299 / 5000000000000000)) * (126 / 100) + 8 * ((1966299 / 5000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12360 161) (d.f1 12360 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12360 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12360 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12360 161) (d.f1 12360 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12360 161) (d.w1 12360 161) (d.w2 12360 161)
  have hwexpr0 : 0 ≤ d.w0 12360 161 + d.w1 12360 161 * √(π / 2) +
      2 * d.w2 12360 161 + energyR16 12360 *
      radiusPolynomialRoot16 (d.w0 12360 161) (d.w1 12360 161) (d.w2 12360 161) := by
    positivity
  constructor
  · change (12360 : ℝ) ^ 8 * (mA 12360 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12360 161) (d.f1 12360 161) d.f2 + locationR16 12360 *
        radiusPolynomialRoot16 (d.f0 12360 161) (d.f1 12360 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12360 : ℝ) ^ 8 * (mA 12360 : ℝ) ^ 8 *
        ((((4904409489 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4904409489 / 1000000000000000000)) * ((40904851 / 25000000000000000)) * (126 / 100) +
          2 * (((40904851 / 25000000000000000)) ^ 2 + 2 * ((4904409489 / 1000000000000000000)) * ((1966299 / 5000000000000000))) +
          6 * ((40904851 / 25000000000000000)) * ((1966299 / 5000000000000000)) * (126 / 100) + 8 * ((1966299 / 5000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12360) *
          (32 * (((4904409489 / 1000000000000000000) : ℝ) + (40904851 / 25000000000000000) + (1966299 / 5000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12360 : ℝ) ^ 16 *
      (d.w0 12360 161 + d.w1 12360 161 * √(π / 2) + 2 * d.w2 12360 161 +
        energyR16 12360 * radiusPolynomialRoot16 (d.w0 12360 161) (d.w1 12360 161)
          (d.w2 12360 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12360 : ℝ) ^ 16 *
        (((1988691339 / 100000000000000000000) : ℝ) + ((1414915857 / 100000000000000000000)) * (126 / 100) + 2 * ((258487693 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12360) *
          (32 * (((1988691339 / 100000000000000000000) : ℝ) + (1414915857 / 100000000000000000000) + (258487693 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12360

/-! A coarse bound on the actual paper statistics constant at dimension 12361. -/
namespace BstLean.Part266.Row12361
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12359 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12359 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12359 128 ≤ (12613 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12613 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12361) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12361 : ℕ))
    (by norm_num : (12361 : ℕ) ≤ 16384)
  have ht : paperTail256 12361 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12361 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12361 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12361 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12361 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12361 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12359 128 * √(2 / (12361 : ℝ)) *
      (√(12361 : ℝ) + paperT0 12361 + paperTail256 12361) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12361 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12361 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12361 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12359 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12359 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12361 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12361

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12361
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12361 (61 / 100) 161 (17 / (100 * 12361)) (26 / (10 * 12361)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12361 (61 / 100) 161 (17 / (100 * 12361)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (103368751 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1672498221 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6361665159 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12361 / 12361 * (61 / 100)) ^ 4 * inverseRadius8 (12361 - 1) /
            envelopeGap 12361 (61 / 100) 161 (17 / (100 * 12361)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12361

namespace BstLean.Part266.Row12361
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12361 161 ≤ (4903417509 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12361 161 ≤ (817931553 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (196590131 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12361 161 ≤ (994104343 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12361 161 ≤ (707286231 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12361 161 ≤ (258424959 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (103368751 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (103368751 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1672498221 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6361665159 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1854247 / 500000000) : ℝ) ≤ √(17 / (100 * 12361) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12361) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (142088737 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (5112023543 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12361) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12361) ≤ (114409317 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12361) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12361 * (161 : ℝ) ^ 2 + 26 / (10 * 12361) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12361) : ℝ)) (tA 12361 * 161 ^ 2 + 26 / (10 * 12361)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1854247 / 500000000))) * ((103368751 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1854247 / 500000000)) ^ 3) * ((1672498221 / 1000000000000000000000000))) + ((6361665159 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1854247 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12361) : ℝ)) d.D d.V d.P (√(tA 12361) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1854247 / 500000000)) ^ 2 * (((142088737 / 62500000000000)) * ((5112023543 / 125000000000000000)))) + ((6361665159 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12361) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1854247 / 500000000)) * ((103368751 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12361) : ℝ)) (tA 12361 * 161 ^ 2 + 26 / (10 * 12361)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((103368751 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1854247 / 500000000)) ^ 2) * ((1672498221 / 1000000000000000000000000)) + ((6361665159 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12361) : ℝ)) (√(26 / (10 * 12361) : ℝ)) d.D d.V d.P (√(tA 12361) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1854247 / 500000000)) * (((142088737 / 62500000000000)) * ((5112023543 / 125000000000000000))) + ((6361665159 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12361) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((103368751 / 20000000000000000000) : ℝ) + ((6361665159 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12361

namespace BstLean.Part266.Row12361
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12361 161 ∧
    0 ≤ (tableEnvelope C).f1 12361 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12361 161 ∧
    0 ≤ (tableEnvelope C).w1 12361 161 ∧ 0 ≤ (tableEnvelope C).w2 12361 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12361 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12361 161 ∧ 0 ≤ d.f1 12361 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12361 161 ∧ 0 ≤ d.w1 12361 161 ∧ 0 ≤ d.w2 12361 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12361 ≤ 2 * (228 / 100 : ℝ) / 12361 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12361 ≤ 2 * (370 / 100 : ℝ) / 12361 := by
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
    (completeRAData (tableEnvelope C) 12361 161).locationBound 12361 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12361 161).energyBound 12361 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12361 161) (d.f1 12361 161) d.f2 ≤
      32 * (((4903417509 / 1000000000000000000) : ℝ) + (817931553 / 500000000000000000) + (196590131 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12361 161) (d.w1 12361 161)
      (d.w2 12361 161) ≤
      32 * (((994104343 / 50000000000000000000) : ℝ) + (707286231 / 50000000000000000000) + (258424959 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12361 161) (d.f1 12361 161) d.f2 ≤
      ((4903417509 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4903417509 / 1000000000000000000)) * ((817931553 / 500000000000000000)) * (126 / 100) +
      2 * (((817931553 / 500000000000000000)) ^ 2 + 2 * ((4903417509 / 1000000000000000000)) * ((196590131 / 500000000000000000))) +
      6 * ((817931553 / 500000000000000000)) * ((196590131 / 500000000000000000)) * (126 / 100) + 8 * ((196590131 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12361 161) (d.f1 12361 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12361 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12361 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12361 161) (d.f1 12361 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12361 161) (d.w1 12361 161) (d.w2 12361 161)
  have hwexpr0 : 0 ≤ d.w0 12361 161 + d.w1 12361 161 * √(π / 2) +
      2 * d.w2 12361 161 + energyR16 12361 *
      radiusPolynomialRoot16 (d.w0 12361 161) (d.w1 12361 161) (d.w2 12361 161) := by
    positivity
  constructor
  · change (12361 : ℝ) ^ 8 * (mA 12361 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12361 161) (d.f1 12361 161) d.f2 + locationR16 12361 *
        radiusPolynomialRoot16 (d.f0 12361 161) (d.f1 12361 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12361 : ℝ) ^ 8 * (mA 12361 : ℝ) ^ 8 *
        ((((4903417509 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4903417509 / 1000000000000000000)) * ((817931553 / 500000000000000000)) * (126 / 100) +
          2 * (((817931553 / 500000000000000000)) ^ 2 + 2 * ((4903417509 / 1000000000000000000)) * ((196590131 / 500000000000000000))) +
          6 * ((817931553 / 500000000000000000)) * ((196590131 / 500000000000000000)) * (126 / 100) + 8 * ((196590131 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12361) *
          (32 * (((4903417509 / 1000000000000000000) : ℝ) + (817931553 / 500000000000000000) + (196590131 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12361 : ℝ) ^ 16 *
      (d.w0 12361 161 + d.w1 12361 161 * √(π / 2) + 2 * d.w2 12361 161 +
        energyR16 12361 * radiusPolynomialRoot16 (d.w0 12361 161) (d.w1 12361 161)
          (d.w2 12361 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12361 : ℝ) ^ 16 *
        (((994104343 / 50000000000000000000) : ℝ) + ((707286231 / 50000000000000000000)) * (126 / 100) + 2 * ((258424959 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12361) *
          (32 * (((994104343 / 50000000000000000000) : ℝ) + (707286231 / 50000000000000000000) + (258424959 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12361

/-! A coarse bound on the actual paper statistics constant at dimension 12362. -/
namespace BstLean.Part266.Row12362
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12360 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12360 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12360 128 ≤ (12614 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12614 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12362) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12362 : ℕ))
    (by norm_num : (12362 : ℕ) ≤ 16384)
  have ht : paperTail256 12362 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12362 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12362 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12362 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12362 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12362 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12360 128 * √(2 / (12362 : ℝ)) *
      (√(12362 : ℝ) + paperT0 12362 + paperTail256 12362) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12362 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12362 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12362 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12360 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12360 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12362 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12362

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12362
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12362 (61 / 100) 161 (17 / (100 * 12362)) (26 / (10 * 12362)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12362 (61 / 100) 161 (17 / (100 * 12362)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (516718331 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1671957091 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6357508133 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12362 / 12362 * (61 / 100)) ^ 4 * inverseRadius8 (12362 - 1) /
            envelopeGap 12362 (61 / 100) 161 (17 / (100 * 12362)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12362

namespace BstLean.Part266.Row12362
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12362 161 ≤ (4902425879 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12362 161 ≤ (40888307 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (98275187 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12362 161 ≤ (993863101 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12362 161 ≤ (22097331 / 1562500000000000000)
  w2 : (tableEnvelope C).w2 12362 161 ≤ (51672449 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (516718331 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (516718331 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1671957091 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6357508133 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((463543 / 125000000) : ℝ) ≤ √(17 / (100 * 12362) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12362) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2273143927 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40889571911 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12362) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12362) ≤ (57200031 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12362) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12362 * (161 : ℝ) ^ 2 + 26 / (10 * 12362) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12362) : ℝ)) (tA 12362 * 161 ^ 2 + 26 / (10 * 12362)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((463543 / 125000000))) * ((516718331 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((463543 / 125000000)) ^ 3) * ((1671957091 / 1000000000000000000000000))) + ((6357508133 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((463543 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12362) : ℝ)) d.D d.V d.P (√(tA 12362) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((463543 / 125000000)) ^ 2 * (((2273143927 / 1000000000000000)) * ((40889571911 / 1000000000000000000)))) + ((6357508133 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12362) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((463543 / 125000000)) * ((516718331 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12362) : ℝ)) (tA 12362 * 161 ^ 2 + 26 / (10 * 12362)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((516718331 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((463543 / 125000000)) ^ 2) * ((1671957091 / 1000000000000000000000000)) + ((6357508133 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12362) : ℝ)) (√(26 / (10 * 12362) : ℝ)) d.D d.V d.P (√(tA 12362) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((463543 / 125000000)) * (((2273143927 / 1000000000000000)) * ((40889571911 / 1000000000000000000))) + ((6357508133 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12362) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((516718331 / 100000000000000000000) : ℝ) + ((6357508133 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12362

namespace BstLean.Part266.Row12362
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12362 161 ∧
    0 ≤ (tableEnvelope C).f1 12362 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12362 161 ∧
    0 ≤ (tableEnvelope C).w1 12362 161 ∧ 0 ≤ (tableEnvelope C).w2 12362 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12362 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12362 161 ∧ 0 ≤ d.f1 12362 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12362 161 ∧ 0 ≤ d.w1 12362 161 ∧ 0 ≤ d.w2 12362 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12362 ≤ 2 * (228 / 100 : ℝ) / 12362 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12362 ≤ 2 * (370 / 100 : ℝ) / 12362 := by
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
    (completeRAData (tableEnvelope C) 12362 161).locationBound 12362 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12362 161).energyBound 12362 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12362 161) (d.f1 12362 161) d.f2 ≤
      32 * (((4902425879 / 1000000000000000000) : ℝ) + (40888307 / 25000000000000000) + (98275187 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12362 161) (d.w1 12362 161)
      (d.w2 12362 161) ≤
      32 * (((993863101 / 50000000000000000000) : ℝ) + (22097331 / 1562500000000000000) + (51672449 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12362 161) (d.f1 12362 161) d.f2 ≤
      ((4902425879 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4902425879 / 1000000000000000000)) * ((40888307 / 25000000000000000)) * (126 / 100) +
      2 * (((40888307 / 25000000000000000)) ^ 2 + 2 * ((4902425879 / 1000000000000000000)) * ((98275187 / 250000000000000000))) +
      6 * ((40888307 / 25000000000000000)) * ((98275187 / 250000000000000000)) * (126 / 100) + 8 * ((98275187 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12362 161) (d.f1 12362 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12362 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12362 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12362 161) (d.f1 12362 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12362 161) (d.w1 12362 161) (d.w2 12362 161)
  have hwexpr0 : 0 ≤ d.w0 12362 161 + d.w1 12362 161 * √(π / 2) +
      2 * d.w2 12362 161 + energyR16 12362 *
      radiusPolynomialRoot16 (d.w0 12362 161) (d.w1 12362 161) (d.w2 12362 161) := by
    positivity
  constructor
  · change (12362 : ℝ) ^ 8 * (mA 12362 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12362 161) (d.f1 12362 161) d.f2 + locationR16 12362 *
        radiusPolynomialRoot16 (d.f0 12362 161) (d.f1 12362 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12362 : ℝ) ^ 8 * (mA 12362 : ℝ) ^ 8 *
        ((((4902425879 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4902425879 / 1000000000000000000)) * ((40888307 / 25000000000000000)) * (126 / 100) +
          2 * (((40888307 / 25000000000000000)) ^ 2 + 2 * ((4902425879 / 1000000000000000000)) * ((98275187 / 250000000000000000))) +
          6 * ((40888307 / 25000000000000000)) * ((98275187 / 250000000000000000)) * (126 / 100) + 8 * ((98275187 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12362) *
          (32 * (((4902425879 / 1000000000000000000) : ℝ) + (40888307 / 25000000000000000) + (98275187 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12362 : ℝ) ^ 16 *
      (d.w0 12362 161 + d.w1 12362 161 * √(π / 2) + 2 * d.w2 12362 161 +
        energyR16 12362 * radiusPolynomialRoot16 (d.w0 12362 161) (d.w1 12362 161)
          (d.w2 12362 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12362 : ℝ) ^ 16 *
        (((993863101 / 50000000000000000000) : ℝ) + ((22097331 / 1562500000000000000)) * (126 / 100) + 2 * ((51672449 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12362) *
          (32 * (((993863101 / 50000000000000000000) : ℝ) + (22097331 / 1562500000000000000) + (51672449 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12362

/-! A coarse bound on the actual paper statistics constant at dimension 12363. -/
namespace BstLean.Part266.Row12363
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12361 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12361 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12361 128 ≤ (12615 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12615 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12363) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12363 : ℕ))
    (by norm_num : (12363 : ℕ) ≤ 16384)
  have ht : paperTail256 12363 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12363 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12363 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12363 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12363 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12363 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12361 128 * √(2 / (12363 : ℝ)) *
      (√(12363 : ℝ) + paperT0 12363 + paperTail256 12363) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12363 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12363 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12363 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12361 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12361 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12363 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12363

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12363
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12363 (61 / 100) 161 (17 / (100 * 12363)) (26 / (10 * 12363)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12363 (61 / 100) 161 (17 / (100 * 12363)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (129148237 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (83570809 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6353354167 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12363 / 12363 * (61 / 100)) ^ 4 * inverseRadius8 (12363 - 1) /
            envelopeGap 12363 (61 / 100) 161 (17 / (100 * 12363)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12363

namespace BstLean.Part266.Row12363
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12363 161 ≤ (24507173 / 5000000000000000)
  f1 : (tableEnvelope C).f1 12363 161 ≤ (327040313 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (393021259 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12363 161 ≤ (198724389 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12363 161 ≤ (176735753 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12363 161 ≤ (516599103 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (129148237 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (129148237 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (83570809 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6353354167 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1854097 / 500000000) : ℝ) ≤ √(17 / (100 * 12363) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12363) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1136434059 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8176591417 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12363) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12363) ≤ (114390809 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12363) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12363 * (161 : ℝ) ^ 2 + 26 / (10 * 12363) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12363) : ℝ)) (tA 12363 * 161 ^ 2 + 26 / (10 * 12363)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1854097 / 500000000))) * ((129148237 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1854097 / 500000000)) ^ 3) * ((83570809 / 50000000000000000000000))) + ((6353354167 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1854097 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12363) : ℝ)) d.D d.V d.P (√(tA 12363) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1854097 / 500000000)) ^ 2 * (((1136434059 / 500000000000000)) * ((8176591417 / 200000000000000000)))) + ((6353354167 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12363) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1854097 / 500000000)) * ((129148237 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12363) : ℝ)) (tA 12363 * 161 ^ 2 + 26 / (10 * 12363)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((129148237 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1854097 / 500000000)) ^ 2) * ((83570809 / 50000000000000000000000)) + ((6353354167 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12363) : ℝ)) (√(26 / (10 * 12363) : ℝ)) d.D d.V d.P (√(tA 12363) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1854097 / 500000000)) * (((1136434059 / 500000000000000)) * ((8176591417 / 200000000000000000))) + ((6353354167 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12363) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((129148237 / 25000000000000000000) : ℝ) + ((6353354167 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12363

namespace BstLean.Part266.Row12363
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12363 161 ∧
    0 ≤ (tableEnvelope C).f1 12363 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12363 161 ∧
    0 ≤ (tableEnvelope C).w1 12363 161 ∧ 0 ≤ (tableEnvelope C).w2 12363 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12363 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12363 161 ∧ 0 ≤ d.f1 12363 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12363 161 ∧ 0 ≤ d.w1 12363 161 ∧ 0 ≤ d.w2 12363 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12363 ≤ 2 * (228 / 100 : ℝ) / 12363 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12363 ≤ 2 * (370 / 100 : ℝ) / 12363 := by
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
    (completeRAData (tableEnvelope C) 12363 161).locationBound 12363 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12363 161).energyBound 12363 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12363 161) (d.f1 12363 161) d.f2 ≤
      32 * (((24507173 / 5000000000000000) : ℝ) + (327040313 / 200000000000000000) + (393021259 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12363 161) (d.w1 12363 161)
      (d.w2 12363 161) ≤
      32 * (((198724389 / 10000000000000000000) : ℝ) + (176735753 / 12500000000000000000) + (516599103 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12363 161) (d.f1 12363 161) d.f2 ≤
      ((24507173 / 5000000000000000) : ℝ) ^ 2 + 2 * ((24507173 / 5000000000000000)) * ((327040313 / 200000000000000000)) * (126 / 100) +
      2 * (((327040313 / 200000000000000000)) ^ 2 + 2 * ((24507173 / 5000000000000000)) * ((393021259 / 1000000000000000000))) +
      6 * ((327040313 / 200000000000000000)) * ((393021259 / 1000000000000000000)) * (126 / 100) + 8 * ((393021259 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12363 161) (d.f1 12363 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12363 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12363 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12363 161) (d.f1 12363 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12363 161) (d.w1 12363 161) (d.w2 12363 161)
  have hwexpr0 : 0 ≤ d.w0 12363 161 + d.w1 12363 161 * √(π / 2) +
      2 * d.w2 12363 161 + energyR16 12363 *
      radiusPolynomialRoot16 (d.w0 12363 161) (d.w1 12363 161) (d.w2 12363 161) := by
    positivity
  constructor
  · change (12363 : ℝ) ^ 8 * (mA 12363 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12363 161) (d.f1 12363 161) d.f2 + locationR16 12363 *
        radiusPolynomialRoot16 (d.f0 12363 161) (d.f1 12363 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12363 : ℝ) ^ 8 * (mA 12363 : ℝ) ^ 8 *
        ((((24507173 / 5000000000000000) : ℝ) ^ 2 + 2 * ((24507173 / 5000000000000000)) * ((327040313 / 200000000000000000)) * (126 / 100) +
          2 * (((327040313 / 200000000000000000)) ^ 2 + 2 * ((24507173 / 5000000000000000)) * ((393021259 / 1000000000000000000))) +
          6 * ((327040313 / 200000000000000000)) * ((393021259 / 1000000000000000000)) * (126 / 100) + 8 * ((393021259 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12363) *
          (32 * (((24507173 / 5000000000000000) : ℝ) + (327040313 / 200000000000000000) + (393021259 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12363 : ℝ) ^ 16 *
      (d.w0 12363 161 + d.w1 12363 161 * √(π / 2) + 2 * d.w2 12363 161 +
        energyR16 12363 * radiusPolynomialRoot16 (d.w0 12363 161) (d.w1 12363 161)
          (d.w2 12363 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12363 : ℝ) ^ 16 *
        (((198724389 / 10000000000000000000) : ℝ) + ((176735753 / 12500000000000000000)) * (126 / 100) + 2 * ((516599103 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12363) *
          (32 * (((198724389 / 10000000000000000000) : ℝ) + (176735753 / 12500000000000000000) + (516599103 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12363

/-! A coarse bound on the actual paper statistics constant at dimension 12364. -/
namespace BstLean.Part266.Row12364
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12362 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12362 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12362 128 ≤ (12616 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12616 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12364) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12364 : ℕ))
    (by norm_num : (12364 : ℕ) ≤ 16384)
  have ht : paperTail256 12364 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12364 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12364 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12364 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12364 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12364 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12362 128 * √(2 / (12364 : ℝ)) *
      (√(12364 : ℝ) + paperT0 12364 + paperTail256 12364) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12364 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12364 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12364 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12362 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12362 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12364 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12364

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12364
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12364 (61 / 100) 161 (17 / (100 * 12364)) (26 / (10 * 12364)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12364 (61 / 100) 161 (17 / (100 * 12364)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (103293521 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1670875487 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (793650407 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12364 / 12364 * (61 / 100)) ^ 4 * inverseRadius8 (12364 - 1) /
            envelopeGap 12364 (61 / 100) 161 (17 / (100 * 12364)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12364

namespace BstLean.Part266.Row12364
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12364 161 ≤ (1225110917 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12364 161 ≤ (817435479 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (392941793 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12364 161 ≤ (1986761747 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12364 161 ≤ (706771491 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12364 161 ≤ (129118439 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (103293521 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (103293521 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1670875487 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (793650407 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((927011 / 250000000) : ℝ) ≤ √(17 / (100 * 12364) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12364) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (568148091 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2554771491 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12364) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12364) ≤ (114381557 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12364) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12364 * (161 : ℝ) ^ 2 + 26 / (10 * 12364) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12364) : ℝ)) (tA 12364 * 161 ^ 2 + 26 / (10 * 12364)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((927011 / 250000000))) * ((103293521 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((927011 / 250000000)) ^ 3) * ((1670875487 / 1000000000000000000000000))) + ((793650407 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((927011 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12364) : ℝ)) d.D d.V d.P (√(tA 12364) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((927011 / 250000000)) ^ 2 * (((568148091 / 250000000000000)) * ((2554771491 / 62500000000000000)))) + ((793650407 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12364) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((927011 / 250000000)) * ((103293521 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12364) : ℝ)) (tA 12364 * 161 ^ 2 + 26 / (10 * 12364)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((103293521 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((927011 / 250000000)) ^ 2) * ((1670875487 / 1000000000000000000000000)) + ((793650407 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12364) : ℝ)) (√(26 / (10 * 12364) : ℝ)) d.D d.V d.P (√(tA 12364) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((927011 / 250000000)) * (((568148091 / 250000000000000)) * ((2554771491 / 62500000000000000))) + ((793650407 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12364) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((103293521 / 20000000000000000000) : ℝ) + ((793650407 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12364

namespace BstLean.Part266.Row12364
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12364 161 ∧
    0 ≤ (tableEnvelope C).f1 12364 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12364 161 ∧
    0 ≤ (tableEnvelope C).w1 12364 161 ∧ 0 ≤ (tableEnvelope C).w2 12364 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12364 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12364 161 ∧ 0 ≤ d.f1 12364 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12364 161 ∧ 0 ≤ d.w1 12364 161 ∧ 0 ≤ d.w2 12364 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12364 ≤ 2 * (228 / 100 : ℝ) / 12364 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12364 ≤ 2 * (370 / 100 : ℝ) / 12364 := by
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
    (completeRAData (tableEnvelope C) 12364 161).locationBound 12364 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12364 161).energyBound 12364 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12364 161) (d.f1 12364 161) d.f2 ≤
      32 * (((1225110917 / 250000000000000000) : ℝ) + (817435479 / 500000000000000000) + (392941793 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12364 161) (d.w1 12364 161)
      (d.w2 12364 161) ≤
      32 * (((1986761747 / 100000000000000000000) : ℝ) + (706771491 / 50000000000000000000) + (129118439 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12364 161) (d.f1 12364 161) d.f2 ≤
      ((1225110917 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1225110917 / 250000000000000000)) * ((817435479 / 500000000000000000)) * (126 / 100) +
      2 * (((817435479 / 500000000000000000)) ^ 2 + 2 * ((1225110917 / 250000000000000000)) * ((392941793 / 1000000000000000000))) +
      6 * ((817435479 / 500000000000000000)) * ((392941793 / 1000000000000000000)) * (126 / 100) + 8 * ((392941793 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12364 161) (d.f1 12364 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12364 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12364 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12364 161) (d.f1 12364 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12364 161) (d.w1 12364 161) (d.w2 12364 161)
  have hwexpr0 : 0 ≤ d.w0 12364 161 + d.w1 12364 161 * √(π / 2) +
      2 * d.w2 12364 161 + energyR16 12364 *
      radiusPolynomialRoot16 (d.w0 12364 161) (d.w1 12364 161) (d.w2 12364 161) := by
    positivity
  constructor
  · change (12364 : ℝ) ^ 8 * (mA 12364 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12364 161) (d.f1 12364 161) d.f2 + locationR16 12364 *
        radiusPolynomialRoot16 (d.f0 12364 161) (d.f1 12364 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12364 : ℝ) ^ 8 * (mA 12364 : ℝ) ^ 8 *
        ((((1225110917 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1225110917 / 250000000000000000)) * ((817435479 / 500000000000000000)) * (126 / 100) +
          2 * (((817435479 / 500000000000000000)) ^ 2 + 2 * ((1225110917 / 250000000000000000)) * ((392941793 / 1000000000000000000))) +
          6 * ((817435479 / 500000000000000000)) * ((392941793 / 1000000000000000000)) * (126 / 100) + 8 * ((392941793 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12364) *
          (32 * (((1225110917 / 250000000000000000) : ℝ) + (817435479 / 500000000000000000) + (392941793 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12364 : ℝ) ^ 16 *
      (d.w0 12364 161 + d.w1 12364 161 * √(π / 2) + 2 * d.w2 12364 161 +
        energyR16 12364 * radiusPolynomialRoot16 (d.w0 12364 161) (d.w1 12364 161)
          (d.w2 12364 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12364 : ℝ) ^ 16 *
        (((1986761747 / 100000000000000000000) : ℝ) + ((706771491 / 50000000000000000000)) * (126 / 100) + 2 * ((129118439 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12364) *
          (32 * (((1986761747 / 100000000000000000000) : ℝ) + (706771491 / 50000000000000000000) + (129118439 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12364

/-! A coarse bound on the actual paper statistics constant at dimension 12365. -/
namespace BstLean.Part266.Row12365
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12363 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12363 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12363 128 ≤ (12617 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12617 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12365) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12365 : ℕ))
    (by norm_num : (12365 : ℕ) ≤ 16384)
  have ht : paperTail256 12365 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12365 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12365 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12365 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12365 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12365 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12363 128 * √(2 / (12365 : ℝ)) *
      (√(12365 : ℝ) + paperT0 12365 + paperTail256 12365) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12365 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12365 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12365 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12363 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12363 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12365 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12365

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12365
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12365 (61 / 100) 161 (17 / (100 * 12365)) (26 / (10 * 12365)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12365 (61 / 100) 161 (17 / (100 * 12365)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (516342303 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1670335013 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (31725277 / 5000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12365 / 12365 * (61 / 100)) ^ 4 * inverseRadius8 (12365 - 1) /
            envelopeGap 12365 (61 / 100) 161 (17 / (100 * 12365)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12365

namespace BstLean.Part266.Row12365
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12365 161 ≤ (153107909 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12365 161 ≤ (817270231 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (392862353 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12365 161 ≤ (79451191 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12365 161 ≤ (706600029 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12365 161 ≤ (10326969 / 2000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (516342303 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (516342303 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1670335013 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (31725277 / 5000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1853947 / 500000000) : ℝ) ≤ √(17 / (100 * 12365) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12365) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1136158333 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10217433059 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12365) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12365) ≤ (57186153 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12365) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12365 * (161 : ℝ) ^ 2 + 26 / (10 * 12365) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12365) : ℝ)) (tA 12365 * 161 ^ 2 + 26 / (10 * 12365)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1853947 / 500000000))) * ((516342303 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1853947 / 500000000)) ^ 3) * ((1670335013 / 1000000000000000000000000))) + ((31725277 / 5000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1853947 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12365) : ℝ)) d.D d.V d.P (√(tA 12365) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1853947 / 500000000)) ^ 2 * (((1136158333 / 500000000000000)) * ((10217433059 / 250000000000000000)))) + ((31725277 / 5000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12365) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1853947 / 500000000)) * ((516342303 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12365) : ℝ)) (tA 12365 * 161 ^ 2 + 26 / (10 * 12365)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((516342303 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1853947 / 500000000)) ^ 2) * ((1670335013 / 1000000000000000000000000)) + ((31725277 / 5000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12365) : ℝ)) (√(26 / (10 * 12365) : ℝ)) d.D d.V d.P (√(tA 12365) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1853947 / 500000000)) * (((1136158333 / 500000000000000)) * ((10217433059 / 250000000000000000))) + ((31725277 / 5000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12365) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((516342303 / 100000000000000000000) : ℝ) + ((31725277 / 5000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12365

namespace BstLean.Part266.Row12365
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12365 161 ∧
    0 ≤ (tableEnvelope C).f1 12365 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12365 161 ∧
    0 ≤ (tableEnvelope C).w1 12365 161 ∧ 0 ≤ (tableEnvelope C).w2 12365 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12365 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12365 161 ∧ 0 ≤ d.f1 12365 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12365 161 ∧ 0 ≤ d.w1 12365 161 ∧ 0 ≤ d.w2 12365 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12365 ≤ 2 * (228 / 100 : ℝ) / 12365 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12365 ≤ 2 * (370 / 100 : ℝ) / 12365 := by
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
    (completeRAData (tableEnvelope C) 12365 161).locationBound 12365 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12365 161).energyBound 12365 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12365 161) (d.f1 12365 161) d.f2 ≤
      32 * (((153107909 / 31250000000000000) : ℝ) + (817270231 / 500000000000000000) + (392862353 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12365 161) (d.w1 12365 161)
      (d.w2 12365 161) ≤
      32 * (((79451191 / 4000000000000000000) : ℝ) + (706600029 / 50000000000000000000) + (10326969 / 2000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12365 161) (d.f1 12365 161) d.f2 ≤
      ((153107909 / 31250000000000000) : ℝ) ^ 2 + 2 * ((153107909 / 31250000000000000)) * ((817270231 / 500000000000000000)) * (126 / 100) +
      2 * (((817270231 / 500000000000000000)) ^ 2 + 2 * ((153107909 / 31250000000000000)) * ((392862353 / 1000000000000000000))) +
      6 * ((817270231 / 500000000000000000)) * ((392862353 / 1000000000000000000)) * (126 / 100) + 8 * ((392862353 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12365 161) (d.f1 12365 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12365 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12365 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12365 161) (d.f1 12365 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12365 161) (d.w1 12365 161) (d.w2 12365 161)
  have hwexpr0 : 0 ≤ d.w0 12365 161 + d.w1 12365 161 * √(π / 2) +
      2 * d.w2 12365 161 + energyR16 12365 *
      radiusPolynomialRoot16 (d.w0 12365 161) (d.w1 12365 161) (d.w2 12365 161) := by
    positivity
  constructor
  · change (12365 : ℝ) ^ 8 * (mA 12365 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12365 161) (d.f1 12365 161) d.f2 + locationR16 12365 *
        radiusPolynomialRoot16 (d.f0 12365 161) (d.f1 12365 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12365 : ℝ) ^ 8 * (mA 12365 : ℝ) ^ 8 *
        ((((153107909 / 31250000000000000) : ℝ) ^ 2 + 2 * ((153107909 / 31250000000000000)) * ((817270231 / 500000000000000000)) * (126 / 100) +
          2 * (((817270231 / 500000000000000000)) ^ 2 + 2 * ((153107909 / 31250000000000000)) * ((392862353 / 1000000000000000000))) +
          6 * ((817270231 / 500000000000000000)) * ((392862353 / 1000000000000000000)) * (126 / 100) + 8 * ((392862353 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12365) *
          (32 * (((153107909 / 31250000000000000) : ℝ) + (817270231 / 500000000000000000) + (392862353 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12365 : ℝ) ^ 16 *
      (d.w0 12365 161 + d.w1 12365 161 * √(π / 2) + 2 * d.w2 12365 161 +
        energyR16 12365 * radiusPolynomialRoot16 (d.w0 12365 161) (d.w1 12365 161)
          (d.w2 12365 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12365 : ℝ) ^ 16 *
        (((79451191 / 4000000000000000000) : ℝ) + ((706600029 / 50000000000000000000)) * (126 / 100) + 2 * ((10326969 / 2000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12365) *
          (32 * (((79451191 / 4000000000000000000) : ℝ) + (706600029 / 50000000000000000000) + (10326969 / 2000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12365

/-! A coarse bound on the actual paper statistics constant at dimension 12366. -/
namespace BstLean.Part266.Row12366
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12364 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12364 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12364 128 ≤ (12618 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12618 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12366) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12366 : ℕ))
    (by norm_num : (12366 : ℕ) ≤ 16384)
  have ht : paperTail256 12366 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12366 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12366 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12366 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12366 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12366 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12364 128 * √(2 / (12366 : ℝ)) *
      (√(12366 : ℝ) + paperT0 12366 + paperTail256 12366) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12366 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12366 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12366 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12364 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12364 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12366 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12366

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12366
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12366 (61 / 100) 161 (17 / (100 * 12366)) (26 / (10 * 12366)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12366 (61 / 100) 161 (17 / (100 * 12366)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (516217041 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1669794757 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1268182119 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12366 / 12366 * (61 / 100)) ^ 4 * inverseRadius8 (12366 - 1) /
            envelopeGap 12366 (61 / 100) 161 (17 / (100 * 12366)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12366

namespace BstLean.Part266.Row12366
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12366 161 ≤ (979692571 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12366 161 ≤ (817105037 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (49097867 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12366 161 ≤ (496449493 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12366 161 ≤ (1412857251 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12366 161 ≤ (32263949 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (516217041 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (516217041 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1669794757 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1268182119 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((115867 / 31250000) : ℝ) ≤ √(17 / (100 * 12366) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12366) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2272041023 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20431561107 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12366) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12366) ≤ (114363057 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12366) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12366 * (161 : ℝ) ^ 2 + 26 / (10 * 12366) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12366) : ℝ)) (tA 12366 * 161 ^ 2 + 26 / (10 * 12366)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((115867 / 31250000))) * ((516217041 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((115867 / 31250000)) ^ 3) * ((1669794757 / 1000000000000000000000000))) + ((1268182119 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((115867 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12366) : ℝ)) d.D d.V d.P (√(tA 12366) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((115867 / 31250000)) ^ 2 * (((2272041023 / 1000000000000000)) * ((20431561107 / 500000000000000000)))) + ((1268182119 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12366) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((115867 / 31250000)) * ((516217041 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12366) : ℝ)) (tA 12366 * 161 ^ 2 + 26 / (10 * 12366)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((516217041 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((115867 / 31250000)) ^ 2) * ((1669794757 / 1000000000000000000000000)) + ((1268182119 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12366) : ℝ)) (√(26 / (10 * 12366) : ℝ)) d.D d.V d.P (√(tA 12366) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((115867 / 31250000)) * (((2272041023 / 1000000000000000)) * ((20431561107 / 500000000000000000))) + ((1268182119 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12366) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((516217041 / 100000000000000000000) : ℝ) + ((1268182119 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12366

namespace BstLean.Part266.Row12366
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12366 161 ∧
    0 ≤ (tableEnvelope C).f1 12366 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12366 161 ∧
    0 ≤ (tableEnvelope C).w1 12366 161 ∧ 0 ≤ (tableEnvelope C).w2 12366 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12366 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12366 161 ∧ 0 ≤ d.f1 12366 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12366 161 ∧ 0 ≤ d.w1 12366 161 ∧ 0 ≤ d.w2 12366 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12366 ≤ 2 * (228 / 100 : ℝ) / 12366 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12366 ≤ 2 * (370 / 100 : ℝ) / 12366 := by
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
    (completeRAData (tableEnvelope C) 12366 161).locationBound 12366 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12366 161).energyBound 12366 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12366 161) (d.f1 12366 161) d.f2 ≤
      32 * (((979692571 / 200000000000000000) : ℝ) + (817105037 / 500000000000000000) + (49097867 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12366 161) (d.w1 12366 161)
      (d.w2 12366 161) ≤
      32 * (((496449493 / 25000000000000000000) : ℝ) + (1412857251 / 100000000000000000000) + (32263949 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12366 161) (d.f1 12366 161) d.f2 ≤
      ((979692571 / 200000000000000000) : ℝ) ^ 2 + 2 * ((979692571 / 200000000000000000)) * ((817105037 / 500000000000000000)) * (126 / 100) +
      2 * (((817105037 / 500000000000000000)) ^ 2 + 2 * ((979692571 / 200000000000000000)) * ((49097867 / 125000000000000000))) +
      6 * ((817105037 / 500000000000000000)) * ((49097867 / 125000000000000000)) * (126 / 100) + 8 * ((49097867 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12366 161) (d.f1 12366 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12366 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12366 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12366 161) (d.f1 12366 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12366 161) (d.w1 12366 161) (d.w2 12366 161)
  have hwexpr0 : 0 ≤ d.w0 12366 161 + d.w1 12366 161 * √(π / 2) +
      2 * d.w2 12366 161 + energyR16 12366 *
      radiusPolynomialRoot16 (d.w0 12366 161) (d.w1 12366 161) (d.w2 12366 161) := by
    positivity
  constructor
  · change (12366 : ℝ) ^ 8 * (mA 12366 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12366 161) (d.f1 12366 161) d.f2 + locationR16 12366 *
        radiusPolynomialRoot16 (d.f0 12366 161) (d.f1 12366 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12366 : ℝ) ^ 8 * (mA 12366 : ℝ) ^ 8 *
        ((((979692571 / 200000000000000000) : ℝ) ^ 2 + 2 * ((979692571 / 200000000000000000)) * ((817105037 / 500000000000000000)) * (126 / 100) +
          2 * (((817105037 / 500000000000000000)) ^ 2 + 2 * ((979692571 / 200000000000000000)) * ((49097867 / 125000000000000000))) +
          6 * ((817105037 / 500000000000000000)) * ((49097867 / 125000000000000000)) * (126 / 100) + 8 * ((49097867 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12366) *
          (32 * (((979692571 / 200000000000000000) : ℝ) + (817105037 / 500000000000000000) + (49097867 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12366 : ℝ) ^ 16 *
      (d.w0 12366 161 + d.w1 12366 161 * √(π / 2) + 2 * d.w2 12366 161 +
        energyR16 12366 * radiusPolynomialRoot16 (d.w0 12366 161) (d.w1 12366 161)
          (d.w2 12366 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12366 : ℝ) ^ 16 *
        (((496449493 / 25000000000000000000) : ℝ) + ((1412857251 / 100000000000000000000)) * (126 / 100) + 2 * ((32263949 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12366) *
          (32 * (((496449493 / 25000000000000000000) : ℝ) + (1412857251 / 100000000000000000000) + (32263949 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12366

/-! A coarse bound on the actual paper statistics constant at dimension 12367. -/
namespace BstLean.Part266.Row12367
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12365 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12365 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12365 128 ≤ (12619 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12619 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12367) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12367 : ℕ))
    (by norm_num : (12367 : ℕ) ≤ 16384)
  have ht : paperTail256 12367 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12367 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12367 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12367 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12367 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12367 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12365 128 * √(2 / (12367 : ℝ)) *
      (√(12367 : ℝ) + paperT0 12367 + paperTail256 12367) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12367 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12367 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12367 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12365 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12365 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12367 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12367

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12367
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12367 (61 / 100) 161 (17 / (100 * 12367)) (26 / (10 * 12367)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12367 (61 / 100) 161 (17 / (100 * 12367)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (25804591 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (5216421 / 3125000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6336768839 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12367 / 12367 * (61 / 100)) ^ 4 * inverseRadius8 (12367 - 1) /
            envelopeGap 12367 (61 / 100) 161 (17 / (100 * 12367)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12367

namespace BstLean.Part266.Row12367
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12367 161 ≤ (195898919 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12367 161 ≤ (1633879797 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (49087943 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12367 161 ≤ (1985316341 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12367 161 ≤ (706257281 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12367 161 ≤ (516097959 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (25804591 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (25804591 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (5216421 / 3125000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6336768839 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1853797 / 500000000) : ℝ) ≤ √(17 / (100 * 12367) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12367) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2271765437 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20428256901 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12367) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12367) ≤ (11435381 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12367) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12367 * (161 : ℝ) ^ 2 + 26 / (10 * 12367) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12367) : ℝ)) (tA 12367 * 161 ^ 2 + 26 / (10 * 12367)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1853797 / 500000000))) * ((25804591 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1853797 / 500000000)) ^ 3) * ((5216421 / 3125000000000000000000))) + ((6336768839 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1853797 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12367) : ℝ)) d.D d.V d.P (√(tA 12367) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1853797 / 500000000)) ^ 2 * (((2271765437 / 1000000000000000)) * ((20428256901 / 500000000000000000)))) + ((6336768839 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12367) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1853797 / 500000000)) * ((25804591 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12367) : ℝ)) (tA 12367 * 161 ^ 2 + 26 / (10 * 12367)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((25804591 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1853797 / 500000000)) ^ 2) * ((5216421 / 3125000000000000000000)) + ((6336768839 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12367) : ℝ)) (√(26 / (10 * 12367) : ℝ)) d.D d.V d.P (√(tA 12367) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1853797 / 500000000)) * (((2271765437 / 1000000000000000)) * ((20428256901 / 500000000000000000))) + ((6336768839 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12367) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((25804591 / 5000000000000000000) : ℝ) + ((6336768839 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12367

namespace BstLean.Part266.Row12367
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12367 161 ∧
    0 ≤ (tableEnvelope C).f1 12367 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12367 161 ∧
    0 ≤ (tableEnvelope C).w1 12367 161 ∧ 0 ≤ (tableEnvelope C).w2 12367 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12367 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12367 161 ∧ 0 ≤ d.f1 12367 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12367 161 ∧ 0 ≤ d.w1 12367 161 ∧ 0 ≤ d.w2 12367 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12367 ≤ 2 * (228 / 100 : ℝ) / 12367 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12367 ≤ 2 * (370 / 100 : ℝ) / 12367 := by
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
    (completeRAData (tableEnvelope C) 12367 161).locationBound 12367 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12367 161).energyBound 12367 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12367 161) (d.f1 12367 161) d.f2 ≤
      32 * (((195898919 / 40000000000000000) : ℝ) + (1633879797 / 1000000000000000000) + (49087943 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12367 161) (d.w1 12367 161)
      (d.w2 12367 161) ≤
      32 * (((1985316341 / 100000000000000000000) : ℝ) + (706257281 / 50000000000000000000) + (516097959 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12367 161) (d.f1 12367 161) d.f2 ≤
      ((195898919 / 40000000000000000) : ℝ) ^ 2 + 2 * ((195898919 / 40000000000000000)) * ((1633879797 / 1000000000000000000)) * (126 / 100) +
      2 * (((1633879797 / 1000000000000000000)) ^ 2 + 2 * ((195898919 / 40000000000000000)) * ((49087943 / 125000000000000000))) +
      6 * ((1633879797 / 1000000000000000000)) * ((49087943 / 125000000000000000)) * (126 / 100) + 8 * ((49087943 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12367 161) (d.f1 12367 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12367 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12367 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12367 161) (d.f1 12367 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12367 161) (d.w1 12367 161) (d.w2 12367 161)
  have hwexpr0 : 0 ≤ d.w0 12367 161 + d.w1 12367 161 * √(π / 2) +
      2 * d.w2 12367 161 + energyR16 12367 *
      radiusPolynomialRoot16 (d.w0 12367 161) (d.w1 12367 161) (d.w2 12367 161) := by
    positivity
  constructor
  · change (12367 : ℝ) ^ 8 * (mA 12367 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12367 161) (d.f1 12367 161) d.f2 + locationR16 12367 *
        radiusPolynomialRoot16 (d.f0 12367 161) (d.f1 12367 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12367 : ℝ) ^ 8 * (mA 12367 : ℝ) ^ 8 *
        ((((195898919 / 40000000000000000) : ℝ) ^ 2 + 2 * ((195898919 / 40000000000000000)) * ((1633879797 / 1000000000000000000)) * (126 / 100) +
          2 * (((1633879797 / 1000000000000000000)) ^ 2 + 2 * ((195898919 / 40000000000000000)) * ((49087943 / 125000000000000000))) +
          6 * ((1633879797 / 1000000000000000000)) * ((49087943 / 125000000000000000)) * (126 / 100) + 8 * ((49087943 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12367) *
          (32 * (((195898919 / 40000000000000000) : ℝ) + (1633879797 / 1000000000000000000) + (49087943 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12367 : ℝ) ^ 16 *
      (d.w0 12367 161 + d.w1 12367 161 * √(π / 2) + 2 * d.w2 12367 161 +
        energyR16 12367 * radiusPolynomialRoot16 (d.w0 12367 161) (d.w1 12367 161)
          (d.w2 12367 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12367 : ℝ) ^ 16 *
        (((1985316341 / 100000000000000000000) : ℝ) + ((706257281 / 50000000000000000000)) * (126 / 100) + 2 * ((516097959 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12367) *
          (32 * (((1985316341 / 100000000000000000000) : ℝ) + (706257281 / 50000000000000000000) + (516097959 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12367

/-! A coarse bound on the actual paper statistics constant at dimension 12368. -/
namespace BstLean.Part266.Row12368
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12366 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12366 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12366 128 ≤ (12620 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12620 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12368) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12368 : ℕ))
    (by norm_num : (12368 : ℕ) ≤ 16384)
  have ht : paperTail256 12368 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12368 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12368 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12368 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12368 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12368 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12366 128 * √(2 / (12368 : ℝ)) *
      (√(12368 : ℝ) + paperT0 12368 + paperTail256 12368) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12368 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12368 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12368 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12366 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12366 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12368 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12368

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12368
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12368 (61 / 100) 161 (17 / (100 * 12368)) (26 / (10 * 12368)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12368 (61 / 100) 161 (17 / (100 * 12368)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (6449583 / 1250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1668714901 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6332630129 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12368 / 12368 * (61 / 100)) ^ 4 * inverseRadius8 (12368 - 1) /
            envelopeGap 12368 (61 / 100) 161 (17 / (100 * 12368)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12368

namespace BstLean.Part266.Row12368
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12368 161 ≤ (489647963 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12368 161 ≤ (1633548749 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (392624071 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12368 161 ≤ (248104261 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12368 161 ≤ (353042903 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12368 161 ≤ (20638911 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (6449583 / 1250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (6449583 / 1250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1668714901 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6332630129 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741489 / 200000000) : ℝ) ≤ √(17 / (100 * 12368) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12368) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (567872477 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40849906989 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12368) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12368) ≤ (28586141 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12368) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12368 * (161 : ℝ) ^ 2 + 26 / (10 * 12368) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12368) : ℝ)) (tA 12368 * 161 ^ 2 + 26 / (10 * 12368)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741489 / 200000000))) * ((6449583 / 1250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741489 / 200000000)) ^ 3) * ((1668714901 / 1000000000000000000000000))) + ((6332630129 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741489 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12368) : ℝ)) d.D d.V d.P (√(tA 12368) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741489 / 200000000)) ^ 2 * (((567872477 / 250000000000000)) * ((40849906989 / 1000000000000000000)))) + ((6332630129 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12368) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741489 / 200000000)) * ((6449583 / 1250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12368) : ℝ)) (tA 12368 * 161 ^ 2 + 26 / (10 * 12368)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((6449583 / 1250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741489 / 200000000)) ^ 2) * ((1668714901 / 1000000000000000000000000)) + ((6332630129 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12368) : ℝ)) (√(26 / (10 * 12368) : ℝ)) d.D d.V d.P (√(tA 12368) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741489 / 200000000)) * (((567872477 / 250000000000000)) * ((40849906989 / 1000000000000000000))) + ((6332630129 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12368) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((6449583 / 1250000000000000000) : ℝ) + ((6332630129 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12368

namespace BstLean.Part266.Row12368
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12368 161 ∧
    0 ≤ (tableEnvelope C).f1 12368 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12368 161 ∧
    0 ≤ (tableEnvelope C).w1 12368 161 ∧ 0 ≤ (tableEnvelope C).w2 12368 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12368 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12368 161 ∧ 0 ≤ d.f1 12368 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12368 161 ∧ 0 ≤ d.w1 12368 161 ∧ 0 ≤ d.w2 12368 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12368 ≤ 2 * (228 / 100 : ℝ) / 12368 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12368 ≤ 2 * (370 / 100 : ℝ) / 12368 := by
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
    (completeRAData (tableEnvelope C) 12368 161).locationBound 12368 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12368 161).energyBound 12368 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12368 161) (d.f1 12368 161) d.f2 ≤
      32 * (((489647963 / 100000000000000000) : ℝ) + (1633548749 / 1000000000000000000) + (392624071 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12368 161) (d.w1 12368 161)
      (d.w2 12368 161) ≤
      32 * (((248104261 / 12500000000000000000) : ℝ) + (353042903 / 25000000000000000000) + (20638911 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12368 161) (d.f1 12368 161) d.f2 ≤
      ((489647963 / 100000000000000000) : ℝ) ^ 2 + 2 * ((489647963 / 100000000000000000)) * ((1633548749 / 1000000000000000000)) * (126 / 100) +
      2 * (((1633548749 / 1000000000000000000)) ^ 2 + 2 * ((489647963 / 100000000000000000)) * ((392624071 / 1000000000000000000))) +
      6 * ((1633548749 / 1000000000000000000)) * ((392624071 / 1000000000000000000)) * (126 / 100) + 8 * ((392624071 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12368 161) (d.f1 12368 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12368 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12368 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12368 161) (d.f1 12368 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12368 161) (d.w1 12368 161) (d.w2 12368 161)
  have hwexpr0 : 0 ≤ d.w0 12368 161 + d.w1 12368 161 * √(π / 2) +
      2 * d.w2 12368 161 + energyR16 12368 *
      radiusPolynomialRoot16 (d.w0 12368 161) (d.w1 12368 161) (d.w2 12368 161) := by
    positivity
  constructor
  · change (12368 : ℝ) ^ 8 * (mA 12368 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12368 161) (d.f1 12368 161) d.f2 + locationR16 12368 *
        radiusPolynomialRoot16 (d.f0 12368 161) (d.f1 12368 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12368 : ℝ) ^ 8 * (mA 12368 : ℝ) ^ 8 *
        ((((489647963 / 100000000000000000) : ℝ) ^ 2 + 2 * ((489647963 / 100000000000000000)) * ((1633548749 / 1000000000000000000)) * (126 / 100) +
          2 * (((1633548749 / 1000000000000000000)) ^ 2 + 2 * ((489647963 / 100000000000000000)) * ((392624071 / 1000000000000000000))) +
          6 * ((1633548749 / 1000000000000000000)) * ((392624071 / 1000000000000000000)) * (126 / 100) + 8 * ((392624071 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12368) *
          (32 * (((489647963 / 100000000000000000) : ℝ) + (1633548749 / 1000000000000000000) + (392624071 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12368 : ℝ) ^ 16 *
      (d.w0 12368 161 + d.w1 12368 161 * √(π / 2) + 2 * d.w2 12368 161 +
        energyR16 12368 * radiusPolynomialRoot16 (d.w0 12368 161) (d.w1 12368 161)
          (d.w2 12368 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12368 : ℝ) ^ 16 *
        (((248104261 / 12500000000000000000) : ℝ) + ((353042903 / 25000000000000000000)) * (126 / 100) + 2 * ((20638911 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12368) *
          (32 * (((248104261 / 12500000000000000000) : ℝ) + (353042903 / 25000000000000000000) + (20638911 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12368

/-! A coarse bound on the actual paper statistics constant at dimension 12369. -/
namespace BstLean.Part266.Row12369
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12367 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12367 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12367 128 ≤ (12621 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12621 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12369) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12369 : ℕ))
    (by norm_num : (12369 : ℕ) ≤ 16384)
  have ht : paperTail256 12369 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12369 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12369 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12369 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12369 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12369 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12367 128 * √(2 / (12369 : ℝ)) *
      (√(12369 : ℝ) + paperT0 12369 + paperTail256 12369) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12369 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12369 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12369 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12367 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12367 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12369 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12369

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12369
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12369 (61 / 100) 161 (17 / (100 * 12369)) (26 / (10 * 12369)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12369 (61 / 100) 161 (17 / (100 * 12369)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1031683 / 200000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1668175301 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (49441363 / 7812500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12369 / 12369 * (61 / 100)) ^ 4 * inverseRadius8 (12369 - 1) /
            envelopeGap 12369 (61 / 100) 161 (17 / (100 * 12369)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12369

namespace BstLean.Part266.Row12369
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12369 161 ≤ (97909809 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12369 161 ≤ (1633218691 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (49068091 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12369 161 ≤ (1984352797 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12369 161 ≤ (1411829159 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12369 161 ≤ (515847631 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1031683 / 200000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1031683 / 200000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1668175301 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (49441363 / 7812500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741459 / 200000000) : ℝ) ≤ √(17 / (100 * 12369) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12369) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2271214433 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40843301789 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12369) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12369) ≤ (2858383 / 25000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12369) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12369 * (161 : ℝ) ^ 2 + 26 / (10 * 12369) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12369) : ℝ)) (tA 12369 * 161 ^ 2 + 26 / (10 * 12369)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741459 / 200000000))) * ((1031683 / 200000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741459 / 200000000)) ^ 3) * ((1668175301 / 1000000000000000000000000))) + ((49441363 / 7812500000000000000000)) * (3 / 2 * (39895 / 100000) / ((741459 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12369) : ℝ)) d.D d.V d.P (√(tA 12369) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741459 / 200000000)) ^ 2 * (((2271214433 / 1000000000000000)) * ((40843301789 / 1000000000000000000)))) + ((49441363 / 7812500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12369) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741459 / 200000000)) * ((1031683 / 200000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12369) : ℝ)) (tA 12369 * 161 ^ 2 + 26 / (10 * 12369)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1031683 / 200000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741459 / 200000000)) ^ 2) * ((1668175301 / 1000000000000000000000000)) + ((49441363 / 7812500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12369) : ℝ)) (√(26 / (10 * 12369) : ℝ)) d.D d.V d.P (√(tA 12369) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741459 / 200000000)) * (((2271214433 / 1000000000000000)) * ((40843301789 / 1000000000000000000))) + ((49441363 / 7812500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12369) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((1031683 / 200000000000000000) : ℝ) + ((49441363 / 7812500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12369

namespace BstLean.Part266.Row12369
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12369 161 ∧
    0 ≤ (tableEnvelope C).f1 12369 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12369 161 ∧
    0 ≤ (tableEnvelope C).w1 12369 161 ∧ 0 ≤ (tableEnvelope C).w2 12369 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12369 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12369 161 ∧ 0 ≤ d.f1 12369 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12369 161 ∧ 0 ≤ d.w1 12369 161 ∧ 0 ≤ d.w2 12369 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12369 ≤ 2 * (228 / 100 : ℝ) / 12369 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12369 ≤ 2 * (370 / 100 : ℝ) / 12369 := by
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
    (completeRAData (tableEnvelope C) 12369 161).locationBound 12369 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12369 161).energyBound 12369 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12369 161) (d.f1 12369 161) d.f2 ≤
      32 * (((97909809 / 20000000000000000) : ℝ) + (1633218691 / 1000000000000000000) + (49068091 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12369 161) (d.w1 12369 161)
      (d.w2 12369 161) ≤
      32 * (((1984352797 / 100000000000000000000) : ℝ) + (1411829159 / 100000000000000000000) + (515847631 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12369 161) (d.f1 12369 161) d.f2 ≤
      ((97909809 / 20000000000000000) : ℝ) ^ 2 + 2 * ((97909809 / 20000000000000000)) * ((1633218691 / 1000000000000000000)) * (126 / 100) +
      2 * (((1633218691 / 1000000000000000000)) ^ 2 + 2 * ((97909809 / 20000000000000000)) * ((49068091 / 125000000000000000))) +
      6 * ((1633218691 / 1000000000000000000)) * ((49068091 / 125000000000000000)) * (126 / 100) + 8 * ((49068091 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12369 161) (d.f1 12369 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12369 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12369 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12369 161) (d.f1 12369 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12369 161) (d.w1 12369 161) (d.w2 12369 161)
  have hwexpr0 : 0 ≤ d.w0 12369 161 + d.w1 12369 161 * √(π / 2) +
      2 * d.w2 12369 161 + energyR16 12369 *
      radiusPolynomialRoot16 (d.w0 12369 161) (d.w1 12369 161) (d.w2 12369 161) := by
    positivity
  constructor
  · change (12369 : ℝ) ^ 8 * (mA 12369 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12369 161) (d.f1 12369 161) d.f2 + locationR16 12369 *
        radiusPolynomialRoot16 (d.f0 12369 161) (d.f1 12369 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12369 : ℝ) ^ 8 * (mA 12369 : ℝ) ^ 8 *
        ((((97909809 / 20000000000000000) : ℝ) ^ 2 + 2 * ((97909809 / 20000000000000000)) * ((1633218691 / 1000000000000000000)) * (126 / 100) +
          2 * (((1633218691 / 1000000000000000000)) ^ 2 + 2 * ((97909809 / 20000000000000000)) * ((49068091 / 125000000000000000))) +
          6 * ((1633218691 / 1000000000000000000)) * ((49068091 / 125000000000000000)) * (126 / 100) + 8 * ((49068091 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12369) *
          (32 * (((97909809 / 20000000000000000) : ℝ) + (1633218691 / 1000000000000000000) + (49068091 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12369 : ℝ) ^ 16 *
      (d.w0 12369 161 + d.w1 12369 161 * √(π / 2) + 2 * d.w2 12369 161 +
        energyR16 12369 * radiusPolynomialRoot16 (d.w0 12369 161) (d.w1 12369 161)
          (d.w2 12369 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12369 : ℝ) ^ 16 *
        (((1984352797 / 100000000000000000000) : ℝ) + ((1411829159 / 100000000000000000000)) * (126 / 100) + 2 * ((515847631 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12369) *
          (32 * (((1984352797 / 100000000000000000000) : ℝ) + (1411829159 / 100000000000000000000) + (515847631 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12369

/-! A coarse bound on the actual paper statistics constant at dimension 12370. -/
namespace BstLean.Part266.Row12370
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12368 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12368 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12368 128 ≤ (12622 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12622 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12370) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12370 : ℕ))
    (by norm_num : (12370 : ℕ) ≤ 16384)
  have ht : paperTail256 12370 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12370 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12370 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12370 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12370 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12370 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12368 128 * √(2 / (12370 : ℝ)) *
      (√(12370 : ℝ) + paperT0 12370 + paperTail256 12370) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12370 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12370 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12370 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12368 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12368 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12370 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12370

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12370
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12370 (61 / 100) 161 (17 / (100 * 12370)) (26 / (10 * 12370)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12370 (61 / 100) 161 (17 / (100 * 12370)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1289291 / 250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (833817959 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6324361839 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12370 / 12370 * (61 / 100)) ^ 4 * inverseRadius8 (12370 - 1) /
            envelopeGap 12370 (61 / 100) 161 (17 / (100 * 12370)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12370

namespace BstLean.Part266.Row12370
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12370 161 ≤ (305906351 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12370 161 ≤ (1632888741 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (392465409 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12370 161 ≤ (495967919 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12370 161 ≤ (1411486823 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12370 161 ≤ (515722527 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1289291 / 250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1289291 / 250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (833817959 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6324361839 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741429 / 200000000) : ℝ) ≤ √(17 / (100 * 12370) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12370) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2270939013 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20418349089 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12370) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12370) ≤ (114326077 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12370) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12370 * (161 : ℝ) ^ 2 + 26 / (10 * 12370) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12370) : ℝ)) (tA 12370 * 161 ^ 2 + 26 / (10 * 12370)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741429 / 200000000))) * ((1289291 / 250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741429 / 200000000)) ^ 3) * ((833817959 / 500000000000000000000000))) + ((6324361839 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741429 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12370) : ℝ)) d.D d.V d.P (√(tA 12370) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741429 / 200000000)) ^ 2 * (((2270939013 / 1000000000000000)) * ((20418349089 / 500000000000000000)))) + ((6324361839 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12370) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741429 / 200000000)) * ((1289291 / 250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12370) : ℝ)) (tA 12370 * 161 ^ 2 + 26 / (10 * 12370)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1289291 / 250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741429 / 200000000)) ^ 2) * ((833817959 / 500000000000000000000000)) + ((6324361839 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12370) : ℝ)) (√(26 / (10 * 12370) : ℝ)) d.D d.V d.P (√(tA 12370) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741429 / 200000000)) * (((2270939013 / 1000000000000000)) * ((20418349089 / 500000000000000000))) + ((6324361839 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12370) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((1289291 / 250000000000000000) : ℝ) + ((6324361839 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12370

namespace BstLean.Part266.Row12370
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12370 161 ∧
    0 ≤ (tableEnvelope C).f1 12370 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12370 161 ∧
    0 ≤ (tableEnvelope C).w1 12370 161 ∧ 0 ≤ (tableEnvelope C).w2 12370 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12370 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12370 161 ∧ 0 ≤ d.f1 12370 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12370 161 ∧ 0 ≤ d.w1 12370 161 ∧ 0 ≤ d.w2 12370 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12370 ≤ 2 * (228 / 100 : ℝ) / 12370 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12370 ≤ 2 * (370 / 100 : ℝ) / 12370 := by
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
    (completeRAData (tableEnvelope C) 12370 161).locationBound 12370 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12370 161).energyBound 12370 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12370 161) (d.f1 12370 161) d.f2 ≤
      32 * (((305906351 / 62500000000000000) : ℝ) + (1632888741 / 1000000000000000000) + (392465409 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12370 161) (d.w1 12370 161)
      (d.w2 12370 161) ≤
      32 * (((495967919 / 25000000000000000000) : ℝ) + (1411486823 / 100000000000000000000) + (515722527 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12370 161) (d.f1 12370 161) d.f2 ≤
      ((305906351 / 62500000000000000) : ℝ) ^ 2 + 2 * ((305906351 / 62500000000000000)) * ((1632888741 / 1000000000000000000)) * (126 / 100) +
      2 * (((1632888741 / 1000000000000000000)) ^ 2 + 2 * ((305906351 / 62500000000000000)) * ((392465409 / 1000000000000000000))) +
      6 * ((1632888741 / 1000000000000000000)) * ((392465409 / 1000000000000000000)) * (126 / 100) + 8 * ((392465409 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12370 161) (d.f1 12370 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12370 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12370 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12370 161) (d.f1 12370 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12370 161) (d.w1 12370 161) (d.w2 12370 161)
  have hwexpr0 : 0 ≤ d.w0 12370 161 + d.w1 12370 161 * √(π / 2) +
      2 * d.w2 12370 161 + energyR16 12370 *
      radiusPolynomialRoot16 (d.w0 12370 161) (d.w1 12370 161) (d.w2 12370 161) := by
    positivity
  constructor
  · change (12370 : ℝ) ^ 8 * (mA 12370 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12370 161) (d.f1 12370 161) d.f2 + locationR16 12370 *
        radiusPolynomialRoot16 (d.f0 12370 161) (d.f1 12370 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12370 : ℝ) ^ 8 * (mA 12370 : ℝ) ^ 8 *
        ((((305906351 / 62500000000000000) : ℝ) ^ 2 + 2 * ((305906351 / 62500000000000000)) * ((1632888741 / 1000000000000000000)) * (126 / 100) +
          2 * (((1632888741 / 1000000000000000000)) ^ 2 + 2 * ((305906351 / 62500000000000000)) * ((392465409 / 1000000000000000000))) +
          6 * ((1632888741 / 1000000000000000000)) * ((392465409 / 1000000000000000000)) * (126 / 100) + 8 * ((392465409 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12370) *
          (32 * (((305906351 / 62500000000000000) : ℝ) + (1632888741 / 1000000000000000000) + (392465409 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12370 : ℝ) ^ 16 *
      (d.w0 12370 161 + d.w1 12370 161 * √(π / 2) + 2 * d.w2 12370 161 +
        energyR16 12370 * radiusPolynomialRoot16 (d.w0 12370 161) (d.w1 12370 161)
          (d.w2 12370 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12370 : ℝ) ^ 16 *
        (((495967919 / 25000000000000000000) : ℝ) + ((1411486823 / 100000000000000000000)) * (126 / 100) + 2 * ((515722527 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12370) *
          (32 * (((495967919 / 25000000000000000000) : ℝ) + (1411486823 / 100000000000000000000) + (515722527 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12370

/-! A coarse bound on the actual paper statistics constant at dimension 12371. -/
namespace BstLean.Part266.Row12371
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12369 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12369 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12369 128 ≤ (12623 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12623 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12371) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12371 : ℕ))
    (by norm_num : (12371 : ℕ) ≤ 16384)
  have ht : paperTail256 12371 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12371 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12371 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12371 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12371 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12371 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12369 128 * √(2 / (12371 : ℝ)) *
      (√(12371 : ℝ) + paperT0 12371 + paperTail256 12371) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12371 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12371 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12371 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12369 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12369 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12371 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12371

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12371
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12371 (61 / 100) 161 (17 / (100 * 12371)) (26 / (10 * 12371)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12371 (61 / 100) 161 (17 / (100 * 12371)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (515591341 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (833548377 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3160116127 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12371 / 12371 * (61 / 100)) ^ 4 * inverseRadius8 (12371 - 1) /
            envelopeGap 12371 (61 / 100) 161 (17 / (100 * 12371)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12371

namespace BstLean.Part266.Row12371
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12371 161 ≤ (2446756567 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12371 161 ≤ (816279451 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (78477223 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12371 161 ≤ (79335629 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12371 161 ≤ (705572303 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12371 161 ≤ (64449683 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (515591341 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (515591341 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (833548377 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3160116127 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741399 / 200000000) : ℝ) ≤ √(17 / (100 * 12371) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12371) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (45413273 / 20000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2041504809 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12371) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12371) ≤ (22863367 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12371) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12371 * (161 : ℝ) ^ 2 + 26 / (10 * 12371) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12371) : ℝ)) (tA 12371 * 161 ^ 2 + 26 / (10 * 12371)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741399 / 200000000))) * ((515591341 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741399 / 200000000)) ^ 3) * ((833548377 / 500000000000000000000000))) + ((3160116127 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741399 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12371) : ℝ)) d.D d.V d.P (√(tA 12371) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741399 / 200000000)) ^ 2 * (((45413273 / 20000000000000)) * ((2041504809 / 50000000000000000)))) + ((3160116127 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12371) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741399 / 200000000)) * ((515591341 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12371) : ℝ)) (tA 12371 * 161 ^ 2 + 26 / (10 * 12371)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((515591341 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741399 / 200000000)) ^ 2) * ((833548377 / 500000000000000000000000)) + ((3160116127 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12371) : ℝ)) (√(26 / (10 * 12371) : ℝ)) d.D d.V d.P (√(tA 12371) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741399 / 200000000)) * (((45413273 / 20000000000000)) * ((2041504809 / 50000000000000000))) + ((3160116127 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12371) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((515591341 / 100000000000000000000) : ℝ) + ((3160116127 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12371

namespace BstLean.Part266.Row12371
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12371 161 ∧
    0 ≤ (tableEnvelope C).f1 12371 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12371 161 ∧
    0 ≤ (tableEnvelope C).w1 12371 161 ∧ 0 ≤ (tableEnvelope C).w2 12371 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12371 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12371 161 ∧ 0 ≤ d.f1 12371 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12371 161 ∧ 0 ≤ d.w1 12371 161 ∧ 0 ≤ d.w2 12371 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12371 ≤ 2 * (228 / 100 : ℝ) / 12371 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12371 ≤ 2 * (370 / 100 : ℝ) / 12371 := by
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
    (completeRAData (tableEnvelope C) 12371 161).locationBound 12371 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12371 161).energyBound 12371 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12371 161) (d.f1 12371 161) d.f2 ≤
      32 * (((2446756567 / 500000000000000000) : ℝ) + (816279451 / 500000000000000000) + (78477223 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12371 161) (d.w1 12371 161)
      (d.w2 12371 161) ≤
      32 * (((79335629 / 4000000000000000000) : ℝ) + (705572303 / 50000000000000000000) + (64449683 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12371 161) (d.f1 12371 161) d.f2 ≤
      ((2446756567 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2446756567 / 500000000000000000)) * ((816279451 / 500000000000000000)) * (126 / 100) +
      2 * (((816279451 / 500000000000000000)) ^ 2 + 2 * ((2446756567 / 500000000000000000)) * ((78477223 / 200000000000000000))) +
      6 * ((816279451 / 500000000000000000)) * ((78477223 / 200000000000000000)) * (126 / 100) + 8 * ((78477223 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12371 161) (d.f1 12371 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12371 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12371 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12371 161) (d.f1 12371 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12371 161) (d.w1 12371 161) (d.w2 12371 161)
  have hwexpr0 : 0 ≤ d.w0 12371 161 + d.w1 12371 161 * √(π / 2) +
      2 * d.w2 12371 161 + energyR16 12371 *
      radiusPolynomialRoot16 (d.w0 12371 161) (d.w1 12371 161) (d.w2 12371 161) := by
    positivity
  constructor
  · change (12371 : ℝ) ^ 8 * (mA 12371 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12371 161) (d.f1 12371 161) d.f2 + locationR16 12371 *
        radiusPolynomialRoot16 (d.f0 12371 161) (d.f1 12371 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12371 : ℝ) ^ 8 * (mA 12371 : ℝ) ^ 8 *
        ((((2446756567 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2446756567 / 500000000000000000)) * ((816279451 / 500000000000000000)) * (126 / 100) +
          2 * (((816279451 / 500000000000000000)) ^ 2 + 2 * ((2446756567 / 500000000000000000)) * ((78477223 / 200000000000000000))) +
          6 * ((816279451 / 500000000000000000)) * ((78477223 / 200000000000000000)) * (126 / 100) + 8 * ((78477223 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12371) *
          (32 * (((2446756567 / 500000000000000000) : ℝ) + (816279451 / 500000000000000000) + (78477223 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12371 : ℝ) ^ 16 *
      (d.w0 12371 161 + d.w1 12371 161 * √(π / 2) + 2 * d.w2 12371 161 +
        energyR16 12371 * radiusPolynomialRoot16 (d.w0 12371 161) (d.w1 12371 161)
          (d.w2 12371 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12371 : ℝ) ^ 16 *
        (((79335629 / 4000000000000000000) : ℝ) + ((705572303 / 50000000000000000000)) * (126 / 100) + 2 * ((64449683 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12371) *
          (32 * (((79335629 / 4000000000000000000) : ℝ) + (705572303 / 50000000000000000000) + (64449683 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12371

/-! A coarse bound on the actual paper statistics constant at dimension 12372. -/
namespace BstLean.Part266.Row12372
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12370 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12370 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12370 128 ≤ (12624 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12624 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12372) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12372 : ℕ))
    (by norm_num : (12372 : ℕ) ≤ 16384)
  have ht : paperTail256 12372 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12372 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12372 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12372 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12372 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12372 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12370 128 * √(2 / (12372 : ℝ)) *
      (√(12372 : ℝ) + paperT0 12372 + paperTail256 12372) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12372 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12372 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12372 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12370 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12370 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12372 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12372

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12372
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12372 (61 / 100) 161 (17 / (100 * 12372)) (26 / (10 * 12372)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12372 (61 / 100) 161 (17 / (100 * 12372)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (257733161 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1666557807 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3158052853 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12372 / 12372 * (61 / 100)) ^ 4 * inverseRadius8 (12372 - 1) /
            envelopeGap 12372 (61 / 100) 161 (17 / (100 * 12372)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12372

namespace BstLean.Part266.Row12372
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12372 161 ≤ (2446262499 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12372 161 ≤ (408057293 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (98076711 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12372 161 ≤ (1982909943 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12372 161 ≤ (705401253 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12372 161 ≤ (515472441 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (257733161 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (257733161 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1666557807 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3158052853 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741369 / 200000000) : ℝ) ≤ √(17 / (100 * 12372) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12372) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1135194171 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10205873943 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12372) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12372) ≤ (22861519 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12372) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12372 * (161 : ℝ) ^ 2 + 26 / (10 * 12372) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12372) : ℝ)) (tA 12372 * 161 ^ 2 + 26 / (10 * 12372)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741369 / 200000000))) * ((257733161 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741369 / 200000000)) ^ 3) * ((1666557807 / 1000000000000000000000000))) + ((3158052853 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741369 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12372) : ℝ)) d.D d.V d.P (√(tA 12372) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741369 / 200000000)) ^ 2 * (((1135194171 / 500000000000000)) * ((10205873943 / 250000000000000000)))) + ((3158052853 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12372) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741369 / 200000000)) * ((257733161 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12372) : ℝ)) (tA 12372 * 161 ^ 2 + 26 / (10 * 12372)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((257733161 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741369 / 200000000)) ^ 2) * ((1666557807 / 1000000000000000000000000)) + ((3158052853 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12372) : ℝ)) (√(26 / (10 * 12372) : ℝ)) d.D d.V d.P (√(tA 12372) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741369 / 200000000)) * (((1135194171 / 500000000000000)) * ((10205873943 / 250000000000000000))) + ((3158052853 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12372) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((257733161 / 50000000000000000000) : ℝ) + ((3158052853 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12372

namespace BstLean.Part266.Row12372
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12372 161 ∧
    0 ≤ (tableEnvelope C).f1 12372 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12372 161 ∧
    0 ≤ (tableEnvelope C).w1 12372 161 ∧ 0 ≤ (tableEnvelope C).w2 12372 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12372 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12372 161 ∧ 0 ≤ d.f1 12372 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12372 161 ∧ 0 ≤ d.w1 12372 161 ∧ 0 ≤ d.w2 12372 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12372 ≤ 2 * (228 / 100 : ℝ) / 12372 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12372 ≤ 2 * (370 / 100 : ℝ) / 12372 := by
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
    (completeRAData (tableEnvelope C) 12372 161).locationBound 12372 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12372 161).energyBound 12372 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12372 161) (d.f1 12372 161) d.f2 ≤
      32 * (((2446262499 / 500000000000000000) : ℝ) + (408057293 / 250000000000000000) + (98076711 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12372 161) (d.w1 12372 161)
      (d.w2 12372 161) ≤
      32 * (((1982909943 / 100000000000000000000) : ℝ) + (705401253 / 50000000000000000000) + (515472441 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12372 161) (d.f1 12372 161) d.f2 ≤
      ((2446262499 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2446262499 / 500000000000000000)) * ((408057293 / 250000000000000000)) * (126 / 100) +
      2 * (((408057293 / 250000000000000000)) ^ 2 + 2 * ((2446262499 / 500000000000000000)) * ((98076711 / 250000000000000000))) +
      6 * ((408057293 / 250000000000000000)) * ((98076711 / 250000000000000000)) * (126 / 100) + 8 * ((98076711 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12372 161) (d.f1 12372 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12372 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12372 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12372 161) (d.f1 12372 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12372 161) (d.w1 12372 161) (d.w2 12372 161)
  have hwexpr0 : 0 ≤ d.w0 12372 161 + d.w1 12372 161 * √(π / 2) +
      2 * d.w2 12372 161 + energyR16 12372 *
      radiusPolynomialRoot16 (d.w0 12372 161) (d.w1 12372 161) (d.w2 12372 161) := by
    positivity
  constructor
  · change (12372 : ℝ) ^ 8 * (mA 12372 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12372 161) (d.f1 12372 161) d.f2 + locationR16 12372 *
        radiusPolynomialRoot16 (d.f0 12372 161) (d.f1 12372 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12372 : ℝ) ^ 8 * (mA 12372 : ℝ) ^ 8 *
        ((((2446262499 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2446262499 / 500000000000000000)) * ((408057293 / 250000000000000000)) * (126 / 100) +
          2 * (((408057293 / 250000000000000000)) ^ 2 + 2 * ((2446262499 / 500000000000000000)) * ((98076711 / 250000000000000000))) +
          6 * ((408057293 / 250000000000000000)) * ((98076711 / 250000000000000000)) * (126 / 100) + 8 * ((98076711 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12372) *
          (32 * (((2446262499 / 500000000000000000) : ℝ) + (408057293 / 250000000000000000) + (98076711 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12372 : ℝ) ^ 16 *
      (d.w0 12372 161 + d.w1 12372 161 * √(π / 2) + 2 * d.w2 12372 161 +
        energyR16 12372 * radiusPolynomialRoot16 (d.w0 12372 161) (d.w1 12372 161)
          (d.w2 12372 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12372 : ℝ) ^ 16 *
        (((1982909943 / 100000000000000000000) : ℝ) + ((705401253 / 50000000000000000000)) * (126 / 100) + 2 * ((515472441 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12372) *
          (32 * (((1982909943 / 100000000000000000000) : ℝ) + (705401253 / 50000000000000000000) + (515472441 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12372

/-! A coarse bound on the actual paper statistics constant at dimension 12373. -/
namespace BstLean.Part266.Row12373
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12371 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12371 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12371 128 ≤ (12625 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12625 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12373) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12373 : ℕ))
    (by norm_num : (12373 : ℕ) ≤ 16384)
  have ht : paperTail256 12373 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12373 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12373 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12373 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12373 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12373 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12371 128 * √(2 / (12373 : ℝ)) *
      (√(12373 : ℝ) + paperT0 12373 + paperTail256 12373) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12373 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12373 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12373 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12371 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12371 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12373 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12373

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12373
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12373 (61 / 100) 161 (17 / (100 * 12373)) (26 / (10 * 12373)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12373 (61 / 100) 161 (17 / (100 * 12373)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (16104417 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (833009539 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (6311982191 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12373 / 12373 * (61 / 100)) ^ 4 * inverseRadius8 (12373 - 1) /
            envelopeGap 12373 (61 / 100) 161 (17 / (100 * 12373)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12373

namespace BstLean.Part266.Row12373
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12373 161 ≤ (4891537211 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12373 161 ≤ (1631899551 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (392227599 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12373 161 ≤ (495607333 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12373 161 ≤ (1410460523 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12373 161 ≤ (515347459 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (16104417 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (16104417 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (833009539 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (6311982191 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((741339 / 200000000) : ℝ) ≤ √(17 / (100 * 12373) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12373) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (227011309 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40816896967 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12373) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12373) ≤ (114298357 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12373) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12373 * (161 : ℝ) ^ 2 + 26 / (10 * 12373) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12373) : ℝ)) (tA 12373 * 161 ^ 2 + 26 / (10 * 12373)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((741339 / 200000000))) * ((16104417 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((741339 / 200000000)) ^ 3) * ((833009539 / 500000000000000000000000))) + ((6311982191 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((741339 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12373) : ℝ)) d.D d.V d.P (√(tA 12373) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((741339 / 200000000)) ^ 2 * (((227011309 / 100000000000000)) * ((40816896967 / 1000000000000000000)))) + ((6311982191 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12373) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((741339 / 200000000)) * ((16104417 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12373) : ℝ)) (tA 12373 * 161 ^ 2 + 26 / (10 * 12373)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((16104417 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((741339 / 200000000)) ^ 2) * ((833009539 / 500000000000000000000000)) + ((6311982191 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12373) : ℝ)) (√(26 / (10 * 12373) : ℝ)) d.D d.V d.P (√(tA 12373) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((741339 / 200000000)) * (((227011309 / 100000000000000)) * ((40816896967 / 1000000000000000000))) + ((6311982191 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12373) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((16104417 / 3125000000000000000) : ℝ) + ((6311982191 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12373

namespace BstLean.Part266.Row12373
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12373 161 ∧
    0 ≤ (tableEnvelope C).f1 12373 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12373 161 ∧
    0 ≤ (tableEnvelope C).w1 12373 161 ∧ 0 ≤ (tableEnvelope C).w2 12373 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12373 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12373 161 ∧ 0 ≤ d.f1 12373 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12373 161 ∧ 0 ≤ d.w1 12373 161 ∧ 0 ≤ d.w2 12373 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12373 ≤ 2 * (228 / 100 : ℝ) / 12373 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12373 ≤ 2 * (370 / 100 : ℝ) / 12373 := by
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
    (completeRAData (tableEnvelope C) 12373 161).locationBound 12373 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12373 161).energyBound 12373 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12373 161) (d.f1 12373 161) d.f2 ≤
      32 * (((4891537211 / 1000000000000000000) : ℝ) + (1631899551 / 1000000000000000000) + (392227599 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12373 161) (d.w1 12373 161)
      (d.w2 12373 161) ≤
      32 * (((495607333 / 25000000000000000000) : ℝ) + (1410460523 / 100000000000000000000) + (515347459 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12373 161) (d.f1 12373 161) d.f2 ≤
      ((4891537211 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4891537211 / 1000000000000000000)) * ((1631899551 / 1000000000000000000)) * (126 / 100) +
      2 * (((1631899551 / 1000000000000000000)) ^ 2 + 2 * ((4891537211 / 1000000000000000000)) * ((392227599 / 1000000000000000000))) +
      6 * ((1631899551 / 1000000000000000000)) * ((392227599 / 1000000000000000000)) * (126 / 100) + 8 * ((392227599 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12373 161) (d.f1 12373 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12373 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12373 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12373 161) (d.f1 12373 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12373 161) (d.w1 12373 161) (d.w2 12373 161)
  have hwexpr0 : 0 ≤ d.w0 12373 161 + d.w1 12373 161 * √(π / 2) +
      2 * d.w2 12373 161 + energyR16 12373 *
      radiusPolynomialRoot16 (d.w0 12373 161) (d.w1 12373 161) (d.w2 12373 161) := by
    positivity
  constructor
  · change (12373 : ℝ) ^ 8 * (mA 12373 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12373 161) (d.f1 12373 161) d.f2 + locationR16 12373 *
        radiusPolynomialRoot16 (d.f0 12373 161) (d.f1 12373 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12373 : ℝ) ^ 8 * (mA 12373 : ℝ) ^ 8 *
        ((((4891537211 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4891537211 / 1000000000000000000)) * ((1631899551 / 1000000000000000000)) * (126 / 100) +
          2 * (((1631899551 / 1000000000000000000)) ^ 2 + 2 * ((4891537211 / 1000000000000000000)) * ((392227599 / 1000000000000000000))) +
          6 * ((1631899551 / 1000000000000000000)) * ((392227599 / 1000000000000000000)) * (126 / 100) + 8 * ((392227599 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12373) *
          (32 * (((4891537211 / 1000000000000000000) : ℝ) + (1631899551 / 1000000000000000000) + (392227599 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12373 : ℝ) ^ 16 *
      (d.w0 12373 161 + d.w1 12373 161 * √(π / 2) + 2 * d.w2 12373 161 +
        energyR16 12373 * radiusPolynomialRoot16 (d.w0 12373 161) (d.w1 12373 161)
          (d.w2 12373 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12373 : ℝ) ^ 16 *
        (((495607333 / 25000000000000000000) : ℝ) + ((1410460523 / 100000000000000000000)) * (126 / 100) + 2 * ((515347459 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12373) *
          (32 * (((495607333 / 25000000000000000000) : ℝ) + (1410460523 / 100000000000000000000) + (515347459 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12373

/-! A coarse bound on the actual paper statistics constant at dimension 12374. -/
namespace BstLean.Part266.Row12374
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12372 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12372 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12372 128 ≤ (12626 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12626 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12374) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12374 : ℕ))
    (by norm_num : (12374 : ℕ) ≤ 16384)
  have ht : paperTail256 12374 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12374 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12374 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12374 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12374 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12374 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12372 128 * √(2 / (12374 : ℝ)) *
      (√(12374 : ℝ) + paperT0 12374 + paperTail256 12374) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12374 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12374 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12374 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12372 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12372 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12374 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12374

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12374
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12374 (61 / 100) 161 (17 / (100 * 12374)) (26 / (10 * 12374)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12374 (61 / 100) 161 (17 / (100 * 12374)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (257608203 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1665480567 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1576965427 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12374 / 12374 * (61 / 100)) ^ 4 * inverseRadius8 (12374 - 1) /
            envelopeGap 12374 (61 / 100) 161 (17 / (100 * 12374)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12374

namespace BstLean.Part266.Row12374
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12374 161 ≤ (978109193 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12374 161 ≤ (1631569159 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (24509267 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12374 161 ≤ (1981948099 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12374 161 ≤ (705059139 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12374 161 ≤ (515222517 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (257608203 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (257608203 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1665480567 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1576965427 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1853273 / 500000000) : ℝ) ≤ √(17 / (100 * 12374) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12374) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2269837893 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40810299767 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12374) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12374) ≤ (714307 / 6250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12374) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12374 * (161 : ℝ) ^ 2 + 26 / (10 * 12374) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12374) : ℝ)) (tA 12374 * 161 ^ 2 + 26 / (10 * 12374)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1853273 / 500000000))) * ((257608203 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1853273 / 500000000)) ^ 3) * ((1665480567 / 1000000000000000000000000))) + ((1576965427 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1853273 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12374) : ℝ)) d.D d.V d.P (√(tA 12374) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1853273 / 500000000)) ^ 2 * (((2269837893 / 1000000000000000)) * ((40810299767 / 1000000000000000000)))) + ((1576965427 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12374) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1853273 / 500000000)) * ((257608203 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12374) : ℝ)) (tA 12374 * 161 ^ 2 + 26 / (10 * 12374)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((257608203 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1853273 / 500000000)) ^ 2) * ((1665480567 / 1000000000000000000000000)) + ((1576965427 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12374) : ℝ)) (√(26 / (10 * 12374) : ℝ)) d.D d.V d.P (√(tA 12374) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1853273 / 500000000)) * (((2269837893 / 1000000000000000)) * ((40810299767 / 1000000000000000000))) + ((1576965427 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12374) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((257608203 / 50000000000000000000) : ℝ) + ((1576965427 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12374

namespace BstLean.Part266.Row12374
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12374 161 ∧
    0 ≤ (tableEnvelope C).f1 12374 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12374 161 ∧
    0 ≤ (tableEnvelope C).w1 12374 161 ∧ 0 ≤ (tableEnvelope C).w2 12374 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12374 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12374 161 ∧ 0 ≤ d.f1 12374 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12374 161 ∧ 0 ≤ d.w1 12374 161 ∧ 0 ≤ d.w2 12374 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12374 ≤ 2 * (228 / 100 : ℝ) / 12374 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12374 ≤ 2 * (370 / 100 : ℝ) / 12374 := by
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
    (completeRAData (tableEnvelope C) 12374 161).locationBound 12374 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12374 161).energyBound 12374 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12374 161) (d.f1 12374 161) d.f2 ≤
      32 * (((978109193 / 200000000000000000) : ℝ) + (1631569159 / 1000000000000000000) + (24509267 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12374 161) (d.w1 12374 161)
      (d.w2 12374 161) ≤
      32 * (((1981948099 / 100000000000000000000) : ℝ) + (705059139 / 50000000000000000000) + (515222517 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12374 161) (d.f1 12374 161) d.f2 ≤
      ((978109193 / 200000000000000000) : ℝ) ^ 2 + 2 * ((978109193 / 200000000000000000)) * ((1631569159 / 1000000000000000000)) * (126 / 100) +
      2 * (((1631569159 / 1000000000000000000)) ^ 2 + 2 * ((978109193 / 200000000000000000)) * ((24509267 / 62500000000000000))) +
      6 * ((1631569159 / 1000000000000000000)) * ((24509267 / 62500000000000000)) * (126 / 100) + 8 * ((24509267 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12374 161) (d.f1 12374 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12374 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12374 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12374 161) (d.f1 12374 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12374 161) (d.w1 12374 161) (d.w2 12374 161)
  have hwexpr0 : 0 ≤ d.w0 12374 161 + d.w1 12374 161 * √(π / 2) +
      2 * d.w2 12374 161 + energyR16 12374 *
      radiusPolynomialRoot16 (d.w0 12374 161) (d.w1 12374 161) (d.w2 12374 161) := by
    positivity
  constructor
  · change (12374 : ℝ) ^ 8 * (mA 12374 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12374 161) (d.f1 12374 161) d.f2 + locationR16 12374 *
        radiusPolynomialRoot16 (d.f0 12374 161) (d.f1 12374 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12374 : ℝ) ^ 8 * (mA 12374 : ℝ) ^ 8 *
        ((((978109193 / 200000000000000000) : ℝ) ^ 2 + 2 * ((978109193 / 200000000000000000)) * ((1631569159 / 1000000000000000000)) * (126 / 100) +
          2 * (((1631569159 / 1000000000000000000)) ^ 2 + 2 * ((978109193 / 200000000000000000)) * ((24509267 / 62500000000000000))) +
          6 * ((1631569159 / 1000000000000000000)) * ((24509267 / 62500000000000000)) * (126 / 100) + 8 * ((24509267 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12374) *
          (32 * (((978109193 / 200000000000000000) : ℝ) + (1631569159 / 1000000000000000000) + (24509267 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12374 : ℝ) ^ 16 *
      (d.w0 12374 161 + d.w1 12374 161 * √(π / 2) + 2 * d.w2 12374 161 +
        energyR16 12374 * radiusPolynomialRoot16 (d.w0 12374 161) (d.w1 12374 161)
          (d.w2 12374 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12374 : ℝ) ^ 16 *
        (((1981948099 / 100000000000000000000) : ℝ) + ((705059139 / 50000000000000000000)) * (126 / 100) + 2 * ((515222517 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12374) *
          (32 * (((1981948099 / 100000000000000000000) : ℝ) + (705059139 / 50000000000000000000) + (515222517 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12374
