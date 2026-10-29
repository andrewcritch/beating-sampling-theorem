import BstLean.Part266Shard25Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12975. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12973 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12973 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12973 128 ≤ (13227 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13227 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12975) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12975 : ℕ))
    (by norm_num : (12975 : ℕ) ≤ 16384)
  have ht : paperTail256 12975 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12975 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12975 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12975 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12975 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12975 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12973 128 * √(2 / (12975 : ℝ)) *
      (√(12975 : ℝ) + paperT0 12975 + paperTail256 12975) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12975 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12975 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12975 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12973 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12973 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12975 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12975

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12975 (61 / 100) 164 (17 / (100 * 12975)) (26 / (10 * 12975)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12975 (61 / 100) 164 (17 / (100 * 12975)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (446883857 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (27553533 / 20000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (861271349 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12975 / 12975 * (61 / 100)) ^ 4 * inverseRadius8 (12975 - 1) /
            envelopeGap 12975 (61 / 100) 164 (17 / (100 * 12975)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12975

namespace BstLean.Part266.Row12975
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12975 164 ≤ (4343714361 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12975 164 ≤ (144913643 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348300441 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12975 164 ≤ (859542509 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12975 164 ≤ (305774017 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12975 164 ≤ (446888029 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (446883857 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (446883857 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (27553533 / 20000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (861271349 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((904921 / 250000000) : ℝ) ≤ √(17 / (100 * 12975) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12975) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (422792553 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3711706683 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12975) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12975) ≤ (21799053 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12975) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12975 * (164 : ℝ) ^ 2 + 26 / (10 * 12975) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12975) : ℝ)) (tA 12975 * 164 ^ 2 + 26 / (10 * 12975)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((904921 / 250000000))) * ((446883857 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((904921 / 250000000)) ^ 3) * ((27553533 / 20000000000000000000000))) + ((861271349 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((904921 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12975) : ℝ)) d.D d.V d.P (√(tA 12975) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((904921 / 250000000)) ^ 2 * (((422792553 / 200000000000000)) * ((3711706683 / 100000000000000000)))) + ((861271349 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12975) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((904921 / 250000000)) * ((446883857 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12975) : ℝ)) (tA 12975 * 164 ^ 2 + 26 / (10 * 12975)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((446883857 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((904921 / 250000000)) ^ 2) * ((27553533 / 20000000000000000000000)) + ((861271349 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12975) : ℝ)) (√(26 / (10 * 12975) : ℝ)) d.D d.V d.P (√(tA 12975) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((904921 / 250000000)) * (((422792553 / 200000000000000)) * ((3711706683 / 100000000000000000))) + ((861271349 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12975) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((446883857 / 100000000000000000000) : ℝ) + ((861271349 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12975

namespace BstLean.Part266.Row12975
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12975 164 ∧
    0 ≤ (tableEnvelope C).f1 12975 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12975 164 ∧
    0 ≤ (tableEnvelope C).w1 12975 164 ∧ 0 ≤ (tableEnvelope C).w2 12975 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12975 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12975 164 ∧ 0 ≤ d.f1 12975 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12975 164 ∧ 0 ≤ d.w1 12975 164 ∧ 0 ≤ d.w2 12975 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12975 ≤ 2 * (228 / 100 : ℝ) / 12975 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12975 ≤ 2 * (370 / 100 : ℝ) / 12975 := by
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
    (completeRAData (tableEnvelope C) 12975 164).locationBound 12975 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12975 164).energyBound 12975 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12975 164) (d.f1 12975 164) d.f2 ≤
      32 * (((4343714361 / 1000000000000000000) : ℝ) + (144913643 / 100000000000000000) + (348300441 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12975 164) (d.w1 12975 164)
      (d.w2 12975 164) ≤
      32 * (((859542509 / 50000000000000000000) : ℝ) + (305774017 / 25000000000000000000) + (446888029 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12975 164) (d.f1 12975 164) d.f2 ≤
      ((4343714361 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4343714361 / 1000000000000000000)) * ((144913643 / 100000000000000000)) * (126 / 100) +
      2 * (((144913643 / 100000000000000000)) ^ 2 + 2 * ((4343714361 / 1000000000000000000)) * ((348300441 / 1000000000000000000))) +
      6 * ((144913643 / 100000000000000000)) * ((348300441 / 1000000000000000000)) * (126 / 100) + 8 * ((348300441 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12975 164) (d.f1 12975 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12975 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12975 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12975 164) (d.f1 12975 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12975 164) (d.w1 12975 164) (d.w2 12975 164)
  have hwexpr0 : 0 ≤ d.w0 12975 164 + d.w1 12975 164 * √(π / 2) +
      2 * d.w2 12975 164 + energyR16 12975 *
      radiusPolynomialRoot16 (d.w0 12975 164) (d.w1 12975 164) (d.w2 12975 164) := by
    positivity
  constructor
  · change (12975 : ℝ) ^ 8 * (mA 12975 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12975 164) (d.f1 12975 164) d.f2 + locationR16 12975 *
        radiusPolynomialRoot16 (d.f0 12975 164) (d.f1 12975 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12975 : ℝ) ^ 8 * (mA 12975 : ℝ) ^ 8 *
        ((((4343714361 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4343714361 / 1000000000000000000)) * ((144913643 / 100000000000000000)) * (126 / 100) +
          2 * (((144913643 / 100000000000000000)) ^ 2 + 2 * ((4343714361 / 1000000000000000000)) * ((348300441 / 1000000000000000000))) +
          6 * ((144913643 / 100000000000000000)) * ((348300441 / 1000000000000000000)) * (126 / 100) + 8 * ((348300441 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12975) *
          (32 * (((4343714361 / 1000000000000000000) : ℝ) + (144913643 / 100000000000000000) + (348300441 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12975 : ℝ) ^ 16 *
      (d.w0 12975 164 + d.w1 12975 164 * √(π / 2) + 2 * d.w2 12975 164 +
        energyR16 12975 * radiusPolynomialRoot16 (d.w0 12975 164) (d.w1 12975 164)
          (d.w2 12975 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12975 : ℝ) ^ 16 *
        (((859542509 / 50000000000000000000) : ℝ) + ((305774017 / 25000000000000000000)) * (126 / 100) + 2 * ((446888029 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12975) *
          (32 * (((859542509 / 50000000000000000000) : ℝ) + (305774017 / 25000000000000000000) + (446888029 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12975

/-! A coarse bound on the actual paper statistics constant at dimension 12976. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12974 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12974 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12974 128 ≤ (13228 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13228 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12976) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12976 : ℕ))
    (by norm_num : (12976 : ℕ) ≤ 16384)
  have ht : paperTail256 12976 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12976 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12976 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12976 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12976 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12976 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12974 128 * √(2 / (12976 : ℝ)) *
      (√(12976 : ℝ) + paperT0 12976 + paperTail256 12976) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12976 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12976 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12976 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12974 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12974 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12976 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12976

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12976 (61 / 100) 164 (17 / (100 * 12976)) (26 / (10 * 12976)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12976 (61 / 100) 164 (17 / (100 * 12976)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (223390271 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1377251999 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2151838713 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12976 / 12976 * (61 / 100)) ^ 4 * inverseRadius8 (12976 - 1) /
            envelopeGap 12976 (61 / 100) 164 (17 / (100 * 12976)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12976

namespace BstLean.Part266.Row12976
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12976 164 ≤ (4342875827 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12976 164 ≤ (1448856851 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34823329 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12976 164 ≤ (1718687247 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12976 164 ≤ (1222813139 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12976 164 ≤ (446784711 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (223390271 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (223390271 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1377251999 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2151838713 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((723909 / 200000000) : ℝ) ≤ √(17 / (100 * 12976) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12976) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (528429597 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37111345961 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12976) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12976) ≤ (54493433 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12976) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12976 * (164 : ℝ) ^ 2 + 26 / (10 * 12976) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12976) : ℝ)) (tA 12976 * 164 ^ 2 + 26 / (10 * 12976)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((723909 / 200000000))) * ((223390271 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((723909 / 200000000)) ^ 3) * ((1377251999 / 1000000000000000000000000))) + ((2151838713 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((723909 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12976) : ℝ)) d.D d.V d.P (√(tA 12976) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((723909 / 200000000)) ^ 2 * (((528429597 / 250000000000000)) * ((37111345961 / 1000000000000000000)))) + ((2151838713 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12976) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((723909 / 200000000)) * ((223390271 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12976) : ℝ)) (tA 12976 * 164 ^ 2 + 26 / (10 * 12976)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((223390271 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((723909 / 200000000)) ^ 2) * ((1377251999 / 1000000000000000000000000)) + ((2151838713 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12976) : ℝ)) (√(26 / (10 * 12976) : ℝ)) d.D d.V d.P (√(tA 12976) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((723909 / 200000000)) * (((528429597 / 250000000000000)) * ((37111345961 / 1000000000000000000))) + ((2151838713 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12976) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((223390271 / 50000000000000000000) : ℝ) + ((2151838713 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12976

namespace BstLean.Part266.Row12976
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12976 164 ∧
    0 ≤ (tableEnvelope C).f1 12976 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12976 164 ∧
    0 ≤ (tableEnvelope C).w1 12976 164 ∧ 0 ≤ (tableEnvelope C).w2 12976 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12976 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12976 164 ∧ 0 ≤ d.f1 12976 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12976 164 ∧ 0 ≤ d.w1 12976 164 ∧ 0 ≤ d.w2 12976 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12976 ≤ 2 * (228 / 100 : ℝ) / 12976 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12976 ≤ 2 * (370 / 100 : ℝ) / 12976 := by
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
    (completeRAData (tableEnvelope C) 12976 164).locationBound 12976 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12976 164).energyBound 12976 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12976 164) (d.f1 12976 164) d.f2 ≤
      32 * (((4342875827 / 1000000000000000000) : ℝ) + (1448856851 / 1000000000000000000) + (34823329 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12976 164) (d.w1 12976 164)
      (d.w2 12976 164) ≤
      32 * (((1718687247 / 100000000000000000000) : ℝ) + (1222813139 / 100000000000000000000) + (446784711 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12976 164) (d.f1 12976 164) d.f2 ≤
      ((4342875827 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4342875827 / 1000000000000000000)) * ((1448856851 / 1000000000000000000)) * (126 / 100) +
      2 * (((1448856851 / 1000000000000000000)) ^ 2 + 2 * ((4342875827 / 1000000000000000000)) * ((34823329 / 100000000000000000))) +
      6 * ((1448856851 / 1000000000000000000)) * ((34823329 / 100000000000000000)) * (126 / 100) + 8 * ((34823329 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12976 164) (d.f1 12976 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12976 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12976 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12976 164) (d.f1 12976 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12976 164) (d.w1 12976 164) (d.w2 12976 164)
  have hwexpr0 : 0 ≤ d.w0 12976 164 + d.w1 12976 164 * √(π / 2) +
      2 * d.w2 12976 164 + energyR16 12976 *
      radiusPolynomialRoot16 (d.w0 12976 164) (d.w1 12976 164) (d.w2 12976 164) := by
    positivity
  constructor
  · change (12976 : ℝ) ^ 8 * (mA 12976 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12976 164) (d.f1 12976 164) d.f2 + locationR16 12976 *
        radiusPolynomialRoot16 (d.f0 12976 164) (d.f1 12976 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12976 : ℝ) ^ 8 * (mA 12976 : ℝ) ^ 8 *
        ((((4342875827 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4342875827 / 1000000000000000000)) * ((1448856851 / 1000000000000000000)) * (126 / 100) +
          2 * (((1448856851 / 1000000000000000000)) ^ 2 + 2 * ((4342875827 / 1000000000000000000)) * ((34823329 / 100000000000000000))) +
          6 * ((1448856851 / 1000000000000000000)) * ((34823329 / 100000000000000000)) * (126 / 100) + 8 * ((34823329 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12976) *
          (32 * (((4342875827 / 1000000000000000000) : ℝ) + (1448856851 / 1000000000000000000) + (34823329 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12976 : ℝ) ^ 16 *
      (d.w0 12976 164 + d.w1 12976 164 * √(π / 2) + 2 * d.w2 12976 164 +
        energyR16 12976 * radiusPolynomialRoot16 (d.w0 12976 164) (d.w1 12976 164)
          (d.w2 12976 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12976 : ℝ) ^ 16 *
        (((1718687247 / 100000000000000000000) : ℝ) + ((1222813139 / 100000000000000000000)) * (126 / 100) + 2 * ((446784711 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12976) *
          (32 * (((1718687247 / 100000000000000000000) : ℝ) + (1222813139 / 100000000000000000000) + (446784711 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12976

/-! A coarse bound on the actual paper statistics constant at dimension 12977. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12975 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12975 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12975 128 ≤ (13229 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13229 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12977) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12977 : ℕ))
    (by norm_num : (12977 : ℕ) ≤ 16384)
  have ht : paperTail256 12977 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12977 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12977 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12977 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12977 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12977 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12975 128 * √(2 / (12977 : ℝ)) *
      (√(12977 : ℝ) + paperT0 12977 + paperTail256 12977) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12977 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12977 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12977 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12975 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12975 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12977 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12977

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12977 (61 / 100) 164 (17 / (100 * 12977)) (26 / (10 * 12977)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12977 (61 / 100) 164 (17 / (100 * 12977)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (446677259 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (137682751 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (860199997 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12977 / 12977 * (61 / 100)) ^ 4 * inverseRadius8 (12977 - 1) /
            envelopeGap 12977 (61 / 100) 164 (17 / (100 * 12977)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12977

namespace BstLean.Part266.Row12977
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12977 164 ≤ (434203757 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12977 164 ≤ (1448577359 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348166159 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12977 164 ≤ (214786201 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12977 164 ≤ (611265151 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12977 164 ≤ (223340713 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (446677259 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (446677259 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (137682751 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (860199997 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1809703 / 500000000) : ℝ) ≤ √(17 / (100 * 12977) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12977) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1056737029 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37105626393 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12977) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12977) ≤ (108978467 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12977) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12977 * (164 : ℝ) ^ 2 + 26 / (10 * 12977) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12977) : ℝ)) (tA 12977 * 164 ^ 2 + 26 / (10 * 12977)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1809703 / 500000000))) * ((446677259 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1809703 / 500000000)) ^ 3) * ((137682751 / 100000000000000000000000))) + ((860199997 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1809703 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12977) : ℝ)) d.D d.V d.P (√(tA 12977) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1809703 / 500000000)) ^ 2 * (((1056737029 / 500000000000000)) * ((37105626393 / 1000000000000000000)))) + ((860199997 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12977) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1809703 / 500000000)) * ((446677259 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12977) : ℝ)) (tA 12977 * 164 ^ 2 + 26 / (10 * 12977)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((446677259 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1809703 / 500000000)) ^ 2) * ((137682751 / 100000000000000000000000)) + ((860199997 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12977) : ℝ)) (√(26 / (10 * 12977) : ℝ)) d.D d.V d.P (√(tA 12977) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1809703 / 500000000)) * (((1056737029 / 500000000000000)) * ((37105626393 / 1000000000000000000))) + ((860199997 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12977) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((446677259 / 100000000000000000000) : ℝ) + ((860199997 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12977

namespace BstLean.Part266.Row12977
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12977 164 ∧
    0 ≤ (tableEnvelope C).f1 12977 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12977 164 ∧
    0 ≤ (tableEnvelope C).w1 12977 164 ∧ 0 ≤ (tableEnvelope C).w2 12977 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12977 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12977 164 ∧ 0 ≤ d.f1 12977 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12977 164 ∧ 0 ≤ d.w1 12977 164 ∧ 0 ≤ d.w2 12977 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12977 ≤ 2 * (228 / 100 : ℝ) / 12977 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12977 ≤ 2 * (370 / 100 : ℝ) / 12977 := by
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
    (completeRAData (tableEnvelope C) 12977 164).locationBound 12977 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12977 164).energyBound 12977 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12977 164) (d.f1 12977 164) d.f2 ≤
      32 * (((434203757 / 100000000000000000) : ℝ) + (1448577359 / 1000000000000000000) + (348166159 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12977 164) (d.w1 12977 164)
      (d.w2 12977 164) ≤
      32 * (((214786201 / 12500000000000000000) : ℝ) + (611265151 / 50000000000000000000) + (223340713 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12977 164) (d.f1 12977 164) d.f2 ≤
      ((434203757 / 100000000000000000) : ℝ) ^ 2 + 2 * ((434203757 / 100000000000000000)) * ((1448577359 / 1000000000000000000)) * (126 / 100) +
      2 * (((1448577359 / 1000000000000000000)) ^ 2 + 2 * ((434203757 / 100000000000000000)) * ((348166159 / 1000000000000000000))) +
      6 * ((1448577359 / 1000000000000000000)) * ((348166159 / 1000000000000000000)) * (126 / 100) + 8 * ((348166159 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12977 164) (d.f1 12977 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12977 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12977 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12977 164) (d.f1 12977 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12977 164) (d.w1 12977 164) (d.w2 12977 164)
  have hwexpr0 : 0 ≤ d.w0 12977 164 + d.w1 12977 164 * √(π / 2) +
      2 * d.w2 12977 164 + energyR16 12977 *
      radiusPolynomialRoot16 (d.w0 12977 164) (d.w1 12977 164) (d.w2 12977 164) := by
    positivity
  constructor
  · change (12977 : ℝ) ^ 8 * (mA 12977 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12977 164) (d.f1 12977 164) d.f2 + locationR16 12977 *
        radiusPolynomialRoot16 (d.f0 12977 164) (d.f1 12977 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12977 : ℝ) ^ 8 * (mA 12977 : ℝ) ^ 8 *
        ((((434203757 / 100000000000000000) : ℝ) ^ 2 + 2 * ((434203757 / 100000000000000000)) * ((1448577359 / 1000000000000000000)) * (126 / 100) +
          2 * (((1448577359 / 1000000000000000000)) ^ 2 + 2 * ((434203757 / 100000000000000000)) * ((348166159 / 1000000000000000000))) +
          6 * ((1448577359 / 1000000000000000000)) * ((348166159 / 1000000000000000000)) * (126 / 100) + 8 * ((348166159 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12977) *
          (32 * (((434203757 / 100000000000000000) : ℝ) + (1448577359 / 1000000000000000000) + (348166159 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12977 : ℝ) ^ 16 *
      (d.w0 12977 164 + d.w1 12977 164 * √(π / 2) + 2 * d.w2 12977 164 +
        energyR16 12977 * radiusPolynomialRoot16 (d.w0 12977 164) (d.w1 12977 164)
          (d.w2 12977 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12977 : ℝ) ^ 16 *
        (((214786201 / 12500000000000000000) : ℝ) + ((611265151 / 50000000000000000000)) * (126 / 100) + 2 * ((223340713 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12977) *
          (32 * (((214786201 / 12500000000000000000) : ℝ) + (611265151 / 50000000000000000000) + (223340713 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12977

/-! A coarse bound on the actual paper statistics constant at dimension 12978. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12976 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12976 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12976 128 ≤ (13230 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13230 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12978) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12978 : ℕ))
    (by norm_num : (12978 : ℕ) ≤ 16384)
  have ht : paperTail256 12978 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12978 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12978 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12978 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12978 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12978 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12976 128 * √(2 / (12978 : ℝ)) *
      (√(12978 : ℝ) + paperT0 12978 + paperTail256 12978) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12978 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12978 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12978 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12976 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12976 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12978 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12978

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12978 (61 / 100) 164 (17 / (100 * 12978)) (26 / (10 * 12978)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12978 (61 / 100) 164 (17 / (100 * 12978)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (446574007 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (688201593 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4298324419 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12978 / 12978 * (61 / 100)) ^ 4 * inverseRadius8 (12978 - 1) /
            envelopeGap 12978 (61 / 100) 164 (17 / (100 * 12978)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12978

namespace BstLean.Part266.Row12978
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12978 164 ≤ (2170601531 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12978 164 ≤ (362074689 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348099143 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12978 164 ≤ (858946403 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12978 164 ≤ (244449579 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12978 164 ≤ (446578171 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (446574007 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (446574007 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (688201593 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4298324419 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1809633 / 500000000) : ℝ) ≤ √(17 / (100 * 12978) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12978) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2113229773 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4637488521 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12978) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12978) ≤ (10897007 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12978) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12978 * (164 : ℝ) ^ 2 + 26 / (10 * 12978) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12978) : ℝ)) (tA 12978 * 164 ^ 2 + 26 / (10 * 12978)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1809633 / 500000000))) * ((446574007 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1809633 / 500000000)) ^ 3) * ((688201593 / 500000000000000000000000))) + ((4298324419 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1809633 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12978) : ℝ)) d.D d.V d.P (√(tA 12978) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1809633 / 500000000)) ^ 2 * (((2113229773 / 1000000000000000)) * ((4637488521 / 125000000000000000)))) + ((4298324419 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12978) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1809633 / 500000000)) * ((446574007 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12978) : ℝ)) (tA 12978 * 164 ^ 2 + 26 / (10 * 12978)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((446574007 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1809633 / 500000000)) ^ 2) * ((688201593 / 500000000000000000000000)) + ((4298324419 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12978) : ℝ)) (√(26 / (10 * 12978) : ℝ)) d.D d.V d.P (√(tA 12978) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1809633 / 500000000)) * (((2113229773 / 1000000000000000)) * ((4637488521 / 125000000000000000))) + ((4298324419 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12978) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((446574007 / 100000000000000000000) : ℝ) + ((4298324419 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12978

namespace BstLean.Part266.Row12978
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12978 164 ∧
    0 ≤ (tableEnvelope C).f1 12978 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12978 164 ∧
    0 ≤ (tableEnvelope C).w1 12978 164 ∧ 0 ≤ (tableEnvelope C).w2 12978 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12978 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12978 164 ∧ 0 ≤ d.f1 12978 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12978 164 ∧ 0 ≤ d.w1 12978 164 ∧ 0 ≤ d.w2 12978 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12978 ≤ 2 * (228 / 100 : ℝ) / 12978 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12978 ≤ 2 * (370 / 100 : ℝ) / 12978 := by
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
    (completeRAData (tableEnvelope C) 12978 164).locationBound 12978 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12978 164).energyBound 12978 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12978 164) (d.f1 12978 164) d.f2 ≤
      32 * (((2170601531 / 500000000000000000) : ℝ) + (362074689 / 250000000000000000) + (348099143 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12978 164) (d.w1 12978 164)
      (d.w2 12978 164) ≤
      32 * (((858946403 / 50000000000000000000) : ℝ) + (244449579 / 20000000000000000000) + (446578171 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12978 164) (d.f1 12978 164) d.f2 ≤
      ((2170601531 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2170601531 / 500000000000000000)) * ((362074689 / 250000000000000000)) * (126 / 100) +
      2 * (((362074689 / 250000000000000000)) ^ 2 + 2 * ((2170601531 / 500000000000000000)) * ((348099143 / 1000000000000000000))) +
      6 * ((362074689 / 250000000000000000)) * ((348099143 / 1000000000000000000)) * (126 / 100) + 8 * ((348099143 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12978 164) (d.f1 12978 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12978 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12978 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12978 164) (d.f1 12978 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12978 164) (d.w1 12978 164) (d.w2 12978 164)
  have hwexpr0 : 0 ≤ d.w0 12978 164 + d.w1 12978 164 * √(π / 2) +
      2 * d.w2 12978 164 + energyR16 12978 *
      radiusPolynomialRoot16 (d.w0 12978 164) (d.w1 12978 164) (d.w2 12978 164) := by
    positivity
  constructor
  · change (12978 : ℝ) ^ 8 * (mA 12978 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12978 164) (d.f1 12978 164) d.f2 + locationR16 12978 *
        radiusPolynomialRoot16 (d.f0 12978 164) (d.f1 12978 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12978 : ℝ) ^ 8 * (mA 12978 : ℝ) ^ 8 *
        ((((2170601531 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2170601531 / 500000000000000000)) * ((362074689 / 250000000000000000)) * (126 / 100) +
          2 * (((362074689 / 250000000000000000)) ^ 2 + 2 * ((2170601531 / 500000000000000000)) * ((348099143 / 1000000000000000000))) +
          6 * ((362074689 / 250000000000000000)) * ((348099143 / 1000000000000000000)) * (126 / 100) + 8 * ((348099143 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12978) *
          (32 * (((2170601531 / 500000000000000000) : ℝ) + (362074689 / 250000000000000000) + (348099143 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12978 : ℝ) ^ 16 *
      (d.w0 12978 164 + d.w1 12978 164 * √(π / 2) + 2 * d.w2 12978 164 +
        energyR16 12978 * radiusPolynomialRoot16 (d.w0 12978 164) (d.w1 12978 164)
          (d.w2 12978 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12978 : ℝ) ^ 16 *
        (((858946403 / 50000000000000000000) : ℝ) + ((244449579 / 20000000000000000000)) * (126 / 100) + 2 * ((446578171 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12978) *
          (32 * (((858946403 / 50000000000000000000) : ℝ) + (244449579 / 20000000000000000000) + (446578171 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12978

/-! A coarse bound on the actual paper statistics constant at dimension 12979. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12977 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12977 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12977 128 ≤ (13231 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13231 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12979) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12979 : ℕ))
    (by norm_num : (12979 : ℕ) ≤ 16384)
  have ht : paperTail256 12979 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12979 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12979 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12979 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12979 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12979 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12977 128 * √(2 / (12979 : ℝ)) *
      (√(12979 : ℝ) + paperT0 12979 + paperTail256 12979) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12979 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12979 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12979 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12977 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12977 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12979 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12979

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12979 (61 / 100) 164 (17 / (100 * 12979)) (26 / (10 * 12979)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12979 (61 / 100) 164 (17 / (100 * 12979)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (111617697 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (85998689 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4295650727 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12979 / 12979 * (61 / 100)) ^ 4 * inverseRadius8 (12979 - 1) /
            envelopeGap 12979 (61 / 100) 164 (17 / (100 * 12979)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12979

namespace BstLean.Part266.Row12979
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12979 164 ≤ (4340365369 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12979 164 ≤ (1448019441 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (348032051 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12979 164 ≤ (343499087 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12979 164 ≤ (305491311 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12979 164 ≤ (8929499 / 2000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (111617697 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (111617697 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (85998689 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4295650727 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3619127 / 1000000000) : ℝ) ≤ √(17 / (100 * 12979) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12979) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1056492769 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9273547811 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12979) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12979) ≤ (54480837 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12979) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12979 * (164 : ℝ) ^ 2 + 26 / (10 * 12979) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12979) : ℝ)) (tA 12979 * 164 ^ 2 + 26 / (10 * 12979)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3619127 / 1000000000))) * ((111617697 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3619127 / 1000000000)) ^ 3) * ((85998689 / 62500000000000000000000))) + ((4295650727 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3619127 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12979) : ℝ)) d.D d.V d.P (√(tA 12979) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3619127 / 1000000000)) ^ 2 * (((1056492769 / 500000000000000)) * ((9273547811 / 250000000000000000)))) + ((4295650727 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12979) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3619127 / 1000000000)) * ((111617697 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12979) : ℝ)) (tA 12979 * 164 ^ 2 + 26 / (10 * 12979)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((111617697 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3619127 / 1000000000)) ^ 2) * ((85998689 / 62500000000000000000000)) + ((4295650727 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12979) : ℝ)) (√(26 / (10 * 12979) : ℝ)) d.D d.V d.P (√(tA 12979) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3619127 / 1000000000)) * (((1056492769 / 500000000000000)) * ((9273547811 / 250000000000000000))) + ((4295650727 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12979) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((111617697 / 25000000000000000000) : ℝ) + ((4295650727 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12979

namespace BstLean.Part266.Row12979
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12979 164 ∧
    0 ≤ (tableEnvelope C).f1 12979 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12979 164 ∧
    0 ≤ (tableEnvelope C).w1 12979 164 ∧ 0 ≤ (tableEnvelope C).w2 12979 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12979 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12979 164 ∧ 0 ≤ d.f1 12979 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12979 164 ∧ 0 ≤ d.w1 12979 164 ∧ 0 ≤ d.w2 12979 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12979 ≤ 2 * (228 / 100 : ℝ) / 12979 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12979 ≤ 2 * (370 / 100 : ℝ) / 12979 := by
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
    (completeRAData (tableEnvelope C) 12979 164).locationBound 12979 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12979 164).energyBound 12979 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12979 164) (d.f1 12979 164) d.f2 ≤
      32 * (((4340365369 / 1000000000000000000) : ℝ) + (1448019441 / 1000000000000000000) + (348032051 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12979 164) (d.w1 12979 164)
      (d.w2 12979 164) ≤
      32 * (((343499087 / 20000000000000000000) : ℝ) + (305491311 / 25000000000000000000) + (8929499 / 2000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12979 164) (d.f1 12979 164) d.f2 ≤
      ((4340365369 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4340365369 / 1000000000000000000)) * ((1448019441 / 1000000000000000000)) * (126 / 100) +
      2 * (((1448019441 / 1000000000000000000)) ^ 2 + 2 * ((4340365369 / 1000000000000000000)) * ((348032051 / 1000000000000000000))) +
      6 * ((1448019441 / 1000000000000000000)) * ((348032051 / 1000000000000000000)) * (126 / 100) + 8 * ((348032051 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12979 164) (d.f1 12979 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12979 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12979 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12979 164) (d.f1 12979 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12979 164) (d.w1 12979 164) (d.w2 12979 164)
  have hwexpr0 : 0 ≤ d.w0 12979 164 + d.w1 12979 164 * √(π / 2) +
      2 * d.w2 12979 164 + energyR16 12979 *
      radiusPolynomialRoot16 (d.w0 12979 164) (d.w1 12979 164) (d.w2 12979 164) := by
    positivity
  constructor
  · change (12979 : ℝ) ^ 8 * (mA 12979 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12979 164) (d.f1 12979 164) d.f2 + locationR16 12979 *
        radiusPolynomialRoot16 (d.f0 12979 164) (d.f1 12979 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12979 : ℝ) ^ 8 * (mA 12979 : ℝ) ^ 8 *
        ((((4340365369 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4340365369 / 1000000000000000000)) * ((1448019441 / 1000000000000000000)) * (126 / 100) +
          2 * (((1448019441 / 1000000000000000000)) ^ 2 + 2 * ((4340365369 / 1000000000000000000)) * ((348032051 / 1000000000000000000))) +
          6 * ((1448019441 / 1000000000000000000)) * ((348032051 / 1000000000000000000)) * (126 / 100) + 8 * ((348032051 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12979) *
          (32 * (((4340365369 / 1000000000000000000) : ℝ) + (1448019441 / 1000000000000000000) + (348032051 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12979 : ℝ) ^ 16 *
      (d.w0 12979 164 + d.w1 12979 164 * √(π / 2) + 2 * d.w2 12979 164 +
        energyR16 12979 * radiusPolynomialRoot16 (d.w0 12979 164) (d.w1 12979 164)
          (d.w2 12979 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12979 : ℝ) ^ 16 *
        (((343499087 / 20000000000000000000) : ℝ) + ((305491311 / 25000000000000000000)) * (126 / 100) + 2 * ((8929499 / 2000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12979) *
          (32 * (((343499087 / 20000000000000000000) : ℝ) + (305491311 / 25000000000000000000) + (8929499 / 2000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12979

/-! A coarse bound on the actual paper statistics constant at dimension 12980. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12978 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12978 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12978 128 ≤ (13232 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13232 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12980) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12980 : ℕ))
    (by norm_num : (12980 : ℕ) ≤ 16384)
  have ht : paperTail256 12980 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12980 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12980 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12980 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12980 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12980 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12978 128 * √(2 / (12980 : ℝ)) *
      (√(12980 : ℝ) + paperT0 12980 + paperTail256 12980) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12980 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12980 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12980 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12978 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12978 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12980 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12980

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12980 (61 / 100) 164 (17 / (100 * 12980)) (26 / (10 * 12980)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12980 (61 / 100) 164 (17 / (100 * 12980)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1115919 / 250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1375555027 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1073244727 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12980 / 12980 * (61 / 100)) ^ 4 * inverseRadius8 (12980 - 1) /
            envelopeGap 12980 (61 / 100) 164 (17 / (100 * 12980)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12980

namespace BstLean.Part266.Row12980
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12980 164 ≤ (4339531423 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12980 164 ≤ (723870507 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (13918603 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12980 164 ≤ (1717098901 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12980 164 ≤ (610841511 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12980 164 ≤ (446371759 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1115919 / 250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1115919 / 250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1375555027 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1073244727 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3618987 / 1000000000) : ℝ) ≤ √(17 / (100 * 12980) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12980) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (528185337 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37088475663 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12980) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12980) ≤ (340479 / 3125000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12980) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12980 * (164 : ℝ) ^ 2 + 26 / (10 * 12980) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12980) : ℝ)) (tA 12980 * 164 ^ 2 + 26 / (10 * 12980)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3618987 / 1000000000))) * ((1115919 / 250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3618987 / 1000000000)) ^ 3) * ((1375555027 / 1000000000000000000000000))) + ((1073244727 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3618987 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12980) : ℝ)) d.D d.V d.P (√(tA 12980) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3618987 / 1000000000)) ^ 2 * (((528185337 / 250000000000000)) * ((37088475663 / 1000000000000000000)))) + ((1073244727 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12980) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3618987 / 1000000000)) * ((1115919 / 250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12980) : ℝ)) (tA 12980 * 164 ^ 2 + 26 / (10 * 12980)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1115919 / 250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3618987 / 1000000000)) ^ 2) * ((1375555027 / 1000000000000000000000000)) + ((1073244727 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12980) : ℝ)) (√(26 / (10 * 12980) : ℝ)) d.D d.V d.P (√(tA 12980) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3618987 / 1000000000)) * (((528185337 / 250000000000000)) * ((37088475663 / 1000000000000000000))) + ((1073244727 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12980) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((1115919 / 250000000000000000) : ℝ) + ((1073244727 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12980

namespace BstLean.Part266.Row12980
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12980 164 ∧
    0 ≤ (tableEnvelope C).f1 12980 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12980 164 ∧
    0 ≤ (tableEnvelope C).w1 12980 164 ∧ 0 ≤ (tableEnvelope C).w2 12980 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12980 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12980 164 ∧ 0 ≤ d.f1 12980 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12980 164 ∧ 0 ≤ d.w1 12980 164 ∧ 0 ≤ d.w2 12980 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12980 ≤ 2 * (228 / 100 : ℝ) / 12980 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12980 ≤ 2 * (370 / 100 : ℝ) / 12980 := by
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
    (completeRAData (tableEnvelope C) 12980 164).locationBound 12980 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12980 164).energyBound 12980 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12980 164) (d.f1 12980 164) d.f2 ≤
      32 * (((4339531423 / 1000000000000000000) : ℝ) + (723870507 / 500000000000000000) + (13918603 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12980 164) (d.w1 12980 164)
      (d.w2 12980 164) ≤
      32 * (((1717098901 / 100000000000000000000) : ℝ) + (610841511 / 50000000000000000000) + (446371759 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12980 164) (d.f1 12980 164) d.f2 ≤
      ((4339531423 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4339531423 / 1000000000000000000)) * ((723870507 / 500000000000000000)) * (126 / 100) +
      2 * (((723870507 / 500000000000000000)) ^ 2 + 2 * ((4339531423 / 1000000000000000000)) * ((13918603 / 40000000000000000))) +
      6 * ((723870507 / 500000000000000000)) * ((13918603 / 40000000000000000)) * (126 / 100) + 8 * ((13918603 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12980 164) (d.f1 12980 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12980 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12980 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12980 164) (d.f1 12980 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12980 164) (d.w1 12980 164) (d.w2 12980 164)
  have hwexpr0 : 0 ≤ d.w0 12980 164 + d.w1 12980 164 * √(π / 2) +
      2 * d.w2 12980 164 + energyR16 12980 *
      radiusPolynomialRoot16 (d.w0 12980 164) (d.w1 12980 164) (d.w2 12980 164) := by
    positivity
  constructor
  · change (12980 : ℝ) ^ 8 * (mA 12980 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12980 164) (d.f1 12980 164) d.f2 + locationR16 12980 *
        radiusPolynomialRoot16 (d.f0 12980 164) (d.f1 12980 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12980 : ℝ) ^ 8 * (mA 12980 : ℝ) ^ 8 *
        ((((4339531423 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4339531423 / 1000000000000000000)) * ((723870507 / 500000000000000000)) * (126 / 100) +
          2 * (((723870507 / 500000000000000000)) ^ 2 + 2 * ((4339531423 / 1000000000000000000)) * ((13918603 / 40000000000000000))) +
          6 * ((723870507 / 500000000000000000)) * ((13918603 / 40000000000000000)) * (126 / 100) + 8 * ((13918603 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12980) *
          (32 * (((4339531423 / 1000000000000000000) : ℝ) + (723870507 / 500000000000000000) + (13918603 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12980 : ℝ) ^ 16 *
      (d.w0 12980 164 + d.w1 12980 164 * √(π / 2) + 2 * d.w2 12980 164 +
        energyR16 12980 * radiusPolynomialRoot16 (d.w0 12980 164) (d.w1 12980 164)
          (d.w2 12980 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12980 : ℝ) ^ 16 *
        (((1717098901 / 100000000000000000000) : ℝ) + ((610841511 / 50000000000000000000)) * (126 / 100) + 2 * ((446371759 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12980) *
          (32 * (((1717098901 / 100000000000000000000) : ℝ) + (610841511 / 50000000000000000000) + (446371759 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12980

/-! A coarse bound on the actual paper statistics constant at dimension 12981. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12979 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12979 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12979 128 ≤ (13233 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13233 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12981) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12981 : ℕ))
    (by norm_num : (12981 : ℕ) ≤ 16384)
  have ht : paperTail256 12981 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12981 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12981 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12981 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12981 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12981 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12979 128 * √(2 / (12981 : ℝ)) *
      (√(12981 : ℝ) + paperT0 12981 + paperTail256 12981) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12981 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12981 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12981 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12979 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12979 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12981 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12981

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12981 (61 / 100) 164 (17 / (100 * 12981)) (26 / (10 * 12981)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12981 (61 / 100) 164 (17 / (100 * 12981)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (111566111 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (171891399 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4290308961 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12981 / 12981 * (61 / 100)) ^ 4 * inverseRadius8 (12981 - 1) /
            envelopeGap 12981 (61 / 100) 164 (17 / (100 * 12981)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12981

namespace BstLean.Part266.Row12981
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12981 164 ≤ (2169347147 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12981 164 ≤ (723730937 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (173949011 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12981 164 ≤ (858350899 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12981 164 ≤ (244280111 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12981 164 ≤ (2231343 / 500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (111566111 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (111566111 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (171891399 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4290308961 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((113089 / 31250000) : ℝ) ≤ √(17 / (100 * 12981) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12981) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (422499441 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18541380693 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12981) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12981) ≤ (54472443 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12981) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12981 * (164 : ℝ) ^ 2 + 26 / (10 * 12981) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12981) : ℝ)) (tA 12981 * 164 ^ 2 + 26 / (10 * 12981)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((113089 / 31250000))) * ((111566111 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((113089 / 31250000)) ^ 3) * ((171891399 / 125000000000000000000000))) + ((4290308961 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((113089 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12981) : ℝ)) d.D d.V d.P (√(tA 12981) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((113089 / 31250000)) ^ 2 * (((422499441 / 200000000000000)) * ((18541380693 / 500000000000000000)))) + ((4290308961 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12981) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((113089 / 31250000)) * ((111566111 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12981) : ℝ)) (tA 12981 * 164 ^ 2 + 26 / (10 * 12981)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((111566111 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((113089 / 31250000)) ^ 2) * ((171891399 / 125000000000000000000000)) + ((4290308961 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12981) : ℝ)) (√(26 / (10 * 12981) : ℝ)) d.D d.V d.P (√(tA 12981) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((113089 / 31250000)) * (((422499441 / 200000000000000)) * ((18541380693 / 500000000000000000))) + ((4290308961 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12981) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((111566111 / 25000000000000000000) : ℝ) + ((4290308961 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12981

namespace BstLean.Part266.Row12981
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12981 164 ∧
    0 ≤ (tableEnvelope C).f1 12981 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12981 164 ∧
    0 ≤ (tableEnvelope C).w1 12981 164 ∧ 0 ≤ (tableEnvelope C).w2 12981 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12981 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12981 164 ∧ 0 ≤ d.f1 12981 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12981 164 ∧ 0 ≤ d.w1 12981 164 ∧ 0 ≤ d.w2 12981 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12981 ≤ 2 * (228 / 100 : ℝ) / 12981 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12981 ≤ 2 * (370 / 100 : ℝ) / 12981 := by
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
    (completeRAData (tableEnvelope C) 12981 164).locationBound 12981 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12981 164).energyBound 12981 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12981 164) (d.f1 12981 164) d.f2 ≤
      32 * (((2169347147 / 500000000000000000) : ℝ) + (723730937 / 500000000000000000) + (173949011 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12981 164) (d.w1 12981 164)
      (d.w2 12981 164) ≤
      32 * (((858350899 / 50000000000000000000) : ℝ) + (244280111 / 20000000000000000000) + (2231343 / 500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12981 164) (d.f1 12981 164) d.f2 ≤
      ((2169347147 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2169347147 / 500000000000000000)) * ((723730937 / 500000000000000000)) * (126 / 100) +
      2 * (((723730937 / 500000000000000000)) ^ 2 + 2 * ((2169347147 / 500000000000000000)) * ((173949011 / 500000000000000000))) +
      6 * ((723730937 / 500000000000000000)) * ((173949011 / 500000000000000000)) * (126 / 100) + 8 * ((173949011 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12981 164) (d.f1 12981 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12981 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12981 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12981 164) (d.f1 12981 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12981 164) (d.w1 12981 164) (d.w2 12981 164)
  have hwexpr0 : 0 ≤ d.w0 12981 164 + d.w1 12981 164 * √(π / 2) +
      2 * d.w2 12981 164 + energyR16 12981 *
      radiusPolynomialRoot16 (d.w0 12981 164) (d.w1 12981 164) (d.w2 12981 164) := by
    positivity
  constructor
  · change (12981 : ℝ) ^ 8 * (mA 12981 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12981 164) (d.f1 12981 164) d.f2 + locationR16 12981 *
        radiusPolynomialRoot16 (d.f0 12981 164) (d.f1 12981 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12981 : ℝ) ^ 8 * (mA 12981 : ℝ) ^ 8 *
        ((((2169347147 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2169347147 / 500000000000000000)) * ((723730937 / 500000000000000000)) * (126 / 100) +
          2 * (((723730937 / 500000000000000000)) ^ 2 + 2 * ((2169347147 / 500000000000000000)) * ((173949011 / 500000000000000000))) +
          6 * ((723730937 / 500000000000000000)) * ((173949011 / 500000000000000000)) * (126 / 100) + 8 * ((173949011 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12981) *
          (32 * (((2169347147 / 500000000000000000) : ℝ) + (723730937 / 500000000000000000) + (173949011 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12981 : ℝ) ^ 16 *
      (d.w0 12981 164 + d.w1 12981 164 * √(π / 2) + 2 * d.w2 12981 164 +
        energyR16 12981 * radiusPolynomialRoot16 (d.w0 12981 164) (d.w1 12981 164)
          (d.w2 12981 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12981 : ℝ) ^ 16 *
        (((858350899 / 50000000000000000000) : ℝ) + ((244280111 / 20000000000000000000)) * (126 / 100) + 2 * ((2231343 / 500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12981) *
          (32 * (((858350899 / 50000000000000000000) : ℝ) + (244280111 / 20000000000000000000) + (2231343 / 500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12981

/-! A coarse bound on the actual paper statistics constant at dimension 12982. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12980 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12980 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12980 128 ≤ (13234 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13234 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12982) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12982 : ℕ))
    (by norm_num : (12982 : ℕ) ≤ 16384)
  have ht : paperTail256 12982 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12982 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12982 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12982 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12982 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12982 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12980 128 * √(2 / (12982 : ℝ)) *
      (√(12982 : ℝ) + paperT0 12982 + paperTail256 12982) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12982 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12982 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12982 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12980 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12980 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12982 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12982

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12982 (61 / 100) 164 (17 / (100 * 12982)) (26 / (10 * 12982)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12982 (61 / 100) 164 (17 / (100 * 12982)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (11154033 / 2500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1374707521 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4287640883 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12982 / 12982 * (61 / 100)) ^ 4 * inverseRadius8 (12982 - 1) /
            envelopeGap 12982 (61 / 100) 164 (17 / (100 * 12982)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12982

namespace BstLean.Part266.Row12982
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12982 164 ≤ (1084465227 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12982 164 ≤ (180897953 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (69566217 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12982 164 ≤ (171630553 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12982 164 ≤ (610559259 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12982 164 ≤ (223082737 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (11154033 / 2500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (11154033 / 2500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1374707521 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4287640883 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((904677 / 250000000) : ℝ) ≤ √(17 / (100 * 12982) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12982) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (211225311 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (926926211 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12982) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12982) ≤ (54468247 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12982) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12982 * (164 : ℝ) ^ 2 + 26 / (10 * 12982) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12982) : ℝ)) (tA 12982 * 164 ^ 2 + 26 / (10 * 12982)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((904677 / 250000000))) * ((11154033 / 2500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((904677 / 250000000)) ^ 3) * ((1374707521 / 1000000000000000000000000))) + ((4287640883 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((904677 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12982) : ℝ)) d.D d.V d.P (√(tA 12982) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((904677 / 250000000)) ^ 2 * (((211225311 / 100000000000000)) * ((926926211 / 25000000000000000)))) + ((4287640883 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12982) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((904677 / 250000000)) * ((11154033 / 2500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12982) : ℝ)) (tA 12982 * 164 ^ 2 + 26 / (10 * 12982)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((11154033 / 2500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((904677 / 250000000)) ^ 2) * ((1374707521 / 1000000000000000000000000)) + ((4287640883 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12982) : ℝ)) (√(26 / (10 * 12982) : ℝ)) d.D d.V d.P (√(tA 12982) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((904677 / 250000000)) * (((211225311 / 100000000000000)) * ((926926211 / 25000000000000000))) + ((4287640883 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12982) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((11154033 / 2500000000000000000) : ℝ) + ((4287640883 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12982

namespace BstLean.Part266.Row12982
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12982 164 ∧
    0 ≤ (tableEnvelope C).f1 12982 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12982 164 ∧
    0 ≤ (tableEnvelope C).w1 12982 164 ∧ 0 ≤ (tableEnvelope C).w2 12982 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12982 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12982 164 ∧ 0 ≤ d.f1 12982 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12982 164 ∧ 0 ≤ d.w1 12982 164 ∧ 0 ≤ d.w2 12982 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12982 ≤ 2 * (228 / 100 : ℝ) / 12982 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12982 ≤ 2 * (370 / 100 : ℝ) / 12982 := by
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
    (completeRAData (tableEnvelope C) 12982 164).locationBound 12982 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12982 164).energyBound 12982 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12982 164) (d.f1 12982 164) d.f2 ≤
      32 * (((1084465227 / 250000000000000000) : ℝ) + (180897953 / 125000000000000000) + (69566217 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12982 164) (d.w1 12982 164)
      (d.w2 12982 164) ≤
      32 * (((171630553 / 10000000000000000000) : ℝ) + (610559259 / 50000000000000000000) + (223082737 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12982 164) (d.f1 12982 164) d.f2 ≤
      ((1084465227 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1084465227 / 250000000000000000)) * ((180897953 / 125000000000000000)) * (126 / 100) +
      2 * (((180897953 / 125000000000000000)) ^ 2 + 2 * ((1084465227 / 250000000000000000)) * ((69566217 / 200000000000000000))) +
      6 * ((180897953 / 125000000000000000)) * ((69566217 / 200000000000000000)) * (126 / 100) + 8 * ((69566217 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12982 164) (d.f1 12982 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12982 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12982 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12982 164) (d.f1 12982 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12982 164) (d.w1 12982 164) (d.w2 12982 164)
  have hwexpr0 : 0 ≤ d.w0 12982 164 + d.w1 12982 164 * √(π / 2) +
      2 * d.w2 12982 164 + energyR16 12982 *
      radiusPolynomialRoot16 (d.w0 12982 164) (d.w1 12982 164) (d.w2 12982 164) := by
    positivity
  constructor
  · change (12982 : ℝ) ^ 8 * (mA 12982 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12982 164) (d.f1 12982 164) d.f2 + locationR16 12982 *
        radiusPolynomialRoot16 (d.f0 12982 164) (d.f1 12982 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12982 : ℝ) ^ 8 * (mA 12982 : ℝ) ^ 8 *
        ((((1084465227 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1084465227 / 250000000000000000)) * ((180897953 / 125000000000000000)) * (126 / 100) +
          2 * (((180897953 / 125000000000000000)) ^ 2 + 2 * ((1084465227 / 250000000000000000)) * ((69566217 / 200000000000000000))) +
          6 * ((180897953 / 125000000000000000)) * ((69566217 / 200000000000000000)) * (126 / 100) + 8 * ((69566217 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12982) *
          (32 * (((1084465227 / 250000000000000000) : ℝ) + (180897953 / 125000000000000000) + (69566217 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12982 : ℝ) ^ 16 *
      (d.w0 12982 164 + d.w1 12982 164 * √(π / 2) + 2 * d.w2 12982 164 +
        energyR16 12982 * radiusPolynomialRoot16 (d.w0 12982 164) (d.w1 12982 164)
          (d.w2 12982 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12982 : ℝ) ^ 16 *
        (((171630553 / 10000000000000000000) : ℝ) + ((610559259 / 50000000000000000000)) * (126 / 100) + 2 * ((223082737 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12982) *
          (32 * (((171630553 / 10000000000000000000) : ℝ) + (610559259 / 50000000000000000000) + (223082737 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12982

/-! A coarse bound on the actual paper statistics constant at dimension 12983. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12981 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12981 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12981 128 ≤ (13235 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13235 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12983) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12983 : ℕ))
    (by norm_num : (12983 : ℕ) ≤ 16384)
  have ht : paperTail256 12983 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12983 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12983 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12983 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12983 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12983 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12981 128 * √(2 / (12983 : ℝ)) *
      (√(12983 : ℝ) + paperT0 12983 + paperTail256 12983) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12983 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12983 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12983 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12981 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12981 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12983 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12983

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12983 (61 / 100) 164 (17 / (100 * 12983)) (26 / (10 * 12983)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12983 (61 / 100) 164 (17 / (100 * 12983)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (446058227 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1374284013 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2142487337 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12983 / 12983 * (61 / 100)) ^ 4 * inverseRadius8 (12983 - 1) /
            envelopeGap 12983 (61 / 100) 164 (17 / (100 * 12983)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12983

namespace BstLean.Part266.Row12983
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12983 164 ≤ (4337024343 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12983 164 ≤ (1446904661 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (347764071 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12983 164 ≤ (857954347 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12983 164 ≤ (305209059 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12983 164 ≤ (223031189 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (446058227 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (446058227 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1374284013 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2142487337 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3618569 / 1000000000) : ℝ) ≤ √(17 / (100 * 12983) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12983) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2112009061 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9267834203 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12983) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12983) ≤ (13616013 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12983) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12983 * (164 : ℝ) ^ 2 + 26 / (10 * 12983) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12983) : ℝ)) (tA 12983 * 164 ^ 2 + 26 / (10 * 12983)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3618569 / 1000000000))) * ((446058227 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3618569 / 1000000000)) ^ 3) * ((1374284013 / 1000000000000000000000000))) + ((2142487337 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3618569 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12983) : ℝ)) d.D d.V d.P (√(tA 12983) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3618569 / 1000000000)) ^ 2 * (((2112009061 / 1000000000000000)) * ((9267834203 / 250000000000000000)))) + ((2142487337 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12983) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3618569 / 1000000000)) * ((446058227 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12983) : ℝ)) (tA 12983 * 164 ^ 2 + 26 / (10 * 12983)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((446058227 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3618569 / 1000000000)) ^ 2) * ((1374284013 / 1000000000000000000000000)) + ((2142487337 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12983) : ℝ)) (√(26 / (10 * 12983) : ℝ)) d.D d.V d.P (√(tA 12983) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3618569 / 1000000000)) * (((2112009061 / 1000000000000000)) * ((9267834203 / 250000000000000000))) + ((2142487337 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12983) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((446058227 / 100000000000000000000) : ℝ) + ((2142487337 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12983

namespace BstLean.Part266.Row12983
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12983 164 ∧
    0 ≤ (tableEnvelope C).f1 12983 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12983 164 ∧
    0 ≤ (tableEnvelope C).w1 12983 164 ∧ 0 ≤ (tableEnvelope C).w2 12983 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12983 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12983 164 ∧ 0 ≤ d.f1 12983 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12983 164 ∧ 0 ≤ d.w1 12983 164 ∧ 0 ≤ d.w2 12983 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12983 ≤ 2 * (228 / 100 : ℝ) / 12983 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12983 ≤ 2 * (370 / 100 : ℝ) / 12983 := by
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
    (completeRAData (tableEnvelope C) 12983 164).locationBound 12983 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12983 164).energyBound 12983 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12983 164) (d.f1 12983 164) d.f2 ≤
      32 * (((4337024343 / 1000000000000000000) : ℝ) + (1446904661 / 1000000000000000000) + (347764071 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12983 164) (d.w1 12983 164)
      (d.w2 12983 164) ≤
      32 * (((857954347 / 50000000000000000000) : ℝ) + (305209059 / 25000000000000000000) + (223031189 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12983 164) (d.f1 12983 164) d.f2 ≤
      ((4337024343 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4337024343 / 1000000000000000000)) * ((1446904661 / 1000000000000000000)) * (126 / 100) +
      2 * (((1446904661 / 1000000000000000000)) ^ 2 + 2 * ((4337024343 / 1000000000000000000)) * ((347764071 / 1000000000000000000))) +
      6 * ((1446904661 / 1000000000000000000)) * ((347764071 / 1000000000000000000)) * (126 / 100) + 8 * ((347764071 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12983 164) (d.f1 12983 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12983 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12983 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12983 164) (d.f1 12983 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12983 164) (d.w1 12983 164) (d.w2 12983 164)
  have hwexpr0 : 0 ≤ d.w0 12983 164 + d.w1 12983 164 * √(π / 2) +
      2 * d.w2 12983 164 + energyR16 12983 *
      radiusPolynomialRoot16 (d.w0 12983 164) (d.w1 12983 164) (d.w2 12983 164) := by
    positivity
  constructor
  · change (12983 : ℝ) ^ 8 * (mA 12983 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12983 164) (d.f1 12983 164) d.f2 + locationR16 12983 *
        radiusPolynomialRoot16 (d.f0 12983 164) (d.f1 12983 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12983 : ℝ) ^ 8 * (mA 12983 : ℝ) ^ 8 *
        ((((4337024343 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4337024343 / 1000000000000000000)) * ((1446904661 / 1000000000000000000)) * (126 / 100) +
          2 * (((1446904661 / 1000000000000000000)) ^ 2 + 2 * ((4337024343 / 1000000000000000000)) * ((347764071 / 1000000000000000000))) +
          6 * ((1446904661 / 1000000000000000000)) * ((347764071 / 1000000000000000000)) * (126 / 100) + 8 * ((347764071 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12983) *
          (32 * (((4337024343 / 1000000000000000000) : ℝ) + (1446904661 / 1000000000000000000) + (347764071 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12983 : ℝ) ^ 16 *
      (d.w0 12983 164 + d.w1 12983 164 * √(π / 2) + 2 * d.w2 12983 164 +
        energyR16 12983 * radiusPolynomialRoot16 (d.w0 12983 164) (d.w1 12983 164)
          (d.w2 12983 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12983 : ℝ) ^ 16 *
        (((857954347 / 50000000000000000000) : ℝ) + ((305209059 / 25000000000000000000)) * (126 / 100) + 2 * ((223031189 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12983) *
          (32 * (((857954347 / 50000000000000000000) : ℝ) + (305209059 / 25000000000000000000) + (223031189 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12983

/-! A coarse bound on the actual paper statistics constant at dimension 12984. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12982 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12982 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12982 128 ≤ (13236 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13236 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12984) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12984 : ℕ))
    (by norm_num : (12984 : ℕ) ≤ 16384)
  have ht : paperTail256 12984 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12984 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12984 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12984 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12984 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12984 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12982 128 * √(2 / (12984 : ℝ)) *
      (√(12984 : ℝ) + paperT0 12984 + paperTail256 12984) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12984 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12984 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12984 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12982 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12982 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12984 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12984

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12984 (61 / 100) 164 (17 / (100 * 12984)) (26 / (10 * 12984)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12984 (61 / 100) 164 (17 / (100 * 12984)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (445955167 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1373860667 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4282310331 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12984 / 12984 * (61 / 100)) ^ 4 * inverseRadius8 (12984 - 1) /
            envelopeGap 12984 (61 / 100) 164 (17 / (100 * 12984)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12984

namespace BstLean.Part266.Row12984
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12984 164 ≤ (542023507 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12984 164 ≤ (723312893 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (173848539 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12984 164 ≤ (1715511991 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12984 164 ≤ (1220554047 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12984 164 ≤ (111489829 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (445955167 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (445955167 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1373860667 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4282310331 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((361843 / 100000000) : ℝ) ≤ √(17 / (100 * 12984) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12984) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2111765061 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37065626489 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12984) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12984) ≤ (54459857 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12984) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12984 * (164 : ℝ) ^ 2 + 26 / (10 * 12984) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12984) : ℝ)) (tA 12984 * 164 ^ 2 + 26 / (10 * 12984)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((361843 / 100000000))) * ((445955167 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((361843 / 100000000)) ^ 3) * ((1373860667 / 1000000000000000000000000))) + ((4282310331 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((361843 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12984) : ℝ)) d.D d.V d.P (√(tA 12984) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((361843 / 100000000)) ^ 2 * (((2111765061 / 1000000000000000)) * ((37065626489 / 1000000000000000000)))) + ((4282310331 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12984) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((361843 / 100000000)) * ((445955167 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12984) : ℝ)) (tA 12984 * 164 ^ 2 + 26 / (10 * 12984)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((445955167 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((361843 / 100000000)) ^ 2) * ((1373860667 / 1000000000000000000000000)) + ((4282310331 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12984) : ℝ)) (√(26 / (10 * 12984) : ℝ)) d.D d.V d.P (√(tA 12984) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((361843 / 100000000)) * (((2111765061 / 1000000000000000)) * ((37065626489 / 1000000000000000000))) + ((4282310331 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12984) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((445955167 / 100000000000000000000) : ℝ) + ((4282310331 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12984

namespace BstLean.Part266.Row12984
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12984 164 ∧
    0 ≤ (tableEnvelope C).f1 12984 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12984 164 ∧
    0 ≤ (tableEnvelope C).w1 12984 164 ∧ 0 ≤ (tableEnvelope C).w2 12984 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12984 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12984 164 ∧ 0 ≤ d.f1 12984 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12984 164 ∧ 0 ≤ d.w1 12984 164 ∧ 0 ≤ d.w2 12984 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12984 ≤ 2 * (228 / 100 : ℝ) / 12984 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12984 ≤ 2 * (370 / 100 : ℝ) / 12984 := by
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
    (completeRAData (tableEnvelope C) 12984 164).locationBound 12984 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12984 164).energyBound 12984 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12984 164) (d.f1 12984 164) d.f2 ≤
      32 * (((542023507 / 125000000000000000) : ℝ) + (723312893 / 500000000000000000) + (173848539 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12984 164) (d.w1 12984 164)
      (d.w2 12984 164) ≤
      32 * (((1715511991 / 100000000000000000000) : ℝ) + (1220554047 / 100000000000000000000) + (111489829 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12984 164) (d.f1 12984 164) d.f2 ≤
      ((542023507 / 125000000000000000) : ℝ) ^ 2 + 2 * ((542023507 / 125000000000000000)) * ((723312893 / 500000000000000000)) * (126 / 100) +
      2 * (((723312893 / 500000000000000000)) ^ 2 + 2 * ((542023507 / 125000000000000000)) * ((173848539 / 500000000000000000))) +
      6 * ((723312893 / 500000000000000000)) * ((173848539 / 500000000000000000)) * (126 / 100) + 8 * ((173848539 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12984 164) (d.f1 12984 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12984 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12984 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12984 164) (d.f1 12984 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12984 164) (d.w1 12984 164) (d.w2 12984 164)
  have hwexpr0 : 0 ≤ d.w0 12984 164 + d.w1 12984 164 * √(π / 2) +
      2 * d.w2 12984 164 + energyR16 12984 *
      radiusPolynomialRoot16 (d.w0 12984 164) (d.w1 12984 164) (d.w2 12984 164) := by
    positivity
  constructor
  · change (12984 : ℝ) ^ 8 * (mA 12984 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12984 164) (d.f1 12984 164) d.f2 + locationR16 12984 *
        radiusPolynomialRoot16 (d.f0 12984 164) (d.f1 12984 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12984 : ℝ) ^ 8 * (mA 12984 : ℝ) ^ 8 *
        ((((542023507 / 125000000000000000) : ℝ) ^ 2 + 2 * ((542023507 / 125000000000000000)) * ((723312893 / 500000000000000000)) * (126 / 100) +
          2 * (((723312893 / 500000000000000000)) ^ 2 + 2 * ((542023507 / 125000000000000000)) * ((173848539 / 500000000000000000))) +
          6 * ((723312893 / 500000000000000000)) * ((173848539 / 500000000000000000)) * (126 / 100) + 8 * ((173848539 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12984) *
          (32 * (((542023507 / 125000000000000000) : ℝ) + (723312893 / 500000000000000000) + (173848539 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12984 : ℝ) ^ 16 *
      (d.w0 12984 164 + d.w1 12984 164 * √(π / 2) + 2 * d.w2 12984 164 +
        energyR16 12984 * radiusPolynomialRoot16 (d.w0 12984 164) (d.w1 12984 164)
          (d.w2 12984 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12984 : ℝ) ^ 16 *
        (((1715511991 / 100000000000000000000) : ℝ) + ((1220554047 / 100000000000000000000)) * (126 / 100) + 2 * ((111489829 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12984) *
          (32 * (((1715511991 / 100000000000000000000) : ℝ) + (1220554047 / 100000000000000000000) + (111489829 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12984

/-! A coarse bound on the actual paper statistics constant at dimension 12985. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12983 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12983 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12983 128 ≤ (13237 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13237 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12985) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12985 : ℕ))
    (by norm_num : (12985 : ℕ) ≤ 16384)
  have ht : paperTail256 12985 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12985 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12985 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12985 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12985 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12985 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12983 128 * √(2 / (12985 : ℝ)) *
      (√(12985 : ℝ) + paperT0 12985 + paperTail256 12985) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12985 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12985 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12985 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12983 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12983 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12985 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12985

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12985 (61 / 100) 164 (17 / (100 * 12985)) (26 / (10 * 12985)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12985 (61 / 100) 164 (17 / (100 * 12985)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (222926069 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (274687497 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2139823927 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12985 / 12985 * (61 / 100)) ^ 4 * inverseRadius8 (12985 - 1) /
            envelopeGap 12985 (61 / 100) 164 (17 / (100 * 12985)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12985

namespace BstLean.Part266.Row12985
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12985 164 ≤ (4335355511 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12985 164 ≤ (1446347799 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (347630199 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12985 164 ≤ (428779031 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12985 164 ≤ (610136143 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12985 164 ≤ (111464071 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (222926069 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (222926069 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (274687497 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2139823927 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((361829 / 100000000) : ℝ) ≤ √(17 / (100 * 12985) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12985) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1055760553 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37059917499 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12985) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12985) ≤ (54455663 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12985) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12985 * (164 : ℝ) ^ 2 + 26 / (10 * 12985) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12985) : ℝ)) (tA 12985 * 164 ^ 2 + 26 / (10 * 12985)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((361829 / 100000000))) * ((222926069 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((361829 / 100000000)) ^ 3) * ((274687497 / 200000000000000000000000))) + ((2139823927 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((361829 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12985) : ℝ)) d.D d.V d.P (√(tA 12985) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((361829 / 100000000)) ^ 2 * (((1055760553 / 500000000000000)) * ((37059917499 / 1000000000000000000)))) + ((2139823927 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12985) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((361829 / 100000000)) * ((222926069 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12985) : ℝ)) (tA 12985 * 164 ^ 2 + 26 / (10 * 12985)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((222926069 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((361829 / 100000000)) ^ 2) * ((274687497 / 200000000000000000000000)) + ((2139823927 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12985) : ℝ)) (√(26 / (10 * 12985) : ℝ)) d.D d.V d.P (√(tA 12985) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((361829 / 100000000)) * (((1055760553 / 500000000000000)) * ((37059917499 / 1000000000000000000))) + ((2139823927 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12985) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((222926069 / 50000000000000000000) : ℝ) + ((2139823927 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12985

namespace BstLean.Part266.Row12985
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12985 164 ∧
    0 ≤ (tableEnvelope C).f1 12985 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12985 164 ∧
    0 ≤ (tableEnvelope C).w1 12985 164 ∧ 0 ≤ (tableEnvelope C).w2 12985 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12985 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12985 164 ∧ 0 ≤ d.f1 12985 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12985 164 ∧ 0 ≤ d.w1 12985 164 ∧ 0 ≤ d.w2 12985 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12985 ≤ 2 * (228 / 100 : ℝ) / 12985 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12985 ≤ 2 * (370 / 100 : ℝ) / 12985 := by
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
    (completeRAData (tableEnvelope C) 12985 164).locationBound 12985 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12985 164).energyBound 12985 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12985 164) (d.f1 12985 164) d.f2 ≤
      32 * (((4335355511 / 1000000000000000000) : ℝ) + (1446347799 / 1000000000000000000) + (347630199 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12985 164) (d.w1 12985 164)
      (d.w2 12985 164) ≤
      32 * (((428779031 / 25000000000000000000) : ℝ) + (610136143 / 50000000000000000000) + (111464071 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12985 164) (d.f1 12985 164) d.f2 ≤
      ((4335355511 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4335355511 / 1000000000000000000)) * ((1446347799 / 1000000000000000000)) * (126 / 100) +
      2 * (((1446347799 / 1000000000000000000)) ^ 2 + 2 * ((4335355511 / 1000000000000000000)) * ((347630199 / 1000000000000000000))) +
      6 * ((1446347799 / 1000000000000000000)) * ((347630199 / 1000000000000000000)) * (126 / 100) + 8 * ((347630199 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12985 164) (d.f1 12985 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12985 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12985 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12985 164) (d.f1 12985 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12985 164) (d.w1 12985 164) (d.w2 12985 164)
  have hwexpr0 : 0 ≤ d.w0 12985 164 + d.w1 12985 164 * √(π / 2) +
      2 * d.w2 12985 164 + energyR16 12985 *
      radiusPolynomialRoot16 (d.w0 12985 164) (d.w1 12985 164) (d.w2 12985 164) := by
    positivity
  constructor
  · change (12985 : ℝ) ^ 8 * (mA 12985 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12985 164) (d.f1 12985 164) d.f2 + locationR16 12985 *
        radiusPolynomialRoot16 (d.f0 12985 164) (d.f1 12985 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12985 : ℝ) ^ 8 * (mA 12985 : ℝ) ^ 8 *
        ((((4335355511 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4335355511 / 1000000000000000000)) * ((1446347799 / 1000000000000000000)) * (126 / 100) +
          2 * (((1446347799 / 1000000000000000000)) ^ 2 + 2 * ((4335355511 / 1000000000000000000)) * ((347630199 / 1000000000000000000))) +
          6 * ((1446347799 / 1000000000000000000)) * ((347630199 / 1000000000000000000)) * (126 / 100) + 8 * ((347630199 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12985) *
          (32 * (((4335355511 / 1000000000000000000) : ℝ) + (1446347799 / 1000000000000000000) + (347630199 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12985 : ℝ) ^ 16 *
      (d.w0 12985 164 + d.w1 12985 164 * √(π / 2) + 2 * d.w2 12985 164 +
        energyR16 12985 * radiusPolynomialRoot16 (d.w0 12985 164) (d.w1 12985 164)
          (d.w2 12985 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12985 : ℝ) ^ 16 *
        (((428779031 / 25000000000000000000) : ℝ) + ((610136143 / 50000000000000000000)) * (126 / 100) + 2 * ((111464071 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12985) *
          (32 * (((428779031 / 25000000000000000000) : ℝ) + (610136143 / 50000000000000000000) + (111464071 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12985

/-! A coarse bound on the actual paper statistics constant at dimension 12986. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12984 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12984 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12984 128 ≤ (13238 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13238 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12986) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12986 : ℕ))
    (by norm_num : (12986 : ℕ) ≤ 16384)
  have ht : paperTail256 12986 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12986 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12986 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12986 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12986 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12986 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12984 128 * √(2 / (12986 : ℝ)) *
      (√(12986 : ℝ) + paperT0 12986 + paperTail256 12986) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12986 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12986 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12986 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12984 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12984 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12986 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12986

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12986 (61 / 100) 164 (17 / (100 * 12986)) (26 / (10 * 12986)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12986 (61 / 100) 164 (17 / (100 * 12986)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (22287457 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (686507233 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4276987241 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12986 / 12986 * (61 / 100)) ^ 4 * inverseRadius8 (12986 - 1) /
            envelopeGap 12986 (61 / 100) 164 (17 / (100 * 12986)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12986

namespace BstLean.Part266.Row12986
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12986 164 ≤ (1083629947 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12986 164 ≤ (1446069099 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86890811 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12986 164 ≤ (1714719687 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12986 164 ≤ (30499757 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12986 164 ≤ (111438321 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (22287457 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (22287457 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (686507233 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4276987241 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3618151 / 1000000000) : ℝ) ≤ √(17 / (100 * 12986) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12986) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2111277197 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37054209829 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12986) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12986) ≤ (108902939 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12986) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12986 * (164 : ℝ) ^ 2 + 26 / (10 * 12986) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12986) : ℝ)) (tA 12986 * 164 ^ 2 + 26 / (10 * 12986)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3618151 / 1000000000))) * ((22287457 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3618151 / 1000000000)) ^ 3) * ((686507233 / 500000000000000000000000))) + ((4276987241 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3618151 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12986) : ℝ)) d.D d.V d.P (√(tA 12986) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3618151 / 1000000000)) ^ 2 * (((2111277197 / 1000000000000000)) * ((37054209829 / 1000000000000000000)))) + ((4276987241 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12986) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3618151 / 1000000000)) * ((22287457 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12986) : ℝ)) (tA 12986 * 164 ^ 2 + 26 / (10 * 12986)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((22287457 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3618151 / 1000000000)) ^ 2) * ((686507233 / 500000000000000000000000)) + ((4276987241 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12986) : ℝ)) (√(26 / (10 * 12986) : ℝ)) d.D d.V d.P (√(tA 12986) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3618151 / 1000000000)) * (((2111277197 / 1000000000000000)) * ((37054209829 / 1000000000000000000))) + ((4276987241 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12986) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((22287457 / 5000000000000000000) : ℝ) + ((4276987241 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12986

namespace BstLean.Part266.Row12986
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12986 164 ∧
    0 ≤ (tableEnvelope C).f1 12986 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12986 164 ∧
    0 ≤ (tableEnvelope C).w1 12986 164 ∧ 0 ≤ (tableEnvelope C).w2 12986 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12986 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12986 164 ∧ 0 ≤ d.f1 12986 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12986 164 ∧ 0 ≤ d.w1 12986 164 ∧ 0 ≤ d.w2 12986 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12986 ≤ 2 * (228 / 100 : ℝ) / 12986 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12986 ≤ 2 * (370 / 100 : ℝ) / 12986 := by
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
    (completeRAData (tableEnvelope C) 12986 164).locationBound 12986 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12986 164).energyBound 12986 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12986 164) (d.f1 12986 164) d.f2 ≤
      32 * (((1083629947 / 250000000000000000) : ℝ) + (1446069099 / 1000000000000000000) + (86890811 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12986 164) (d.w1 12986 164)
      (d.w2 12986 164) ≤
      32 * (((1714719687 / 100000000000000000000) : ℝ) + (30499757 / 2500000000000000000) + (111438321 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12986 164) (d.f1 12986 164) d.f2 ≤
      ((1083629947 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1083629947 / 250000000000000000)) * ((1446069099 / 1000000000000000000)) * (126 / 100) +
      2 * (((1446069099 / 1000000000000000000)) ^ 2 + 2 * ((1083629947 / 250000000000000000)) * ((86890811 / 250000000000000000))) +
      6 * ((1446069099 / 1000000000000000000)) * ((86890811 / 250000000000000000)) * (126 / 100) + 8 * ((86890811 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12986 164) (d.f1 12986 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12986 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12986 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12986 164) (d.f1 12986 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12986 164) (d.w1 12986 164) (d.w2 12986 164)
  have hwexpr0 : 0 ≤ d.w0 12986 164 + d.w1 12986 164 * √(π / 2) +
      2 * d.w2 12986 164 + energyR16 12986 *
      radiusPolynomialRoot16 (d.w0 12986 164) (d.w1 12986 164) (d.w2 12986 164) := by
    positivity
  constructor
  · change (12986 : ℝ) ^ 8 * (mA 12986 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12986 164) (d.f1 12986 164) d.f2 + locationR16 12986 *
        radiusPolynomialRoot16 (d.f0 12986 164) (d.f1 12986 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12986 : ℝ) ^ 8 * (mA 12986 : ℝ) ^ 8 *
        ((((1083629947 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1083629947 / 250000000000000000)) * ((1446069099 / 1000000000000000000)) * (126 / 100) +
          2 * (((1446069099 / 1000000000000000000)) ^ 2 + 2 * ((1083629947 / 250000000000000000)) * ((86890811 / 250000000000000000))) +
          6 * ((1446069099 / 1000000000000000000)) * ((86890811 / 250000000000000000)) * (126 / 100) + 8 * ((86890811 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12986) *
          (32 * (((1083629947 / 250000000000000000) : ℝ) + (1446069099 / 1000000000000000000) + (86890811 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12986 : ℝ) ^ 16 *
      (d.w0 12986 164 + d.w1 12986 164 * √(π / 2) + 2 * d.w2 12986 164 +
        energyR16 12986 * radiusPolynomialRoot16 (d.w0 12986 164) (d.w1 12986 164)
          (d.w2 12986 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12986 : ℝ) ^ 16 *
        (((1714719687 / 100000000000000000000) : ℝ) + ((30499757 / 2500000000000000000)) * (126 / 100) + 2 * ((111438321 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12986) *
          (32 * (((1714719687 / 100000000000000000000) : ℝ) + (30499757 / 2500000000000000000) + (111438321 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12986

/-! A coarse bound on the actual paper statistics constant at dimension 12987. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12985 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12985 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12985 128 ≤ (13239 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13239 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12987) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12987 : ℕ))
    (by norm_num : (12987 : ℕ) ≤ 16384)
  have ht : paperTail256 12987 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12987 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12987 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12987 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12987 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12987 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12985 128 * √(2 / (12987 : ℝ)) *
      (√(12987 : ℝ) + paperT0 12987 + paperTail256 12987) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12987 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12987 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12987 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12985 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12985 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12987 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12987

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12987 (61 / 100) 164 (17 / (100 * 12987)) (26 / (10 * 12987)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12987 (61 / 100) 164 (17 / (100 * 12987)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (17825847 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (137259161 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (427432849 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12987 / 12987 * (61 / 100)) ^ 4 * inverseRadius8 (12987 - 1) /
            envelopeGap 12987 (61 / 100) 164 (17 / (100 * 12987)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12987

namespace BstLean.Part266.Row12987
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12987 164 ≤ (4333684347 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12987 164 ≤ (1445790489 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (347496309 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12987 164 ≤ (857161693 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12987 164 ≤ (1219708369 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12987 164 ≤ (111412579 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (17825847 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (17825847 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (137259161 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (427432849 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((904503 / 250000000) : ℝ) ≤ √(17 / (100 * 12987) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12987) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1055516669 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37048503479 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12987) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12987) ≤ (54447277 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12987) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12987 * (164 : ℝ) ^ 2 + 26 / (10 * 12987) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12987) : ℝ)) (tA 12987 * 164 ^ 2 + 26 / (10 * 12987)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((904503 / 250000000))) * ((17825847 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((904503 / 250000000)) ^ 3) * ((137259161 / 100000000000000000000000))) + ((427432849 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((904503 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12987) : ℝ)) d.D d.V d.P (√(tA 12987) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((904503 / 250000000)) ^ 2 * (((1055516669 / 500000000000000)) * ((37048503479 / 1000000000000000000)))) + ((427432849 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12987) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((904503 / 250000000)) * ((17825847 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12987) : ℝ)) (tA 12987 * 164 ^ 2 + 26 / (10 * 12987)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((17825847 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((904503 / 250000000)) ^ 2) * ((137259161 / 100000000000000000000000)) + ((427432849 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12987) : ℝ)) (√(26 / (10 * 12987) : ℝ)) d.D d.V d.P (√(tA 12987) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((904503 / 250000000)) * (((1055516669 / 500000000000000)) * ((37048503479 / 1000000000000000000))) + ((427432849 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12987) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((17825847 / 4000000000000000000) : ℝ) + ((427432849 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12987

namespace BstLean.Part266.Row12987
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12987 164 ∧
    0 ≤ (tableEnvelope C).f1 12987 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12987 164 ∧
    0 ≤ (tableEnvelope C).w1 12987 164 ∧ 0 ≤ (tableEnvelope C).w2 12987 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12987 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12987 164 ∧ 0 ≤ d.f1 12987 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12987 164 ∧ 0 ≤ d.w1 12987 164 ∧ 0 ≤ d.w2 12987 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12987 ≤ 2 * (228 / 100 : ℝ) / 12987 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12987 ≤ 2 * (370 / 100 : ℝ) / 12987 := by
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
    (completeRAData (tableEnvelope C) 12987 164).locationBound 12987 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12987 164).energyBound 12987 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12987 164) (d.f1 12987 164) d.f2 ≤
      32 * (((4333684347 / 1000000000000000000) : ℝ) + (1445790489 / 1000000000000000000) + (347496309 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12987 164) (d.w1 12987 164)
      (d.w2 12987 164) ≤
      32 * (((857161693 / 50000000000000000000) : ℝ) + (1219708369 / 100000000000000000000) + (111412579 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12987 164) (d.f1 12987 164) d.f2 ≤
      ((4333684347 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4333684347 / 1000000000000000000)) * ((1445790489 / 1000000000000000000)) * (126 / 100) +
      2 * (((1445790489 / 1000000000000000000)) ^ 2 + 2 * ((4333684347 / 1000000000000000000)) * ((347496309 / 1000000000000000000))) +
      6 * ((1445790489 / 1000000000000000000)) * ((347496309 / 1000000000000000000)) * (126 / 100) + 8 * ((347496309 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12987 164) (d.f1 12987 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12987 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12987 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12987 164) (d.f1 12987 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12987 164) (d.w1 12987 164) (d.w2 12987 164)
  have hwexpr0 : 0 ≤ d.w0 12987 164 + d.w1 12987 164 * √(π / 2) +
      2 * d.w2 12987 164 + energyR16 12987 *
      radiusPolynomialRoot16 (d.w0 12987 164) (d.w1 12987 164) (d.w2 12987 164) := by
    positivity
  constructor
  · change (12987 : ℝ) ^ 8 * (mA 12987 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12987 164) (d.f1 12987 164) d.f2 + locationR16 12987 *
        radiusPolynomialRoot16 (d.f0 12987 164) (d.f1 12987 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12987 : ℝ) ^ 8 * (mA 12987 : ℝ) ^ 8 *
        ((((4333684347 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4333684347 / 1000000000000000000)) * ((1445790489 / 1000000000000000000)) * (126 / 100) +
          2 * (((1445790489 / 1000000000000000000)) ^ 2 + 2 * ((4333684347 / 1000000000000000000)) * ((347496309 / 1000000000000000000))) +
          6 * ((1445790489 / 1000000000000000000)) * ((347496309 / 1000000000000000000)) * (126 / 100) + 8 * ((347496309 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12987) *
          (32 * (((4333684347 / 1000000000000000000) : ℝ) + (1445790489 / 1000000000000000000) + (347496309 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12987 : ℝ) ^ 16 *
      (d.w0 12987 164 + d.w1 12987 164 * √(π / 2) + 2 * d.w2 12987 164 +
        energyR16 12987 * radiusPolynomialRoot16 (d.w0 12987 164) (d.w1 12987 164)
          (d.w2 12987 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12987 : ℝ) ^ 16 *
        (((857161693 / 50000000000000000000) : ℝ) + ((1219708369 / 100000000000000000000)) * (126 / 100) + 2 * ((111412579 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12987) *
          (32 * (((857161693 / 50000000000000000000) : ℝ) + (1219708369 / 100000000000000000000) + (111412579 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12987

/-! A coarse bound on the actual paper statistics constant at dimension 12988. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12986 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12986 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12986 128 ≤ (13240 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13240 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12988) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12988 : ℕ))
    (by norm_num : (12988 : ℕ) ≤ 16384)
  have ht : paperTail256 12988 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12988 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12988 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12988 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12988 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12988 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12986 128 * √(2 / (12988 : ℝ)) *
      (√(12988 : ℝ) + paperT0 12988 + paperTail256 12988) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12988 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12988 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12988 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12986 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12986 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12988 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12988

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12988 (61 / 100) 164 (17 / (100 * 12988)) (26 / (10 * 12988)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12988 (61 / 100) 164 (17 / (100 * 12988)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (445543241 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (343042229 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4271671601 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12988 / 12988 * (61 / 100)) ^ 4 * inverseRadius8 (12988 - 1) /
            envelopeGap 12988 (61 / 100) 164 (17 / (100 * 12988)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12988

namespace BstLean.Part266.Row12988
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12988 164 ≤ (135401537 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12988 164 ≤ (289102393 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (347429393 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12988 164 ≤ (107120451 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12988 164 ≤ (1219426547 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12988 164 ≤ (445547379 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (445543241 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (445543241 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (343042229 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4271671601 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3617873 / 1000000000) : ℝ) ≤ √(17 / (100 * 12988) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12988) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2110789523 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37042798437 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12988) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12988) ≤ (108886169 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12988) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12988 * (164 : ℝ) ^ 2 + 26 / (10 * 12988) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12988) : ℝ)) (tA 12988 * 164 ^ 2 + 26 / (10 * 12988)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3617873 / 1000000000))) * ((445543241 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3617873 / 1000000000)) ^ 3) * ((343042229 / 250000000000000000000000))) + ((4271671601 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3617873 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12988) : ℝ)) d.D d.V d.P (√(tA 12988) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3617873 / 1000000000)) ^ 2 * (((2110789523 / 1000000000000000)) * ((37042798437 / 1000000000000000000)))) + ((4271671601 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12988) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3617873 / 1000000000)) * ((445543241 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12988) : ℝ)) (tA 12988 * 164 ^ 2 + 26 / (10 * 12988)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((445543241 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3617873 / 1000000000)) ^ 2) * ((343042229 / 250000000000000000000000)) + ((4271671601 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12988) : ℝ)) (√(26 / (10 * 12988) : ℝ)) d.D d.V d.P (√(tA 12988) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3617873 / 1000000000)) * (((2110789523 / 1000000000000000)) * ((37042798437 / 1000000000000000000))) + ((4271671601 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12988) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((445543241 / 100000000000000000000) : ℝ) + ((4271671601 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12988

namespace BstLean.Part266.Row12988
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12988 164 ∧
    0 ≤ (tableEnvelope C).f1 12988 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12988 164 ∧
    0 ≤ (tableEnvelope C).w1 12988 164 ∧ 0 ≤ (tableEnvelope C).w2 12988 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12988 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12988 164 ∧ 0 ≤ d.f1 12988 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12988 164 ∧ 0 ≤ d.w1 12988 164 ∧ 0 ≤ d.w2 12988 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12988 ≤ 2 * (228 / 100 : ℝ) / 12988 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12988 ≤ 2 * (370 / 100 : ℝ) / 12988 := by
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
    (completeRAData (tableEnvelope C) 12988 164).locationBound 12988 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12988 164).energyBound 12988 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12988 164) (d.f1 12988 164) d.f2 ≤
      32 * (((135401537 / 31250000000000000) : ℝ) + (289102393 / 200000000000000000) + (347429393 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12988 164) (d.w1 12988 164)
      (d.w2 12988 164) ≤
      32 * (((107120451 / 6250000000000000000) : ℝ) + (1219426547 / 100000000000000000000) + (445547379 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12988 164) (d.f1 12988 164) d.f2 ≤
      ((135401537 / 31250000000000000) : ℝ) ^ 2 + 2 * ((135401537 / 31250000000000000)) * ((289102393 / 200000000000000000)) * (126 / 100) +
      2 * (((289102393 / 200000000000000000)) ^ 2 + 2 * ((135401537 / 31250000000000000)) * ((347429393 / 1000000000000000000))) +
      6 * ((289102393 / 200000000000000000)) * ((347429393 / 1000000000000000000)) * (126 / 100) + 8 * ((347429393 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12988 164) (d.f1 12988 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12988 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12988 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12988 164) (d.f1 12988 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12988 164) (d.w1 12988 164) (d.w2 12988 164)
  have hwexpr0 : 0 ≤ d.w0 12988 164 + d.w1 12988 164 * √(π / 2) +
      2 * d.w2 12988 164 + energyR16 12988 *
      radiusPolynomialRoot16 (d.w0 12988 164) (d.w1 12988 164) (d.w2 12988 164) := by
    positivity
  constructor
  · change (12988 : ℝ) ^ 8 * (mA 12988 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12988 164) (d.f1 12988 164) d.f2 + locationR16 12988 *
        radiusPolynomialRoot16 (d.f0 12988 164) (d.f1 12988 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12988 : ℝ) ^ 8 * (mA 12988 : ℝ) ^ 8 *
        ((((135401537 / 31250000000000000) : ℝ) ^ 2 + 2 * ((135401537 / 31250000000000000)) * ((289102393 / 200000000000000000)) * (126 / 100) +
          2 * (((289102393 / 200000000000000000)) ^ 2 + 2 * ((135401537 / 31250000000000000)) * ((347429393 / 1000000000000000000))) +
          6 * ((289102393 / 200000000000000000)) * ((347429393 / 1000000000000000000)) * (126 / 100) + 8 * ((347429393 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12988) *
          (32 * (((135401537 / 31250000000000000) : ℝ) + (289102393 / 200000000000000000) + (347429393 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12988 : ℝ) ^ 16 *
      (d.w0 12988 164 + d.w1 12988 164 * √(π / 2) + 2 * d.w2 12988 164 +
        energyR16 12988 * radiusPolynomialRoot16 (d.w0 12988 164) (d.w1 12988 164)
          (d.w2 12988 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12988 : ℝ) ^ 16 *
        (((107120451 / 6250000000000000000) : ℝ) + ((1219426547 / 100000000000000000000)) * (126 / 100) + 2 * ((445547379 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12988) *
          (32 * (((107120451 / 6250000000000000000) : ℝ) + (1219426547 / 100000000000000000000) + (445547379 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12988

/-! A coarse bound on the actual paper statistics constant at dimension 12989. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12987 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12987 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12987 128 ≤ (13241 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13241 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12989) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12989 : ℕ))
    (by norm_num : (12989 : ℕ) ≤ 16384)
  have ht : paperTail256 12989 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12989 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12989 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12989 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12989 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12989 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12987 128 * √(2 / (12989 : ℝ)) *
      (√(12989 : ℝ) + paperT0 12989 + paperTail256 12989) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12989 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12989 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12989 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12987 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12987 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12989 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12989

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12989 (61 / 100) 165 (17 / (100 * 12989)) (26 / (10 * 12989)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12989 (61 / 100) 165 (17 / (100 * 12989)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (445440339 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (274349277 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4270937903 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12989 / 12989 * (61 / 100)) ^ 4 * inverseRadius8 (12989 - 1) /
            envelopeGap 12989 (61 / 100) 165 (17 / (100 * 12989)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12989

namespace BstLean.Part266.Row12989
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12989 165 ≤ (27075111 / 6250000000000000)
  f1 : (tableEnvelope C).f1 12989 165 ≤ (144523433 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (347362593 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12989 165 ≤ (856765941 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12989 165 ≤ (1219145157 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12989 165 ≤ (445444477 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (445440339 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (445440339 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (274349277 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4270937903 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3617733 / 1000000000) : ℝ) ≤ √(17 / (100 * 12989) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12989) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2110545757 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9259273679 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12989) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12989) ≤ (108877787 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12989) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12989 * (165 : ℝ) ^ 2 + 26 / (10 * 12989) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12989) : ℝ)) (tA 12989 * 165 ^ 2 + 26 / (10 * 12989)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3617733 / 1000000000))) * ((445440339 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3617733 / 1000000000)) ^ 3) * ((274349277 / 200000000000000000000000))) + ((4270937903 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3617733 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12989) : ℝ)) d.D d.V d.P (√(tA 12989) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3617733 / 1000000000)) ^ 2 * (((2110545757 / 1000000000000000)) * ((9259273679 / 250000000000000000)))) + ((4270937903 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12989) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3617733 / 1000000000)) * ((445440339 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12989) : ℝ)) (tA 12989 * 165 ^ 2 + 26 / (10 * 12989)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((445440339 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3617733 / 1000000000)) ^ 2) * ((274349277 / 200000000000000000000000)) + ((4270937903 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12989) : ℝ)) (√(26 / (10 * 12989) : ℝ)) d.D d.V d.P (√(tA 12989) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3617733 / 1000000000)) * (((2110545757 / 1000000000000000)) * ((9259273679 / 250000000000000000))) + ((4270937903 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12989) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((445440339 / 100000000000000000000) : ℝ) + ((4270937903 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12989

namespace BstLean.Part266.Row12989
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12989 165 ∧
    0 ≤ (tableEnvelope C).f1 12989 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12989 165 ∧
    0 ≤ (tableEnvelope C).w1 12989 165 ∧ 0 ≤ (tableEnvelope C).w2 12989 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12989 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12989 165 ∧ 0 ≤ d.f1 12989 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12989 165 ∧ 0 ≤ d.w1 12989 165 ∧ 0 ≤ d.w2 12989 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12989 ≤ 2 * (228 / 100 : ℝ) / 12989 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12989 ≤ 2 * (370 / 100 : ℝ) / 12989 := by
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
    (completeRAData (tableEnvelope C) 12989 165).locationBound 12989 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12989 165).energyBound 12989 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12989 165) (d.f1 12989 165) d.f2 ≤
      32 * (((27075111 / 6250000000000000) : ℝ) + (144523433 / 100000000000000000) + (347362593 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12989 165) (d.w1 12989 165)
      (d.w2 12989 165) ≤
      32 * (((856765941 / 50000000000000000000) : ℝ) + (1219145157 / 100000000000000000000) + (445444477 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12989 165) (d.f1 12989 165) d.f2 ≤
      ((27075111 / 6250000000000000) : ℝ) ^ 2 + 2 * ((27075111 / 6250000000000000)) * ((144523433 / 100000000000000000)) * (126 / 100) +
      2 * (((144523433 / 100000000000000000)) ^ 2 + 2 * ((27075111 / 6250000000000000)) * ((347362593 / 1000000000000000000))) +
      6 * ((144523433 / 100000000000000000)) * ((347362593 / 1000000000000000000)) * (126 / 100) + 8 * ((347362593 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12989 165) (d.f1 12989 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12989 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12989 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12989 165) (d.f1 12989 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12989 165) (d.w1 12989 165) (d.w2 12989 165)
  have hwexpr0 : 0 ≤ d.w0 12989 165 + d.w1 12989 165 * √(π / 2) +
      2 * d.w2 12989 165 + energyR16 12989 *
      radiusPolynomialRoot16 (d.w0 12989 165) (d.w1 12989 165) (d.w2 12989 165) := by
    positivity
  constructor
  · change (12989 : ℝ) ^ 8 * (mA 12989 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12989 165) (d.f1 12989 165) d.f2 + locationR16 12989 *
        radiusPolynomialRoot16 (d.f0 12989 165) (d.f1 12989 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12989 : ℝ) ^ 8 * (mA 12989 : ℝ) ^ 8 *
        ((((27075111 / 6250000000000000) : ℝ) ^ 2 + 2 * ((27075111 / 6250000000000000)) * ((144523433 / 100000000000000000)) * (126 / 100) +
          2 * (((144523433 / 100000000000000000)) ^ 2 + 2 * ((27075111 / 6250000000000000)) * ((347362593 / 1000000000000000000))) +
          6 * ((144523433 / 100000000000000000)) * ((347362593 / 1000000000000000000)) * (126 / 100) + 8 * ((347362593 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12989) *
          (32 * (((27075111 / 6250000000000000) : ℝ) + (144523433 / 100000000000000000) + (347362593 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12989 : ℝ) ^ 16 *
      (d.w0 12989 165 + d.w1 12989 165 * √(π / 2) + 2 * d.w2 12989 165 +
        energyR16 12989 * radiusPolynomialRoot16 (d.w0 12989 165) (d.w1 12989 165)
          (d.w2 12989 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12989 : ℝ) ^ 16 *
        (((856765941 / 50000000000000000000) : ℝ) + ((1219145157 / 100000000000000000000)) * (126 / 100) + 2 * ((445444477 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12989) *
          (32 * (((856765941 / 50000000000000000000) : ℝ) + (1219145157 / 100000000000000000000) + (445444477 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12989

/-! A coarse bound on the actual paper statistics constant at dimension 12990. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12988 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12988 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12988 128 ≤ (13242 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13242 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12990) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12990 : ℕ))
    (by norm_num : (12990 : ℕ) ≤ 16384)
  have ht : paperTail256 12990 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12990 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12990 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12990 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12990 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12990 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12988 128 * √(2 / (12990 : ℝ)) *
      (√(12990 : ℝ) + paperT0 12990 + paperTail256 12990) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12990 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12990 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12990 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12988 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12988 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12990 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12990

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12990 (61 / 100) 165 (17 / (100 * 12990)) (26 / (10 * 12990)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12990 (61 / 100) 165 (17 / (100 * 12990)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (111334367 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1371324017 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (106707081 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12990 / 12990 * (61 / 100)) ^ 4 * inverseRadius8 (12990 - 1) /
            envelopeGap 12990 (61 / 100) 165 (17 / (100 * 12990)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12990

namespace BstLean.Part266.Row12990
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12990 165 ≤ (4331183159 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12990 165 ≤ (722477991 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86823929 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12990 165 ≤ (1713135979 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12990 165 ≤ (7617897 / 625000000000000000)
  w2 : (tableEnvelope C).w2 12990 165 ≤ (445341603 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (111334367 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (111334367 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1371324017 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (106707081 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1808797 / 500000000) : ℝ) ≤ √(17 / (100 * 12990) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12990) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (527575509 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18515696159 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12990) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12990) ≤ (21773881 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12990) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12990 * (165 : ℝ) ^ 2 + 26 / (10 * 12990) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12990) : ℝ)) (tA 12990 * 165 ^ 2 + 26 / (10 * 12990)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1808797 / 500000000))) * ((111334367 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1808797 / 500000000)) ^ 3) * ((1371324017 / 1000000000000000000000000))) + ((106707081 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1808797 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12990) : ℝ)) d.D d.V d.P (√(tA 12990) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1808797 / 500000000)) ^ 2 * (((527575509 / 250000000000000)) * ((18515696159 / 500000000000000000)))) + ((106707081 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12990) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1808797 / 500000000)) * ((111334367 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12990) : ℝ)) (tA 12990 * 165 ^ 2 + 26 / (10 * 12990)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((111334367 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1808797 / 500000000)) ^ 2) * ((1371324017 / 1000000000000000000000000)) + ((106707081 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12990) : ℝ)) (√(26 / (10 * 12990) : ℝ)) d.D d.V d.P (√(tA 12990) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1808797 / 500000000)) * (((527575509 / 250000000000000)) * ((18515696159 / 500000000000000000))) + ((106707081 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12990) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((111334367 / 25000000000000000000) : ℝ) + ((106707081 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12990

namespace BstLean.Part266.Row12990
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12990 165 ∧
    0 ≤ (tableEnvelope C).f1 12990 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12990 165 ∧
    0 ≤ (tableEnvelope C).w1 12990 165 ∧ 0 ≤ (tableEnvelope C).w2 12990 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12990 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12990 165 ∧ 0 ≤ d.f1 12990 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12990 165 ∧ 0 ≤ d.w1 12990 165 ∧ 0 ≤ d.w2 12990 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12990 ≤ 2 * (228 / 100 : ℝ) / 12990 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12990 ≤ 2 * (370 / 100 : ℝ) / 12990 := by
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
    (completeRAData (tableEnvelope C) 12990 165).locationBound 12990 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12990 165).energyBound 12990 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12990 165) (d.f1 12990 165) d.f2 ≤
      32 * (((4331183159 / 1000000000000000000) : ℝ) + (722477991 / 500000000000000000) + (86823929 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12990 165) (d.w1 12990 165)
      (d.w2 12990 165) ≤
      32 * (((1713135979 / 100000000000000000000) : ℝ) + (7617897 / 625000000000000000) + (445341603 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12990 165) (d.f1 12990 165) d.f2 ≤
      ((4331183159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4331183159 / 1000000000000000000)) * ((722477991 / 500000000000000000)) * (126 / 100) +
      2 * (((722477991 / 500000000000000000)) ^ 2 + 2 * ((4331183159 / 1000000000000000000)) * ((86823929 / 250000000000000000))) +
      6 * ((722477991 / 500000000000000000)) * ((86823929 / 250000000000000000)) * (126 / 100) + 8 * ((86823929 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12990 165) (d.f1 12990 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12990 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12990 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12990 165) (d.f1 12990 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12990 165) (d.w1 12990 165) (d.w2 12990 165)
  have hwexpr0 : 0 ≤ d.w0 12990 165 + d.w1 12990 165 * √(π / 2) +
      2 * d.w2 12990 165 + energyR16 12990 *
      radiusPolynomialRoot16 (d.w0 12990 165) (d.w1 12990 165) (d.w2 12990 165) := by
    positivity
  constructor
  · change (12990 : ℝ) ^ 8 * (mA 12990 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12990 165) (d.f1 12990 165) d.f2 + locationR16 12990 *
        radiusPolynomialRoot16 (d.f0 12990 165) (d.f1 12990 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12990 : ℝ) ^ 8 * (mA 12990 : ℝ) ^ 8 *
        ((((4331183159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4331183159 / 1000000000000000000)) * ((722477991 / 500000000000000000)) * (126 / 100) +
          2 * (((722477991 / 500000000000000000)) ^ 2 + 2 * ((4331183159 / 1000000000000000000)) * ((86823929 / 250000000000000000))) +
          6 * ((722477991 / 500000000000000000)) * ((86823929 / 250000000000000000)) * (126 / 100) + 8 * ((86823929 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12990) *
          (32 * (((4331183159 / 1000000000000000000) : ℝ) + (722477991 / 500000000000000000) + (86823929 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12990 : ℝ) ^ 16 *
      (d.w0 12990 165 + d.w1 12990 165 * √(π / 2) + 2 * d.w2 12990 165 +
        energyR16 12990 * radiusPolynomialRoot16 (d.w0 12990 165) (d.w1 12990 165)
          (d.w2 12990 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12990 : ℝ) ^ 16 *
        (((1713135979 / 100000000000000000000) : ℝ) + ((7617897 / 625000000000000000)) * (126 / 100) + 2 * ((445341603 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12990) *
          (32 * (((1713135979 / 100000000000000000000) : ℝ) + (7617897 / 625000000000000000) + (445341603 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12990

/-! A coarse bound on the actual paper statistics constant at dimension 12991. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12989 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12989 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12989 128 ≤ (13243 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13243 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12991) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12991 : ℕ))
    (by norm_num : (12991 : ℕ) ≤ 16384)
  have ht : paperTail256 12991 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12991 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12991 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12991 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12991 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12991 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12989 128 * √(2 / (12991 : ℝ)) *
      (√(12991 : ℝ) + paperT0 12991 + paperTail256 12991) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12991 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12991 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12991 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12989 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12989 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12991 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12991

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12991 (61 / 100) 165 (17 / (100 * 12991)) (26 / (10 * 12991)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12991 (61 / 100) 165 (17 / (100 * 12991)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (44523463 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (342725453 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (853126087 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12991 / 12991 * (61 / 100)) ^ 4 * inverseRadius8 (12991 - 1) /
            envelopeGap 12991 (61 / 100) 165 (17 / (100 * 12991)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12991

namespace BstLean.Part266.Row12991
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12991 165 ≤ (4330348841 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12991 165 ≤ (361169431 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17361443 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12991 165 ≤ (171274021 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12991 165 ≤ (1218581977 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12991 165 ≤ (445238763 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (44523463 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (44523463 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (342725453 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (853126087 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((723491 / 200000000) : ℝ) ≤ √(17 / (100 * 12991) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12991) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (422011673 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37025691243 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12991) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12991) ≤ (3401907 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12991) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12991 * (165 : ℝ) ^ 2 + 26 / (10 * 12991) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12991) : ℝ)) (tA 12991 * 165 ^ 2 + 26 / (10 * 12991)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((723491 / 200000000))) * ((44523463 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((723491 / 200000000)) ^ 3) * ((342725453 / 250000000000000000000000))) + ((853126087 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((723491 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12991) : ℝ)) d.D d.V d.P (√(tA 12991) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((723491 / 200000000)) ^ 2 * (((422011673 / 200000000000000)) * ((37025691243 / 1000000000000000000)))) + ((853126087 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12991) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((723491 / 200000000)) * ((44523463 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12991) : ℝ)) (tA 12991 * 165 ^ 2 + 26 / (10 * 12991)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((44523463 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((723491 / 200000000)) ^ 2) * ((342725453 / 250000000000000000000000)) + ((853126087 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12991) : ℝ)) (√(26 / (10 * 12991) : ℝ)) d.D d.V d.P (√(tA 12991) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((723491 / 200000000)) * (((422011673 / 200000000000000)) * ((37025691243 / 1000000000000000000))) + ((853126087 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12991) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((44523463 / 10000000000000000000) : ℝ) + ((853126087 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12991

namespace BstLean.Part266.Row12991
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12991 165 ∧
    0 ≤ (tableEnvelope C).f1 12991 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12991 165 ∧
    0 ≤ (tableEnvelope C).w1 12991 165 ∧ 0 ≤ (tableEnvelope C).w2 12991 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12991 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12991 165 ∧ 0 ≤ d.f1 12991 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12991 165 ∧ 0 ≤ d.w1 12991 165 ∧ 0 ≤ d.w2 12991 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12991 ≤ 2 * (228 / 100 : ℝ) / 12991 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12991 ≤ 2 * (370 / 100 : ℝ) / 12991 := by
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
    (completeRAData (tableEnvelope C) 12991 165).locationBound 12991 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12991 165).energyBound 12991 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12991 165) (d.f1 12991 165) d.f2 ≤
      32 * (((4330348841 / 1000000000000000000) : ℝ) + (361169431 / 250000000000000000) + (17361443 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12991 165) (d.w1 12991 165)
      (d.w2 12991 165) ≤
      32 * (((171274021 / 10000000000000000000) : ℝ) + (1218581977 / 100000000000000000000) + (445238763 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12991 165) (d.f1 12991 165) d.f2 ≤
      ((4330348841 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4330348841 / 1000000000000000000)) * ((361169431 / 250000000000000000)) * (126 / 100) +
      2 * (((361169431 / 250000000000000000)) ^ 2 + 2 * ((4330348841 / 1000000000000000000)) * ((17361443 / 50000000000000000))) +
      6 * ((361169431 / 250000000000000000)) * ((17361443 / 50000000000000000)) * (126 / 100) + 8 * ((17361443 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12991 165) (d.f1 12991 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12991 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12991 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12991 165) (d.f1 12991 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12991 165) (d.w1 12991 165) (d.w2 12991 165)
  have hwexpr0 : 0 ≤ d.w0 12991 165 + d.w1 12991 165 * √(π / 2) +
      2 * d.w2 12991 165 + energyR16 12991 *
      radiusPolynomialRoot16 (d.w0 12991 165) (d.w1 12991 165) (d.w2 12991 165) := by
    positivity
  constructor
  · change (12991 : ℝ) ^ 8 * (mA 12991 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12991 165) (d.f1 12991 165) d.f2 + locationR16 12991 *
        radiusPolynomialRoot16 (d.f0 12991 165) (d.f1 12991 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12991 : ℝ) ^ 8 * (mA 12991 : ℝ) ^ 8 *
        ((((4330348841 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4330348841 / 1000000000000000000)) * ((361169431 / 250000000000000000)) * (126 / 100) +
          2 * (((361169431 / 250000000000000000)) ^ 2 + 2 * ((4330348841 / 1000000000000000000)) * ((17361443 / 50000000000000000))) +
          6 * ((361169431 / 250000000000000000)) * ((17361443 / 50000000000000000)) * (126 / 100) + 8 * ((17361443 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12991) *
          (32 * (((4330348841 / 1000000000000000000) : ℝ) + (361169431 / 250000000000000000) + (17361443 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12991 : ℝ) ^ 16 *
      (d.w0 12991 165 + d.w1 12991 165 * √(π / 2) + 2 * d.w2 12991 165 +
        energyR16 12991 * radiusPolynomialRoot16 (d.w0 12991 165) (d.w1 12991 165)
          (d.w2 12991 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12991 : ℝ) ^ 16 *
        (((171274021 / 10000000000000000000) : ℝ) + ((1218581977 / 100000000000000000000)) * (126 / 100) + 2 * ((445238763 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12991) *
          (32 * (((171274021 / 10000000000000000000) : ℝ) + (1218581977 / 100000000000000000000) + (445238763 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12991

/-! A coarse bound on the actual paper statistics constant at dimension 12992. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12990 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12990 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12990 128 ≤ (13244 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13244 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12992) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12992 : ℕ))
    (by norm_num : (12992 : ℕ) ≤ 16384)
  have ht : paperTail256 12992 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12992 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12992 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12992 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12992 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12992 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12990 128 * √(2 / (12992 : ℝ)) *
      (√(12992 : ℝ) + paperT0 12992 + paperTail256 12992) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12992 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12992 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12992 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12990 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12990 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12992 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12992

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12992 (61 / 100) 165 (17 / (100 * 12992)) (26 / (10 * 12992)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12992 (61 / 100) 165 (17 / (100 * 12992)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (445131823 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (171309971 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4262979487 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12992 / 12992 * (61 / 100)) ^ 4 * inverseRadius8 (12992 - 1) /
            envelopeGap 12992 (61 / 100) 165 (17 / (100 * 12992)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12992

namespace BstLean.Part266.Row12992
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12992 165 ≤ (4329514799 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12992 165 ≤ (22568743 / 15625000000000000)
  f2 : (tableEnvelope C).f2 ≤ (347162023 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12992 165 ≤ (1712344573 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12992 165 ≤ (48732021 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12992 165 ≤ (445135953 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (445131823 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (445131823 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (171309971 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4262979487 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((904329 / 250000000) : ℝ) ≤ √(17 / (100 * 12992) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12992) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2109814739 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7403998293 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12992) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12992) ≤ (21770529 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12992) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12992 * (165 : ℝ) ^ 2 + 26 / (10 * 12992) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12992) : ℝ)) (tA 12992 * 165 ^ 2 + 26 / (10 * 12992)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((904329 / 250000000))) * ((445131823 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((904329 / 250000000)) ^ 3) * ((171309971 / 125000000000000000000000))) + ((4262979487 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((904329 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12992) : ℝ)) d.D d.V d.P (√(tA 12992) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((904329 / 250000000)) ^ 2 * (((2109814739 / 1000000000000000)) * ((7403998293 / 200000000000000000)))) + ((4262979487 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12992) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((904329 / 250000000)) * ((445131823 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12992) : ℝ)) (tA 12992 * 165 ^ 2 + 26 / (10 * 12992)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((445131823 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((904329 / 250000000)) ^ 2) * ((171309971 / 125000000000000000000000)) + ((4262979487 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12992) : ℝ)) (√(26 / (10 * 12992) : ℝ)) d.D d.V d.P (√(tA 12992) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((904329 / 250000000)) * (((2109814739 / 1000000000000000)) * ((7403998293 / 200000000000000000))) + ((4262979487 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12992) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((445131823 / 100000000000000000000) : ℝ) + ((4262979487 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12992

namespace BstLean.Part266.Row12992
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12992 165 ∧
    0 ≤ (tableEnvelope C).f1 12992 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12992 165 ∧
    0 ≤ (tableEnvelope C).w1 12992 165 ∧ 0 ≤ (tableEnvelope C).w2 12992 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12992 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12992 165 ∧ 0 ≤ d.f1 12992 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12992 165 ∧ 0 ≤ d.w1 12992 165 ∧ 0 ≤ d.w2 12992 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12992 ≤ 2 * (228 / 100 : ℝ) / 12992 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12992 ≤ 2 * (370 / 100 : ℝ) / 12992 := by
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
    (completeRAData (tableEnvelope C) 12992 165).locationBound 12992 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12992 165).energyBound 12992 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12992 165) (d.f1 12992 165) d.f2 ≤
      32 * (((4329514799 / 1000000000000000000) : ℝ) + (22568743 / 15625000000000000) + (347162023 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12992 165) (d.w1 12992 165)
      (d.w2 12992 165) ≤
      32 * (((1712344573 / 100000000000000000000) : ℝ) + (48732021 / 4000000000000000000) + (445135953 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12992 165) (d.f1 12992 165) d.f2 ≤
      ((4329514799 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4329514799 / 1000000000000000000)) * ((22568743 / 15625000000000000)) * (126 / 100) +
      2 * (((22568743 / 15625000000000000)) ^ 2 + 2 * ((4329514799 / 1000000000000000000)) * ((347162023 / 1000000000000000000))) +
      6 * ((22568743 / 15625000000000000)) * ((347162023 / 1000000000000000000)) * (126 / 100) + 8 * ((347162023 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12992 165) (d.f1 12992 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12992 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12992 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12992 165) (d.f1 12992 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12992 165) (d.w1 12992 165) (d.w2 12992 165)
  have hwexpr0 : 0 ≤ d.w0 12992 165 + d.w1 12992 165 * √(π / 2) +
      2 * d.w2 12992 165 + energyR16 12992 *
      radiusPolynomialRoot16 (d.w0 12992 165) (d.w1 12992 165) (d.w2 12992 165) := by
    positivity
  constructor
  · change (12992 : ℝ) ^ 8 * (mA 12992 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12992 165) (d.f1 12992 165) d.f2 + locationR16 12992 *
        radiusPolynomialRoot16 (d.f0 12992 165) (d.f1 12992 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12992 : ℝ) ^ 8 * (mA 12992 : ℝ) ^ 8 *
        ((((4329514799 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4329514799 / 1000000000000000000)) * ((22568743 / 15625000000000000)) * (126 / 100) +
          2 * (((22568743 / 15625000000000000)) ^ 2 + 2 * ((4329514799 / 1000000000000000000)) * ((347162023 / 1000000000000000000))) +
          6 * ((22568743 / 15625000000000000)) * ((347162023 / 1000000000000000000)) * (126 / 100) + 8 * ((347162023 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12992) *
          (32 * (((4329514799 / 1000000000000000000) : ℝ) + (22568743 / 15625000000000000) + (347162023 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12992 : ℝ) ^ 16 *
      (d.w0 12992 165 + d.w1 12992 165 * √(π / 2) + 2 * d.w2 12992 165 +
        energyR16 12992 * radiusPolynomialRoot16 (d.w0 12992 165) (d.w1 12992 165)
          (d.w2 12992 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12992 : ℝ) ^ 16 *
        (((1712344573 / 100000000000000000000) : ℝ) + ((48732021 / 4000000000000000000)) * (126 / 100) + 2 * ((445135953 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12992) *
          (32 * (((1712344573 / 100000000000000000000) : ℝ) + (48732021 / 4000000000000000000) + (445135953 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12992

/-! A coarse bound on the actual paper statistics constant at dimension 12993. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12991 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12991 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12991 128 ≤ (13245 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13245 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12993) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12993 : ℕ))
    (by norm_num : (12993 : ℕ) ≤ 16384)
  have ht : paperTail256 12993 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12993 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12993 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12993 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12993 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12993 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12991 128 * √(2 / (12993 : ℝ)) *
      (√(12993 : ℝ) + paperT0 12993 + paperTail256 12993) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12993 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12993 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12993 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12991 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12991 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12993 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12993

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12993 (61 / 100) 165 (17 / (100 * 12993)) (26 / (10 * 12993)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12993 (61 / 100) 165 (17 / (100 * 12993)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (445029047 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (42814309 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2130165197 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12993 / 12993 * (61 / 100)) ^ 4 * inverseRadius8 (12993 - 1) /
            envelopeGap 12993 (61 / 100) 165 (17 / (100 * 12993)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12993

namespace BstLean.Part266.Row12993
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12993 165 ≤ (270542781 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12993 165 ≤ (288824453 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (3470953 / 10000000000000000)
  w0 : (tableEnvelope C).w0 12993 165 ≤ (1711949771 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12993 165 ≤ (1218019501 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12993 165 ≤ (222516587 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (445029047 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (445029047 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (42814309 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2130165197 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((452147 / 125000000) : ℝ) ≤ √(17 / (100 * 12993) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12993) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1054785579 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1156696657 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12993) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12993) ≤ (27211067 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12993) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12993 * (165 : ℝ) ^ 2 + 26 / (10 * 12993) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12993) : ℝ)) (tA 12993 * 165 ^ 2 + 26 / (10 * 12993)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((452147 / 125000000))) * ((445029047 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((452147 / 125000000)) ^ 3) * ((42814309 / 31250000000000000000000))) + ((2130165197 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((452147 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12993) : ℝ)) d.D d.V d.P (√(tA 12993) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((452147 / 125000000)) ^ 2 * (((1054785579 / 500000000000000)) * ((1156696657 / 31250000000000000)))) + ((2130165197 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12993) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((452147 / 125000000)) * ((445029047 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12993) : ℝ)) (tA 12993 * 165 ^ 2 + 26 / (10 * 12993)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((445029047 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((452147 / 125000000)) ^ 2) * ((42814309 / 31250000000000000000000)) + ((2130165197 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12993) : ℝ)) (√(26 / (10 * 12993) : ℝ)) d.D d.V d.P (√(tA 12993) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((452147 / 125000000)) * (((1054785579 / 500000000000000)) * ((1156696657 / 31250000000000000))) + ((2130165197 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12993) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((445029047 / 100000000000000000000) : ℝ) + ((2130165197 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12993

namespace BstLean.Part266.Row12993
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12993 165 ∧
    0 ≤ (tableEnvelope C).f1 12993 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12993 165 ∧
    0 ≤ (tableEnvelope C).w1 12993 165 ∧ 0 ≤ (tableEnvelope C).w2 12993 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12993 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12993 165 ∧ 0 ≤ d.f1 12993 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12993 165 ∧ 0 ≤ d.w1 12993 165 ∧ 0 ≤ d.w2 12993 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12993 ≤ 2 * (228 / 100 : ℝ) / 12993 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12993 ≤ 2 * (370 / 100 : ℝ) / 12993 := by
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
    (completeRAData (tableEnvelope C) 12993 165).locationBound 12993 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12993 165).energyBound 12993 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12993 165) (d.f1 12993 165) d.f2 ≤
      32 * (((270542781 / 62500000000000000) : ℝ) + (288824453 / 200000000000000000) + (3470953 / 10000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12993 165) (d.w1 12993 165)
      (d.w2 12993 165) ≤
      32 * (((1711949771 / 100000000000000000000) : ℝ) + (1218019501 / 100000000000000000000) + (222516587 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12993 165) (d.f1 12993 165) d.f2 ≤
      ((270542781 / 62500000000000000) : ℝ) ^ 2 + 2 * ((270542781 / 62500000000000000)) * ((288824453 / 200000000000000000)) * (126 / 100) +
      2 * (((288824453 / 200000000000000000)) ^ 2 + 2 * ((270542781 / 62500000000000000)) * ((3470953 / 10000000000000000))) +
      6 * ((288824453 / 200000000000000000)) * ((3470953 / 10000000000000000)) * (126 / 100) + 8 * ((3470953 / 10000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12993 165) (d.f1 12993 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12993 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12993 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12993 165) (d.f1 12993 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12993 165) (d.w1 12993 165) (d.w2 12993 165)
  have hwexpr0 : 0 ≤ d.w0 12993 165 + d.w1 12993 165 * √(π / 2) +
      2 * d.w2 12993 165 + energyR16 12993 *
      radiusPolynomialRoot16 (d.w0 12993 165) (d.w1 12993 165) (d.w2 12993 165) := by
    positivity
  constructor
  · change (12993 : ℝ) ^ 8 * (mA 12993 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12993 165) (d.f1 12993 165) d.f2 + locationR16 12993 *
        radiusPolynomialRoot16 (d.f0 12993 165) (d.f1 12993 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12993 : ℝ) ^ 8 * (mA 12993 : ℝ) ^ 8 *
        ((((270542781 / 62500000000000000) : ℝ) ^ 2 + 2 * ((270542781 / 62500000000000000)) * ((288824453 / 200000000000000000)) * (126 / 100) +
          2 * (((288824453 / 200000000000000000)) ^ 2 + 2 * ((270542781 / 62500000000000000)) * ((3470953 / 10000000000000000))) +
          6 * ((288824453 / 200000000000000000)) * ((3470953 / 10000000000000000)) * (126 / 100) + 8 * ((3470953 / 10000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12993) *
          (32 * (((270542781 / 62500000000000000) : ℝ) + (288824453 / 200000000000000000) + (3470953 / 10000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12993 : ℝ) ^ 16 *
      (d.w0 12993 165 + d.w1 12993 165 * √(π / 2) + 2 * d.w2 12993 165 +
        energyR16 12993 * radiusPolynomialRoot16 (d.w0 12993 165) (d.w1 12993 165)
          (d.w2 12993 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12993 : ℝ) ^ 16 *
        (((1711949771 / 100000000000000000000) : ℝ) + ((1218019501 / 100000000000000000000)) * (126 / 100) + 2 * ((222516587 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12993) *
          (32 * (((1711949771 / 100000000000000000000) : ℝ) + (1218019501 / 100000000000000000000) + (222516587 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12993

/-! A coarse bound on the actual paper statistics constant at dimension 12994. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12992 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12992 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12992 128 ≤ (13246 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13246 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12994) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12994 : ℕ))
    (by norm_num : (12994 : ℕ) ≤ 16384)
  have ht : paperTail256 12994 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12994 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12994 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12994 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12994 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12994 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12992 128 * √(2 / (12994 : ℝ)) *
      (√(12994 : ℝ) + paperT0 12994 + paperTail256 12994) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12994 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12994 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12994 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12992 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12992 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12994 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12994

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12994 (61 / 100) 165 (17 / (100 * 12994)) (26 / (10 * 12994)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12994 (61 / 100) 165 (17 / (100 * 12994)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (444926303 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1369636169 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (851536631 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12994 / 12994 * (61 / 100)) ^ 4 * inverseRadius8 (12994 - 1) /
            envelopeGap 12994 (61 / 100) 165 (17 / (100 * 12994)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12994

namespace BstLean.Part266.Row12994
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12994 165 ≤ (2163925507 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12994 165 ≤ (1443844269 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (173514251 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12994 165 ≤ (2139443 / 125000000000000000)
  w1 : (tableEnvelope C).w1 12994 165 ≤ (1217738233 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12994 165 ≤ (111232607 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (444926303 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (444926303 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1369636169 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (851536631 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3617037 / 1000000000) : ℝ) ≤ √(17 / (100 * 12994) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12994) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1054663813 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (925214897 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12994) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12994) ≤ (108835891 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12994) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12994 * (165 : ℝ) ^ 2 + 26 / (10 * 12994) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12994) : ℝ)) (tA 12994 * 165 ^ 2 + 26 / (10 * 12994)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3617037 / 1000000000))) * ((444926303 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3617037 / 1000000000)) ^ 3) * ((1369636169 / 1000000000000000000000000))) + ((851536631 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3617037 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12994) : ℝ)) d.D d.V d.P (√(tA 12994) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3617037 / 1000000000)) ^ 2 * (((1054663813 / 500000000000000)) * ((925214897 / 25000000000000000)))) + ((851536631 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12994) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3617037 / 1000000000)) * ((444926303 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12994) : ℝ)) (tA 12994 * 165 ^ 2 + 26 / (10 * 12994)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((444926303 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3617037 / 1000000000)) ^ 2) * ((1369636169 / 1000000000000000000000000)) + ((851536631 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12994) : ℝ)) (√(26 / (10 * 12994) : ℝ)) d.D d.V d.P (√(tA 12994) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3617037 / 1000000000)) * (((1054663813 / 500000000000000)) * ((925214897 / 25000000000000000))) + ((851536631 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12994) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((444926303 / 100000000000000000000) : ℝ) + ((851536631 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12994

namespace BstLean.Part266.Row12994
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12994 165 ∧
    0 ≤ (tableEnvelope C).f1 12994 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12994 165 ∧
    0 ≤ (tableEnvelope C).w1 12994 165 ∧ 0 ≤ (tableEnvelope C).w2 12994 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12994 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12994 165 ∧ 0 ≤ d.f1 12994 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12994 165 ∧ 0 ≤ d.w1 12994 165 ∧ 0 ≤ d.w2 12994 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12994 ≤ 2 * (228 / 100 : ℝ) / 12994 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12994 ≤ 2 * (370 / 100 : ℝ) / 12994 := by
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
    (completeRAData (tableEnvelope C) 12994 165).locationBound 12994 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12994 165).energyBound 12994 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12994 165) (d.f1 12994 165) d.f2 ≤
      32 * (((2163925507 / 500000000000000000) : ℝ) + (1443844269 / 1000000000000000000) + (173514251 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12994 165) (d.w1 12994 165)
      (d.w2 12994 165) ≤
      32 * (((2139443 / 125000000000000000) : ℝ) + (1217738233 / 100000000000000000000) + (111232607 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12994 165) (d.f1 12994 165) d.f2 ≤
      ((2163925507 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2163925507 / 500000000000000000)) * ((1443844269 / 1000000000000000000)) * (126 / 100) +
      2 * (((1443844269 / 1000000000000000000)) ^ 2 + 2 * ((2163925507 / 500000000000000000)) * ((173514251 / 500000000000000000))) +
      6 * ((1443844269 / 1000000000000000000)) * ((173514251 / 500000000000000000)) * (126 / 100) + 8 * ((173514251 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12994 165) (d.f1 12994 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12994 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12994 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12994 165) (d.f1 12994 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12994 165) (d.w1 12994 165) (d.w2 12994 165)
  have hwexpr0 : 0 ≤ d.w0 12994 165 + d.w1 12994 165 * √(π / 2) +
      2 * d.w2 12994 165 + energyR16 12994 *
      radiusPolynomialRoot16 (d.w0 12994 165) (d.w1 12994 165) (d.w2 12994 165) := by
    positivity
  constructor
  · change (12994 : ℝ) ^ 8 * (mA 12994 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12994 165) (d.f1 12994 165) d.f2 + locationR16 12994 *
        radiusPolynomialRoot16 (d.f0 12994 165) (d.f1 12994 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12994 : ℝ) ^ 8 * (mA 12994 : ℝ) ^ 8 *
        ((((2163925507 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2163925507 / 500000000000000000)) * ((1443844269 / 1000000000000000000)) * (126 / 100) +
          2 * (((1443844269 / 1000000000000000000)) ^ 2 + 2 * ((2163925507 / 500000000000000000)) * ((173514251 / 500000000000000000))) +
          6 * ((1443844269 / 1000000000000000000)) * ((173514251 / 500000000000000000)) * (126 / 100) + 8 * ((173514251 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12994) *
          (32 * (((2163925507 / 500000000000000000) : ℝ) + (1443844269 / 1000000000000000000) + (173514251 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12994 : ℝ) ^ 16 *
      (d.w0 12994 165 + d.w1 12994 165 * √(π / 2) + 2 * d.w2 12994 165 +
        energyR16 12994 * radiusPolynomialRoot16 (d.w0 12994 165) (d.w1 12994 165)
          (d.w2 12994 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12994 : ℝ) ^ 16 *
        (((2139443 / 125000000000000000) : ℝ) + ((1217738233 / 100000000000000000000)) * (126 / 100) + 2 * ((111232607 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12994) *
          (32 * (((2139443 / 125000000000000000) : ℝ) + (1217738233 / 100000000000000000000) + (111232607 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12994

/-! A coarse bound on the actual paper statistics constant at dimension 12995. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12993 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12993 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12993 128 ≤ (13247 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13247 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12995) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12995 : ℕ))
    (by norm_num : (12995 : ℕ) ≤ 16384)
  have ht : paperTail256 12995 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12995 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12995 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12995 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12995 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12995 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12993 128 * √(2 / (12995 : ℝ)) *
      (√(12995 : ℝ) + paperT0 12995 + paperTail256 12995) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12995 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12995 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12995 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12993 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12993 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12995 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12995

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12995 (61 / 100) 165 (17 / (100 * 12995)) (26 / (10 * 12995)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12995 (61 / 100) 165 (17 / (100 * 12995)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (444823591 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1369214613 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (531879721 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12995 / 12995 * (61 / 100)) ^ 4 * inverseRadius8 (12995 - 1) /
            envelopeGap 12995 (61 / 100) 165 (17 / (100 * 12995)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12995

namespace BstLean.Part266.Row12995
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12995 165 ≤ (865403563 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12995 165 ≤ (1443566361 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (346961723 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12995 165 ≤ (1711159163 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12995 165 ≤ (1217457057 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12995 165 ≤ (444827713 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (444823591 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (444823591 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1369214613 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (531879721 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1808449 / 500000000) : ℝ) ≤ √(17 / (100 * 12995) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12995) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2109084141 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37002900063 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12995) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12995) ≤ (27206879 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12995) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12995 * (165 : ℝ) ^ 2 + 26 / (10 * 12995) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12995) : ℝ)) (tA 12995 * 165 ^ 2 + 26 / (10 * 12995)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1808449 / 500000000))) * ((444823591 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1808449 / 500000000)) ^ 3) * ((1369214613 / 1000000000000000000000000))) + ((531879721 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1808449 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12995) : ℝ)) d.D d.V d.P (√(tA 12995) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1808449 / 500000000)) ^ 2 * (((2109084141 / 1000000000000000)) * ((37002900063 / 1000000000000000000)))) + ((531879721 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12995) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1808449 / 500000000)) * ((444823591 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12995) : ℝ)) (tA 12995 * 165 ^ 2 + 26 / (10 * 12995)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((444823591 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1808449 / 500000000)) ^ 2) * ((1369214613 / 1000000000000000000000000)) + ((531879721 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12995) : ℝ)) (√(26 / (10 * 12995) : ℝ)) d.D d.V d.P (√(tA 12995) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1808449 / 500000000)) * (((2109084141 / 1000000000000000)) * ((37002900063 / 1000000000000000000))) + ((531879721 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12995) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((444823591 / 100000000000000000000) : ℝ) + ((531879721 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12995

namespace BstLean.Part266.Row12995
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12995 165 ∧
    0 ≤ (tableEnvelope C).f1 12995 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12995 165 ∧
    0 ≤ (tableEnvelope C).w1 12995 165 ∧ 0 ≤ (tableEnvelope C).w2 12995 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12995 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12995 165 ∧ 0 ≤ d.f1 12995 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12995 165 ∧ 0 ≤ d.w1 12995 165 ∧ 0 ≤ d.w2 12995 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12995 ≤ 2 * (228 / 100 : ℝ) / 12995 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12995 ≤ 2 * (370 / 100 : ℝ) / 12995 := by
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
    (completeRAData (tableEnvelope C) 12995 165).locationBound 12995 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12995 165).energyBound 12995 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12995 165) (d.f1 12995 165) d.f2 ≤
      32 * (((865403563 / 200000000000000000) : ℝ) + (1443566361 / 1000000000000000000) + (346961723 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12995 165) (d.w1 12995 165)
      (d.w2 12995 165) ≤
      32 * (((1711159163 / 100000000000000000000) : ℝ) + (1217457057 / 100000000000000000000) + (444827713 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12995 165) (d.f1 12995 165) d.f2 ≤
      ((865403563 / 200000000000000000) : ℝ) ^ 2 + 2 * ((865403563 / 200000000000000000)) * ((1443566361 / 1000000000000000000)) * (126 / 100) +
      2 * (((1443566361 / 1000000000000000000)) ^ 2 + 2 * ((865403563 / 200000000000000000)) * ((346961723 / 1000000000000000000))) +
      6 * ((1443566361 / 1000000000000000000)) * ((346961723 / 1000000000000000000)) * (126 / 100) + 8 * ((346961723 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12995 165) (d.f1 12995 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12995 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12995 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12995 165) (d.f1 12995 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12995 165) (d.w1 12995 165) (d.w2 12995 165)
  have hwexpr0 : 0 ≤ d.w0 12995 165 + d.w1 12995 165 * √(π / 2) +
      2 * d.w2 12995 165 + energyR16 12995 *
      radiusPolynomialRoot16 (d.w0 12995 165) (d.w1 12995 165) (d.w2 12995 165) := by
    positivity
  constructor
  · change (12995 : ℝ) ^ 8 * (mA 12995 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12995 165) (d.f1 12995 165) d.f2 + locationR16 12995 *
        radiusPolynomialRoot16 (d.f0 12995 165) (d.f1 12995 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12995 : ℝ) ^ 8 * (mA 12995 : ℝ) ^ 8 *
        ((((865403563 / 200000000000000000) : ℝ) ^ 2 + 2 * ((865403563 / 200000000000000000)) * ((1443566361 / 1000000000000000000)) * (126 / 100) +
          2 * (((1443566361 / 1000000000000000000)) ^ 2 + 2 * ((865403563 / 200000000000000000)) * ((346961723 / 1000000000000000000))) +
          6 * ((1443566361 / 1000000000000000000)) * ((346961723 / 1000000000000000000)) * (126 / 100) + 8 * ((346961723 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12995) *
          (32 * (((865403563 / 200000000000000000) : ℝ) + (1443566361 / 1000000000000000000) + (346961723 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12995 : ℝ) ^ 16 *
      (d.w0 12995 165 + d.w1 12995 165 * √(π / 2) + 2 * d.w2 12995 165 +
        energyR16 12995 * radiusPolynomialRoot16 (d.w0 12995 165) (d.w1 12995 165)
          (d.w2 12995 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12995 : ℝ) ^ 16 *
        (((1711159163 / 100000000000000000000) : ℝ) + ((1217457057 / 100000000000000000000)) * (126 / 100) + 2 * ((444827713 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12995) *
          (32 * (((1711159163 / 100000000000000000000) : ℝ) + (1217457057 / 100000000000000000000) + (444827713 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12995

/-! A coarse bound on the actual paper statistics constant at dimension 12996. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12994 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12994 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12994 128 ≤ (13248 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13248 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12996) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12996 : ℕ))
    (by norm_num : (12996 : ℕ) ≤ 16384)
  have ht : paperTail256 12996 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12996 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12996 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12996 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12996 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12996 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 12994 128 * √(2 / (12996 : ℝ)) *
      (√(12996 : ℝ) + paperT0 12996 + paperTail256 12996) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12996 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12996 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12996 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12994 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12994 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12996 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12996

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12996 (61 / 100) 165 (17 / (100 * 12996)) (26 / (10 * 12996)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12996 (61 / 100) 165 (17 / (100 * 12996)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (444720911 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1368793219 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (531549279 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12996 / 12996 * (61 / 100)) ^ 4 * inverseRadius8 (12996 - 1) /
            envelopeGap 12996 (61 / 100) 165 (17 / (100 * 12996)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12996

namespace BstLean.Part266.Row12996
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12996 165 ≤ (865236979 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12996 165 ≤ (72164427 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (86723741 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12996 165 ≤ (1710764059 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12996 165 ≤ (608587987 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12996 165 ≤ (444725031 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (444720911 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (444720911 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1368793219 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (531549279 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3616759 / 1000000000) : ℝ) ≤ √(17 / (100 * 12996) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12996) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2108840703 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36997205557 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12996) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12996) ≤ (54409571 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12996) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12996 * (165 : ℝ) ^ 2 + 26 / (10 * 12996) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12996) : ℝ)) (tA 12996 * 165 ^ 2 + 26 / (10 * 12996)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3616759 / 1000000000))) * ((444720911 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3616759 / 1000000000)) ^ 3) * ((1368793219 / 1000000000000000000000000))) + ((531549279 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3616759 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12996) : ℝ)) d.D d.V d.P (√(tA 12996) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3616759 / 1000000000)) ^ 2 * (((2108840703 / 1000000000000000)) * ((36997205557 / 1000000000000000000)))) + ((531549279 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12996) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3616759 / 1000000000)) * ((444720911 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12996) : ℝ)) (tA 12996 * 165 ^ 2 + 26 / (10 * 12996)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((444720911 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3616759 / 1000000000)) ^ 2) * ((1368793219 / 1000000000000000000000000)) + ((531549279 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12996) : ℝ)) (√(26 / (10 * 12996) : ℝ)) d.D d.V d.P (√(tA 12996) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3616759 / 1000000000)) * (((2108840703 / 1000000000000000)) * ((36997205557 / 1000000000000000000))) + ((531549279 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12996) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((444720911 / 100000000000000000000) : ℝ) + ((531549279 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12996

namespace BstLean.Part266.Row12996
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12996 165 ∧
    0 ≤ (tableEnvelope C).f1 12996 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12996 165 ∧
    0 ≤ (tableEnvelope C).w1 12996 165 ∧ 0 ≤ (tableEnvelope C).w2 12996 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12996 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12996 165 ∧ 0 ≤ d.f1 12996 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12996 165 ∧ 0 ≤ d.w1 12996 165 ∧ 0 ≤ d.w2 12996 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12996 ≤ 2 * (228 / 100 : ℝ) / 12996 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12996 ≤ 2 * (370 / 100 : ℝ) / 12996 := by
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
    (completeRAData (tableEnvelope C) 12996 165).locationBound 12996 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12996 165).energyBound 12996 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12996 165) (d.f1 12996 165) d.f2 ≤
      32 * (((865236979 / 200000000000000000) : ℝ) + (72164427 / 50000000000000000) + (86723741 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12996 165) (d.w1 12996 165)
      (d.w2 12996 165) ≤
      32 * (((1710764059 / 100000000000000000000) : ℝ) + (608587987 / 50000000000000000000) + (444725031 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12996 165) (d.f1 12996 165) d.f2 ≤
      ((865236979 / 200000000000000000) : ℝ) ^ 2 + 2 * ((865236979 / 200000000000000000)) * ((72164427 / 50000000000000000)) * (126 / 100) +
      2 * (((72164427 / 50000000000000000)) ^ 2 + 2 * ((865236979 / 200000000000000000)) * ((86723741 / 250000000000000000))) +
      6 * ((72164427 / 50000000000000000)) * ((86723741 / 250000000000000000)) * (126 / 100) + 8 * ((86723741 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12996 165) (d.f1 12996 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12996 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12996 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12996 165) (d.f1 12996 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12996 165) (d.w1 12996 165) (d.w2 12996 165)
  have hwexpr0 : 0 ≤ d.w0 12996 165 + d.w1 12996 165 * √(π / 2) +
      2 * d.w2 12996 165 + energyR16 12996 *
      radiusPolynomialRoot16 (d.w0 12996 165) (d.w1 12996 165) (d.w2 12996 165) := by
    positivity
  constructor
  · change (12996 : ℝ) ^ 8 * (mA 12996 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12996 165) (d.f1 12996 165) d.f2 + locationR16 12996 *
        radiusPolynomialRoot16 (d.f0 12996 165) (d.f1 12996 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12996 : ℝ) ^ 8 * (mA 12996 : ℝ) ^ 8 *
        ((((865236979 / 200000000000000000) : ℝ) ^ 2 + 2 * ((865236979 / 200000000000000000)) * ((72164427 / 50000000000000000)) * (126 / 100) +
          2 * (((72164427 / 50000000000000000)) ^ 2 + 2 * ((865236979 / 200000000000000000)) * ((86723741 / 250000000000000000))) +
          6 * ((72164427 / 50000000000000000)) * ((86723741 / 250000000000000000)) * (126 / 100) + 8 * ((86723741 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12996) *
          (32 * (((865236979 / 200000000000000000) : ℝ) + (72164427 / 50000000000000000) + (86723741 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12996 : ℝ) ^ 16 *
      (d.w0 12996 165 + d.w1 12996 165 * √(π / 2) + 2 * d.w2 12996 165 +
        energyR16 12996 * radiusPolynomialRoot16 (d.w0 12996 165) (d.w1 12996 165)
          (d.w2 12996 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12996 : ℝ) ^ 16 *
        (((1710764059 / 100000000000000000000) : ℝ) + ((608587987 / 50000000000000000000)) * (126 / 100) + 2 * ((444725031 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12996) *
          (32 * (((1710764059 / 100000000000000000000) : ℝ) + (608587987 / 50000000000000000000) + (444725031 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12996

/-! A coarse bound on the actual paper statistics constant at dimension 12997. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12995 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12995 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12995 128 ≤ (13249 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13249 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12997) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12997 : ℕ))
    (by norm_num : (12997 : ℕ) ≤ 16384)
  have ht : paperTail256 12997 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12997 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12997 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12997 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12997 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12997 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 12995 128 * √(2 / (12997 : ℝ)) *
      (√(12997 : ℝ) + paperT0 12997 + paperTail256 12997) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12997 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12997 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12997 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12995 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12995 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12997 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12997

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12997 (61 / 100) 165 (17 / (100 * 12997)) (26 / (10 * 12997)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12997 (61 / 100) 165 (17 / (100 * 12997)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (222309131 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1368371987 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (849950509 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12997 / 12997 * (61 / 100)) ^ 4 * inverseRadius8 (12997 - 1) /
            envelopeGap 12997 (61 / 100) 165 (17 / (100 * 12997)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12997

namespace BstLean.Part266.Row12997
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12997 165 ≤ (2162676127 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12997 165 ≤ (180376351 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (13873129 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12997 165 ≤ (1710369087 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12997 165 ≤ (608447491 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12997 165 ≤ (444622379 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (222309131 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (222309131 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1368371987 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (849950509 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((180831 / 50000000) : ℝ) ≤ √(17 / (100 * 12997) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12997) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (32946833 / 15625000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7398302473 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12997) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12997) ≤ (108810769 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12997) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12997 * (165 : ℝ) ^ 2 + 26 / (10 * 12997) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12997) : ℝ)) (tA 12997 * 165 ^ 2 + 26 / (10 * 12997)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((180831 / 50000000))) * ((222309131 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((180831 / 50000000)) ^ 3) * ((1368371987 / 1000000000000000000000000))) + ((849950509 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((180831 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12997) : ℝ)) d.D d.V d.P (√(tA 12997) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((180831 / 50000000)) ^ 2 * (((32946833 / 15625000000000)) * ((7398302473 / 200000000000000000)))) + ((849950509 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12997) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((180831 / 50000000)) * ((222309131 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12997) : ℝ)) (tA 12997 * 165 ^ 2 + 26 / (10 * 12997)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((222309131 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((180831 / 50000000)) ^ 2) * ((1368371987 / 1000000000000000000000000)) + ((849950509 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12997) : ℝ)) (√(26 / (10 * 12997) : ℝ)) d.D d.V d.P (√(tA 12997) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((180831 / 50000000)) * (((32946833 / 15625000000000)) * ((7398302473 / 200000000000000000))) + ((849950509 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12997) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((222309131 / 50000000000000000000) : ℝ) + ((849950509 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12997

namespace BstLean.Part266.Row12997
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12997 165 ∧
    0 ≤ (tableEnvelope C).f1 12997 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12997 165 ∧
    0 ≤ (tableEnvelope C).w1 12997 165 ∧ 0 ≤ (tableEnvelope C).w2 12997 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12997 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12997 165 ∧ 0 ≤ d.f1 12997 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12997 165 ∧ 0 ≤ d.w1 12997 165 ∧ 0 ≤ d.w2 12997 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12997 ≤ 2 * (228 / 100 : ℝ) / 12997 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12997 ≤ 2 * (370 / 100 : ℝ) / 12997 := by
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
    (completeRAData (tableEnvelope C) 12997 165).locationBound 12997 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12997 165).energyBound 12997 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12997 165) (d.f1 12997 165) d.f2 ≤
      32 * (((2162676127 / 500000000000000000) : ℝ) + (180376351 / 125000000000000000) + (13873129 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12997 165) (d.w1 12997 165)
      (d.w2 12997 165) ≤
      32 * (((1710369087 / 100000000000000000000) : ℝ) + (608447491 / 50000000000000000000) + (444622379 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12997 165) (d.f1 12997 165) d.f2 ≤
      ((2162676127 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2162676127 / 500000000000000000)) * ((180376351 / 125000000000000000)) * (126 / 100) +
      2 * (((180376351 / 125000000000000000)) ^ 2 + 2 * ((2162676127 / 500000000000000000)) * ((13873129 / 40000000000000000))) +
      6 * ((180376351 / 125000000000000000)) * ((13873129 / 40000000000000000)) * (126 / 100) + 8 * ((13873129 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12997 165) (d.f1 12997 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12997 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12997 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12997 165) (d.f1 12997 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12997 165) (d.w1 12997 165) (d.w2 12997 165)
  have hwexpr0 : 0 ≤ d.w0 12997 165 + d.w1 12997 165 * √(π / 2) +
      2 * d.w2 12997 165 + energyR16 12997 *
      radiusPolynomialRoot16 (d.w0 12997 165) (d.w1 12997 165) (d.w2 12997 165) := by
    positivity
  constructor
  · change (12997 : ℝ) ^ 8 * (mA 12997 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12997 165) (d.f1 12997 165) d.f2 + locationR16 12997 *
        radiusPolynomialRoot16 (d.f0 12997 165) (d.f1 12997 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12997 : ℝ) ^ 8 * (mA 12997 : ℝ) ^ 8 *
        ((((2162676127 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2162676127 / 500000000000000000)) * ((180376351 / 125000000000000000)) * (126 / 100) +
          2 * (((180376351 / 125000000000000000)) ^ 2 + 2 * ((2162676127 / 500000000000000000)) * ((13873129 / 40000000000000000))) +
          6 * ((180376351 / 125000000000000000)) * ((13873129 / 40000000000000000)) * (126 / 100) + 8 * ((13873129 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12997) *
          (32 * (((2162676127 / 500000000000000000) : ℝ) + (180376351 / 125000000000000000) + (13873129 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12997 : ℝ) ^ 16 *
      (d.w0 12997 165 + d.w1 12997 165 * √(π / 2) + 2 * d.w2 12997 165 +
        energyR16 12997 * radiusPolynomialRoot16 (d.w0 12997 165) (d.w1 12997 165)
          (d.w2 12997 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12997 : ℝ) ^ 16 *
        (((1710369087 / 100000000000000000000) : ℝ) + ((608447491 / 50000000000000000000)) * (126 / 100) + 2 * ((444622379 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12997) *
          (32 * (((1710369087 / 100000000000000000000) : ℝ) + (608447491 / 50000000000000000000) + (444622379 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12997

/-! A coarse bound on the actual paper statistics constant at dimension 12998. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12996 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12996 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12996 128 ≤ (13250 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13250 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12998) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12998 : ℕ))
    (by norm_num : (12998 : ℕ) ≤ 16384)
  have ht : paperTail256 12998 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12998 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12998 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12998 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12998 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12998 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 12996 128 * √(2 / (12998 : ℝ)) *
      (√(12998 : ℝ) + paperT0 12998 + paperTail256 12998) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12998 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12998 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12998 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12996 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12996 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12998 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12998

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12998 (61 / 100) 165 (17 / (100 * 12998)) (26 / (10 * 12998)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12998 (61 / 100) 165 (17 / (100 * 12998)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (111128911 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1367950917 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2123556353 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12998 / 12998 * (61 / 100)) ^ 4 * inverseRadius8 (12998 - 1) /
            envelopeGap 12998 (61 / 100) 165 (17 / (100 * 12998)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12998

namespace BstLean.Part266.Row12998
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12998 165 ≤ (4324519893 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12998 165 ≤ (1442733161 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (10836297 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12998 165 ≤ (1709974247 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12998 165 ≤ (1216614081 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12998 165 ≤ (444519759 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (111128911 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (111128911 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1367950917 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2123556353 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3616481 / 1000000000) : ℝ) ≤ √(17 / (100 * 12998) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12998) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (421670793 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18492910243 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12998) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12998) ≤ (54401199 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12998) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12998 * (165 : ℝ) ^ 2 + 26 / (10 * 12998) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12998) : ℝ)) (tA 12998 * 165 ^ 2 + 26 / (10 * 12998)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3616481 / 1000000000))) * ((111128911 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3616481 / 1000000000)) ^ 3) * ((1367950917 / 1000000000000000000000000))) + ((2123556353 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3616481 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12998) : ℝ)) d.D d.V d.P (√(tA 12998) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3616481 / 1000000000)) ^ 2 * (((421670793 / 200000000000000)) * ((18492910243 / 500000000000000000)))) + ((2123556353 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12998) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3616481 / 1000000000)) * ((111128911 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12998) : ℝ)) (tA 12998 * 165 ^ 2 + 26 / (10 * 12998)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((111128911 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3616481 / 1000000000)) ^ 2) * ((1367950917 / 1000000000000000000000000)) + ((2123556353 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12998) : ℝ)) (√(26 / (10 * 12998) : ℝ)) d.D d.V d.P (√(tA 12998) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3616481 / 1000000000)) * (((421670793 / 200000000000000)) * ((18492910243 / 500000000000000000))) + ((2123556353 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12998) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((111128911 / 25000000000000000000) : ℝ) + ((2123556353 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12998

namespace BstLean.Part266.Row12998
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12998 165 ∧
    0 ≤ (tableEnvelope C).f1 12998 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12998 165 ∧
    0 ≤ (tableEnvelope C).w1 12998 165 ∧ 0 ≤ (tableEnvelope C).w2 12998 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12998 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12998 165 ∧ 0 ≤ d.f1 12998 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12998 165 ∧ 0 ≤ d.w1 12998 165 ∧ 0 ≤ d.w2 12998 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12998 ≤ 2 * (228 / 100 : ℝ) / 12998 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12998 ≤ 2 * (370 / 100 : ℝ) / 12998 := by
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
    (completeRAData (tableEnvelope C) 12998 165).locationBound 12998 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12998 165).energyBound 12998 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12998 165) (d.f1 12998 165) d.f2 ≤
      32 * (((4324519893 / 1000000000000000000) : ℝ) + (1442733161 / 1000000000000000000) + (10836297 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12998 165) (d.w1 12998 165)
      (d.w2 12998 165) ≤
      32 * (((1709974247 / 100000000000000000000) : ℝ) + (1216614081 / 100000000000000000000) + (444519759 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12998 165) (d.f1 12998 165) d.f2 ≤
      ((4324519893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4324519893 / 1000000000000000000)) * ((1442733161 / 1000000000000000000)) * (126 / 100) +
      2 * (((1442733161 / 1000000000000000000)) ^ 2 + 2 * ((4324519893 / 1000000000000000000)) * ((10836297 / 31250000000000000))) +
      6 * ((1442733161 / 1000000000000000000)) * ((10836297 / 31250000000000000)) * (126 / 100) + 8 * ((10836297 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12998 165) (d.f1 12998 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12998 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12998 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12998 165) (d.f1 12998 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12998 165) (d.w1 12998 165) (d.w2 12998 165)
  have hwexpr0 : 0 ≤ d.w0 12998 165 + d.w1 12998 165 * √(π / 2) +
      2 * d.w2 12998 165 + energyR16 12998 *
      radiusPolynomialRoot16 (d.w0 12998 165) (d.w1 12998 165) (d.w2 12998 165) := by
    positivity
  constructor
  · change (12998 : ℝ) ^ 8 * (mA 12998 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12998 165) (d.f1 12998 165) d.f2 + locationR16 12998 *
        radiusPolynomialRoot16 (d.f0 12998 165) (d.f1 12998 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12998 : ℝ) ^ 8 * (mA 12998 : ℝ) ^ 8 *
        ((((4324519893 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4324519893 / 1000000000000000000)) * ((1442733161 / 1000000000000000000)) * (126 / 100) +
          2 * (((1442733161 / 1000000000000000000)) ^ 2 + 2 * ((4324519893 / 1000000000000000000)) * ((10836297 / 31250000000000000))) +
          6 * ((1442733161 / 1000000000000000000)) * ((10836297 / 31250000000000000)) * (126 / 100) + 8 * ((10836297 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12998) *
          (32 * (((4324519893 / 1000000000000000000) : ℝ) + (1442733161 / 1000000000000000000) + (10836297 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12998 : ℝ) ^ 16 *
      (d.w0 12998 165 + d.w1 12998 165 * √(π / 2) + 2 * d.w2 12998 165 +
        energyR16 12998 * radiusPolynomialRoot16 (d.w0 12998 165) (d.w1 12998 165)
          (d.w2 12998 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12998 : ℝ) ^ 16 *
        (((1709974247 / 100000000000000000000) : ℝ) + ((1216614081 / 100000000000000000000)) * (126 / 100) + 2 * ((444519759 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12998) *
          (32 * (((1709974247 / 100000000000000000000) : ℝ) + (1216614081 / 100000000000000000000) + (444519759 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12998

/-! A coarse bound on the actual paper statistics constant at dimension 12999. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12997 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12997 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12997 128 ≤ (13251 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13251 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12999) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12999 : ℕ))
    (by norm_num : (12999 : ℕ) ≤ 16384)
  have ht : paperTail256 12999 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12999 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12999 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12999 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12999 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12999 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 12997 128 * √(2 / (12999 : ℝ)) *
      (√(12999 : ℝ) + paperT0 12999 + paperTail256 12999) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12999 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12999 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12999 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12997 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12997 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12999 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12999

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12999 (61 / 100) 165 (17 / (100 * 12999)) (26 / (10 * 12999)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12999 (61 / 100) 165 (17 / (100 * 12999)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (444413059 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1367530009 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2122237357 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12999 / 12999 * (61 / 100)) ^ 4 * inverseRadius8 (12999 - 1) /
            envelopeGap 12999 (61 / 100) 165 (17 / (100 * 12999)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12999

namespace BstLean.Part266.Row12999
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12999 165 ≤ (4323691263 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12999 165 ≤ (721228201 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (3466949 / 10000000000000000)
  w0 : (tableEnvelope C).w0 12999 165 ≤ (854790121 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12999 165 ≤ (121633361 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12999 165 ≤ (444417171 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (444413059 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (444413059 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1367530009 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2122237357 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3616341 / 1000000000) : ℝ) ≤ √(17 / (100 * 12999) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12999) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2108110669 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18490064961 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12999) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 12999) ≤ (27198507 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12999) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12999 * (165 : ℝ) ^ 2 + 26 / (10 * 12999) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12999) : ℝ)) (tA 12999 * 165 ^ 2 + 26 / (10 * 12999)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3616341 / 1000000000))) * ((444413059 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3616341 / 1000000000)) ^ 3) * ((1367530009 / 1000000000000000000000000))) + ((2122237357 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3616341 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12999) : ℝ)) d.D d.V d.P (√(tA 12999) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3616341 / 1000000000)) ^ 2 * (((2108110669 / 1000000000000000)) * ((18490064961 / 500000000000000000)))) + ((2122237357 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12999) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3616341 / 1000000000)) * ((444413059 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12999) : ℝ)) (tA 12999 * 165 ^ 2 + 26 / (10 * 12999)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((444413059 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3616341 / 1000000000)) ^ 2) * ((1367530009 / 1000000000000000000000000)) + ((2122237357 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12999) : ℝ)) (√(26 / (10 * 12999) : ℝ)) d.D d.V d.P (√(tA 12999) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3616341 / 1000000000)) * (((2108110669 / 1000000000000000)) * ((18490064961 / 500000000000000000))) + ((2122237357 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12999) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((444413059 / 100000000000000000000) : ℝ) + ((2122237357 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12999

namespace BstLean.Part266.Row12999
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12999 165 ∧
    0 ≤ (tableEnvelope C).f1 12999 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12999 165 ∧
    0 ≤ (tableEnvelope C).w1 12999 165 ∧ 0 ≤ (tableEnvelope C).w2 12999 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12999 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12999 165 ∧ 0 ≤ d.f1 12999 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12999 165 ∧ 0 ≤ d.w1 12999 165 ∧ 0 ≤ d.w2 12999 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12999 ≤ 2 * (228 / 100 : ℝ) / 12999 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12999 ≤ 2 * (370 / 100 : ℝ) / 12999 := by
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
    (completeRAData (tableEnvelope C) 12999 165).locationBound 12999 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12999 165).energyBound 12999 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12999 165) (d.f1 12999 165) d.f2 ≤
      32 * (((4323691263 / 1000000000000000000) : ℝ) + (721228201 / 500000000000000000) + (3466949 / 10000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12999 165) (d.w1 12999 165)
      (d.w2 12999 165) ≤
      32 * (((854790121 / 50000000000000000000) : ℝ) + (121633361 / 10000000000000000000) + (444417171 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12999 165) (d.f1 12999 165) d.f2 ≤
      ((4323691263 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4323691263 / 1000000000000000000)) * ((721228201 / 500000000000000000)) * (126 / 100) +
      2 * (((721228201 / 500000000000000000)) ^ 2 + 2 * ((4323691263 / 1000000000000000000)) * ((3466949 / 10000000000000000))) +
      6 * ((721228201 / 500000000000000000)) * ((3466949 / 10000000000000000)) * (126 / 100) + 8 * ((3466949 / 10000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12999 165) (d.f1 12999 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12999 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12999 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12999 165) (d.f1 12999 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12999 165) (d.w1 12999 165) (d.w2 12999 165)
  have hwexpr0 : 0 ≤ d.w0 12999 165 + d.w1 12999 165 * √(π / 2) +
      2 * d.w2 12999 165 + energyR16 12999 *
      radiusPolynomialRoot16 (d.w0 12999 165) (d.w1 12999 165) (d.w2 12999 165) := by
    positivity
  constructor
  · change (12999 : ℝ) ^ 8 * (mA 12999 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12999 165) (d.f1 12999 165) d.f2 + locationR16 12999 *
        radiusPolynomialRoot16 (d.f0 12999 165) (d.f1 12999 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12999 : ℝ) ^ 8 * (mA 12999 : ℝ) ^ 8 *
        ((((4323691263 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4323691263 / 1000000000000000000)) * ((721228201 / 500000000000000000)) * (126 / 100) +
          2 * (((721228201 / 500000000000000000)) ^ 2 + 2 * ((4323691263 / 1000000000000000000)) * ((3466949 / 10000000000000000))) +
          6 * ((721228201 / 500000000000000000)) * ((3466949 / 10000000000000000)) * (126 / 100) + 8 * ((3466949 / 10000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12999) *
          (32 * (((4323691263 / 1000000000000000000) : ℝ) + (721228201 / 500000000000000000) + (3466949 / 10000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12999 : ℝ) ^ 16 *
      (d.w0 12999 165 + d.w1 12999 165 * √(π / 2) + 2 * d.w2 12999 165 +
        energyR16 12999 * radiusPolynomialRoot16 (d.w0 12999 165) (d.w1 12999 165)
          (d.w2 12999 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12999 : ℝ) ^ 16 *
        (((854790121 / 50000000000000000000) : ℝ) + ((121633361 / 10000000000000000000)) * (126 / 100) + 2 * ((444417171 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12999) *
          (32 * (((854790121 / 50000000000000000000) : ℝ) + (121633361 / 10000000000000000000) + (444417171 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12999
