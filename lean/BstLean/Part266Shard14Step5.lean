import BstLean.Part266Shard14Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12700. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12698 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12698 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12698 128 ≤ (12952 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12952 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12700) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12700 : ℕ))
    (by norm_num : (12700 : ℕ) ≤ 16384)
  have ht : paperTail256 12700 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12700 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12700 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12700 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12700 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12700 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12698 128 * √(2 / (12700 : ℝ)) *
      (√(12700 : ℝ) + paperT0 12700 + paperTail256 12700) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12700 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12700 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12700 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12698 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12698 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12700 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12700

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12700 (61 / 100) 163 (17 / (100 * 12700)) (26 / (10 * 12700)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12700 (61 / 100) 163 (17 / (100 * 12700)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (476548441 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (300187999 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2558729291 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12700 / 12700 * (61 / 100)) ^ 4 * inverseRadius8 (12700 - 1) /
            envelopeGap 12700 (61 / 100) 163 (17 / (100 * 12700)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12700

namespace BstLean.Part266.Row12700
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12700 163 ≤ (4582702809 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12700 163 ≤ (764433599 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (367463783 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12700 163 ≤ (91659969 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12700 163 ≤ (652143157 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12700 163 ≤ (476553399 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (476548441 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (476548441 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (300187999 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2558729291 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457333 / 125000000) : ℝ) ≤ √(17 / (100 * 12700) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12700) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2182998949 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7748393369 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12700) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12700) ≤ (111355399 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12700) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12700 * (163 : ℝ) ^ 2 + 26 / (10 * 12700) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12700) : ℝ)) (tA 12700 * 163 ^ 2 + 26 / (10 * 12700)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457333 / 125000000))) * ((476548441 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457333 / 125000000)) ^ 3) * ((300187999 / 200000000000000000000000))) + ((2558729291 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457333 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12700) : ℝ)) d.D d.V d.P (√(tA 12700) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457333 / 125000000)) ^ 2 * (((2182998949 / 1000000000000000)) * ((7748393369 / 200000000000000000)))) + ((2558729291 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12700) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457333 / 125000000)) * ((476548441 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12700) : ℝ)) (tA 12700 * 163 ^ 2 + 26 / (10 * 12700)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((476548441 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457333 / 125000000)) ^ 2) * ((300187999 / 200000000000000000000000)) + ((2558729291 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12700) : ℝ)) (√(26 / (10 * 12700) : ℝ)) d.D d.V d.P (√(tA 12700) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457333 / 125000000)) * (((2182998949 / 1000000000000000)) * ((7748393369 / 200000000000000000))) + ((2558729291 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12700) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((476548441 / 100000000000000000000) : ℝ) + ((2558729291 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12700

namespace BstLean.Part266.Row12700
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12700 163 ∧
    0 ≤ (tableEnvelope C).f1 12700 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12700 163 ∧
    0 ≤ (tableEnvelope C).w1 12700 163 ∧ 0 ≤ (tableEnvelope C).w2 12700 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12700 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12700 163 ∧ 0 ≤ d.f1 12700 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12700 163 ∧ 0 ≤ d.w1 12700 163 ∧ 0 ≤ d.w2 12700 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12700 ≤ 2 * (228 / 100 : ℝ) / 12700 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12700 ≤ 2 * (370 / 100 : ℝ) / 12700 := by
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
    (completeRAData (tableEnvelope C) 12700 163).locationBound 12700 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12700 163).energyBound 12700 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12700 163) (d.f1 12700 163) d.f2 ≤
      32 * (((4582702809 / 1000000000000000000) : ℝ) + (764433599 / 500000000000000000) + (367463783 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12700 163) (d.w1 12700 163)
      (d.w2 12700 163) ≤
      32 * (((91659969 / 5000000000000000000) : ℝ) + (652143157 / 50000000000000000000) + (476553399 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12700 163) (d.f1 12700 163) d.f2 ≤
      ((4582702809 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4582702809 / 1000000000000000000)) * ((764433599 / 500000000000000000)) * (126 / 100) +
      2 * (((764433599 / 500000000000000000)) ^ 2 + 2 * ((4582702809 / 1000000000000000000)) * ((367463783 / 1000000000000000000))) +
      6 * ((764433599 / 500000000000000000)) * ((367463783 / 1000000000000000000)) * (126 / 100) + 8 * ((367463783 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12700 163) (d.f1 12700 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12700 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12700 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12700 163) (d.f1 12700 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12700 163) (d.w1 12700 163) (d.w2 12700 163)
  have hwexpr0 : 0 ≤ d.w0 12700 163 + d.w1 12700 163 * √(π / 2) +
      2 * d.w2 12700 163 + energyR16 12700 *
      radiusPolynomialRoot16 (d.w0 12700 163) (d.w1 12700 163) (d.w2 12700 163) := by
    positivity
  constructor
  · change (12700 : ℝ) ^ 8 * (mA 12700 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12700 163) (d.f1 12700 163) d.f2 + locationR16 12700 *
        radiusPolynomialRoot16 (d.f0 12700 163) (d.f1 12700 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12700 : ℝ) ^ 8 * (mA 12700 : ℝ) ^ 8 *
        ((((4582702809 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4582702809 / 1000000000000000000)) * ((764433599 / 500000000000000000)) * (126 / 100) +
          2 * (((764433599 / 500000000000000000)) ^ 2 + 2 * ((4582702809 / 1000000000000000000)) * ((367463783 / 1000000000000000000))) +
          6 * ((764433599 / 500000000000000000)) * ((367463783 / 1000000000000000000)) * (126 / 100) + 8 * ((367463783 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12700) *
          (32 * (((4582702809 / 1000000000000000000) : ℝ) + (764433599 / 500000000000000000) + (367463783 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12700 : ℝ) ^ 16 *
      (d.w0 12700 163 + d.w1 12700 163 * √(π / 2) + 2 * d.w2 12700 163 +
        energyR16 12700 * radiusPolynomialRoot16 (d.w0 12700 163) (d.w1 12700 163)
          (d.w2 12700 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12700 : ℝ) ^ 16 *
        (((91659969 / 5000000000000000000) : ℝ) + ((652143157 / 50000000000000000000)) * (126 / 100) + 2 * ((476553399 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12700) *
          (32 * (((91659969 / 5000000000000000000) : ℝ) + (652143157 / 50000000000000000000) + (476553399 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12700

/-! A coarse bound on the actual paper statistics constant at dimension 12701. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12699 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12699 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12699 128 ≤ (12953 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12953 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12701) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12701 : ℕ))
    (by norm_num : (12701 : ℕ) ≤ 16384)
  have ht : paperTail256 12701 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12701 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12701 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12701 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12701 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12701 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12699 128 * √(2 / (12701 : ℝ)) *
      (√(12701 : ℝ) + paperT0 12701 + paperTail256 12701) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12701 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12701 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12701 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12699 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12699 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12701 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12701

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12701 (61 / 100) 163 (17 / (100 * 12701)) (26 / (10 * 12701)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12701 (61 / 100) 163 (17 / (100 * 12701)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (476435883 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (375116833 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5114204751 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12701 / 12701 * (61 / 100)) ^ 4 * inverseRadius8 (12701 - 1) /
            envelopeGap 12701 (61 / 100) 163 (17 / (100 * 12701)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12701

namespace BstLean.Part266.Row12701
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12701 163 ≤ (572725081 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12701 163 ≤ (382141559 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (7347829 / 20000000000000000)
  w0 : (tableEnvelope C).w0 12701 163 ≤ (916383181 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12701 163 ≤ (325994559 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12701 163 ≤ (238220419 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (476435883 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (476435883 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (375116833 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5114204751 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((91463 / 25000000) : ℝ) ≤ √(17 / (100 * 12701) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12701) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (272842641 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38735866223 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12701) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12701) ≤ (13918329 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12701) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12701 * (163 : ℝ) ^ 2 + 26 / (10 * 12701) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12701) : ℝ)) (tA 12701 * 163 ^ 2 + 26 / (10 * 12701)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((91463 / 25000000))) * ((476435883 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((91463 / 25000000)) ^ 3) * ((375116833 / 250000000000000000000000))) + ((5114204751 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((91463 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12701) : ℝ)) d.D d.V d.P (√(tA 12701) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((91463 / 25000000)) ^ 2 * (((272842641 / 125000000000000)) * ((38735866223 / 1000000000000000000)))) + ((5114204751 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12701) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((91463 / 25000000)) * ((476435883 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12701) : ℝ)) (tA 12701 * 163 ^ 2 + 26 / (10 * 12701)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((476435883 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((91463 / 25000000)) ^ 2) * ((375116833 / 250000000000000000000000)) + ((5114204751 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12701) : ℝ)) (√(26 / (10 * 12701) : ℝ)) d.D d.V d.P (√(tA 12701) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((91463 / 25000000)) * (((272842641 / 125000000000000)) * ((38735866223 / 1000000000000000000))) + ((5114204751 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12701) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((476435883 / 100000000000000000000) : ℝ) + ((5114204751 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12701

namespace BstLean.Part266.Row12701
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12701 163 ∧
    0 ≤ (tableEnvelope C).f1 12701 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12701 163 ∧
    0 ≤ (tableEnvelope C).w1 12701 163 ∧ 0 ≤ (tableEnvelope C).w2 12701 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12701 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12701 163 ∧ 0 ≤ d.f1 12701 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12701 163 ∧ 0 ≤ d.w1 12701 163 ∧ 0 ≤ d.w2 12701 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12701 ≤ 2 * (228 / 100 : ℝ) / 12701 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12701 ≤ 2 * (370 / 100 : ℝ) / 12701 := by
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
    (completeRAData (tableEnvelope C) 12701 163).locationBound 12701 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12701 163).energyBound 12701 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12701 163) (d.f1 12701 163) d.f2 ≤
      32 * (((572725081 / 125000000000000000) : ℝ) + (382141559 / 250000000000000000) + (7347829 / 20000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12701 163) (d.w1 12701 163)
      (d.w2 12701 163) ≤
      32 * (((916383181 / 50000000000000000000) : ℝ) + (325994559 / 25000000000000000000) + (238220419 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12701 163) (d.f1 12701 163) d.f2 ≤
      ((572725081 / 125000000000000000) : ℝ) ^ 2 + 2 * ((572725081 / 125000000000000000)) * ((382141559 / 250000000000000000)) * (126 / 100) +
      2 * (((382141559 / 250000000000000000)) ^ 2 + 2 * ((572725081 / 125000000000000000)) * ((7347829 / 20000000000000000))) +
      6 * ((382141559 / 250000000000000000)) * ((7347829 / 20000000000000000)) * (126 / 100) + 8 * ((7347829 / 20000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12701 163) (d.f1 12701 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12701 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12701 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12701 163) (d.f1 12701 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12701 163) (d.w1 12701 163) (d.w2 12701 163)
  have hwexpr0 : 0 ≤ d.w0 12701 163 + d.w1 12701 163 * √(π / 2) +
      2 * d.w2 12701 163 + energyR16 12701 *
      radiusPolynomialRoot16 (d.w0 12701 163) (d.w1 12701 163) (d.w2 12701 163) := by
    positivity
  constructor
  · change (12701 : ℝ) ^ 8 * (mA 12701 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12701 163) (d.f1 12701 163) d.f2 + locationR16 12701 *
        radiusPolynomialRoot16 (d.f0 12701 163) (d.f1 12701 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12701 : ℝ) ^ 8 * (mA 12701 : ℝ) ^ 8 *
        ((((572725081 / 125000000000000000) : ℝ) ^ 2 + 2 * ((572725081 / 125000000000000000)) * ((382141559 / 250000000000000000)) * (126 / 100) +
          2 * (((382141559 / 250000000000000000)) ^ 2 + 2 * ((572725081 / 125000000000000000)) * ((7347829 / 20000000000000000))) +
          6 * ((382141559 / 250000000000000000)) * ((7347829 / 20000000000000000)) * (126 / 100) + 8 * ((7347829 / 20000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12701) *
          (32 * (((572725081 / 125000000000000000) : ℝ) + (382141559 / 250000000000000000) + (7347829 / 20000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12701 : ℝ) ^ 16 *
      (d.w0 12701 163 + d.w1 12701 163 * √(π / 2) + 2 * d.w2 12701 163 +
        energyR16 12701 * radiusPolynomialRoot16 (d.w0 12701 163) (d.w1 12701 163)
          (d.w2 12701 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12701 : ℝ) ^ 16 *
        (((916383181 / 50000000000000000000) : ℝ) + ((325994559 / 25000000000000000000)) * (126 / 100) + 2 * ((238220419 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12701) *
          (32 * (((916383181 / 50000000000000000000) : ℝ) + (325994559 / 25000000000000000000) + (238220419 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12701

/-! A coarse bound on the actual paper statistics constant at dimension 12702. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12700 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12700 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12700 128 ≤ (12954 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12954 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12702) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12702 : ℕ))
    (by norm_num : (12702 : ℕ) ≤ 16384)
  have ht : paperTail256 12702 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12702 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12702 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12702 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12702 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12702 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12700 128 * √(2 / (12702 : ℝ)) *
      (√(12702 : ℝ) + paperT0 12702 + paperTail256 12702) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12702 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12702 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12702 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12700 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12700 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12702 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12702

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12702 (61 / 100) 163 (17 / (100 * 12702)) (26 / (10 * 12702)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12702 (61 / 100) 163 (17 / (100 * 12702)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (476323359 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (299998971 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5110953249 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12702 / 12702 * (61 / 100)) ^ 4 * inverseRadius8 (12702 - 1) /
            envelopeGap 12702 (61 / 100) 163 (17 / (100 * 12702)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12702

namespace BstLean.Part266.Row12702
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12702 163 ≤ (1145224699 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12702 163 ≤ (1528265367 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183659569 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12702 163 ≤ (1832333491 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12702 163 ≤ (1303670259 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12702 163 ≤ (47632831 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (476323359 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (476323359 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (299998971 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5110953249 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457297 / 125000000) : ℝ) ≤ √(17 / (100 * 12702) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12702) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1091241677 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38729767041 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12702) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12702) ≤ (55668933 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12702) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12702 * (163 : ℝ) ^ 2 + 26 / (10 * 12702) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12702) : ℝ)) (tA 12702 * 163 ^ 2 + 26 / (10 * 12702)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457297 / 125000000))) * ((476323359 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457297 / 125000000)) ^ 3) * ((299998971 / 200000000000000000000000))) + ((5110953249 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457297 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12702) : ℝ)) d.D d.V d.P (√(tA 12702) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457297 / 125000000)) ^ 2 * (((1091241677 / 500000000000000)) * ((38729767041 / 1000000000000000000)))) + ((5110953249 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12702) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457297 / 125000000)) * ((476323359 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12702) : ℝ)) (tA 12702 * 163 ^ 2 + 26 / (10 * 12702)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((476323359 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457297 / 125000000)) ^ 2) * ((299998971 / 200000000000000000000000)) + ((5110953249 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12702) : ℝ)) (√(26 / (10 * 12702) : ℝ)) d.D d.V d.P (√(tA 12702) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457297 / 125000000)) * (((1091241677 / 500000000000000)) * ((38729767041 / 1000000000000000000))) + ((5110953249 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12702) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((476323359 / 100000000000000000000) : ℝ) + ((5110953249 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12702

namespace BstLean.Part266.Row12702
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12702 163 ∧
    0 ≤ (tableEnvelope C).f1 12702 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12702 163 ∧
    0 ≤ (tableEnvelope C).w1 12702 163 ∧ 0 ≤ (tableEnvelope C).w2 12702 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12702 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12702 163 ∧ 0 ≤ d.f1 12702 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12702 163 ∧ 0 ≤ d.w1 12702 163 ∧ 0 ≤ d.w2 12702 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12702 ≤ 2 * (228 / 100 : ℝ) / 12702 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12702 ≤ 2 * (370 / 100 : ℝ) / 12702 := by
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
    (completeRAData (tableEnvelope C) 12702 163).locationBound 12702 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12702 163).energyBound 12702 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12702 163) (d.f1 12702 163) d.f2 ≤
      32 * (((1145224699 / 250000000000000000) : ℝ) + (1528265367 / 1000000000000000000) + (183659569 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12702 163) (d.w1 12702 163)
      (d.w2 12702 163) ≤
      32 * (((1832333491 / 100000000000000000000) : ℝ) + (1303670259 / 100000000000000000000) + (47632831 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12702 163) (d.f1 12702 163) d.f2 ≤
      ((1145224699 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1145224699 / 250000000000000000)) * ((1528265367 / 1000000000000000000)) * (126 / 100) +
      2 * (((1528265367 / 1000000000000000000)) ^ 2 + 2 * ((1145224699 / 250000000000000000)) * ((183659569 / 500000000000000000))) +
      6 * ((1528265367 / 1000000000000000000)) * ((183659569 / 500000000000000000)) * (126 / 100) + 8 * ((183659569 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12702 163) (d.f1 12702 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12702 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12702 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12702 163) (d.f1 12702 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12702 163) (d.w1 12702 163) (d.w2 12702 163)
  have hwexpr0 : 0 ≤ d.w0 12702 163 + d.w1 12702 163 * √(π / 2) +
      2 * d.w2 12702 163 + energyR16 12702 *
      radiusPolynomialRoot16 (d.w0 12702 163) (d.w1 12702 163) (d.w2 12702 163) := by
    positivity
  constructor
  · change (12702 : ℝ) ^ 8 * (mA 12702 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12702 163) (d.f1 12702 163) d.f2 + locationR16 12702 *
        radiusPolynomialRoot16 (d.f0 12702 163) (d.f1 12702 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12702 : ℝ) ^ 8 * (mA 12702 : ℝ) ^ 8 *
        ((((1145224699 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1145224699 / 250000000000000000)) * ((1528265367 / 1000000000000000000)) * (126 / 100) +
          2 * (((1528265367 / 1000000000000000000)) ^ 2 + 2 * ((1145224699 / 250000000000000000)) * ((183659569 / 500000000000000000))) +
          6 * ((1528265367 / 1000000000000000000)) * ((183659569 / 500000000000000000)) * (126 / 100) + 8 * ((183659569 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12702) *
          (32 * (((1145224699 / 250000000000000000) : ℝ) + (1528265367 / 1000000000000000000) + (183659569 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12702 : ℝ) ^ 16 *
      (d.w0 12702 163 + d.w1 12702 163 * √(π / 2) + 2 * d.w2 12702 163 +
        energyR16 12702 * radiusPolynomialRoot16 (d.w0 12702 163) (d.w1 12702 163)
          (d.w2 12702 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12702 : ℝ) ^ 16 *
        (((1832333491 / 100000000000000000000) : ℝ) + ((1303670259 / 100000000000000000000)) * (126 / 100) + 2 * ((47632831 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12702) *
          (32 * (((1832333491 / 100000000000000000000) : ℝ) + (1303670259 / 100000000000000000000) + (47632831 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12702

/-! A coarse bound on the actual paper statistics constant at dimension 12703. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12701 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12701 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12701 128 ≤ (12955 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12955 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12703) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12703 : ℕ))
    (by norm_num : (12703 : ℕ) ≤ 16384)
  have ht : paperTail256 12703 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12703 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12703 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12703 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12703 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12703 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12701 128 * √(2 / (12703 : ℝ)) *
      (√(12703 : ℝ) + paperT0 12703 + paperTail256 12703) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12703 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12703 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12703 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12701 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12701 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12703 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12703

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12703 (61 / 100) 163 (17 / (100 * 12703)) (26 / (10 * 12703)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12703 (61 / 100) 163 (17 / (100 * 12703)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (59526359 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (299904513 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1276926019 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12703 / 12703 * (61 / 100)) ^ 4 * inverseRadius8 (12703 - 1) /
            envelopeGap 12703 (61 / 100) 163 (17 / (100 * 12703)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12703

namespace BstLean.Part266.Row12703
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12703 163 ≤ (2289998629 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12703 163 ≤ (7639823 / 5000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (717279 / 1953125000000000)
  w0 : (tableEnvelope C).w0 12703 163 ≤ (1831900771 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12703 163 ≤ (325840597 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12703 163 ≤ (23810791 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (59526359 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (59526359 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (299904513 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1276926019 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457279 / 125000000) : ℝ) ≤ √(17 / (100 * 12703) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12703) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (436445127 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38723669313 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12703) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12703) ≤ (111329101 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12703) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12703 * (163 : ℝ) ^ 2 + 26 / (10 * 12703) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12703) : ℝ)) (tA 12703 * 163 ^ 2 + 26 / (10 * 12703)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457279 / 125000000))) * ((59526359 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457279 / 125000000)) ^ 3) * ((299904513 / 200000000000000000000000))) + ((1276926019 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457279 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12703) : ℝ)) d.D d.V d.P (√(tA 12703) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457279 / 125000000)) ^ 2 * (((436445127 / 200000000000000)) * ((38723669313 / 1000000000000000000)))) + ((1276926019 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12703) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457279 / 125000000)) * ((59526359 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12703) : ℝ)) (tA 12703 * 163 ^ 2 + 26 / (10 * 12703)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((59526359 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457279 / 125000000)) ^ 2) * ((299904513 / 200000000000000000000000)) + ((1276926019 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12703) : ℝ)) (√(26 / (10 * 12703) : ℝ)) d.D d.V d.P (√(tA 12703) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457279 / 125000000)) * (((436445127 / 200000000000000)) * ((38723669313 / 1000000000000000000))) + ((1276926019 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12703) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((59526359 / 12500000000000000000) : ℝ) + ((1276926019 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12703

namespace BstLean.Part266.Row12703
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12703 163 ∧
    0 ≤ (tableEnvelope C).f1 12703 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12703 163 ∧
    0 ≤ (tableEnvelope C).w1 12703 163 ∧ 0 ≤ (tableEnvelope C).w2 12703 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12703 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12703 163 ∧ 0 ≤ d.f1 12703 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12703 163 ∧ 0 ≤ d.w1 12703 163 ∧ 0 ≤ d.w2 12703 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12703 ≤ 2 * (228 / 100 : ℝ) / 12703 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12703 ≤ 2 * (370 / 100 : ℝ) / 12703 := by
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
    (completeRAData (tableEnvelope C) 12703 163).locationBound 12703 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12703 163).energyBound 12703 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12703 163) (d.f1 12703 163) d.f2 ≤
      32 * (((2289998629 / 500000000000000000) : ℝ) + (7639823 / 5000000000000000) + (717279 / 1953125000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12703 163) (d.w1 12703 163)
      (d.w2 12703 163) ≤
      32 * (((1831900771 / 100000000000000000000) : ℝ) + (325840597 / 25000000000000000000) + (23810791 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12703 163) (d.f1 12703 163) d.f2 ≤
      ((2289998629 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2289998629 / 500000000000000000)) * ((7639823 / 5000000000000000)) * (126 / 100) +
      2 * (((7639823 / 5000000000000000)) ^ 2 + 2 * ((2289998629 / 500000000000000000)) * ((717279 / 1953125000000000))) +
      6 * ((7639823 / 5000000000000000)) * ((717279 / 1953125000000000)) * (126 / 100) + 8 * ((717279 / 1953125000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12703 163) (d.f1 12703 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12703 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12703 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12703 163) (d.f1 12703 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12703 163) (d.w1 12703 163) (d.w2 12703 163)
  have hwexpr0 : 0 ≤ d.w0 12703 163 + d.w1 12703 163 * √(π / 2) +
      2 * d.w2 12703 163 + energyR16 12703 *
      radiusPolynomialRoot16 (d.w0 12703 163) (d.w1 12703 163) (d.w2 12703 163) := by
    positivity
  constructor
  · change (12703 : ℝ) ^ 8 * (mA 12703 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12703 163) (d.f1 12703 163) d.f2 + locationR16 12703 *
        radiusPolynomialRoot16 (d.f0 12703 163) (d.f1 12703 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12703 : ℝ) ^ 8 * (mA 12703 : ℝ) ^ 8 *
        ((((2289998629 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2289998629 / 500000000000000000)) * ((7639823 / 5000000000000000)) * (126 / 100) +
          2 * (((7639823 / 5000000000000000)) ^ 2 + 2 * ((2289998629 / 500000000000000000)) * ((717279 / 1953125000000000))) +
          6 * ((7639823 / 5000000000000000)) * ((717279 / 1953125000000000)) * (126 / 100) + 8 * ((717279 / 1953125000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12703) *
          (32 * (((2289998629 / 500000000000000000) : ℝ) + (7639823 / 5000000000000000) + (717279 / 1953125000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12703 : ℝ) ^ 16 *
      (d.w0 12703 163 + d.w1 12703 163 * √(π / 2) + 2 * d.w2 12703 163 +
        energyR16 12703 * radiusPolynomialRoot16 (d.w0 12703 163) (d.w1 12703 163)
          (d.w2 12703 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12703 : ℝ) ^ 16 *
        (((1831900771 / 100000000000000000000) : ℝ) + ((325840597 / 25000000000000000000)) * (126 / 100) + 2 * ((23810791 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12703) *
          (32 * (((1831900771 / 100000000000000000000) : ℝ) + (325840597 / 25000000000000000000) + (23810791 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12703

/-! A coarse bound on the actual paper statistics constant at dimension 12704. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12702 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12702 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12702 128 ≤ (12956 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12956 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12704) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12704 : ℕ))
    (by norm_num : (12704 : ℕ) ≤ 16384)
  have ht : paperTail256 12704 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12704 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12704 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12704 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12704 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12704 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12702 128 * √(2 / (12704 : ℝ)) *
      (√(12704 : ℝ) + paperT0 12704 + paperTail256 12704) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12704 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12704 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12704 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12702 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12702 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12704 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12704

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12704 (61 / 100) 163 (17 / (100 * 12704)) (26 / (10 * 12704)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12704 (61 / 100) 163 (17 / (100 * 12704)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (476098419 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (74952523 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1276114307 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12704 / 12704 * (61 / 100)) ^ 4 * inverseRadius8 (12704 - 1) /
            envelopeGap 12704 (61 / 100) 163 (17 / (100 * 12704)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12704

namespace BstLean.Part266.Row12704
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12704 163 ≤ (2289548013 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12704 163 ≤ (763831963 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (18358729 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12704 163 ≤ (915734099 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12704 163 ≤ (1303054617 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12704 163 ≤ (119025841 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (476098419 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (476098419 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (74952523 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1276114307 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457261 / 125000000) : ℝ) ≤ √(17 / (100 * 12704) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12704) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2181967963 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38717573013 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12704) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12704) ≤ (55660169 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12704) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12704 * (163 : ℝ) ^ 2 + 26 / (10 * 12704) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12704) : ℝ)) (tA 12704 * 163 ^ 2 + 26 / (10 * 12704)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457261 / 125000000))) * ((476098419 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457261 / 125000000)) ^ 3) * ((74952523 / 50000000000000000000000))) + ((1276114307 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457261 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12704) : ℝ)) d.D d.V d.P (√(tA 12704) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457261 / 125000000)) ^ 2 * (((2181967963 / 1000000000000000)) * ((38717573013 / 1000000000000000000)))) + ((1276114307 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12704) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457261 / 125000000)) * ((476098419 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12704) : ℝ)) (tA 12704 * 163 ^ 2 + 26 / (10 * 12704)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((476098419 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457261 / 125000000)) ^ 2) * ((74952523 / 50000000000000000000000)) + ((1276114307 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12704) : ℝ)) (√(26 / (10 * 12704) : ℝ)) d.D d.V d.P (√(tA 12704) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457261 / 125000000)) * (((2181967963 / 1000000000000000)) * ((38717573013 / 1000000000000000000))) + ((1276114307 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12704) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((476098419 / 100000000000000000000) : ℝ) + ((1276114307 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12704

namespace BstLean.Part266.Row12704
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12704 163 ∧
    0 ≤ (tableEnvelope C).f1 12704 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12704 163 ∧
    0 ≤ (tableEnvelope C).w1 12704 163 ∧ 0 ≤ (tableEnvelope C).w2 12704 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12704 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12704 163 ∧ 0 ≤ d.f1 12704 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12704 163 ∧ 0 ≤ d.w1 12704 163 ∧ 0 ≤ d.w2 12704 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12704 ≤ 2 * (228 / 100 : ℝ) / 12704 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12704 ≤ 2 * (370 / 100 : ℝ) / 12704 := by
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
    (completeRAData (tableEnvelope C) 12704 163).locationBound 12704 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12704 163).energyBound 12704 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12704 163) (d.f1 12704 163) d.f2 ≤
      32 * (((2289548013 / 500000000000000000) : ℝ) + (763831963 / 500000000000000000) + (18358729 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12704 163) (d.w1 12704 163)
      (d.w2 12704 163) ≤
      32 * (((915734099 / 50000000000000000000) : ℝ) + (1303054617 / 100000000000000000000) + (119025841 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12704 163) (d.f1 12704 163) d.f2 ≤
      ((2289548013 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2289548013 / 500000000000000000)) * ((763831963 / 500000000000000000)) * (126 / 100) +
      2 * (((763831963 / 500000000000000000)) ^ 2 + 2 * ((2289548013 / 500000000000000000)) * ((18358729 / 50000000000000000))) +
      6 * ((763831963 / 500000000000000000)) * ((18358729 / 50000000000000000)) * (126 / 100) + 8 * ((18358729 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12704 163) (d.f1 12704 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12704 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12704 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12704 163) (d.f1 12704 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12704 163) (d.w1 12704 163) (d.w2 12704 163)
  have hwexpr0 : 0 ≤ d.w0 12704 163 + d.w1 12704 163 * √(π / 2) +
      2 * d.w2 12704 163 + energyR16 12704 *
      radiusPolynomialRoot16 (d.w0 12704 163) (d.w1 12704 163) (d.w2 12704 163) := by
    positivity
  constructor
  · change (12704 : ℝ) ^ 8 * (mA 12704 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12704 163) (d.f1 12704 163) d.f2 + locationR16 12704 *
        radiusPolynomialRoot16 (d.f0 12704 163) (d.f1 12704 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12704 : ℝ) ^ 8 * (mA 12704 : ℝ) ^ 8 *
        ((((2289548013 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2289548013 / 500000000000000000)) * ((763831963 / 500000000000000000)) * (126 / 100) +
          2 * (((763831963 / 500000000000000000)) ^ 2 + 2 * ((2289548013 / 500000000000000000)) * ((18358729 / 50000000000000000))) +
          6 * ((763831963 / 500000000000000000)) * ((18358729 / 50000000000000000)) * (126 / 100) + 8 * ((18358729 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12704) *
          (32 * (((2289548013 / 500000000000000000) : ℝ) + (763831963 / 500000000000000000) + (18358729 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12704 : ℝ) ^ 16 *
      (d.w0 12704 163 + d.w1 12704 163 * √(π / 2) + 2 * d.w2 12704 163 +
        energyR16 12704 * radiusPolynomialRoot16 (d.w0 12704 163) (d.w1 12704 163)
          (d.w2 12704 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12704 : ℝ) ^ 16 *
        (((915734099 / 50000000000000000000) : ℝ) + ((1303054617 / 100000000000000000000)) * (126 / 100) + 2 * ((119025841 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12704) *
          (32 * (((915734099 / 50000000000000000000) : ℝ) + (1303054617 / 100000000000000000000) + (119025841 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12704

/-! A coarse bound on the actual paper statistics constant at dimension 12705. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12703 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12703 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12703 128 ≤ (12957 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12957 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12705) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12705 : ℕ))
    (by norm_num : (12705 : ℕ) ≤ 16384)
  have ht : paperTail256 12705 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12705 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12705 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12705 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12705 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12705 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12703 128 * √(2 / (12705 : ℝ)) *
      (√(12705 : ℝ) + paperT0 12705 + paperTail256 12705) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12705 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12705 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12705 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12703 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12703 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12705 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12705

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12705 (61 / 100) 163 (17 / (100 * 12705)) (26 / (10 * 12705)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12705 (61 / 100) 163 (17 / (100 * 12705)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (237993001 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1498578541 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1020242541 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12705 / 12705 * (61 / 100)) ^ 4 * inverseRadius8 (12705 - 1) /
            envelopeGap 12705 (61 / 100) 163 (17 / (100 * 12705)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12705

namespace BstLean.Part266.Row12705
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12705 163 ≤ (2289097553 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12705 163 ≤ (30547267 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (367102333 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12705 163 ≤ (915517887 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12705 163 ≤ (26054939 / 2000000000000000000)
  w2 : (tableEnvelope C).w2 12705 163 ≤ (14874717 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (237993001 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (237993001 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1498578541 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1020242541 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457243 / 125000000) : ℝ) ≤ √(17 / (100 * 12705) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12705) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2181710343 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9677869539 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12705) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12705) ≤ (13913947 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12705) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12705 * (163 : ℝ) ^ 2 + 26 / (10 * 12705) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12705) : ℝ)) (tA 12705 * 163 ^ 2 + 26 / (10 * 12705)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457243 / 125000000))) * ((237993001 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457243 / 125000000)) ^ 3) * ((1498578541 / 1000000000000000000000000))) + ((1020242541 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457243 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12705) : ℝ)) d.D d.V d.P (√(tA 12705) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457243 / 125000000)) ^ 2 * (((2181710343 / 1000000000000000)) * ((9677869539 / 250000000000000000)))) + ((1020242541 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12705) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457243 / 125000000)) * ((237993001 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12705) : ℝ)) (tA 12705 * 163 ^ 2 + 26 / (10 * 12705)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((237993001 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457243 / 125000000)) ^ 2) * ((1498578541 / 1000000000000000000000000)) + ((1020242541 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12705) : ℝ)) (√(26 / (10 * 12705) : ℝ)) d.D d.V d.P (√(tA 12705) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457243 / 125000000)) * (((2181710343 / 1000000000000000)) * ((9677869539 / 250000000000000000))) + ((1020242541 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12705) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((237993001 / 50000000000000000000) : ℝ) + ((1020242541 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12705

namespace BstLean.Part266.Row12705
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12705 163 ∧
    0 ≤ (tableEnvelope C).f1 12705 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12705 163 ∧
    0 ≤ (tableEnvelope C).w1 12705 163 ∧ 0 ≤ (tableEnvelope C).w2 12705 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12705 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12705 163 ∧ 0 ≤ d.f1 12705 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12705 163 ∧ 0 ≤ d.w1 12705 163 ∧ 0 ≤ d.w2 12705 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12705 ≤ 2 * (228 / 100 : ℝ) / 12705 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12705 ≤ 2 * (370 / 100 : ℝ) / 12705 := by
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
    (completeRAData (tableEnvelope C) 12705 163).locationBound 12705 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12705 163).energyBound 12705 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12705 163) (d.f1 12705 163) d.f2 ≤
      32 * (((2289097553 / 500000000000000000) : ℝ) + (30547267 / 20000000000000000) + (367102333 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12705 163) (d.w1 12705 163)
      (d.w2 12705 163) ≤
      32 * (((915517887 / 50000000000000000000) : ℝ) + (26054939 / 2000000000000000000) + (14874717 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12705 163) (d.f1 12705 163) d.f2 ≤
      ((2289097553 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2289097553 / 500000000000000000)) * ((30547267 / 20000000000000000)) * (126 / 100) +
      2 * (((30547267 / 20000000000000000)) ^ 2 + 2 * ((2289097553 / 500000000000000000)) * ((367102333 / 1000000000000000000))) +
      6 * ((30547267 / 20000000000000000)) * ((367102333 / 1000000000000000000)) * (126 / 100) + 8 * ((367102333 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12705 163) (d.f1 12705 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12705 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12705 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12705 163) (d.f1 12705 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12705 163) (d.w1 12705 163) (d.w2 12705 163)
  have hwexpr0 : 0 ≤ d.w0 12705 163 + d.w1 12705 163 * √(π / 2) +
      2 * d.w2 12705 163 + energyR16 12705 *
      radiusPolynomialRoot16 (d.w0 12705 163) (d.w1 12705 163) (d.w2 12705 163) := by
    positivity
  constructor
  · change (12705 : ℝ) ^ 8 * (mA 12705 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12705 163) (d.f1 12705 163) d.f2 + locationR16 12705 *
        radiusPolynomialRoot16 (d.f0 12705 163) (d.f1 12705 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12705 : ℝ) ^ 8 * (mA 12705 : ℝ) ^ 8 *
        ((((2289097553 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2289097553 / 500000000000000000)) * ((30547267 / 20000000000000000)) * (126 / 100) +
          2 * (((30547267 / 20000000000000000)) ^ 2 + 2 * ((2289097553 / 500000000000000000)) * ((367102333 / 1000000000000000000))) +
          6 * ((30547267 / 20000000000000000)) * ((367102333 / 1000000000000000000)) * (126 / 100) + 8 * ((367102333 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12705) *
          (32 * (((2289097553 / 500000000000000000) : ℝ) + (30547267 / 20000000000000000) + (367102333 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12705 : ℝ) ^ 16 *
      (d.w0 12705 163 + d.w1 12705 163 * √(π / 2) + 2 * d.w2 12705 163 +
        energyR16 12705 * radiusPolynomialRoot16 (d.w0 12705 163) (d.w1 12705 163)
          (d.w2 12705 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12705 : ℝ) ^ 16 *
        (((915517887 / 50000000000000000000) : ℝ) + ((26054939 / 2000000000000000000)) * (126 / 100) + 2 * ((14874717 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12705) *
          (32 * (((915517887 / 50000000000000000000) : ℝ) + (26054939 / 2000000000000000000) + (14874717 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12705

/-! A coarse bound on the actual paper statistics constant at dimension 12706. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12704 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12704 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12704 128 ≤ (12958 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12958 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12706) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12706 : ℕ))
    (by norm_num : (12706 : ℕ) ≤ 16384)
  have ht : paperTail256 12706 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12706 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12706 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12706 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12706 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12706 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12704 128 * √(2 / (12706 : ℝ)) *
      (√(12706 : ℝ) + paperT0 12706 + paperTail256 12706) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12706 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12706 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12706 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12704 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12704 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12706 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12706

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12706 (61 / 100) 163 (17 / (100 * 12706)) (26 / (10 * 12706)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12706 (61 / 100) 163 (17 / (100 * 12706)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (475873621 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (187263351 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (637246313 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12706 / 12706 * (61 / 100)) ^ 4 * inverseRadius8 (12706 - 1) /
            envelopeGap 12706 (61 / 100) 163 (17 / (100 * 12706)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12706

namespace BstLean.Part266.Row12706
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12706 163 ≤ (915458899 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12706 163 ≤ (763531437 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (91757527 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12706 163 ≤ (3661207 / 200000000000000000)
  w1 : (tableEnvelope C).w1 12706 163 ≤ (1302439387 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12706 163 ≤ (2974241 / 625000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (475873621 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (475873621 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (187263351 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (637246313 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((18289 / 5000000) : ℝ) ≤ √(17 / (100 * 12706) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12706) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (272681597 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19352692371 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12706) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12706) ≤ (22260563 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12706) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12706 * (163 : ℝ) ^ 2 + 26 / (10 * 12706) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12706) : ℝ)) (tA 12706 * 163 ^ 2 + 26 / (10 * 12706)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((18289 / 5000000))) * ((475873621 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((18289 / 5000000)) ^ 3) * ((187263351 / 125000000000000000000000))) + ((637246313 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((18289 / 5000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12706) : ℝ)) d.D d.V d.P (√(tA 12706) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((18289 / 5000000)) ^ 2 * (((272681597 / 125000000000000)) * ((19352692371 / 500000000000000000)))) + ((637246313 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12706) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((18289 / 5000000)) * ((475873621 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12706) : ℝ)) (tA 12706 * 163 ^ 2 + 26 / (10 * 12706)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((475873621 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((18289 / 5000000)) ^ 2) * ((187263351 / 125000000000000000000000)) + ((637246313 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12706) : ℝ)) (√(26 / (10 * 12706) : ℝ)) d.D d.V d.P (√(tA 12706) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((18289 / 5000000)) * (((272681597 / 125000000000000)) * ((19352692371 / 500000000000000000))) + ((637246313 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12706) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((475873621 / 100000000000000000000) : ℝ) + ((637246313 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12706

namespace BstLean.Part266.Row12706
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12706 163 ∧
    0 ≤ (tableEnvelope C).f1 12706 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12706 163 ∧
    0 ≤ (tableEnvelope C).w1 12706 163 ∧ 0 ≤ (tableEnvelope C).w2 12706 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12706 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12706 163 ∧ 0 ≤ d.f1 12706 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12706 163 ∧ 0 ≤ d.w1 12706 163 ∧ 0 ≤ d.w2 12706 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12706 ≤ 2 * (228 / 100 : ℝ) / 12706 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12706 ≤ 2 * (370 / 100 : ℝ) / 12706 := by
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
    (completeRAData (tableEnvelope C) 12706 163).locationBound 12706 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12706 163).energyBound 12706 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12706 163) (d.f1 12706 163) d.f2 ≤
      32 * (((915458899 / 200000000000000000) : ℝ) + (763531437 / 500000000000000000) + (91757527 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12706 163) (d.w1 12706 163)
      (d.w2 12706 163) ≤
      32 * (((3661207 / 200000000000000000) : ℝ) + (1302439387 / 100000000000000000000) + (2974241 / 625000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12706 163) (d.f1 12706 163) d.f2 ≤
      ((915458899 / 200000000000000000) : ℝ) ^ 2 + 2 * ((915458899 / 200000000000000000)) * ((763531437 / 500000000000000000)) * (126 / 100) +
      2 * (((763531437 / 500000000000000000)) ^ 2 + 2 * ((915458899 / 200000000000000000)) * ((91757527 / 250000000000000000))) +
      6 * ((763531437 / 500000000000000000)) * ((91757527 / 250000000000000000)) * (126 / 100) + 8 * ((91757527 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12706 163) (d.f1 12706 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12706 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12706 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12706 163) (d.f1 12706 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12706 163) (d.w1 12706 163) (d.w2 12706 163)
  have hwexpr0 : 0 ≤ d.w0 12706 163 + d.w1 12706 163 * √(π / 2) +
      2 * d.w2 12706 163 + energyR16 12706 *
      radiusPolynomialRoot16 (d.w0 12706 163) (d.w1 12706 163) (d.w2 12706 163) := by
    positivity
  constructor
  · change (12706 : ℝ) ^ 8 * (mA 12706 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12706 163) (d.f1 12706 163) d.f2 + locationR16 12706 *
        radiusPolynomialRoot16 (d.f0 12706 163) (d.f1 12706 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12706 : ℝ) ^ 8 * (mA 12706 : ℝ) ^ 8 *
        ((((915458899 / 200000000000000000) : ℝ) ^ 2 + 2 * ((915458899 / 200000000000000000)) * ((763531437 / 500000000000000000)) * (126 / 100) +
          2 * (((763531437 / 500000000000000000)) ^ 2 + 2 * ((915458899 / 200000000000000000)) * ((91757527 / 250000000000000000))) +
          6 * ((763531437 / 500000000000000000)) * ((91757527 / 250000000000000000)) * (126 / 100) + 8 * ((91757527 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12706) *
          (32 * (((915458899 / 200000000000000000) : ℝ) + (763531437 / 500000000000000000) + (91757527 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12706 : ℝ) ^ 16 *
      (d.w0 12706 163 + d.w1 12706 163 * √(π / 2) + 2 * d.w2 12706 163 +
        energyR16 12706 * radiusPolynomialRoot16 (d.w0 12706 163) (d.w1 12706 163)
          (d.w2 12706 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12706 : ℝ) ^ 16 *
        (((3661207 / 200000000000000000) : ℝ) + ((1302439387 / 100000000000000000000)) * (126 / 100) + 2 * ((2974241 / 625000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12706) *
          (32 * (((3661207 / 200000000000000000) : ℝ) + (1302439387 / 100000000000000000000) + (2974241 / 625000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12706

/-! A coarse bound on the actual paper statistics constant at dimension 12707. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12705 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12705 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12705 128 ≤ (12959 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12959 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12707) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12707 : ℕ))
    (by norm_num : (12707 : ℕ) ≤ 16384)
  have ht : paperTail256 12707 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12707 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12707 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12707 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12707 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12707 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12705 128 * √(2 / (12707 : ℝ)) *
      (√(12707 : ℝ) + paperT0 12707 + paperTail256 12707) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12707 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12707 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12707 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12705 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12705 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12707 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12707

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12707 (61 / 100) 163 (17 / (100 * 12707)) (26 / (10 * 12707)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12707 (61 / 100) 163 (17 / (100 * 12707)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (237880637 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (74881763 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5094730623 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12707 / 12707 * (61 / 100)) ^ 4 * inverseRadius8 (12707 - 1) /
            envelopeGap 12707 (61 / 100) 163 (17 / (100 * 12707)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12707

namespace BstLean.Part266.Row12707
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12707 163 ≤ (286024637 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12707 163 ≤ (152676249 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22934869 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12707 163 ≤ (1830171373 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12707 163 ≤ (325532981 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12707 163 ≤ (47576621 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (237880637 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (237880637 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (74881763 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5094730623 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457207 / 125000000) : ℝ) ≤ √(17 / (100 * 12707) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12707) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (436239051 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38699292759 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12707) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12707) ≤ (13911757 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12707) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12707 * (163 : ℝ) ^ 2 + 26 / (10 * 12707) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12707) : ℝ)) (tA 12707 * 163 ^ 2 + 26 / (10 * 12707)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457207 / 125000000))) * ((237880637 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457207 / 125000000)) ^ 3) * ((74881763 / 50000000000000000000000))) + ((5094730623 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457207 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12707) : ℝ)) d.D d.V d.P (√(tA 12707) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457207 / 125000000)) ^ 2 * (((436239051 / 200000000000000)) * ((38699292759 / 1000000000000000000)))) + ((5094730623 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12707) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457207 / 125000000)) * ((237880637 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12707) : ℝ)) (tA 12707 * 163 ^ 2 + 26 / (10 * 12707)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((237880637 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457207 / 125000000)) ^ 2) * ((74881763 / 50000000000000000000000)) + ((5094730623 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12707) : ℝ)) (√(26 / (10 * 12707) : ℝ)) d.D d.V d.P (√(tA 12707) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457207 / 125000000)) * (((436239051 / 200000000000000)) * ((38699292759 / 1000000000000000000))) + ((5094730623 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12707) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((237880637 / 50000000000000000000) : ℝ) + ((5094730623 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12707

namespace BstLean.Part266.Row12707
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12707 163 ∧
    0 ≤ (tableEnvelope C).f1 12707 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12707 163 ∧
    0 ≤ (tableEnvelope C).w1 12707 163 ∧ 0 ≤ (tableEnvelope C).w2 12707 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12707 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12707 163 ∧ 0 ≤ d.f1 12707 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12707 163 ∧ 0 ≤ d.w1 12707 163 ∧ 0 ≤ d.w2 12707 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12707 ≤ 2 * (228 / 100 : ℝ) / 12707 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12707 ≤ 2 * (370 / 100 : ℝ) / 12707 := by
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
    (completeRAData (tableEnvelope C) 12707 163).locationBound 12707 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12707 163).energyBound 12707 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12707 163) (d.f1 12707 163) d.f2 ≤
      32 * (((286024637 / 62500000000000000) : ℝ) + (152676249 / 100000000000000000) + (22934869 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12707 163) (d.w1 12707 163)
      (d.w2 12707 163) ≤
      32 * (((1830171373 / 100000000000000000000) : ℝ) + (325532981 / 25000000000000000000) + (47576621 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12707 163) (d.f1 12707 163) d.f2 ≤
      ((286024637 / 62500000000000000) : ℝ) ^ 2 + 2 * ((286024637 / 62500000000000000)) * ((152676249 / 100000000000000000)) * (126 / 100) +
      2 * (((152676249 / 100000000000000000)) ^ 2 + 2 * ((286024637 / 62500000000000000)) * ((22934869 / 62500000000000000))) +
      6 * ((152676249 / 100000000000000000)) * ((22934869 / 62500000000000000)) * (126 / 100) + 8 * ((22934869 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12707 163) (d.f1 12707 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12707 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12707 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12707 163) (d.f1 12707 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12707 163) (d.w1 12707 163) (d.w2 12707 163)
  have hwexpr0 : 0 ≤ d.w0 12707 163 + d.w1 12707 163 * √(π / 2) +
      2 * d.w2 12707 163 + energyR16 12707 *
      radiusPolynomialRoot16 (d.w0 12707 163) (d.w1 12707 163) (d.w2 12707 163) := by
    positivity
  constructor
  · change (12707 : ℝ) ^ 8 * (mA 12707 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12707 163) (d.f1 12707 163) d.f2 + locationR16 12707 *
        radiusPolynomialRoot16 (d.f0 12707 163) (d.f1 12707 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12707 : ℝ) ^ 8 * (mA 12707 : ℝ) ^ 8 *
        ((((286024637 / 62500000000000000) : ℝ) ^ 2 + 2 * ((286024637 / 62500000000000000)) * ((152676249 / 100000000000000000)) * (126 / 100) +
          2 * (((152676249 / 100000000000000000)) ^ 2 + 2 * ((286024637 / 62500000000000000)) * ((22934869 / 62500000000000000))) +
          6 * ((152676249 / 100000000000000000)) * ((22934869 / 62500000000000000)) * (126 / 100) + 8 * ((22934869 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12707) *
          (32 * (((286024637 / 62500000000000000) : ℝ) + (152676249 / 100000000000000000) + (22934869 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12707 : ℝ) ^ 16 *
      (d.w0 12707 163 + d.w1 12707 163 * √(π / 2) + 2 * d.w2 12707 163 +
        energyR16 12707 * radiusPolynomialRoot16 (d.w0 12707 163) (d.w1 12707 163)
          (d.w2 12707 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12707 : ℝ) ^ 16 *
        (((1830171373 / 100000000000000000000) : ℝ) + ((325532981 / 25000000000000000000)) * (126 / 100) + 2 * ((47576621 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12707) *
          (32 * (((1830171373 / 100000000000000000000) : ℝ) + (325532981 / 25000000000000000000) + (47576621 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12707

/-! A coarse bound on the actual paper statistics constant at dimension 12708. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12706 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12706 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12706 128 ≤ (12960 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12960 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12708) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12708 : ℕ))
    (by norm_num : (12708 : ℕ) ≤ 16384)
  have ht : paperTail256 12708 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12708 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12708 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12708 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12708 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12708 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12706 128 * √(2 / (12708 : ℝ)) *
      (√(12708 : ℝ) + paperT0 12708 + paperTail256 12708) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12708 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12708 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12708 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12706 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12706 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12708 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12708

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12708 (61 / 100) 163 (17 / (100 * 12708)) (26 / (10 * 12708)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12708 (61 / 100) 163 (17 / (100 * 12708)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118912241 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (748581949 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5091493061 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12708 / 12708 * (61 / 100)) ^ 4 * inverseRadius8 (12708 - 1) /
            envelopeGap 12708 (61 / 100) 163 (17 / (100 * 12708)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12708

namespace BstLean.Part266.Row12708
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12708 163 ≤ (22877471 / 5000000000000000)
  f1 : (tableEnvelope C).f1 12708 163 ≤ (5962743 / 3906250000000000)
  f2 : (tableEnvelope C).f2 ≤ (183442861 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12708 163 ≤ (457434849 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12708 163 ≤ (1301824567 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12708 163 ≤ (475653897 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118912241 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118912241 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (748581949 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5091493061 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457189 / 125000000) : ℝ) ≤ √(17 / (100 * 12708) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12708) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (218093779 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1934660111 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12708) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12708) ≤ (55642649 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12708) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12708 * (163 : ℝ) ^ 2 + 26 / (10 * 12708) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12708) : ℝ)) (tA 12708 * 163 ^ 2 + 26 / (10 * 12708)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457189 / 125000000))) * ((118912241 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457189 / 125000000)) ^ 3) * ((748581949 / 500000000000000000000000))) + ((5091493061 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457189 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12708) : ℝ)) d.D d.V d.P (√(tA 12708) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457189 / 125000000)) ^ 2 * (((218093779 / 100000000000000)) * ((1934660111 / 50000000000000000)))) + ((5091493061 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12708) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457189 / 125000000)) * ((118912241 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12708) : ℝ)) (tA 12708 * 163 ^ 2 + 26 / (10 * 12708)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118912241 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457189 / 125000000)) ^ 2) * ((748581949 / 500000000000000000000000)) + ((5091493061 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12708) : ℝ)) (√(26 / (10 * 12708) : ℝ)) d.D d.V d.P (√(tA 12708) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457189 / 125000000)) * (((218093779 / 100000000000000)) * ((1934660111 / 50000000000000000))) + ((5091493061 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12708) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118912241 / 25000000000000000000) : ℝ) + ((5091493061 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12708

namespace BstLean.Part266.Row12708
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12708 163 ∧
    0 ≤ (tableEnvelope C).f1 12708 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12708 163 ∧
    0 ≤ (tableEnvelope C).w1 12708 163 ∧ 0 ≤ (tableEnvelope C).w2 12708 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12708 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12708 163 ∧ 0 ≤ d.f1 12708 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12708 163 ∧ 0 ≤ d.w1 12708 163 ∧ 0 ≤ d.w2 12708 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12708 ≤ 2 * (228 / 100 : ℝ) / 12708 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12708 ≤ 2 * (370 / 100 : ℝ) / 12708 := by
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
    (completeRAData (tableEnvelope C) 12708 163).locationBound 12708 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12708 163).energyBound 12708 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12708 163) (d.f1 12708 163) d.f2 ≤
      32 * (((22877471 / 5000000000000000) : ℝ) + (5962743 / 3906250000000000) + (183442861 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12708 163) (d.w1 12708 163)
      (d.w2 12708 163) ≤
      32 * (((457434849 / 25000000000000000000) : ℝ) + (1301824567 / 100000000000000000000) + (475653897 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12708 163) (d.f1 12708 163) d.f2 ≤
      ((22877471 / 5000000000000000) : ℝ) ^ 2 + 2 * ((22877471 / 5000000000000000)) * ((5962743 / 3906250000000000)) * (126 / 100) +
      2 * (((5962743 / 3906250000000000)) ^ 2 + 2 * ((22877471 / 5000000000000000)) * ((183442861 / 500000000000000000))) +
      6 * ((5962743 / 3906250000000000)) * ((183442861 / 500000000000000000)) * (126 / 100) + 8 * ((183442861 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12708 163) (d.f1 12708 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12708 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12708 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12708 163) (d.f1 12708 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12708 163) (d.w1 12708 163) (d.w2 12708 163)
  have hwexpr0 : 0 ≤ d.w0 12708 163 + d.w1 12708 163 * √(π / 2) +
      2 * d.w2 12708 163 + energyR16 12708 *
      radiusPolynomialRoot16 (d.w0 12708 163) (d.w1 12708 163) (d.w2 12708 163) := by
    positivity
  constructor
  · change (12708 : ℝ) ^ 8 * (mA 12708 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12708 163) (d.f1 12708 163) d.f2 + locationR16 12708 *
        radiusPolynomialRoot16 (d.f0 12708 163) (d.f1 12708 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12708 : ℝ) ^ 8 * (mA 12708 : ℝ) ^ 8 *
        ((((22877471 / 5000000000000000) : ℝ) ^ 2 + 2 * ((22877471 / 5000000000000000)) * ((5962743 / 3906250000000000)) * (126 / 100) +
          2 * (((5962743 / 3906250000000000)) ^ 2 + 2 * ((22877471 / 5000000000000000)) * ((183442861 / 500000000000000000))) +
          6 * ((5962743 / 3906250000000000)) * ((183442861 / 500000000000000000)) * (126 / 100) + 8 * ((183442861 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12708) *
          (32 * (((22877471 / 5000000000000000) : ℝ) + (5962743 / 3906250000000000) + (183442861 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12708 : ℝ) ^ 16 *
      (d.w0 12708 163 + d.w1 12708 163 * √(π / 2) + 2 * d.w2 12708 163 +
        energyR16 12708 * radiusPolynomialRoot16 (d.w0 12708 163) (d.w1 12708 163)
          (d.w2 12708 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12708 : ℝ) ^ 16 *
        (((457434849 / 25000000000000000000) : ℝ) + ((1301824567 / 100000000000000000000)) * (126 / 100) + 2 * ((475653897 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12708) *
          (32 * (((457434849 / 25000000000000000000) : ℝ) + (1301824567 / 100000000000000000000) + (475653897 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12708

/-! A coarse bound on the actual paper statistics constant at dimension 12709. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12707 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12707 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12707 128 ≤ (12961 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12961 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12709) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12709 : ℕ))
    (by norm_num : (12709 : ℕ) ≤ 16384)
  have ht : paperTail256 12709 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12709 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12709 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12709 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12709 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12709 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12707 128 * √(2 / (12709 : ℝ)) *
      (√(12709 : ℝ) + paperT0 12709 + paperTail256 12709) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12709 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12709 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12709 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12707 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12707 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12709 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12709

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12709 (61 / 100) 163 (17 / (100 * 12709)) (26 / (10 * 12709)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12709 (61 / 100) 163 (17 / (100 * 12709)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (29721043 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (748346361 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (636032227 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12709 / 12709 * (61 / 100)) ^ 4 * inverseRadius8 (12709 - 1) /
            envelopeGap 12709 (61 / 100) 163 (17 / (100 * 12709)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12709

namespace BstLean.Part266.Row12709
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12709 163 ≤ (4574594519 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12709 163 ≤ (1526162019 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183406781 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12709 163 ≤ (1829307567 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12709 163 ≤ (1301517311 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12709 163 ≤ (475541617 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (29721043 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (29721043 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (748346361 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (636032227 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((457171 / 125000000) : ℝ) ≤ √(17 / (100 * 12709) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12709) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2180680371 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19343556563 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12709) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12709) ≤ (55638271 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12709) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12709 * (163 : ℝ) ^ 2 + 26 / (10 * 12709) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12709) : ℝ)) (tA 12709 * 163 ^ 2 + 26 / (10 * 12709)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((457171 / 125000000))) * ((29721043 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((457171 / 125000000)) ^ 3) * ((748346361 / 500000000000000000000000))) + ((636032227 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((457171 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12709) : ℝ)) d.D d.V d.P (√(tA 12709) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((457171 / 125000000)) ^ 2 * (((2180680371 / 1000000000000000)) * ((19343556563 / 500000000000000000)))) + ((636032227 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12709) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((457171 / 125000000)) * ((29721043 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12709) : ℝ)) (tA 12709 * 163 ^ 2 + 26 / (10 * 12709)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((29721043 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((457171 / 125000000)) ^ 2) * ((748346361 / 500000000000000000000000)) + ((636032227 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12709) : ℝ)) (√(26 / (10 * 12709) : ℝ)) d.D d.V d.P (√(tA 12709) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((457171 / 125000000)) * (((2180680371 / 1000000000000000)) * ((19343556563 / 500000000000000000))) + ((636032227 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12709) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((29721043 / 6250000000000000000) : ℝ) + ((636032227 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12709

namespace BstLean.Part266.Row12709
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12709 163 ∧
    0 ≤ (tableEnvelope C).f1 12709 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12709 163 ∧
    0 ≤ (tableEnvelope C).w1 12709 163 ∧ 0 ≤ (tableEnvelope C).w2 12709 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12709 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12709 163 ∧ 0 ≤ d.f1 12709 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12709 163 ∧ 0 ≤ d.w1 12709 163 ∧ 0 ≤ d.w2 12709 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12709 ≤ 2 * (228 / 100 : ℝ) / 12709 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12709 ≤ 2 * (370 / 100 : ℝ) / 12709 := by
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
    (completeRAData (tableEnvelope C) 12709 163).locationBound 12709 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12709 163).energyBound 12709 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12709 163) (d.f1 12709 163) d.f2 ≤
      32 * (((4574594519 / 1000000000000000000) : ℝ) + (1526162019 / 1000000000000000000) + (183406781 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12709 163) (d.w1 12709 163)
      (d.w2 12709 163) ≤
      32 * (((1829307567 / 100000000000000000000) : ℝ) + (1301517311 / 100000000000000000000) + (475541617 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12709 163) (d.f1 12709 163) d.f2 ≤
      ((4574594519 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4574594519 / 1000000000000000000)) * ((1526162019 / 1000000000000000000)) * (126 / 100) +
      2 * (((1526162019 / 1000000000000000000)) ^ 2 + 2 * ((4574594519 / 1000000000000000000)) * ((183406781 / 500000000000000000))) +
      6 * ((1526162019 / 1000000000000000000)) * ((183406781 / 500000000000000000)) * (126 / 100) + 8 * ((183406781 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12709 163) (d.f1 12709 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12709 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12709 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12709 163) (d.f1 12709 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12709 163) (d.w1 12709 163) (d.w2 12709 163)
  have hwexpr0 : 0 ≤ d.w0 12709 163 + d.w1 12709 163 * √(π / 2) +
      2 * d.w2 12709 163 + energyR16 12709 *
      radiusPolynomialRoot16 (d.w0 12709 163) (d.w1 12709 163) (d.w2 12709 163) := by
    positivity
  constructor
  · change (12709 : ℝ) ^ 8 * (mA 12709 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12709 163) (d.f1 12709 163) d.f2 + locationR16 12709 *
        radiusPolynomialRoot16 (d.f0 12709 163) (d.f1 12709 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12709 : ℝ) ^ 8 * (mA 12709 : ℝ) ^ 8 *
        ((((4574594519 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4574594519 / 1000000000000000000)) * ((1526162019 / 1000000000000000000)) * (126 / 100) +
          2 * (((1526162019 / 1000000000000000000)) ^ 2 + 2 * ((4574594519 / 1000000000000000000)) * ((183406781 / 500000000000000000))) +
          6 * ((1526162019 / 1000000000000000000)) * ((183406781 / 500000000000000000)) * (126 / 100) + 8 * ((183406781 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12709) *
          (32 * (((4574594519 / 1000000000000000000) : ℝ) + (1526162019 / 1000000000000000000) + (183406781 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12709 : ℝ) ^ 16 *
      (d.w0 12709 163 + d.w1 12709 163 * √(π / 2) + 2 * d.w2 12709 163 +
        energyR16 12709 * radiusPolynomialRoot16 (d.w0 12709 163) (d.w1 12709 163)
          (d.w2 12709 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12709 : ℝ) ^ 16 *
        (((1829307567 / 100000000000000000000) : ℝ) + ((1301517311 / 100000000000000000000)) * (126 / 100) + 2 * ((475541617 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12709) *
          (32 * (((1829307567 / 100000000000000000000) : ℝ) + (1301517311 / 100000000000000000000) + (475541617 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12709

/-! A coarse bound on the actual paper statistics constant at dimension 12710. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12708 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12708 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12708 128 ≤ (12962 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12962 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12710) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12710 : ℕ))
    (by norm_num : (12710 : ℕ) ≤ 16384)
  have ht : paperTail256 12710 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12710 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12710 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12710 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12710 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12710 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12708 128 * √(2 / (12710 : ℝ)) *
      (√(12710 : ℝ) + paperT0 12710 + paperTail256 12710) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12710 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12710 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12710 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12708 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12708 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12710 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12710

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12710 (61 / 100) 163 (17 / (100 * 12710)) (26 / (10 * 12710)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12710 (61 / 100) 163 (17 / (100 * 12710)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (7428507 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (149622173 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2542512443 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12710 / 12710 * (61 / 100)) ^ 4 * inverseRadius8 (12710 - 1) /
            envelopeGap 12710 (61 / 100) 163 (17 / (100 * 12710)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12710

namespace BstLean.Part266.Row12710
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12710 163 ≤ (4573691533 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12710 163 ≤ (762930547 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (366741323 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12710 163 ≤ (914437573 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12710 163 ≤ (650604901 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12710 163 ≤ (237714687 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (7428507 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (7428507 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (149622173 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2542512443 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((146289 / 40000000) : ℝ) ≤ √(17 / (100 * 12710) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12710) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (436084601 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9670256363 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12710) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12710) ≤ (111267787 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12710) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12710 * (163 : ℝ) ^ 2 + 26 / (10 * 12710) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12710) : ℝ)) (tA 12710 * 163 ^ 2 + 26 / (10 * 12710)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((146289 / 40000000))) * ((7428507 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((146289 / 40000000)) ^ 3) * ((149622173 / 100000000000000000000000))) + ((2542512443 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((146289 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12710) : ℝ)) d.D d.V d.P (√(tA 12710) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((146289 / 40000000)) ^ 2 * (((436084601 / 200000000000000)) * ((9670256363 / 250000000000000000)))) + ((2542512443 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12710) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((146289 / 40000000)) * ((7428507 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12710) : ℝ)) (tA 12710 * 163 ^ 2 + 26 / (10 * 12710)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((7428507 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((146289 / 40000000)) ^ 2) * ((149622173 / 100000000000000000000000)) + ((2542512443 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12710) : ℝ)) (√(26 / (10 * 12710) : ℝ)) d.D d.V d.P (√(tA 12710) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((146289 / 40000000)) * (((436084601 / 200000000000000)) * ((9670256363 / 250000000000000000))) + ((2542512443 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12710) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((7428507 / 1562500000000000000) : ℝ) + ((2542512443 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12710

namespace BstLean.Part266.Row12710
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12710 163 ∧
    0 ≤ (tableEnvelope C).f1 12710 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12710 163 ∧
    0 ≤ (tableEnvelope C).w1 12710 163 ∧ 0 ≤ (tableEnvelope C).w2 12710 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12710 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12710 163 ∧ 0 ≤ d.f1 12710 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12710 163 ∧ 0 ≤ d.w1 12710 163 ∧ 0 ≤ d.w2 12710 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12710 ≤ 2 * (228 / 100 : ℝ) / 12710 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12710 ≤ 2 * (370 / 100 : ℝ) / 12710 := by
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
    (completeRAData (tableEnvelope C) 12710 163).locationBound 12710 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12710 163).energyBound 12710 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12710 163) (d.f1 12710 163) d.f2 ≤
      32 * (((4573691533 / 1000000000000000000) : ℝ) + (762930547 / 500000000000000000) + (366741323 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12710 163) (d.w1 12710 163)
      (d.w2 12710 163) ≤
      32 * (((914437573 / 50000000000000000000) : ℝ) + (650604901 / 50000000000000000000) + (237714687 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12710 163) (d.f1 12710 163) d.f2 ≤
      ((4573691533 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4573691533 / 1000000000000000000)) * ((762930547 / 500000000000000000)) * (126 / 100) +
      2 * (((762930547 / 500000000000000000)) ^ 2 + 2 * ((4573691533 / 1000000000000000000)) * ((366741323 / 1000000000000000000))) +
      6 * ((762930547 / 500000000000000000)) * ((366741323 / 1000000000000000000)) * (126 / 100) + 8 * ((366741323 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12710 163) (d.f1 12710 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12710 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12710 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12710 163) (d.f1 12710 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12710 163) (d.w1 12710 163) (d.w2 12710 163)
  have hwexpr0 : 0 ≤ d.w0 12710 163 + d.w1 12710 163 * √(π / 2) +
      2 * d.w2 12710 163 + energyR16 12710 *
      radiusPolynomialRoot16 (d.w0 12710 163) (d.w1 12710 163) (d.w2 12710 163) := by
    positivity
  constructor
  · change (12710 : ℝ) ^ 8 * (mA 12710 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12710 163) (d.f1 12710 163) d.f2 + locationR16 12710 *
        radiusPolynomialRoot16 (d.f0 12710 163) (d.f1 12710 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12710 : ℝ) ^ 8 * (mA 12710 : ℝ) ^ 8 *
        ((((4573691533 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4573691533 / 1000000000000000000)) * ((762930547 / 500000000000000000)) * (126 / 100) +
          2 * (((762930547 / 500000000000000000)) ^ 2 + 2 * ((4573691533 / 1000000000000000000)) * ((366741323 / 1000000000000000000))) +
          6 * ((762930547 / 500000000000000000)) * ((366741323 / 1000000000000000000)) * (126 / 100) + 8 * ((366741323 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12710) *
          (32 * (((4573691533 / 1000000000000000000) : ℝ) + (762930547 / 500000000000000000) + (366741323 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12710 : ℝ) ^ 16 *
      (d.w0 12710 163 + d.w1 12710 163 * √(π / 2) + 2 * d.w2 12710 163 +
        energyR16 12710 * radiusPolynomialRoot16 (d.w0 12710 163) (d.w1 12710 163)
          (d.w2 12710 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12710 : ℝ) ^ 16 *
        (((914437573 / 50000000000000000000) : ℝ) + ((650604901 / 50000000000000000000)) * (126 / 100) + 2 * ((237714687 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12710) *
          (32 * (((914437573 / 50000000000000000000) : ℝ) + (650604901 / 50000000000000000000) + (237714687 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12710

/-! A coarse bound on the actual paper statistics constant at dimension 12711. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12709 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12709 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12709 128 ≤ (12963 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12963 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12711) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12711 : ℕ))
    (by norm_num : (12711 : ℕ) ≤ 16384)
  have ht : paperTail256 12711 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12711 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12711 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12711 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12711 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12711 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12709 128 * √(2 / (12711 : ℝ)) *
      (√(12711 : ℝ) + paperT0 12711 + paperTail256 12711) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12711 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12711 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12711 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12709 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12709 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12711 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12711

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12711 (61 / 100) 163 (17 / (100 * 12711)) (26 / (10 * 12711)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12711 (61 / 100) 163 (17 / (100 * 12711)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (475312243 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (373937731 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5081794269 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12711 / 12711 * (61 / 100)) ^ 4 * inverseRadius8 (12711 - 1) /
            envelopeGap 12711 (61 / 100) 163 (17 / (100 * 12711)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12711

namespace BstLean.Part266.Row12711
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12711 163 ≤ (1143198117 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12711 163 ≤ (15255611 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (73333841 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12711 163 ≤ (914221807 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12711 163 ≤ (40653211 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12711 163 ≤ (237658583 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (475312243 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (475312243 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (373937731 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5081794269 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3657081 / 1000000000) : ℝ) ≤ √(17 / (100 * 12711) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12711) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2180165689 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1546997569 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12711) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12711) ≤ (111259033 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12711) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12711 * (163 : ℝ) ^ 2 + 26 / (10 * 12711) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12711) : ℝ)) (tA 12711 * 163 ^ 2 + 26 / (10 * 12711)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3657081 / 1000000000))) * ((475312243 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3657081 / 1000000000)) ^ 3) * ((373937731 / 250000000000000000000000))) + ((5081794269 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3657081 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12711) : ℝ)) d.D d.V d.P (√(tA 12711) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3657081 / 1000000000)) ^ 2 * (((2180165689 / 1000000000000000)) * ((1546997569 / 40000000000000000)))) + ((5081794269 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12711) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3657081 / 1000000000)) * ((475312243 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12711) : ℝ)) (tA 12711 * 163 ^ 2 + 26 / (10 * 12711)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((475312243 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3657081 / 1000000000)) ^ 2) * ((373937731 / 250000000000000000000000)) + ((5081794269 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12711) : ℝ)) (√(26 / (10 * 12711) : ℝ)) d.D d.V d.P (√(tA 12711) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3657081 / 1000000000)) * (((2180165689 / 1000000000000000)) * ((1546997569 / 40000000000000000))) + ((5081794269 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12711) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((475312243 / 100000000000000000000) : ℝ) + ((5081794269 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12711

namespace BstLean.Part266.Row12711
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12711 163 ∧
    0 ≤ (tableEnvelope C).f1 12711 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12711 163 ∧
    0 ≤ (tableEnvelope C).w1 12711 163 ∧ 0 ≤ (tableEnvelope C).w2 12711 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12711 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12711 163 ∧ 0 ≤ d.f1 12711 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12711 163 ∧ 0 ≤ d.w1 12711 163 ∧ 0 ≤ d.w2 12711 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12711 ≤ 2 * (228 / 100 : ℝ) / 12711 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12711 ≤ 2 * (370 / 100 : ℝ) / 12711 := by
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
    (completeRAData (tableEnvelope C) 12711 163).locationBound 12711 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12711 163).energyBound 12711 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12711 163) (d.f1 12711 163) d.f2 ≤
      32 * (((1143198117 / 250000000000000000) : ℝ) + (15255611 / 10000000000000000) + (73333841 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12711 163) (d.w1 12711 163)
      (d.w2 12711 163) ≤
      32 * (((914221807 / 50000000000000000000) : ℝ) + (40653211 / 3125000000000000000) + (237658583 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12711 163) (d.f1 12711 163) d.f2 ≤
      ((1143198117 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1143198117 / 250000000000000000)) * ((15255611 / 10000000000000000)) * (126 / 100) +
      2 * (((15255611 / 10000000000000000)) ^ 2 + 2 * ((1143198117 / 250000000000000000)) * ((73333841 / 200000000000000000))) +
      6 * ((15255611 / 10000000000000000)) * ((73333841 / 200000000000000000)) * (126 / 100) + 8 * ((73333841 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12711 163) (d.f1 12711 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12711 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12711 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12711 163) (d.f1 12711 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12711 163) (d.w1 12711 163) (d.w2 12711 163)
  have hwexpr0 : 0 ≤ d.w0 12711 163 + d.w1 12711 163 * √(π / 2) +
      2 * d.w2 12711 163 + energyR16 12711 *
      radiusPolynomialRoot16 (d.w0 12711 163) (d.w1 12711 163) (d.w2 12711 163) := by
    positivity
  constructor
  · change (12711 : ℝ) ^ 8 * (mA 12711 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12711 163) (d.f1 12711 163) d.f2 + locationR16 12711 *
        radiusPolynomialRoot16 (d.f0 12711 163) (d.f1 12711 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12711 : ℝ) ^ 8 * (mA 12711 : ℝ) ^ 8 *
        ((((1143198117 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1143198117 / 250000000000000000)) * ((15255611 / 10000000000000000)) * (126 / 100) +
          2 * (((15255611 / 10000000000000000)) ^ 2 + 2 * ((1143198117 / 250000000000000000)) * ((73333841 / 200000000000000000))) +
          6 * ((15255611 / 10000000000000000)) * ((73333841 / 200000000000000000)) * (126 / 100) + 8 * ((73333841 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12711) *
          (32 * (((1143198117 / 250000000000000000) : ℝ) + (15255611 / 10000000000000000) + (73333841 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12711 : ℝ) ^ 16 *
      (d.w0 12711 163 + d.w1 12711 163 * √(π / 2) + 2 * d.w2 12711 163 +
        energyR16 12711 * radiusPolynomialRoot16 (d.w0 12711 163) (d.w1 12711 163)
          (d.w2 12711 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12711 : ℝ) ^ 16 *
        (((914221807 / 50000000000000000000) : ℝ) + ((40653211 / 3125000000000000000)) * (126 / 100) + 2 * ((237658583 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12711) *
          (32 * (((914221807 / 50000000000000000000) : ℝ) + (40653211 / 3125000000000000000) + (237658583 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12711

/-! A coarse bound on the actual paper statistics constant at dimension 12712. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12710 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12710 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12710 128 ≤ (12964 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12964 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12712) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12712 : ℕ))
    (by norm_num : (12712 : ℕ) ≤ 16384)
  have ht : paperTail256 12712 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12712 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12712 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12712 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12712 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12712 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12710 128 * √(2 / (12712 : ℝ)) *
      (√(12712 : ℝ) + paperT0 12712 + paperTail256 12712) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12712 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12712 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12712 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12710 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12710 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12712 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12712

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12712 (61 / 100) 163 (17 / (100 * 12712)) (26 / (10 * 12712)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12712 (61 / 100) 163 (17 / (100 * 12712)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (237600037 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1495280303 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5078565963 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12712 / 12712 * (61 / 100)) ^ 4 * inverseRadius8 (12712 - 1) /
            envelopeGap 12712 (61 / 100) 163 (17 / (100 * 12712)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12712

namespace BstLean.Part266.Row12712
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12712 163 ≤ (285743357 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12712 163 ≤ (1525261203 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36659711 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12712 163 ≤ (1828012231 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12712 163 ≤ (260119161 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12712 163 ≤ (237602497 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (237600037 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (237600037 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1495280303 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5078565963 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3656937 / 1000000000) : ℝ) ≤ √(17 / (100 * 12712) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12712) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (87196337 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38668854431 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12712) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12712) ≤ (111250281 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12712) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12712 * (163 : ℝ) ^ 2 + 26 / (10 * 12712) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12712) : ℝ)) (tA 12712 * 163 ^ 2 + 26 / (10 * 12712)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3656937 / 1000000000))) * ((237600037 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3656937 / 1000000000)) ^ 3) * ((1495280303 / 1000000000000000000000000))) + ((5078565963 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3656937 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12712) : ℝ)) d.D d.V d.P (√(tA 12712) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3656937 / 1000000000)) ^ 2 * (((87196337 / 40000000000000)) * ((38668854431 / 1000000000000000000)))) + ((5078565963 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12712) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3656937 / 1000000000)) * ((237600037 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12712) : ℝ)) (tA 12712 * 163 ^ 2 + 26 / (10 * 12712)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((237600037 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3656937 / 1000000000)) ^ 2) * ((1495280303 / 1000000000000000000000000)) + ((5078565963 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12712) : ℝ)) (√(26 / (10 * 12712) : ℝ)) d.D d.V d.P (√(tA 12712) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3656937 / 1000000000)) * (((87196337 / 40000000000000)) * ((38668854431 / 1000000000000000000))) + ((5078565963 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12712) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((237600037 / 50000000000000000000) : ℝ) + ((5078565963 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12712

namespace BstLean.Part266.Row12712
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12712 163 ∧
    0 ≤ (tableEnvelope C).f1 12712 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12712 163 ∧
    0 ≤ (tableEnvelope C).w1 12712 163 ∧ 0 ≤ (tableEnvelope C).w2 12712 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12712 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12712 163 ∧ 0 ≤ d.f1 12712 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12712 163 ∧ 0 ≤ d.w1 12712 163 ∧ 0 ≤ d.w2 12712 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12712 ≤ 2 * (228 / 100 : ℝ) / 12712 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12712 ≤ 2 * (370 / 100 : ℝ) / 12712 := by
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
    (completeRAData (tableEnvelope C) 12712 163).locationBound 12712 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12712 163).energyBound 12712 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12712 163) (d.f1 12712 163) d.f2 ≤
      32 * (((285743357 / 62500000000000000) : ℝ) + (1525261203 / 1000000000000000000) + (36659711 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12712 163) (d.w1 12712 163)
      (d.w2 12712 163) ≤
      32 * (((1828012231 / 100000000000000000000) : ℝ) + (260119161 / 20000000000000000000) + (237602497 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12712 163) (d.f1 12712 163) d.f2 ≤
      ((285743357 / 62500000000000000) : ℝ) ^ 2 + 2 * ((285743357 / 62500000000000000)) * ((1525261203 / 1000000000000000000)) * (126 / 100) +
      2 * (((1525261203 / 1000000000000000000)) ^ 2 + 2 * ((285743357 / 62500000000000000)) * ((36659711 / 100000000000000000))) +
      6 * ((1525261203 / 1000000000000000000)) * ((36659711 / 100000000000000000)) * (126 / 100) + 8 * ((36659711 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12712 163) (d.f1 12712 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12712 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12712 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12712 163) (d.f1 12712 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12712 163) (d.w1 12712 163) (d.w2 12712 163)
  have hwexpr0 : 0 ≤ d.w0 12712 163 + d.w1 12712 163 * √(π / 2) +
      2 * d.w2 12712 163 + energyR16 12712 *
      radiusPolynomialRoot16 (d.w0 12712 163) (d.w1 12712 163) (d.w2 12712 163) := by
    positivity
  constructor
  · change (12712 : ℝ) ^ 8 * (mA 12712 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12712 163) (d.f1 12712 163) d.f2 + locationR16 12712 *
        radiusPolynomialRoot16 (d.f0 12712 163) (d.f1 12712 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12712 : ℝ) ^ 8 * (mA 12712 : ℝ) ^ 8 *
        ((((285743357 / 62500000000000000) : ℝ) ^ 2 + 2 * ((285743357 / 62500000000000000)) * ((1525261203 / 1000000000000000000)) * (126 / 100) +
          2 * (((1525261203 / 1000000000000000000)) ^ 2 + 2 * ((285743357 / 62500000000000000)) * ((36659711 / 100000000000000000))) +
          6 * ((1525261203 / 1000000000000000000)) * ((36659711 / 100000000000000000)) * (126 / 100) + 8 * ((36659711 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12712) *
          (32 * (((285743357 / 62500000000000000) : ℝ) + (1525261203 / 1000000000000000000) + (36659711 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12712 : ℝ) ^ 16 *
      (d.w0 12712 163 + d.w1 12712 163 * √(π / 2) + 2 * d.w2 12712 163 +
        energyR16 12712 * radiusPolynomialRoot16 (d.w0 12712 163) (d.w1 12712 163)
          (d.w2 12712 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12712 : ℝ) ^ 16 *
        (((1828012231 / 100000000000000000000) : ℝ) + ((260119161 / 20000000000000000000)) * (126 / 100) + 2 * ((237602497 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12712) *
          (32 * (((1828012231 / 100000000000000000000) : ℝ) + (260119161 / 20000000000000000000) + (237602497 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12712

/-! A coarse bound on the actual paper statistics constant at dimension 12713. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12711 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12711 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12711 128 ≤ (12965 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12965 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12713) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12713 : ℕ))
    (by norm_num : (12713 : ℕ) ≤ 16384)
  have ht : paperTail256 12713 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12713 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12713 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12713 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12713 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12713 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12711 128 * √(2 / (12713 : ℝ)) *
      (√(12713 : ℝ) + paperT0 12713 + paperTail256 12713) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12713 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12713 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12713 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12711 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12711 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12713 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12713

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12713 (61 / 100) 163 (17 / (100 * 12713)) (26 / (10 * 12713)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12713 (61 / 100) 163 (17 / (100 * 12713)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (475087939 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1494809867 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2537669983 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12713 / 12713 * (61 / 100)) ^ 4 * inverseRadius8 (12713 - 1) /
            envelopeGap 12713 (61 / 100) 163 (17 / (100 * 12713)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12713

namespace BstLean.Part266.Row12713
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12713 163 ≤ (71421801 / 15625000000000000)
  f1 : (tableEnvelope C).f1 12713 163 ≤ (762480701 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (73305007 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12713 163 ≤ (365516199 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12713 163 ≤ (4063403 / 312500000000000000)
  w2 : (tableEnvelope C).w2 12713 163 ≤ (59386607 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (475087939 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (475087939 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1494809867 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2537669983 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3656793 / 1000000000) : ℝ) ≤ √(17 / (100 * 12713) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12713) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2179651209 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38662771073 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12713) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12713) ≤ (11124153 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12713) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12713 * (163 : ℝ) ^ 2 + 26 / (10 * 12713) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12713) : ℝ)) (tA 12713 * 163 ^ 2 + 26 / (10 * 12713)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3656793 / 1000000000))) * ((475087939 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3656793 / 1000000000)) ^ 3) * ((1494809867 / 1000000000000000000000000))) + ((2537669983 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3656793 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12713) : ℝ)) d.D d.V d.P (√(tA 12713) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3656793 / 1000000000)) ^ 2 * (((2179651209 / 1000000000000000)) * ((38662771073 / 1000000000000000000)))) + ((2537669983 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12713) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3656793 / 1000000000)) * ((475087939 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12713) : ℝ)) (tA 12713 * 163 ^ 2 + 26 / (10 * 12713)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((475087939 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3656793 / 1000000000)) ^ 2) * ((1494809867 / 1000000000000000000000000)) + ((2537669983 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12713) : ℝ)) (√(26 / (10 * 12713) : ℝ)) d.D d.V d.P (√(tA 12713) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3656793 / 1000000000)) * (((2179651209 / 1000000000000000)) * ((38662771073 / 1000000000000000000))) + ((2537669983 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12713) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((475087939 / 100000000000000000000) : ℝ) + ((2537669983 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12713

namespace BstLean.Part266.Row12713
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12713 163 ∧
    0 ≤ (tableEnvelope C).f1 12713 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12713 163 ∧
    0 ≤ (tableEnvelope C).w1 12713 163 ∧ 0 ≤ (tableEnvelope C).w2 12713 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12713 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12713 163 ∧ 0 ≤ d.f1 12713 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12713 163 ∧ 0 ≤ d.w1 12713 163 ∧ 0 ≤ d.w2 12713 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12713 ≤ 2 * (228 / 100 : ℝ) / 12713 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12713 ≤ 2 * (370 / 100 : ℝ) / 12713 := by
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
    (completeRAData (tableEnvelope C) 12713 163).locationBound 12713 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12713 163).energyBound 12713 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12713 163) (d.f1 12713 163) d.f2 ≤
      32 * (((71421801 / 15625000000000000) : ℝ) + (762480701 / 500000000000000000) + (73305007 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12713 163) (d.w1 12713 163)
      (d.w2 12713 163) ≤
      32 * (((365516199 / 20000000000000000000) : ℝ) + (4063403 / 312500000000000000) + (59386607 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12713 163) (d.f1 12713 163) d.f2 ≤
      ((71421801 / 15625000000000000) : ℝ) ^ 2 + 2 * ((71421801 / 15625000000000000)) * ((762480701 / 500000000000000000)) * (126 / 100) +
      2 * (((762480701 / 500000000000000000)) ^ 2 + 2 * ((71421801 / 15625000000000000)) * ((73305007 / 200000000000000000))) +
      6 * ((762480701 / 500000000000000000)) * ((73305007 / 200000000000000000)) * (126 / 100) + 8 * ((73305007 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12713 163) (d.f1 12713 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12713 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12713 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12713 163) (d.f1 12713 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12713 163) (d.w1 12713 163) (d.w2 12713 163)
  have hwexpr0 : 0 ≤ d.w0 12713 163 + d.w1 12713 163 * √(π / 2) +
      2 * d.w2 12713 163 + energyR16 12713 *
      radiusPolynomialRoot16 (d.w0 12713 163) (d.w1 12713 163) (d.w2 12713 163) := by
    positivity
  constructor
  · change (12713 : ℝ) ^ 8 * (mA 12713 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12713 163) (d.f1 12713 163) d.f2 + locationR16 12713 *
        radiusPolynomialRoot16 (d.f0 12713 163) (d.f1 12713 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12713 : ℝ) ^ 8 * (mA 12713 : ℝ) ^ 8 *
        ((((71421801 / 15625000000000000) : ℝ) ^ 2 + 2 * ((71421801 / 15625000000000000)) * ((762480701 / 500000000000000000)) * (126 / 100) +
          2 * (((762480701 / 500000000000000000)) ^ 2 + 2 * ((71421801 / 15625000000000000)) * ((73305007 / 200000000000000000))) +
          6 * ((762480701 / 500000000000000000)) * ((73305007 / 200000000000000000)) * (126 / 100) + 8 * ((73305007 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12713) *
          (32 * (((71421801 / 15625000000000000) : ℝ) + (762480701 / 500000000000000000) + (73305007 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12713 : ℝ) ^ 16 *
      (d.w0 12713 163 + d.w1 12713 163 * √(π / 2) + 2 * d.w2 12713 163 +
        energyR16 12713 * radiusPolynomialRoot16 (d.w0 12713 163) (d.w1 12713 163)
          (d.w2 12713 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12713 : ℝ) ^ 16 *
        (((365516199 / 20000000000000000000) : ℝ) + ((4063403 / 312500000000000000)) * (126 / 100) + 2 * ((59386607 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12713) *
          (32 * (((365516199 / 20000000000000000000) : ℝ) + (4063403 / 312500000000000000) + (59386607 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12713

/-! A coarse bound on the actual paper statistics constant at dimension 12714. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12712 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12712 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12712 128 ≤ (12966 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12966 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12714) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12714 : ℕ))
    (by norm_num : (12714 : ℕ) ≤ 16384)
  have ht : paperTail256 12714 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12714 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12714 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12714 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12714 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12714 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12712 128 * √(2 / (12714 : ℝ)) *
      (√(12714 : ℝ) + paperT0 12714 + paperTail256 12714) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12714 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12714 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12714 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12712 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12712 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12714 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12714

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12714 (61 / 100) 163 (17 / (100 * 12714)) (26 / (10 * 12714)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12714 (61 / 100) 163 (17 / (100 * 12714)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (2968599 / 625000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1494339617 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5072116277 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12714 / 12714 * (61 / 100)) ^ 4 * inverseRadius8 (12714 - 1) /
            envelopeGap 12714 (61 / 100) 163 (17 / (100 * 12714)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12714

namespace BstLean.Part266.Row12714
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12714 163 ≤ (571262141 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12714 163 ≤ (1524661699 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183226491 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12714 163 ≤ (456787477 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12714 163 ≤ (649991109 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12714 163 ≤ (237490377 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (2968599 / 625000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (2968599 / 625000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1494339617 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5072116277 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3656649 / 1000000000) : ℝ) ≤ √(17 / (100 * 12714) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12714) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (435878809 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38656689163 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12714) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12714) ≤ (5561639 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12714) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12714 * (163 : ℝ) ^ 2 + 26 / (10 * 12714) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12714) : ℝ)) (tA 12714 * 163 ^ 2 + 26 / (10 * 12714)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3656649 / 1000000000))) * ((2968599 / 625000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3656649 / 1000000000)) ^ 3) * ((1494339617 / 1000000000000000000000000))) + ((5072116277 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3656649 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12714) : ℝ)) d.D d.V d.P (√(tA 12714) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3656649 / 1000000000)) ^ 2 * (((435878809 / 200000000000000)) * ((38656689163 / 1000000000000000000)))) + ((5072116277 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12714) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3656649 / 1000000000)) * ((2968599 / 625000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12714) : ℝ)) (tA 12714 * 163 ^ 2 + 26 / (10 * 12714)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((2968599 / 625000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3656649 / 1000000000)) ^ 2) * ((1494339617 / 1000000000000000000000000)) + ((5072116277 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12714) : ℝ)) (√(26 / (10 * 12714) : ℝ)) d.D d.V d.P (√(tA 12714) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3656649 / 1000000000)) * (((435878809 / 200000000000000)) * ((38656689163 / 1000000000000000000))) + ((5072116277 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12714) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((2968599 / 625000000000000000) : ℝ) + ((5072116277 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12714

namespace BstLean.Part266.Row12714
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12714 163 ∧
    0 ≤ (tableEnvelope C).f1 12714 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12714 163 ∧
    0 ≤ (tableEnvelope C).w1 12714 163 ∧ 0 ≤ (tableEnvelope C).w2 12714 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12714 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12714 163 ∧ 0 ≤ d.f1 12714 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12714 163 ∧ 0 ≤ d.w1 12714 163 ∧ 0 ≤ d.w2 12714 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12714 ≤ 2 * (228 / 100 : ℝ) / 12714 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12714 ≤ 2 * (370 / 100 : ℝ) / 12714 := by
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
    (completeRAData (tableEnvelope C) 12714 163).locationBound 12714 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12714 163).energyBound 12714 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12714 163) (d.f1 12714 163) d.f2 ≤
      32 * (((571262141 / 125000000000000000) : ℝ) + (1524661699 / 1000000000000000000) + (183226491 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12714 163) (d.w1 12714 163)
      (d.w2 12714 163) ≤
      32 * (((456787477 / 25000000000000000000) : ℝ) + (649991109 / 50000000000000000000) + (237490377 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12714 163) (d.f1 12714 163) d.f2 ≤
      ((571262141 / 125000000000000000) : ℝ) ^ 2 + 2 * ((571262141 / 125000000000000000)) * ((1524661699 / 1000000000000000000)) * (126 / 100) +
      2 * (((1524661699 / 1000000000000000000)) ^ 2 + 2 * ((571262141 / 125000000000000000)) * ((183226491 / 500000000000000000))) +
      6 * ((1524661699 / 1000000000000000000)) * ((183226491 / 500000000000000000)) * (126 / 100) + 8 * ((183226491 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12714 163) (d.f1 12714 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12714 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12714 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12714 163) (d.f1 12714 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12714 163) (d.w1 12714 163) (d.w2 12714 163)
  have hwexpr0 : 0 ≤ d.w0 12714 163 + d.w1 12714 163 * √(π / 2) +
      2 * d.w2 12714 163 + energyR16 12714 *
      radiusPolynomialRoot16 (d.w0 12714 163) (d.w1 12714 163) (d.w2 12714 163) := by
    positivity
  constructor
  · change (12714 : ℝ) ^ 8 * (mA 12714 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12714 163) (d.f1 12714 163) d.f2 + locationR16 12714 *
        radiusPolynomialRoot16 (d.f0 12714 163) (d.f1 12714 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12714 : ℝ) ^ 8 * (mA 12714 : ℝ) ^ 8 *
        ((((571262141 / 125000000000000000) : ℝ) ^ 2 + 2 * ((571262141 / 125000000000000000)) * ((1524661699 / 1000000000000000000)) * (126 / 100) +
          2 * (((1524661699 / 1000000000000000000)) ^ 2 + 2 * ((571262141 / 125000000000000000)) * ((183226491 / 500000000000000000))) +
          6 * ((1524661699 / 1000000000000000000)) * ((183226491 / 500000000000000000)) * (126 / 100) + 8 * ((183226491 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12714) *
          (32 * (((571262141 / 125000000000000000) : ℝ) + (1524661699 / 1000000000000000000) + (183226491 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12714 : ℝ) ^ 16 *
      (d.w0 12714 163 + d.w1 12714 163 * √(π / 2) + 2 * d.w2 12714 163 +
        energyR16 12714 * radiusPolynomialRoot16 (d.w0 12714 163) (d.w1 12714 163)
          (d.w2 12714 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12714 : ℝ) ^ 16 *
        (((456787477 / 25000000000000000000) : ℝ) + ((649991109 / 50000000000000000000)) * (126 / 100) + 2 * ((237490377 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12714) *
          (32 * (((456787477 / 25000000000000000000) : ℝ) + (649991109 / 50000000000000000000) + (237490377 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12714

/-! A coarse bound on the actual paper statistics constant at dimension 12715. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12713 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12713 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12713 128 ≤ (12967 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12967 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12715) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12715 : ℕ))
    (by norm_num : (12715 : ℕ) ≤ 16384)
  have ht : paperTail256 12715 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12715 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12715 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12715 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12715 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12715 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12713 128 * √(2 / (12715 : ℝ)) *
      (√(12715 : ℝ) + paperT0 12715 + paperTail256 12715) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12715 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12715 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12715 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12713 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12713 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12715 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12715

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12715 (61 / 100) 163 (17 / (100 * 12715)) (26 / (10 * 12715)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12715 (61 / 100) 163 (17 / (100 * 12715)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (474863777 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1493869551 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2534447447 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12715 / 12715 * (61 / 100)) ^ 4 * inverseRadius8 (12715 - 1) /
            envelopeGap 12715 (61 / 100) 163 (17 / (100 * 12715)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12715

namespace BstLean.Part266.Row12715
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12715 163 ≤ (2284599649 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12715 163 ≤ (381090523 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45797619 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12715 163 ≤ (182671897 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12715 163 ≤ (1299675579 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12715 163 ≤ (29679293 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (474863777 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (474863777 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1493869551 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2534447447 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((731301 / 200000000) : ℝ) ≤ √(17 / (100 * 12715) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12715) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2179136933 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9662652169 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12715) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12715) ≤ (3475751 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12715) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12715 * (163 : ℝ) ^ 2 + 26 / (10 * 12715) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12715) : ℝ)) (tA 12715 * 163 ^ 2 + 26 / (10 * 12715)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((731301 / 200000000))) * ((474863777 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((731301 / 200000000)) ^ 3) * ((1493869551 / 1000000000000000000000000))) + ((2534447447 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((731301 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12715) : ℝ)) d.D d.V d.P (√(tA 12715) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((731301 / 200000000)) ^ 2 * (((2179136933 / 1000000000000000)) * ((9662652169 / 250000000000000000)))) + ((2534447447 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12715) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((731301 / 200000000)) * ((474863777 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12715) : ℝ)) (tA 12715 * 163 ^ 2 + 26 / (10 * 12715)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((474863777 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((731301 / 200000000)) ^ 2) * ((1493869551 / 1000000000000000000000000)) + ((2534447447 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12715) : ℝ)) (√(26 / (10 * 12715) : ℝ)) d.D d.V d.P (√(tA 12715) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((731301 / 200000000)) * (((2179136933 / 1000000000000000)) * ((9662652169 / 250000000000000000))) + ((2534447447 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12715) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((474863777 / 100000000000000000000) : ℝ) + ((2534447447 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12715

namespace BstLean.Part266.Row12715
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12715 163 ∧
    0 ≤ (tableEnvelope C).f1 12715 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12715 163 ∧
    0 ≤ (tableEnvelope C).w1 12715 163 ∧ 0 ≤ (tableEnvelope C).w2 12715 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12715 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12715 163 ∧ 0 ≤ d.f1 12715 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12715 163 ∧ 0 ≤ d.w1 12715 163 ∧ 0 ≤ d.w2 12715 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12715 ≤ 2 * (228 / 100 : ℝ) / 12715 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12715 ≤ 2 * (370 / 100 : ℝ) / 12715 := by
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
    (completeRAData (tableEnvelope C) 12715 163).locationBound 12715 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12715 163).energyBound 12715 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12715 163) (d.f1 12715 163) d.f2 ≤
      32 * (((2284599649 / 500000000000000000) : ℝ) + (381090523 / 250000000000000000) + (45797619 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12715 163) (d.w1 12715 163)
      (d.w2 12715 163) ≤
      32 * (((182671897 / 10000000000000000000) : ℝ) + (1299675579 / 100000000000000000000) + (29679293 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12715 163) (d.f1 12715 163) d.f2 ≤
      ((2284599649 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2284599649 / 500000000000000000)) * ((381090523 / 250000000000000000)) * (126 / 100) +
      2 * (((381090523 / 250000000000000000)) ^ 2 + 2 * ((2284599649 / 500000000000000000)) * ((45797619 / 125000000000000000))) +
      6 * ((381090523 / 250000000000000000)) * ((45797619 / 125000000000000000)) * (126 / 100) + 8 * ((45797619 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12715 163) (d.f1 12715 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12715 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12715 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12715 163) (d.f1 12715 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12715 163) (d.w1 12715 163) (d.w2 12715 163)
  have hwexpr0 : 0 ≤ d.w0 12715 163 + d.w1 12715 163 * √(π / 2) +
      2 * d.w2 12715 163 + energyR16 12715 *
      radiusPolynomialRoot16 (d.w0 12715 163) (d.w1 12715 163) (d.w2 12715 163) := by
    positivity
  constructor
  · change (12715 : ℝ) ^ 8 * (mA 12715 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12715 163) (d.f1 12715 163) d.f2 + locationR16 12715 *
        radiusPolynomialRoot16 (d.f0 12715 163) (d.f1 12715 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12715 : ℝ) ^ 8 * (mA 12715 : ℝ) ^ 8 *
        ((((2284599649 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2284599649 / 500000000000000000)) * ((381090523 / 250000000000000000)) * (126 / 100) +
          2 * (((381090523 / 250000000000000000)) ^ 2 + 2 * ((2284599649 / 500000000000000000)) * ((45797619 / 125000000000000000))) +
          6 * ((381090523 / 250000000000000000)) * ((45797619 / 125000000000000000)) * (126 / 100) + 8 * ((45797619 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12715) *
          (32 * (((2284599649 / 500000000000000000) : ℝ) + (381090523 / 250000000000000000) + (45797619 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12715 : ℝ) ^ 16 *
      (d.w0 12715 163 + d.w1 12715 163 * √(π / 2) + 2 * d.w2 12715 163 +
        energyR16 12715 * radiusPolynomialRoot16 (d.w0 12715 163) (d.w1 12715 163)
          (d.w2 12715 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12715 : ℝ) ^ 16 *
        (((182671897 / 10000000000000000000) : ℝ) + ((1299675579 / 100000000000000000000)) * (126 / 100) + 2 * ((29679293 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12715) *
          (32 * (((182671897 / 10000000000000000000) : ℝ) + (1299675579 / 100000000000000000000) + (29679293 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12715

/-! A coarse bound on the actual paper statistics constant at dimension 12716. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12714 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12714 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12714 128 ≤ (12968 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12968 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12716) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12716 : ℕ))
    (by norm_num : (12716 : ℕ) ≤ 16384)
  have ht : paperTail256 12716 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12716 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12716 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12716 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12716 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12716 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12714 128 * √(2 / (12716 : ℝ)) *
      (√(12716 : ℝ) + paperT0 12716 + paperTail256 12716) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12716 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12716 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12716 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12714 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12714 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12716 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12716

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12716 (61 / 100) 163 (17 / (100 * 12716)) (26 / (10 * 12716)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12716 (61 / 100) 163 (17 / (100 * 12716)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118687937 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1493399669 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2532837907 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12716 / 12716 * (61 / 100)) ^ 4 * inverseRadius8 (12716 - 1) /
            envelopeGap 12716 (61 / 100) 163 (17 / (100 * 12716)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12716

namespace BstLean.Part266.Row12716
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12716 163 ≤ (2284149083 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12716 163 ≤ (1524061747 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183154421 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12716 163 ≤ (1826287439 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12716 163 ≤ (259873737 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12716 163 ≤ (29672291 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118687937 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118687937 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1493399669 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2532837907 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1828181 / 500000000) : ℝ) ≤ √(17 / (100 * 12716) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12716) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2178879869 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38644529613 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12716) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12716) ≤ (22243057 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12716) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12716 * (163 : ℝ) ^ 2 + 26 / (10 * 12716) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12716) : ℝ)) (tA 12716 * 163 ^ 2 + 26 / (10 * 12716)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1828181 / 500000000))) * ((118687937 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1828181 / 500000000)) ^ 3) * ((1493399669 / 1000000000000000000000000))) + ((2532837907 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1828181 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12716) : ℝ)) d.D d.V d.P (√(tA 12716) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1828181 / 500000000)) ^ 2 * (((2178879869 / 1000000000000000)) * ((38644529613 / 1000000000000000000)))) + ((2532837907 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12716) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1828181 / 500000000)) * ((118687937 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12716) : ℝ)) (tA 12716 * 163 ^ 2 + 26 / (10 * 12716)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118687937 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1828181 / 500000000)) ^ 2) * ((1493399669 / 1000000000000000000000000)) + ((2532837907 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12716) : ℝ)) (√(26 / (10 * 12716) : ℝ)) d.D d.V d.P (√(tA 12716) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1828181 / 500000000)) * (((2178879869 / 1000000000000000)) * ((38644529613 / 1000000000000000000))) + ((2532837907 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12716) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118687937 / 25000000000000000000) : ℝ) + ((2532837907 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12716

namespace BstLean.Part266.Row12716
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12716 163 ∧
    0 ≤ (tableEnvelope C).f1 12716 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12716 163 ∧
    0 ≤ (tableEnvelope C).w1 12716 163 ∧ 0 ≤ (tableEnvelope C).w2 12716 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12716 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12716 163 ∧ 0 ≤ d.f1 12716 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12716 163 ∧ 0 ≤ d.w1 12716 163 ∧ 0 ≤ d.w2 12716 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12716 ≤ 2 * (228 / 100 : ℝ) / 12716 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12716 ≤ 2 * (370 / 100 : ℝ) / 12716 := by
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
    (completeRAData (tableEnvelope C) 12716 163).locationBound 12716 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12716 163).energyBound 12716 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12716 163) (d.f1 12716 163) d.f2 ≤
      32 * (((2284149083 / 500000000000000000) : ℝ) + (1524061747 / 1000000000000000000) + (183154421 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12716 163) (d.w1 12716 163)
      (d.w2 12716 163) ≤
      32 * (((1826287439 / 100000000000000000000) : ℝ) + (259873737 / 20000000000000000000) + (29672291 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12716 163) (d.f1 12716 163) d.f2 ≤
      ((2284149083 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2284149083 / 500000000000000000)) * ((1524061747 / 1000000000000000000)) * (126 / 100) +
      2 * (((1524061747 / 1000000000000000000)) ^ 2 + 2 * ((2284149083 / 500000000000000000)) * ((183154421 / 500000000000000000))) +
      6 * ((1524061747 / 1000000000000000000)) * ((183154421 / 500000000000000000)) * (126 / 100) + 8 * ((183154421 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12716 163) (d.f1 12716 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12716 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12716 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12716 163) (d.f1 12716 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12716 163) (d.w1 12716 163) (d.w2 12716 163)
  have hwexpr0 : 0 ≤ d.w0 12716 163 + d.w1 12716 163 * √(π / 2) +
      2 * d.w2 12716 163 + energyR16 12716 *
      radiusPolynomialRoot16 (d.w0 12716 163) (d.w1 12716 163) (d.w2 12716 163) := by
    positivity
  constructor
  · change (12716 : ℝ) ^ 8 * (mA 12716 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12716 163) (d.f1 12716 163) d.f2 + locationR16 12716 *
        radiusPolynomialRoot16 (d.f0 12716 163) (d.f1 12716 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12716 : ℝ) ^ 8 * (mA 12716 : ℝ) ^ 8 *
        ((((2284149083 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2284149083 / 500000000000000000)) * ((1524061747 / 1000000000000000000)) * (126 / 100) +
          2 * (((1524061747 / 1000000000000000000)) ^ 2 + 2 * ((2284149083 / 500000000000000000)) * ((183154421 / 500000000000000000))) +
          6 * ((1524061747 / 1000000000000000000)) * ((183154421 / 500000000000000000)) * (126 / 100) + 8 * ((183154421 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12716) *
          (32 * (((2284149083 / 500000000000000000) : ℝ) + (1524061747 / 1000000000000000000) + (183154421 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12716 : ℝ) ^ 16 *
      (d.w0 12716 163 + d.w1 12716 163 * √(π / 2) + 2 * d.w2 12716 163 +
        energyR16 12716 * radiusPolynomialRoot16 (d.w0 12716 163) (d.w1 12716 163)
          (d.w2 12716 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12716 : ℝ) ^ 16 *
        (((1826287439 / 100000000000000000000) : ℝ) + ((259873737 / 20000000000000000000)) * (126 / 100) + 2 * ((29672291 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12716) *
          (32 * (((1826287439 / 100000000000000000000) : ℝ) + (259873737 / 20000000000000000000) + (29672291 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12716

/-! A coarse bound on the actual paper statistics constant at dimension 12717. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12715 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12715 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12715 128 ≤ (12969 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12969 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12717) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12717 : ℕ))
    (by norm_num : (12717 : ℕ) ≤ 16384)
  have ht : paperTail256 12717 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12717 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12717 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12717 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12717 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12717 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12715 128 * √(2 / (12717 : ℝ)) *
      (√(12717 : ℝ) + paperT0 12717 + paperTail256 12717) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12717 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12717 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12717 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12715 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12715 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12717 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12717

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12717 (61 / 100) 163 (17 / (100 * 12717)) (26 / (10 * 12717)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12717 (61 / 100) 163 (17 / (100 * 12717)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (94927951 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1492929973 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5062459037 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12717 / 12717 * (61 / 100)) ^ 4 * inverseRadius8 (12717 - 1) /
            envelopeGap 12717 (61 / 100) 163 (17 / (100 * 12717)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12717

namespace BstLean.Part266.Row12717
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12717 163 ≤ (2283700477 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12717 163 ≤ (761881167 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183118427 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12717 163 ≤ (456464199 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12717 163 ≤ (1299062251 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12717 163 ≤ (474644659 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (94927951 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (94927951 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1492929973 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5062459037 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1828109 / 500000000) : ℝ) ≤ √(17 / (100 * 12717) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12717) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2178622857 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38638452001 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12717) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12717) ≤ (5560327 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12717) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12717 * (163 : ℝ) ^ 2 + 26 / (10 * 12717) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12717) : ℝ)) (tA 12717 * 163 ^ 2 + 26 / (10 * 12717)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1828109 / 500000000))) * ((94927951 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1828109 / 500000000)) ^ 3) * ((1492929973 / 1000000000000000000000000))) + ((5062459037 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1828109 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12717) : ℝ)) d.D d.V d.P (√(tA 12717) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1828109 / 500000000)) ^ 2 * (((2178622857 / 1000000000000000)) * ((38638452001 / 1000000000000000000)))) + ((5062459037 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12717) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1828109 / 500000000)) * ((94927951 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12717) : ℝ)) (tA 12717 * 163 ^ 2 + 26 / (10 * 12717)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((94927951 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1828109 / 500000000)) ^ 2) * ((1492929973 / 1000000000000000000000000)) + ((5062459037 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12717) : ℝ)) (√(26 / (10 * 12717) : ℝ)) d.D d.V d.P (√(tA 12717) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1828109 / 500000000)) * (((2178622857 / 1000000000000000)) * ((38638452001 / 1000000000000000000))) + ((5062459037 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12717) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((94927951 / 20000000000000000000) : ℝ) + ((5062459037 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12717

namespace BstLean.Part266.Row12717
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12717 163 ∧
    0 ≤ (tableEnvelope C).f1 12717 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12717 163 ∧
    0 ≤ (tableEnvelope C).w1 12717 163 ∧ 0 ≤ (tableEnvelope C).w2 12717 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12717 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12717 163 ∧ 0 ≤ d.f1 12717 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12717 163 ∧ 0 ≤ d.w1 12717 163 ∧ 0 ≤ d.w2 12717 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12717 ≤ 2 * (228 / 100 : ℝ) / 12717 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12717 ≤ 2 * (370 / 100 : ℝ) / 12717 := by
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
    (completeRAData (tableEnvelope C) 12717 163).locationBound 12717 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12717 163).energyBound 12717 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12717 163) (d.f1 12717 163) d.f2 ≤
      32 * (((2283700477 / 500000000000000000) : ℝ) + (761881167 / 500000000000000000) + (183118427 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12717 163) (d.w1 12717 163)
      (d.w2 12717 163) ≤
      32 * (((456464199 / 25000000000000000000) : ℝ) + (1299062251 / 100000000000000000000) + (474644659 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12717 163) (d.f1 12717 163) d.f2 ≤
      ((2283700477 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2283700477 / 500000000000000000)) * ((761881167 / 500000000000000000)) * (126 / 100) +
      2 * (((761881167 / 500000000000000000)) ^ 2 + 2 * ((2283700477 / 500000000000000000)) * ((183118427 / 500000000000000000))) +
      6 * ((761881167 / 500000000000000000)) * ((183118427 / 500000000000000000)) * (126 / 100) + 8 * ((183118427 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12717 163) (d.f1 12717 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12717 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12717 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12717 163) (d.f1 12717 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12717 163) (d.w1 12717 163) (d.w2 12717 163)
  have hwexpr0 : 0 ≤ d.w0 12717 163 + d.w1 12717 163 * √(π / 2) +
      2 * d.w2 12717 163 + energyR16 12717 *
      radiusPolynomialRoot16 (d.w0 12717 163) (d.w1 12717 163) (d.w2 12717 163) := by
    positivity
  constructor
  · change (12717 : ℝ) ^ 8 * (mA 12717 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12717 163) (d.f1 12717 163) d.f2 + locationR16 12717 *
        radiusPolynomialRoot16 (d.f0 12717 163) (d.f1 12717 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12717 : ℝ) ^ 8 * (mA 12717 : ℝ) ^ 8 *
        ((((2283700477 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2283700477 / 500000000000000000)) * ((761881167 / 500000000000000000)) * (126 / 100) +
          2 * (((761881167 / 500000000000000000)) ^ 2 + 2 * ((2283700477 / 500000000000000000)) * ((183118427 / 500000000000000000))) +
          6 * ((761881167 / 500000000000000000)) * ((183118427 / 500000000000000000)) * (126 / 100) + 8 * ((183118427 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12717) *
          (32 * (((2283700477 / 500000000000000000) : ℝ) + (761881167 / 500000000000000000) + (183118427 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12717 : ℝ) ^ 16 *
      (d.w0 12717 163 + d.w1 12717 163 * √(π / 2) + 2 * d.w2 12717 163 +
        energyR16 12717 * radiusPolynomialRoot16 (d.w0 12717 163) (d.w1 12717 163)
          (d.w2 12717 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12717 : ℝ) ^ 16 *
        (((456464199 / 25000000000000000000) : ℝ) + ((1299062251 / 100000000000000000000)) * (126 / 100) + 2 * ((474644659 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12717) *
          (32 * (((456464199 / 25000000000000000000) : ℝ) + (1299062251 / 100000000000000000000) + (474644659 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12717

/-! A coarse bound on the actual paper statistics constant at dimension 12718. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12716 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12716 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12716 128 ≤ (12970 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12970 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12718) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12718 : ℕ))
    (by norm_num : (12718 : ℕ) ≤ 16384)
  have ht : paperTail256 12718 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12718 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12718 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12718 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12718 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12718 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12716 128 * √(2 / (12718 : ℝ)) *
      (√(12718 : ℝ) + paperT0 12718 + paperTail256 12718) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12718 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12718 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12718 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12716 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12716 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12718 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12718

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12718 (61 / 100) 163 (17 / (100 * 12718)) (26 / (10 * 12718)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12718 (61 / 100) 163 (17 / (100 * 12718)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (474527797 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1492460461 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (63240557 / 12500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12718 / 12718 * (61 / 100)) ^ 4 * inverseRadius8 (12718 - 1) /
            envelopeGap 12718 (61 / 100) 163 (17 / (100 * 12718)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12718

namespace BstLean.Part266.Row12718
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12718 163 ≤ (285406503 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12718 163 ≤ (190432877 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (366164887 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12718 163 ≤ (1825426301 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12718 163 ≤ (649377959 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12718 163 ≤ (237266349 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (474527797 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (474527797 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1492460461 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (63240557 / 12500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1828037 / 500000000) : ℝ) ≤ √(17 / (100 * 12718) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12718) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (435673179 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19316187907 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12718) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12718) ≤ (27799449 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12718) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12718 * (163 : ℝ) ^ 2 + 26 / (10 * 12718) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12718) : ℝ)) (tA 12718 * 163 ^ 2 + 26 / (10 * 12718)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1828037 / 500000000))) * ((474527797 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1828037 / 500000000)) ^ 3) * ((1492460461 / 1000000000000000000000000))) + ((63240557 / 12500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1828037 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12718) : ℝ)) d.D d.V d.P (√(tA 12718) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1828037 / 500000000)) ^ 2 * (((435673179 / 200000000000000)) * ((19316187907 / 500000000000000000)))) + ((63240557 / 12500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12718) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1828037 / 500000000)) * ((474527797 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12718) : ℝ)) (tA 12718 * 163 ^ 2 + 26 / (10 * 12718)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((474527797 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1828037 / 500000000)) ^ 2) * ((1492460461 / 1000000000000000000000000)) + ((63240557 / 12500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12718) : ℝ)) (√(26 / (10 * 12718) : ℝ)) d.D d.V d.P (√(tA 12718) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1828037 / 500000000)) * (((435673179 / 200000000000000)) * ((19316187907 / 500000000000000000))) + ((63240557 / 12500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12718) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((474527797 / 100000000000000000000) : ℝ) + ((63240557 / 12500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12718

namespace BstLean.Part266.Row12718
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12718 163 ∧
    0 ≤ (tableEnvelope C).f1 12718 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12718 163 ∧
    0 ≤ (tableEnvelope C).w1 12718 163 ∧ 0 ≤ (tableEnvelope C).w2 12718 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12718 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12718 163 ∧ 0 ≤ d.f1 12718 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12718 163 ∧ 0 ≤ d.w1 12718 163 ∧ 0 ≤ d.w2 12718 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12718 ≤ 2 * (228 / 100 : ℝ) / 12718 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12718 ≤ 2 * (370 / 100 : ℝ) / 12718 := by
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
    (completeRAData (tableEnvelope C) 12718 163).locationBound 12718 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12718 163).energyBound 12718 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12718 163) (d.f1 12718 163) d.f2 ≤
      32 * (((285406503 / 62500000000000000) : ℝ) + (190432877 / 125000000000000000) + (366164887 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12718 163) (d.w1 12718 163)
      (d.w2 12718 163) ≤
      32 * (((1825426301 / 100000000000000000000) : ℝ) + (649377959 / 50000000000000000000) + (237266349 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12718 163) (d.f1 12718 163) d.f2 ≤
      ((285406503 / 62500000000000000) : ℝ) ^ 2 + 2 * ((285406503 / 62500000000000000)) * ((190432877 / 125000000000000000)) * (126 / 100) +
      2 * (((190432877 / 125000000000000000)) ^ 2 + 2 * ((285406503 / 62500000000000000)) * ((366164887 / 1000000000000000000))) +
      6 * ((190432877 / 125000000000000000)) * ((366164887 / 1000000000000000000)) * (126 / 100) + 8 * ((366164887 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12718 163) (d.f1 12718 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12718 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12718 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12718 163) (d.f1 12718 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12718 163) (d.w1 12718 163) (d.w2 12718 163)
  have hwexpr0 : 0 ≤ d.w0 12718 163 + d.w1 12718 163 * √(π / 2) +
      2 * d.w2 12718 163 + energyR16 12718 *
      radiusPolynomialRoot16 (d.w0 12718 163) (d.w1 12718 163) (d.w2 12718 163) := by
    positivity
  constructor
  · change (12718 : ℝ) ^ 8 * (mA 12718 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12718 163) (d.f1 12718 163) d.f2 + locationR16 12718 *
        radiusPolynomialRoot16 (d.f0 12718 163) (d.f1 12718 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12718 : ℝ) ^ 8 * (mA 12718 : ℝ) ^ 8 *
        ((((285406503 / 62500000000000000) : ℝ) ^ 2 + 2 * ((285406503 / 62500000000000000)) * ((190432877 / 125000000000000000)) * (126 / 100) +
          2 * (((190432877 / 125000000000000000)) ^ 2 + 2 * ((285406503 / 62500000000000000)) * ((366164887 / 1000000000000000000))) +
          6 * ((190432877 / 125000000000000000)) * ((366164887 / 1000000000000000000)) * (126 / 100) + 8 * ((366164887 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12718) *
          (32 * (((285406503 / 62500000000000000) : ℝ) + (190432877 / 125000000000000000) + (366164887 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12718 : ℝ) ^ 16 *
      (d.w0 12718 163 + d.w1 12718 163 * √(π / 2) + 2 * d.w2 12718 163 +
        energyR16 12718 * radiusPolynomialRoot16 (d.w0 12718 163) (d.w1 12718 163)
          (d.w2 12718 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12718 : ℝ) ^ 16 *
        (((1825426301 / 100000000000000000000) : ℝ) + ((649377959 / 50000000000000000000)) * (126 / 100) + 2 * ((237266349 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12718) *
          (32 * (((1825426301 / 100000000000000000000) : ℝ) + (649377959 / 50000000000000000000) + (237266349 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12718

/-! A coarse bound on the actual paper statistics constant at dimension 12719. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12717 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12717 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12717 128 ≤ (12971 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12971 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12719) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12719 : ℕ))
    (by norm_num : (12719 : ℕ) ≤ 16384)
  have ht : paperTail256 12719 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12719 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12719 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12719 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12719 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12719 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12717 128 * √(2 / (12719 : ℝ)) *
      (√(12719 : ℝ) + paperT0 12719 + paperTail256 12719) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12719 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12719 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12719 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12717 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12717 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12719 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12719

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12719 (61 / 100) 163 (17 / (100 * 12719)) (26 / (10 * 12719)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12719 (61 / 100) 163 (17 / (100 * 12719)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (237207937 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (745995567 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5056032381 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12719 / 12719 * (61 / 100)) ^ 4 * inverseRadius8 (12719 - 1) /
            envelopeGap 12719 (61 / 100) 163 (17 / (100 * 12719)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12719

namespace BstLean.Part266.Row12719
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12719 163 ≤ (4565607451 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12719 163 ≤ (304632759 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183046471 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12719 163 ≤ (912497977 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12719 163 ≤ (162306211 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12719 163 ≤ (118605193 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (237207937 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (237207937 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (745995567 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5056032381 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((365593 / 100000000) : ℝ) ≤ √(17 / (100 * 12719) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12719) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2178108983 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19313150533 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12719) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12719) ≤ (111189053 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12719) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12719 * (163 : ℝ) ^ 2 + 26 / (10 * 12719) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12719) : ℝ)) (tA 12719 * 163 ^ 2 + 26 / (10 * 12719)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((365593 / 100000000))) * ((237207937 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((365593 / 100000000)) ^ 3) * ((745995567 / 500000000000000000000000))) + ((5056032381 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((365593 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12719) : ℝ)) d.D d.V d.P (√(tA 12719) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((365593 / 100000000)) ^ 2 * (((2178108983 / 1000000000000000)) * ((19313150533 / 500000000000000000)))) + ((5056032381 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12719) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((365593 / 100000000)) * ((237207937 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12719) : ℝ)) (tA 12719 * 163 ^ 2 + 26 / (10 * 12719)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((237207937 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((365593 / 100000000)) ^ 2) * ((745995567 / 500000000000000000000000)) + ((5056032381 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12719) : ℝ)) (√(26 / (10 * 12719) : ℝ)) d.D d.V d.P (√(tA 12719) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((365593 / 100000000)) * (((2178108983 / 1000000000000000)) * ((19313150533 / 500000000000000000))) + ((5056032381 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12719) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((237207937 / 50000000000000000000) : ℝ) + ((5056032381 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12719

namespace BstLean.Part266.Row12719
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12719 163 ∧
    0 ≤ (tableEnvelope C).f1 12719 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12719 163 ∧
    0 ≤ (tableEnvelope C).w1 12719 163 ∧ 0 ≤ (tableEnvelope C).w2 12719 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12719 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12719 163 ∧ 0 ≤ d.f1 12719 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12719 163 ∧ 0 ≤ d.w1 12719 163 ∧ 0 ≤ d.w2 12719 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12719 ≤ 2 * (228 / 100 : ℝ) / 12719 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12719 ≤ 2 * (370 / 100 : ℝ) / 12719 := by
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
    (completeRAData (tableEnvelope C) 12719 163).locationBound 12719 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12719 163).energyBound 12719 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12719 163) (d.f1 12719 163) d.f2 ≤
      32 * (((4565607451 / 1000000000000000000) : ℝ) + (304632759 / 200000000000000000) + (183046471 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12719 163) (d.w1 12719 163)
      (d.w2 12719 163) ≤
      32 * (((912497977 / 50000000000000000000) : ℝ) + (162306211 / 12500000000000000000) + (118605193 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12719 163) (d.f1 12719 163) d.f2 ≤
      ((4565607451 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4565607451 / 1000000000000000000)) * ((304632759 / 200000000000000000)) * (126 / 100) +
      2 * (((304632759 / 200000000000000000)) ^ 2 + 2 * ((4565607451 / 1000000000000000000)) * ((183046471 / 500000000000000000))) +
      6 * ((304632759 / 200000000000000000)) * ((183046471 / 500000000000000000)) * (126 / 100) + 8 * ((183046471 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12719 163) (d.f1 12719 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12719 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12719 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12719 163) (d.f1 12719 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12719 163) (d.w1 12719 163) (d.w2 12719 163)
  have hwexpr0 : 0 ≤ d.w0 12719 163 + d.w1 12719 163 * √(π / 2) +
      2 * d.w2 12719 163 + energyR16 12719 *
      radiusPolynomialRoot16 (d.w0 12719 163) (d.w1 12719 163) (d.w2 12719 163) := by
    positivity
  constructor
  · change (12719 : ℝ) ^ 8 * (mA 12719 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12719 163) (d.f1 12719 163) d.f2 + locationR16 12719 *
        radiusPolynomialRoot16 (d.f0 12719 163) (d.f1 12719 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12719 : ℝ) ^ 8 * (mA 12719 : ℝ) ^ 8 *
        ((((4565607451 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4565607451 / 1000000000000000000)) * ((304632759 / 200000000000000000)) * (126 / 100) +
          2 * (((304632759 / 200000000000000000)) ^ 2 + 2 * ((4565607451 / 1000000000000000000)) * ((183046471 / 500000000000000000))) +
          6 * ((304632759 / 200000000000000000)) * ((183046471 / 500000000000000000)) * (126 / 100) + 8 * ((183046471 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12719) *
          (32 * (((4565607451 / 1000000000000000000) : ℝ) + (304632759 / 200000000000000000) + (183046471 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12719 : ℝ) ^ 16 *
      (d.w0 12719 163 + d.w1 12719 163 * √(π / 2) + 2 * d.w2 12719 163 +
        energyR16 12719 * radiusPolynomialRoot16 (d.w0 12719 163) (d.w1 12719 163)
          (d.w2 12719 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12719 : ℝ) ^ 16 *
        (((912497977 / 50000000000000000000) : ℝ) + ((162306211 / 12500000000000000000)) * (126 / 100) + 2 * ((118605193 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12719) *
          (32 * (((912497977 / 50000000000000000000) : ℝ) + (162306211 / 12500000000000000000) + (118605193 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12719

/-! A coarse bound on the actual paper statistics constant at dimension 12720. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12718 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12718 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12718 128 ≤ (12972 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12972 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12720) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12720 : ℕ))
    (by norm_num : (12720 : ℕ) ≤ 16384)
  have ht : paperTail256 12720 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12720 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12720 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12720 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12720 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12720 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12718 128 * √(2 / (12720 : ℝ)) *
      (√(12720 : ℝ) + paperT0 12720 + paperTail256 12720) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12720 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12720 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12720 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12718 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12718 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12720 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12720

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12720 (61 / 100) 163 (17 / (100 * 12720)) (26 / (10 * 12720)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12720 (61 / 100) 163 (17 / (100 * 12720)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (237151993 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1491521991 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5052822499 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12720 / 12720 * (61 / 100)) ^ 4 * inverseRadius8 (12720 - 1) /
            envelopeGap 12720 (61 / 100) 163 (17 / (100 * 12720)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12720

namespace BstLean.Part266.Row12720
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12720 163 ≤ (1141176889 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12720 163 ≤ (1522863837 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (183010459 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12720 163 ≤ (228070627 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12720 163 ≤ (259628641 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12720 163 ≤ (474308881 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (237151993 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (237151993 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1491521991 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5052822499 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3655787 / 1000000000) : ℝ) ≤ √(17 / (100 * 12720) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12720) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2177852121 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7724045549 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12720) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12720) ≤ (13897539 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12720) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12720 * (163 : ℝ) ^ 2 + 26 / (10 * 12720) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12720) : ℝ)) (tA 12720 * 163 ^ 2 + 26 / (10 * 12720)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3655787 / 1000000000))) * ((237151993 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3655787 / 1000000000)) ^ 3) * ((1491521991 / 1000000000000000000000000))) + ((5052822499 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3655787 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12720) : ℝ)) d.D d.V d.P (√(tA 12720) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3655787 / 1000000000)) ^ 2 * (((2177852121 / 1000000000000000)) * ((7724045549 / 200000000000000000)))) + ((5052822499 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12720) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3655787 / 1000000000)) * ((237151993 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12720) : ℝ)) (tA 12720 * 163 ^ 2 + 26 / (10 * 12720)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((237151993 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3655787 / 1000000000)) ^ 2) * ((1491521991 / 1000000000000000000000000)) + ((5052822499 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12720) : ℝ)) (√(26 / (10 * 12720) : ℝ)) d.D d.V d.P (√(tA 12720) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3655787 / 1000000000)) * (((2177852121 / 1000000000000000)) * ((7724045549 / 200000000000000000))) + ((5052822499 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12720) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((237151993 / 50000000000000000000) : ℝ) + ((5052822499 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12720

namespace BstLean.Part266.Row12720
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12720 163 ∧
    0 ≤ (tableEnvelope C).f1 12720 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12720 163 ∧
    0 ≤ (tableEnvelope C).w1 12720 163 ∧ 0 ≤ (tableEnvelope C).w2 12720 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12720 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12720 163 ∧ 0 ≤ d.f1 12720 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12720 163 ∧ 0 ≤ d.w1 12720 163 ∧ 0 ≤ d.w2 12720 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12720 ≤ 2 * (228 / 100 : ℝ) / 12720 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12720 ≤ 2 * (370 / 100 : ℝ) / 12720 := by
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
    (completeRAData (tableEnvelope C) 12720 163).locationBound 12720 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12720 163).energyBound 12720 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12720 163) (d.f1 12720 163) d.f2 ≤
      32 * (((1141176889 / 250000000000000000) : ℝ) + (1522863837 / 1000000000000000000) + (183010459 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12720 163) (d.w1 12720 163)
      (d.w2 12720 163) ≤
      32 * (((228070627 / 12500000000000000000) : ℝ) + (259628641 / 20000000000000000000) + (474308881 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12720 163) (d.f1 12720 163) d.f2 ≤
      ((1141176889 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1141176889 / 250000000000000000)) * ((1522863837 / 1000000000000000000)) * (126 / 100) +
      2 * (((1522863837 / 1000000000000000000)) ^ 2 + 2 * ((1141176889 / 250000000000000000)) * ((183010459 / 500000000000000000))) +
      6 * ((1522863837 / 1000000000000000000)) * ((183010459 / 500000000000000000)) * (126 / 100) + 8 * ((183010459 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12720 163) (d.f1 12720 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12720 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12720 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12720 163) (d.f1 12720 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12720 163) (d.w1 12720 163) (d.w2 12720 163)
  have hwexpr0 : 0 ≤ d.w0 12720 163 + d.w1 12720 163 * √(π / 2) +
      2 * d.w2 12720 163 + energyR16 12720 *
      radiusPolynomialRoot16 (d.w0 12720 163) (d.w1 12720 163) (d.w2 12720 163) := by
    positivity
  constructor
  · change (12720 : ℝ) ^ 8 * (mA 12720 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12720 163) (d.f1 12720 163) d.f2 + locationR16 12720 *
        radiusPolynomialRoot16 (d.f0 12720 163) (d.f1 12720 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12720 : ℝ) ^ 8 * (mA 12720 : ℝ) ^ 8 *
        ((((1141176889 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1141176889 / 250000000000000000)) * ((1522863837 / 1000000000000000000)) * (126 / 100) +
          2 * (((1522863837 / 1000000000000000000)) ^ 2 + 2 * ((1141176889 / 250000000000000000)) * ((183010459 / 500000000000000000))) +
          6 * ((1522863837 / 1000000000000000000)) * ((183010459 / 500000000000000000)) * (126 / 100) + 8 * ((183010459 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12720) *
          (32 * (((1141176889 / 250000000000000000) : ℝ) + (1522863837 / 1000000000000000000) + (183010459 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12720 : ℝ) ^ 16 *
      (d.w0 12720 163 + d.w1 12720 163 * √(π / 2) + 2 * d.w2 12720 163 +
        energyR16 12720 * radiusPolynomialRoot16 (d.w0 12720 163) (d.w1 12720 163)
          (d.w2 12720 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12720 : ℝ) ^ 16 *
        (((228070627 / 12500000000000000000) : ℝ) + ((259628641 / 20000000000000000000)) * (126 / 100) + 2 * ((474308881 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12720) *
          (32 * (((228070627 / 12500000000000000000) : ℝ) + (259628641 / 20000000000000000000) + (474308881 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12720

/-! A coarse bound on the actual paper statistics constant at dimension 12721. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12719 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12719 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12719 128 ≤ (12973 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12973 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12721) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12721 : ℕ))
    (by norm_num : (12721 : ℕ) ≤ 16384)
  have ht : paperTail256 12721 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12721 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12721 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12721 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12721 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12721 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12719 128 * √(2 / (12721 : ℝ)) *
      (√(12721 : ℝ) + paperT0 12721 + paperTail256 12721) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12721 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12721 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12721 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12719 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12719 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12721 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12721

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12721 (61 / 100) 163 (17 / (100 * 12721)) (26 / (10 * 12721)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12721 (61 / 100) 163 (17 / (100 * 12721)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (237096067 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1491053033 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5049614911 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12721 / 12721 * (61 / 100)) ^ 4 * inverseRadius8 (12721 - 1) /
            envelopeGap 12721 (61 / 100) 163 (17 / (100 * 12721)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12721

namespace BstLean.Part266.Row12721
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12721 163 ≤ (182552463 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12721 163 ≤ (152256481 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45743627 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12721 163 ≤ (364826993 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12721 163 ≤ (64891859 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12721 163 ≤ (237098513 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (237096067 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (237096067 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1491053033 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5049614911 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3655643 / 1000000000) : ℝ) ≤ √(17 / (100 * 12721) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12721) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (136099707 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38614155863 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12721) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12721) ≤ (27792893 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12721) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12721 * (163 : ℝ) ^ 2 + 26 / (10 * 12721) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12721) : ℝ)) (tA 12721 * 163 ^ 2 + 26 / (10 * 12721)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3655643 / 1000000000))) * ((237096067 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3655643 / 1000000000)) ^ 3) * ((1491053033 / 1000000000000000000000000))) + ((5049614911 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3655643 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12721) : ℝ)) d.D d.V d.P (√(tA 12721) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3655643 / 1000000000)) ^ 2 * (((136099707 / 62500000000000)) * ((38614155863 / 1000000000000000000)))) + ((5049614911 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12721) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3655643 / 1000000000)) * ((237096067 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12721) : ℝ)) (tA 12721 * 163 ^ 2 + 26 / (10 * 12721)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((237096067 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3655643 / 1000000000)) ^ 2) * ((1491053033 / 1000000000000000000000000)) + ((5049614911 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12721) : ℝ)) (√(26 / (10 * 12721) : ℝ)) d.D d.V d.P (√(tA 12721) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3655643 / 1000000000)) * (((136099707 / 62500000000000)) * ((38614155863 / 1000000000000000000))) + ((5049614911 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12721) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((237096067 / 50000000000000000000) : ℝ) + ((5049614911 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12721

namespace BstLean.Part266.Row12721
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12721 163 ∧
    0 ≤ (tableEnvelope C).f1 12721 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12721 163 ∧
    0 ≤ (tableEnvelope C).w1 12721 163 ∧ 0 ≤ (tableEnvelope C).w2 12721 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12721 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12721 163 ∧ 0 ≤ d.f1 12721 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12721 163 ∧ 0 ≤ d.w1 12721 163 ∧ 0 ≤ d.w2 12721 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12721 ≤ 2 * (228 / 100 : ℝ) / 12721 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12721 ≤ 2 * (370 / 100 : ℝ) / 12721 := by
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
    (completeRAData (tableEnvelope C) 12721 163).locationBound 12721 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12721 163).energyBound 12721 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12721 163) (d.f1 12721 163) d.f2 ≤
      32 * (((182552463 / 40000000000000000) : ℝ) + (152256481 / 100000000000000000) + (45743627 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12721 163) (d.w1 12721 163)
      (d.w2 12721 163) ≤
      32 * (((364826993 / 20000000000000000000) : ℝ) + (64891859 / 5000000000000000000) + (237098513 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12721 163) (d.f1 12721 163) d.f2 ≤
      ((182552463 / 40000000000000000) : ℝ) ^ 2 + 2 * ((182552463 / 40000000000000000)) * ((152256481 / 100000000000000000)) * (126 / 100) +
      2 * (((152256481 / 100000000000000000)) ^ 2 + 2 * ((182552463 / 40000000000000000)) * ((45743627 / 125000000000000000))) +
      6 * ((152256481 / 100000000000000000)) * ((45743627 / 125000000000000000)) * (126 / 100) + 8 * ((45743627 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12721 163) (d.f1 12721 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12721 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12721 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12721 163) (d.f1 12721 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12721 163) (d.w1 12721 163) (d.w2 12721 163)
  have hwexpr0 : 0 ≤ d.w0 12721 163 + d.w1 12721 163 * √(π / 2) +
      2 * d.w2 12721 163 + energyR16 12721 *
      radiusPolynomialRoot16 (d.w0 12721 163) (d.w1 12721 163) (d.w2 12721 163) := by
    positivity
  constructor
  · change (12721 : ℝ) ^ 8 * (mA 12721 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12721 163) (d.f1 12721 163) d.f2 + locationR16 12721 *
        radiusPolynomialRoot16 (d.f0 12721 163) (d.f1 12721 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12721 : ℝ) ^ 8 * (mA 12721 : ℝ) ^ 8 *
        ((((182552463 / 40000000000000000) : ℝ) ^ 2 + 2 * ((182552463 / 40000000000000000)) * ((152256481 / 100000000000000000)) * (126 / 100) +
          2 * (((152256481 / 100000000000000000)) ^ 2 + 2 * ((182552463 / 40000000000000000)) * ((45743627 / 125000000000000000))) +
          6 * ((152256481 / 100000000000000000)) * ((45743627 / 125000000000000000)) * (126 / 100) + 8 * ((45743627 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12721) *
          (32 * (((182552463 / 40000000000000000) : ℝ) + (152256481 / 100000000000000000) + (45743627 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12721 : ℝ) ^ 16 *
      (d.w0 12721 163 + d.w1 12721 163 * √(π / 2) + 2 * d.w2 12721 163 +
        energyR16 12721 * radiusPolynomialRoot16 (d.w0 12721 163) (d.w1 12721 163)
          (d.w2 12721 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12721 : ℝ) ^ 16 *
        (((364826993 / 20000000000000000000) : ℝ) + ((64891859 / 5000000000000000000)) * (126 / 100) + 2 * ((237098513 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12721) *
          (32 * (((364826993 / 20000000000000000000) : ℝ) + (64891859 / 5000000000000000000) + (237098513 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12721

/-! A coarse bound on the actual paper statistics constant at dimension 12722. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12720 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12720 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12720 128 ≤ (12974 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12974 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12722) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12722 : ℕ))
    (by norm_num : (12722 : ℕ) ≤ 16384)
  have ht : paperTail256 12722 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12722 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12722 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12722 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12722 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12722 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12720 128 * √(2 / (12722 : ℝ)) *
      (√(12722 : ℝ) + paperT0 12722 + paperTail256 12722) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12722 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12722 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12722 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12720 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12720 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12722 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12722

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12722 (61 / 100) 163 (17 / (100 * 12722)) (26 / (10 * 12722)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12722 (61 / 100) 163 (17 / (100 * 12722)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (474080317 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1490584259 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5046409617 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12722 / 12722 * (61 / 100)) ^ 4 * inverseRadius8 (12722 - 1) /
            envelopeGap 12722 (61 / 100) 163 (17 / (100 * 12722)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12722

namespace BstLean.Part266.Row12722
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12722 163 ≤ (2281457951 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12722 163 ≤ (761132939 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22867321 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12722 163 ≤ (911852531 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12722 163 ≤ (1297531257 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12722 163 ≤ (237042603 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (474080317 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (474080317 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1490584259 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5046409617 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3655499 / 1000000000) : ℝ) ≤ √(17 / (100 * 12722) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12722) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (272167319 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3860808541 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12722) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12722) ≤ (55581417 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12722) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12722 * (163 : ℝ) ^ 2 + 26 / (10 * 12722) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12722) : ℝ)) (tA 12722 * 163 ^ 2 + 26 / (10 * 12722)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3655499 / 1000000000))) * ((474080317 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3655499 / 1000000000)) ^ 3) * ((1490584259 / 1000000000000000000000000))) + ((5046409617 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3655499 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12722) : ℝ)) d.D d.V d.P (√(tA 12722) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3655499 / 1000000000)) ^ 2 * (((272167319 / 125000000000000)) * ((3860808541 / 100000000000000000)))) + ((5046409617 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12722) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3655499 / 1000000000)) * ((474080317 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12722) : ℝ)) (tA 12722 * 163 ^ 2 + 26 / (10 * 12722)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((474080317 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3655499 / 1000000000)) ^ 2) * ((1490584259 / 1000000000000000000000000)) + ((5046409617 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12722) : ℝ)) (√(26 / (10 * 12722) : ℝ)) d.D d.V d.P (√(tA 12722) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3655499 / 1000000000)) * (((272167319 / 125000000000000)) * ((3860808541 / 100000000000000000))) + ((5046409617 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12722) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((474080317 / 100000000000000000000) : ℝ) + ((5046409617 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12722

namespace BstLean.Part266.Row12722
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12722 163 ∧
    0 ≤ (tableEnvelope C).f1 12722 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12722 163 ∧
    0 ≤ (tableEnvelope C).w1 12722 163 ∧ 0 ≤ (tableEnvelope C).w2 12722 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12722 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12722 163 ∧ 0 ≤ d.f1 12722 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12722 163 ∧ 0 ≤ d.w1 12722 163 ∧ 0 ≤ d.w2 12722 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12722 ≤ 2 * (228 / 100 : ℝ) / 12722 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12722 ≤ 2 * (370 / 100 : ℝ) / 12722 := by
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
    (completeRAData (tableEnvelope C) 12722 163).locationBound 12722 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12722 163).energyBound 12722 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12722 163) (d.f1 12722 163) d.f2 ≤
      32 * (((2281457951 / 500000000000000000) : ℝ) + (761132939 / 500000000000000000) + (22867321 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12722 163) (d.w1 12722 163)
      (d.w2 12722 163) ≤
      32 * (((911852531 / 50000000000000000000) : ℝ) + (1297531257 / 100000000000000000000) + (237042603 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12722 163) (d.f1 12722 163) d.f2 ≤
      ((2281457951 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2281457951 / 500000000000000000)) * ((761132939 / 500000000000000000)) * (126 / 100) +
      2 * (((761132939 / 500000000000000000)) ^ 2 + 2 * ((2281457951 / 500000000000000000)) * ((22867321 / 62500000000000000))) +
      6 * ((761132939 / 500000000000000000)) * ((22867321 / 62500000000000000)) * (126 / 100) + 8 * ((22867321 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12722 163) (d.f1 12722 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12722 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12722 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12722 163) (d.f1 12722 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12722 163) (d.w1 12722 163) (d.w2 12722 163)
  have hwexpr0 : 0 ≤ d.w0 12722 163 + d.w1 12722 163 * √(π / 2) +
      2 * d.w2 12722 163 + energyR16 12722 *
      radiusPolynomialRoot16 (d.w0 12722 163) (d.w1 12722 163) (d.w2 12722 163) := by
    positivity
  constructor
  · change (12722 : ℝ) ^ 8 * (mA 12722 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12722 163) (d.f1 12722 163) d.f2 + locationR16 12722 *
        radiusPolynomialRoot16 (d.f0 12722 163) (d.f1 12722 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12722 : ℝ) ^ 8 * (mA 12722 : ℝ) ^ 8 *
        ((((2281457951 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2281457951 / 500000000000000000)) * ((761132939 / 500000000000000000)) * (126 / 100) +
          2 * (((761132939 / 500000000000000000)) ^ 2 + 2 * ((2281457951 / 500000000000000000)) * ((22867321 / 62500000000000000))) +
          6 * ((761132939 / 500000000000000000)) * ((22867321 / 62500000000000000)) * (126 / 100) + 8 * ((22867321 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12722) *
          (32 * (((2281457951 / 500000000000000000) : ℝ) + (761132939 / 500000000000000000) + (22867321 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12722 : ℝ) ^ 16 *
      (d.w0 12722 163 + d.w1 12722 163 * √(π / 2) + 2 * d.w2 12722 163 +
        energyR16 12722 * radiusPolynomialRoot16 (d.w0 12722 163) (d.w1 12722 163)
          (d.w2 12722 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12722 : ℝ) ^ 16 *
        (((911852531 / 50000000000000000000) : ℝ) + ((1297531257 / 100000000000000000000)) * (126 / 100) + 2 * ((237042603 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12722) *
          (32 * (((911852531 / 50000000000000000000) : ℝ) + (1297531257 / 100000000000000000000) + (237042603 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12722

/-! A coarse bound on the actual paper statistics constant at dimension 12723. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12721 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12721 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12721 128 ≤ (12975 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12975 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12723) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12723 : ℕ))
    (by norm_num : (12723 : ℕ) ≤ 16384)
  have ht : paperTail256 12723 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12723 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12723 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12723 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12723 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12723 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12721 128 * √(2 / (12723 : ℝ)) *
      (√(12723 : ℝ) + paperT0 12723 + paperTail256 12723) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12723 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12723 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12723 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12721 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12721 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12723 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12723

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12723 (61 / 100) 163 (17 / (100 * 12723)) (26 / (10 * 12723)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12723 (61 / 100) 163 (17 / (100 * 12723)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (94793707 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1490115669 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5043206613 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12723 / 12723 * (61 / 100)) ^ 4 * inverseRadius8 (12723 - 1) /
            envelopeGap 12723 (61 / 100) 163 (17 / (100 * 12723)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12723

namespace BstLean.Part266.Row12723
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12723 163 ≤ (1140504233 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12723 163 ≤ (1521966211 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365805177 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12723 163 ≤ (227909321 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12723 163 ≤ (1297225081 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12723 163 ≤ (473973421 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (94793707 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (94793707 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1490115669 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5043206613 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((913839 / 250000000) : ℝ) ≤ √(17 / (100 * 12723) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12723) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2177081843 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19301008193 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12723) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12723) ≤ (6947131 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12723) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12723 * (163 : ℝ) ^ 2 + 26 / (10 * 12723) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12723) : ℝ)) (tA 12723 * 163 ^ 2 + 26 / (10 * 12723)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((913839 / 250000000))) * ((94793707 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((913839 / 250000000)) ^ 3) * ((1490115669 / 1000000000000000000000000))) + ((5043206613 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((913839 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12723) : ℝ)) d.D d.V d.P (√(tA 12723) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((913839 / 250000000)) ^ 2 * (((2177081843 / 1000000000000000)) * ((19301008193 / 500000000000000000)))) + ((5043206613 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12723) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((913839 / 250000000)) * ((94793707 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12723) : ℝ)) (tA 12723 * 163 ^ 2 + 26 / (10 * 12723)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((94793707 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((913839 / 250000000)) ^ 2) * ((1490115669 / 1000000000000000000000000)) + ((5043206613 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12723) : ℝ)) (√(26 / (10 * 12723) : ℝ)) d.D d.V d.P (√(tA 12723) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((913839 / 250000000)) * (((2177081843 / 1000000000000000)) * ((19301008193 / 500000000000000000))) + ((5043206613 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12723) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((94793707 / 20000000000000000000) : ℝ) + ((5043206613 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12723

namespace BstLean.Part266.Row12723
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12723 163 ∧
    0 ≤ (tableEnvelope C).f1 12723 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12723 163 ∧
    0 ≤ (tableEnvelope C).w1 12723 163 ∧ 0 ≤ (tableEnvelope C).w2 12723 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12723 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12723 163 ∧ 0 ≤ d.f1 12723 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12723 163 ∧ 0 ≤ d.w1 12723 163 ∧ 0 ≤ d.w2 12723 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12723 ≤ 2 * (228 / 100 : ℝ) / 12723 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12723 ≤ 2 * (370 / 100 : ℝ) / 12723 := by
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
    (completeRAData (tableEnvelope C) 12723 163).locationBound 12723 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12723 163).energyBound 12723 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12723 163) (d.f1 12723 163) d.f2 ≤
      32 * (((1140504233 / 250000000000000000) : ℝ) + (1521966211 / 1000000000000000000) + (365805177 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12723 163) (d.w1 12723 163)
      (d.w2 12723 163) ≤
      32 * (((227909321 / 12500000000000000000) : ℝ) + (1297225081 / 100000000000000000000) + (473973421 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12723 163) (d.f1 12723 163) d.f2 ≤
      ((1140504233 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1140504233 / 250000000000000000)) * ((1521966211 / 1000000000000000000)) * (126 / 100) +
      2 * (((1521966211 / 1000000000000000000)) ^ 2 + 2 * ((1140504233 / 250000000000000000)) * ((365805177 / 1000000000000000000))) +
      6 * ((1521966211 / 1000000000000000000)) * ((365805177 / 1000000000000000000)) * (126 / 100) + 8 * ((365805177 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12723 163) (d.f1 12723 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12723 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12723 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12723 163) (d.f1 12723 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12723 163) (d.w1 12723 163) (d.w2 12723 163)
  have hwexpr0 : 0 ≤ d.w0 12723 163 + d.w1 12723 163 * √(π / 2) +
      2 * d.w2 12723 163 + energyR16 12723 *
      radiusPolynomialRoot16 (d.w0 12723 163) (d.w1 12723 163) (d.w2 12723 163) := by
    positivity
  constructor
  · change (12723 : ℝ) ^ 8 * (mA 12723 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12723 163) (d.f1 12723 163) d.f2 + locationR16 12723 *
        radiusPolynomialRoot16 (d.f0 12723 163) (d.f1 12723 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12723 : ℝ) ^ 8 * (mA 12723 : ℝ) ^ 8 *
        ((((1140504233 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1140504233 / 250000000000000000)) * ((1521966211 / 1000000000000000000)) * (126 / 100) +
          2 * (((1521966211 / 1000000000000000000)) ^ 2 + 2 * ((1140504233 / 250000000000000000)) * ((365805177 / 1000000000000000000))) +
          6 * ((1521966211 / 1000000000000000000)) * ((365805177 / 1000000000000000000)) * (126 / 100) + 8 * ((365805177 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12723) *
          (32 * (((1140504233 / 250000000000000000) : ℝ) + (1521966211 / 1000000000000000000) + (365805177 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12723 : ℝ) ^ 16 *
      (d.w0 12723 163 + d.w1 12723 163 * √(π / 2) + 2 * d.w2 12723 163 +
        energyR16 12723 * radiusPolynomialRoot16 (d.w0 12723 163) (d.w1 12723 163)
          (d.w2 12723 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12723 : ℝ) ^ 16 *
        (((227909321 / 12500000000000000000) : ℝ) + ((1297225081 / 100000000000000000000)) * (126 / 100) + 2 * ((473973421 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12723) *
          (32 * (((227909321 / 12500000000000000000) : ℝ) + (1297225081 / 100000000000000000000) + (473973421 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12723

/-! A coarse bound on the actual paper statistics constant at dimension 12724. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12722 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12722 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12722 128 ≤ (12976 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12976 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12724) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12724 : ℕ))
    (by norm_num : (12724 : ℕ) ≤ 16384)
  have ht : paperTail256 12724 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12724 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12724 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12724 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12724 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12724 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12722 128 * √(2 / (12724 : ℝ)) *
      (√(12724 : ℝ) + paperT0 12724 + paperTail256 12724) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12724 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12724 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12724 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12722 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12722 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12724 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12724

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12724 (61 / 100) 163 (17 / (100 * 12724)) (26 / (10 * 12724)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12724 (61 / 100) 163 (17 / (100 * 12724)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (118464197 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1489647263 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5040005899 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12724 / 12724 * (61 / 100)) ^ 4 * inverseRadius8 (12724 - 1) /
            envelopeGap 12724 (61 / 100) 163 (17 / (100 * 12724)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12724

namespace BstLean.Part266.Row12724
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12724 163 ≤ (285070117 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12724 163 ≤ (95104217 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (365733339 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12724 163 ≤ (11392781 / 625000000000000000)
  w1 : (tableEnvelope C).w1 12724 163 ≤ (648459681 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12724 163 ≤ (473861671 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (118464197 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (118464197 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1489647263 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5040005899 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((913803 / 250000000) : ℝ) ≤ √(17 / (100 * 12724) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12724) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (68025787 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3859594879 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12724) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12724) ≤ (111145361 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12724) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12724 * (163 : ℝ) ^ 2 + 26 / (10 * 12724) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12724) : ℝ)) (tA 12724 * 163 ^ 2 + 26 / (10 * 12724)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((913803 / 250000000))) * ((118464197 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((913803 / 250000000)) ^ 3) * ((1489647263 / 1000000000000000000000000))) + ((5040005899 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((913803 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12724) : ℝ)) d.D d.V d.P (√(tA 12724) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((913803 / 250000000)) ^ 2 * (((68025787 / 31250000000000)) * ((3859594879 / 100000000000000000)))) + ((5040005899 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12724) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((913803 / 250000000)) * ((118464197 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12724) : ℝ)) (tA 12724 * 163 ^ 2 + 26 / (10 * 12724)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((118464197 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((913803 / 250000000)) ^ 2) * ((1489647263 / 1000000000000000000000000)) + ((5040005899 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12724) : ℝ)) (√(26 / (10 * 12724) : ℝ)) d.D d.V d.P (√(tA 12724) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((913803 / 250000000)) * (((68025787 / 31250000000000)) * ((3859594879 / 100000000000000000))) + ((5040005899 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12724) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((118464197 / 25000000000000000000) : ℝ) + ((5040005899 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12724

namespace BstLean.Part266.Row12724
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12724 163 ∧
    0 ≤ (tableEnvelope C).f1 12724 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12724 163 ∧
    0 ≤ (tableEnvelope C).w1 12724 163 ∧ 0 ≤ (tableEnvelope C).w2 12724 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12724 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12724 163 ∧ 0 ≤ d.f1 12724 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12724 163 ∧ 0 ≤ d.w1 12724 163 ∧ 0 ≤ d.w2 12724 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12724 ≤ 2 * (228 / 100 : ℝ) / 12724 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12724 ≤ 2 * (370 / 100 : ℝ) / 12724 := by
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
    (completeRAData (tableEnvelope C) 12724 163).locationBound 12724 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12724 163).energyBound 12724 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12724 163) (d.f1 12724 163) d.f2 ≤
      32 * (((285070117 / 62500000000000000) : ℝ) + (95104217 / 62500000000000000) + (365733339 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12724 163) (d.w1 12724 163)
      (d.w2 12724 163) ≤
      32 * (((11392781 / 625000000000000000) : ℝ) + (648459681 / 50000000000000000000) + (473861671 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12724 163) (d.f1 12724 163) d.f2 ≤
      ((285070117 / 62500000000000000) : ℝ) ^ 2 + 2 * ((285070117 / 62500000000000000)) * ((95104217 / 62500000000000000)) * (126 / 100) +
      2 * (((95104217 / 62500000000000000)) ^ 2 + 2 * ((285070117 / 62500000000000000)) * ((365733339 / 1000000000000000000))) +
      6 * ((95104217 / 62500000000000000)) * ((365733339 / 1000000000000000000)) * (126 / 100) + 8 * ((365733339 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12724 163) (d.f1 12724 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12724 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12724 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12724 163) (d.f1 12724 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12724 163) (d.w1 12724 163) (d.w2 12724 163)
  have hwexpr0 : 0 ≤ d.w0 12724 163 + d.w1 12724 163 * √(π / 2) +
      2 * d.w2 12724 163 + energyR16 12724 *
      radiusPolynomialRoot16 (d.w0 12724 163) (d.w1 12724 163) (d.w2 12724 163) := by
    positivity
  constructor
  · change (12724 : ℝ) ^ 8 * (mA 12724 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12724 163) (d.f1 12724 163) d.f2 + locationR16 12724 *
        radiusPolynomialRoot16 (d.f0 12724 163) (d.f1 12724 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12724 : ℝ) ^ 8 * (mA 12724 : ℝ) ^ 8 *
        ((((285070117 / 62500000000000000) : ℝ) ^ 2 + 2 * ((285070117 / 62500000000000000)) * ((95104217 / 62500000000000000)) * (126 / 100) +
          2 * (((95104217 / 62500000000000000)) ^ 2 + 2 * ((285070117 / 62500000000000000)) * ((365733339 / 1000000000000000000))) +
          6 * ((95104217 / 62500000000000000)) * ((365733339 / 1000000000000000000)) * (126 / 100) + 8 * ((365733339 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12724) *
          (32 * (((285070117 / 62500000000000000) : ℝ) + (95104217 / 62500000000000000) + (365733339 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12724 : ℝ) ^ 16 *
      (d.w0 12724 163 + d.w1 12724 163 * √(π / 2) + 2 * d.w2 12724 163 +
        energyR16 12724 * radiusPolynomialRoot16 (d.w0 12724 163) (d.w1 12724 163)
          (d.w2 12724 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12724 : ℝ) ^ 16 *
        (((11392781 / 625000000000000000) : ℝ) + ((648459681 / 50000000000000000000)) * (126 / 100) + 2 * ((473861671 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12724) *
          (32 * (((11392781 / 625000000000000000) : ℝ) + (648459681 / 50000000000000000000) + (473861671 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12724
